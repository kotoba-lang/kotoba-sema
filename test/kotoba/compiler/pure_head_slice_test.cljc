(ns kotoba.compiler.pure-head-slice-test
  "ADR-544 step 1: the pure S-expression heads admitted as DESUGARING source
  forms, and the ones that are not.

  Admitted, each onto machinery the frontend already had:

      (lam [params] body)     -> (fn [params] body)
      (app f a ...)           -> (f a ...)
      (ref name)              -> name
      (perform :kind/op v)    -> (cap-call :kind/op v)

  Not admitted: `rel`, `query`, `handle`. They are refused, and the tests
  below assert the refusal REASON, not just that something was thrown --
  `(rel x)` with an unbound `x` would be refused either way, so an assertion
  that only checks `threw?` would keep passing after `rel` landed.

  These run on BOTH runtimes. The first version of this file was `.cljc` but
  caught a bare `Exception` and was never registered in `run-tests.cljs`, so
  its ClojureScript half had never executed -- and that is exactly where the
  application bug this slice fixes lived: `((lam [x] (+ x 1)) n)` raised
  `Cannot create property 'closure_uid_...' on bigint '1'` under nbb (a call
  form used as a map key, hashing its own bigint literal) while the JVM
  refused the same program cleanly."
  (:require #?(:clj  [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer [deftest is testing] :include-macros true])
            [kotoba.sema :as sema]
            [kotoba.kir :as kir]))

(defn- unit [source] (str source "\n(defn main [] :i64 0)"))

(defn- refusal [source]
  (try (do (sema/analyze (unit source)) nil)
       (catch #?(:clj Throwable :cljs :default) e
         {:message (ex-message e)
          :code (:kotoba.error/code (ex-data e))
          :phase (:phase (ex-data e))})))

(defn- answer
  "Run `run` and return its value as a plain integer. `.kotoba` integers are
  bigints under ClojureScript, so the comparison is made in one width."
  [source arguments]
  (let [out (kir/execute (kir/lower (sema/analyze (unit source))) 'run arguments {})]
    #?(:clj (long out) :cljs (js/Number out))))

(defn- analyzed [source opts]
  (try {:ok (sema/analyze source opts)}
       (catch #?(:clj Throwable :cljs :default) e
         {:message (ex-message e) :code (:kotoba.error/code (ex-data e))})))

;; ---------------------------------------------------------------------------
;; lam / app -- slice 1, kept measured here

(deftest lam-is-a-fn-value
  (testing "bound to a local, called by name"
    (is (= 2 (answer "(defn run [n :i64] :i64 (let [f (lam [x] (+ x 1))] (f n)))" [1]))))
  (testing "captures its enclosing scope"
    (is (= 10 (answer "(defn run [n :i64] :i64 (let [y 9 f (lam [x] (+ x y))] (app f n)))" [1])))))

(deftest app-applies
  (testing "a top-level definition"
    (is (= 2 (answer (str "(defn inc1 [x :i64] :i64 (+ x 1))\n"
                          "(defn run [n :i64] :i64 (app inc1 n))")
                     [1]))))
  (testing "an operator with no arguments at all"
    (is (= 42 (answer "(defn run [n :i64] :i64 (+ n (app (lam [] 41))))" [1])))))

;; ---------------------------------------------------------------------------
;; The beta-redex: an application whose operator is the lambda itself.
;;
;; Both spellings lower to the same shape a `let`-bound closure call already
;; had, so this admits no new runtime behaviour -- only the spelling.

(deftest an-operator-may-be-the-lambda-itself
  (testing "pure spelling"
    (is (= 2 (answer "(defn run [n :i64] :i64 (app (lam [x] (+ x 1)) n))" [1]))))
  (testing "clojure-shaped spelling, which used to be an internal failure under cljs"
    (is (= 2 (answer "(defn run [n :i64] :i64 ((fn [x] (+ x 1)) n))" [1]))))
  (testing "two arguments"
    (is (= 11 (answer "(defn run [n :i64] :i64 (app (lam [x y] (+ x y)) n 10))" [1]))))
  (testing "no internal failure is reported for any of these"
    (doseq [source ["(defn run [n :i64] :i64 (app (lam [x] (+ x 1)) n))"
                    "(defn run [n :i64] :i64 ((fn [x] (+ x 1)) n))"]]
      (is (nil? (refusal source))
          (str "expected no refusal at all, got: " (pr-str (refusal source)))))))

;; ---------------------------------------------------------------------------
;; ref

(deftest ref-names-a-definition
  (testing "in operator position, directly"
    (is (= 2 (answer (str "(defn inc1 [x :i64] :i64 (+ x 1))\n"
                          "(defn run [n :i64] :i64 ((ref inc1) n))")
                     [1]))))
  (testing "as the operator of an app"
    (is (= 2 (answer (str "(defn inc1 [x :i64] :i64 (+ x 1))\n"
                          "(defn run [n :i64] :i64 (app (ref inc1) n))")
                     [1]))))
  (testing "nested"
    (is (= 3 (answer (str "(defn inc1 [x :i64] :i64 (+ x 1))\n"
                          "(defn run [n :i64] :i64 (app (ref inc1) (app (ref inc1) n)))")
                     [1])))))

(deftest ref-takes-exactly-one-simple-symbol
  (testing "a literal is refused by name, not by whatever trips over it later"
    (is (= :kotoba.error/pure-ref-argument
           (:code (refusal "(defn run [n :i64] :i64 (app (ref 1) n))")))))
  (testing "two names"
    (is (= :kotoba.error/pure-ref-argument
           (:code (refusal "(defn run [n :i64] :i64 (app (ref a b) n))")))))
  (testing "none"
    (is (= :kotoba.error/pure-ref-argument
           (:code (refusal "(defn run [n :i64] :i64 (app (ref) n))"))))))

;; ---------------------------------------------------------------------------
;; perform

(deftest perform-carries-exactly-cap-calls-authority
  (testing "same effect row and same named operation as the cap-call spelling"
    (let [pure (:ok (analyzed (str "(ns m (:capabilities #{:clock/now}))\n"
                                   "(defn run [] :i64 (perform :clock/now 0))\n"
                                   "(defn main [] :i64 (run))")
                              nil))
          shaped (:ok (analyzed (str "(ns m (:capabilities #{:clock/now}))\n"
                                     "(defn run [] :i64 (cap-call :clock/now 0))\n"
                                     "(defn main [] :i64 (run))")
                                nil))]
      (is (some? pure))
      (is (some? shaped))
      (is (= (:effects shaped) (:effects pure)))
      (is (= (:named-operations shaped) (:named-operations pure)))))
  (testing "an undeclared capability is refused, exactly as for cap-call"
    (is (some? (:code (refusal (str "(ns m (:capabilities #{:log/write}))\n"
                                    "(defn run [] :i64 (perform :clock/now 0))"))))))
  (testing "an unregistered capability is refused"
    (is (some? (:code (refusal "(defn run [] :i64 (perform :nope/nope 0))"))))))

(deftest perform-does-not-admit-the-wire-id-form
  ;; Numeric capability ids are the wire ABI. Admitting them as a source
  ;; spelling would make the pure surface carry a number whose meaning lives
  ;; in a registry the source cannot see.
  (testing "an integer id"
    (is (= :kotoba.error/pure-perform-capability
           (:code (refusal "(defn run [n :i64] :i64 (perform 7 n))")))))
  (testing "an unqualified keyword"
    (is (= :kotoba.error/pure-perform-capability
           (:code (refusal "(defn run [n :i64] :i64 (perform :now n))"))))))

(deftest pure-product-refuses-perform-and-names-the-head-the-author-wrote
  (let [pure (analyzed (str "(defn run [] :i64 (perform :clock/now 0))\n"
                            "(defn main [] :i64 (run))")
                       {:language-profile :pure-product})
        shaped (analyzed (str "(defn run [] :i64 (cap-call :clock/now 0))\n"
                              "(defn main [] :i64 (run))")
                         {:language-profile :pure-product})]
    (is (= :kotoba.error/pure-product-forbidden (:code pure)))
    (is (= :kotoba.error/pure-product-forbidden (:code shaped)))
    (is (= "form outside pure-product profile: perform" (:message pure)))
    (is (= "form outside pure-product profile: cap-call" (:message shaped)))))

(deftest lam-app-and-ref-are-inside-the-pure-product-profile
  (doseq [source ["(defn run [n :i64] :i64 (app (lam [x] (+ x 1)) n))\n(defn main [] :i64 (run 1))"
                  (str "(defn inc1 [x :i64] :i64 (+ x 1))\n"
                       "(defn run [n :i64] :i64 (app (ref inc1) n))\n"
                       "(defn main [] :i64 (run 1))")]]
    (is (some? (:ok (analyzed source {:language-profile :pure-product})))
        (str "should be admitted under :pure-product: "
             (pr-str (analyzed source {:language-profile :pure-product}))))))

;; ---------------------------------------------------------------------------
;; The heads that are NOT admitted, refused for the reason they are not.

(deftest rel-query-and-handle-have-no-lowering
  (doseq [head '[rel query handle]]
    (let [r (refusal (str "(defn run [n :i64] :i64 (" head " n))"))]
      (is (= :kotoba.error/subset-reject (:code r))
          (str head ": " (pr-str r)))
      (is (= "operation has no admitted lowering" (:message r))
          (str head " must be refused for HAVING NO LOWERING -- a refusal for "
               "any other reason would keep this test green after " head
               " landed. Got: " (pr-str r))))))

(deftest app-with-no-operator-is-refused-where-the-operator-is-missing
  (is (= :kotoba.error/pure-app-operator
         (:code (refusal "(defn run [n :i64] :i64 (app))")))))
