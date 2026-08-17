(ns kotoba.sema-test
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]]
            [kotoba.hir :as hir]
            [kotoba.sema :as sema]))

(deftest source-to-checked-hir
  (testing "untyped source produces the compatibility HIR profile"
    (let [result (sema/analyze "(defn main [] 42)")]
      (is (= :kotoba.hir/v2 (:format result)))
      (is (= 'main (:entry result)))
      (is (= :i64 (:result result)))
      (is (hir/valid? result))))
  (testing "typed source produces typed HIR"
    (let [result (sema/analyze "(defn main [] :string \"ok\")")]
      (is (= :kotoba.hir/v3 (:format result)))
      (is (= :string (get-in result [:functions 0 :result])))
      (is (hir/valid? result))))
  (testing "a bare bool parameter is a typed host boundary"
    (let [result (sema/analyze
                  "(ns example.predicates (:export [negate]))
                   (defn negate [value :bool witness :i64] :bool
                     (if value false true))")]
      (is (= :kotoba.hir/v3 (:format result)))
      (is (= [:bool :i64] (get-in result [:functions 0 :param-types])))
      (is (= :bool (get-in result [:functions 0 :result])))
      (is (hir/valid? result))))
  (testing "a bool expression without a typed parameter stays compatibility HIR"
    (let [result (sema/analyze "(defn main [] (= 1 1))")]
      (is (= :kotoba.hir/v2 (:format result)))
      (is (= :bool (get-in result [:functions 0 :result])))
      (is (hir/valid? result)))))

(deftest bytes-count-is-a-typed-pure-bytes-operation
  (let [result (sema/analyze
                "(ns example.bytes (:export [size]))
                 (defn size [value :bytes] :i64 (bytes-count value))")]
    (is (= '(bytes-count value) (get-in result [:functions 0 :body])))
    (is (= :i64 (get-in result [:functions 0 :result])))
    (is (empty? (get-in result [:functions 0 :effects])))
    (is (hir/valid? result)))
  (is (thrown-with-msg?
       clojure.lang.ExceptionInfo #"expected bytes, got i64"
       (sema/analyze
        "(ns example.bytes (:export [size]))
         (defn size [value :i64] :i64 (bytes-count value))"))))

(deftest bytes-at-is-a-typed-pure-unsigned-byte-read
  (testing "an indexed byte read is pure and yields i64"
    (let [result (sema/analyze
                  "(ns example.bytes (:export [head]))
                   (defn head [value :bytes] :i64 (bytes-at value 0))")]
      (is (= '(bytes-at value 0) (get-in result [:functions 0 :body])))
      (is (= :i64 (get-in result [:functions 0 :result])))
      (is (empty? (get-in result [:functions 0 :effects])))
      (is (hir/valid? result))))
  (testing "the index is an ordinary i64 expression, not only a literal"
    (let [result (sema/analyze
                  "(ns example.bytes (:export [at]))
                   (defn at [value :bytes index :i64] :i64 (bytes-at value index))")]
      (is (= '(bytes-at value index) (get-in result [:functions 0 :body])))
      (is (= :i64 (get-in result [:functions 0 :result])))
      (is (hir/valid? result))))
  (testing "the sequence operand must be bytes"
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"expected bytes, got i64"
         (sema/analyze
          "(ns example.bytes (:export [head]))
           (defn head [value :i64] :i64 (bytes-at value 0))"))))
  (testing "the index operand must be i64"
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"expected i64, got bytes"
         (sema/analyze
          "(ns example.bytes (:export [head]))
           (defn head [value :bytes] :i64 (bytes-at value value))"))))
  (testing "arity is fixed at two operands"
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"bytes-at requires a bytes operand and an index"
         (sema/analyze
          "(ns example.bytes (:export [head]))
           (defn head [value :bytes] :i64 (bytes-at value))")))
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"bytes-at requires a bytes operand and an index"
         (sema/analyze
          "(ns example.bytes (:export [head]))
           (defn head [value :bytes] :i64 (bytes-at value 0 1))")))))

(deftest bytes-slice-is-a-typed-pure-half-open-subrange
  (testing "a subrange of bytes is itself bytes, and is pure"
    (let [result (sema/analyze
                  "(ns example.bytes (:export [head]))
                   (defn head [value :bytes] :bytes (bytes-slice value 0 2))")]
      (is (= '(bytes-slice value 0 2) (get-in result [:functions 0 :body])))
      (is (= :bytes (get-in result [:functions 0 :result])))
      (is (empty? (get-in result [:functions 0 :effects])))
      (is (hir/valid? result))))
  (testing "the offsets are ordinary i64 expressions"
    (let [result (sema/analyze
                  "(ns example.bytes (:export [part]))
                   (defn part [value :bytes start :i64 end :i64] :bytes
                     (bytes-slice value start end))")]
      (is (= '(bytes-slice value start end) (get-in result [:functions 0 :body])))
      (is (= :bytes (get-in result [:functions 0 :result])))
      (is (hir/valid? result))))
  (testing "it composes with the other bytes operations"
    (let [result (sema/analyze
                  "(ns example.bytes (:export [tail]))
                   (defn tail [value :bytes] :bytes
                     (bytes-slice value 1 (bytes-count value)))")]
      (is (= :bytes (get-in result [:functions 0 :result])))
      (is (hir/valid? result))))
  (testing "the sequence operand must be bytes"
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"expected bytes, got i64"
         (sema/analyze
          "(ns example.bytes (:export [head]))
           (defn head [value :i64] :bytes (bytes-slice value 0 2))"))))
  (testing "both offsets must be i64"
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"expected i64, got bytes"
         (sema/analyze
          "(ns example.bytes (:export [head]))
           (defn head [value :bytes] :bytes (bytes-slice value value 2))")))
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"expected i64, got bytes"
         (sema/analyze
          "(ns example.bytes (:export [head]))
           (defn head [value :bytes] :bytes (bytes-slice value 0 value))"))))
  (testing "arity is fixed at three operands"
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"bytes-slice requires a bytes operand and two offsets"
         (sema/analyze
          "(ns example.bytes (:export [head]))
           (defn head [value :bytes] :bytes (bytes-slice value 0))")))
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"bytes-slice requires a bytes operand and two offsets"
         (sema/analyze
          "(ns example.bytes (:export [head]))
           (defn head [value :bytes] :bytes (bytes-slice value 0 1 2))")))))

(deftest bytes-concat-is-a-typed-pure-join
  (testing "joining two byte sequences yields bytes and stays pure"
    (let [result (sema/analyze
                  "(ns example.bytes (:export [twice]))
                   (defn twice [value :bytes] :bytes (bytes-concat value value))")]
      (is (= '(bytes-concat value value) (get-in result [:functions 0 :body])))
      (is (= :bytes (get-in result [:functions 0 :result])))
      (is (empty? (get-in result [:functions 0 :effects])))
      (is (hir/valid? result))))
  (testing "it composes with the other bytes operations"
    (let [result (sema/analyze
                  "(ns example.bytes (:export [rotate]))
                   (defn rotate [value :bytes] :bytes
                     (bytes-concat (bytes-slice value 1 3) (bytes-slice value 0 1)))")]
      (is (= :bytes (get-in result [:functions 0 :result])))
      (is (hir/valid? result))))
  (testing "the empty sequence is a lawful operand"
    (let [result (sema/analyze
                  "(ns example.bytes (:export [same]))
                   (defn same [value :bytes] :bytes (bytes-concat (bytes) value))")]
      (is (= :bytes (get-in result [:functions 0 :result])))
      (is (hir/valid? result))))
  (testing "both operands must be bytes"
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"expected bytes, got i64"
         (sema/analyze
          "(ns example.bytes (:export [j]))
           (defn j [value :bytes] :bytes (bytes-concat value (bytes-count value)))")))
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"expected bytes, got i64"
         (sema/analyze
          "(ns example.bytes (:export [j]))
           (defn j [value :i64] :bytes (bytes-concat value value))"))))
  (testing "arity is fixed at two operands"
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"bytes-concat requires two bytes operands"
         (sema/analyze
          "(ns example.bytes (:export [j]))
           (defn j [value :bytes] :bytes (bytes-concat value))")))
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"bytes-concat requires two bytes operands"
         (sema/analyze
          "(ns example.bytes (:export [j]))
           (defn j [value :bytes] :bytes (bytes-concat value value value))")))))

(deftest reader-and-schema-contracts
  (is (= 'defn (ffirst (sema/read-forms "(defn main [] 42)"))))
  (let [table {:app/item
               [:record :app/item
                [[:value :i64]
                 [:next [:option [:ref :app/item]]]]]}]
    (is (= table (sema/validate-schema-table! table)))
    (is (re-matches #"[0-9a-f]{64}"
                    (get (sema/schema-identities table) :app/item)))))

(deftest semantic-catalogs-are-on-the-classpath
  (is (some? (io/resource "kotoba/lang/capability-catalog.edn")))
  (is (some? (io/resource "kotoba/lang/guest-grammar.edn")))
  (is (seq sema/capability-registry))
  (is (seq sema/source-operation-registry)))

(deftest dataspace-transact-is-catalog-wire-id-24
  "ADR-2608154100: named dataspace/transact is wire id 24, contiguous with 1–23."
  (let [catalog (edn/read-string
                 (slurp (io/resource "kotoba/lang/capability-catalog.edn")))
        from-catalog (into {} (map (fn [[k e]] [k (:compiler-wire-id e)])
                                   (:capabilities catalog)))]
    (is (= 24 (get from-catalog :dataspace/transact)))
    (is (= 24 (get sema/capability-registry :dataspace/transact)))
    (is (= :dataspace/transact
           (get sema/source-operation-registry 'dataspace/transact)))
    (is (= (set (keys sema/capability-registry))
           (set (vals sema/source-operation-registry))))
    ;; 25/26 are stream/accept and stream/send (root ADR-2608150900). The
    ;; assertion is contiguity, not a fixed ceiling -- it moves when the
    ;; registry legitimately grows and fails when a gap is left.
    (is (= (range 1 27) (sort (vals sema/capability-registry)))
        "wire ids stay contiguous from 1; a gap means named source will reject")))

(deftest stream-ingress-is-catalog-wire-ids-25-and-26
  "root ADR-2608150900: a bidirectional frame stream, where http-ingress is one
  request paired to one reply. Frames in and frames out are separate wire ids
  because they are separate authorities."
  (let [catalog (edn/read-string
                 (slurp (io/resource "kotoba/lang/capability-catalog.edn")))
        from-catalog (into {} (map (fn [[k e]] [k (:compiler-wire-id e)])
                                   (:capabilities catalog)))]
    (is (= 25 (get from-catalog :stream/accept)))
    (is (= 26 (get from-catalog :stream/send)))
    (is (= 25 (get sema/capability-registry :stream/accept)))
    (is (= 26 (get sema/capability-registry :stream/send)))
    (is (= :stream/accept (get sema/source-operation-registry 'stream/accept)))
    (is (= :stream/send (get sema/source-operation-registry 'stream/send)))))

(deftest hearing-a-stream-is-not-permission-to-speak-into-it
  (testing "a guest that declares only accept gets only accept's effect"
    (let [hir (sema/analyze
               "(ns app (:capabilities #{:stream/accept}))
                (defn listen [s] (cap-call :stream/accept s))
                (defn main [] 0)")]
      (is (= #{[:cap/call 25]} (:effects hir)))))
  (testing "and declaring both yields both, separately"
    (let [hir (sema/analyze
               "(ns app (:capabilities #{:stream/accept :stream/send}))
                (defn listen [s] (cap-call :stream/accept s))
                (defn speak [f] (cap-call :stream/send f))
                (defn main [] 0)")]
      (is (= #{[:cap/call 25] [:cap/call 26]} (:effects hir))))))

(deftest named-dataspace-cap-call-resolves-to-wire-id-24
  (let [hir (sema/analyze
             "(ns app (:capabilities #{:dataspace/transact}))
              (defn publish [x] (cap-call :dataspace/transact x))
              (defn main [] 0)")]
    (is (= #{[:cap/call 24]} (:effects hir)))
    (is (= '(cap-call 24 x)
           (->> (:functions hir) (filter #(= 'publish (:name %))) first :body)))))

(deftest dataspace-source-forms-lower-to-one-typed-effect-kernel
  (let [hir (sema/analyze
             "(ns app (:capabilities #{:dataspace/transact}))
              (defn publish [x :document] (assert! x))
              (defn retract [x :document f :i64] (retract! x f))
              (defn subscribe [p :document] (observe! p))
              (defn enter [] (facet-enter!))
              (defn leave [f :i64] (facet-leave! f))
              (defn main [] 0)")
        bodies (into {} (map (juxt :name :body)) (:functions hir))]
    (is (= #{[:cap/call 24]} (:effects hir)))
    (is (= #{:dataspace/transact} (:named-operations hir)))
    (doseq [name '[publish retract subscribe enter leave]]
      (is (= 'typed-cap-call (first (get bodies name))))
      (is (= 24 (second (get bodies name)))))
    (is (= :assert (-> bodies (get 'publish) (nth 4) (nth 2))))
    (is (= 0 (-> bodies (get 'publish) (nth 4) (nth 3) last))
        "one-argument assertion is rooted in facet zero")
    (is (= :observe (-> bodies (get 'subscribe) (nth 4) (nth 2))))
    (is (= :facet-enter (-> bodies (get 'enter) (nth 4) (nth 2))))
    (is (= :facet-leave (-> bodies (get 'leave) (nth 4) (nth 2))))
    (let [result-type (nth (get bodies 'subscribe) 3)
          matches-case (some #(when (= :matches (first %)) %)
                             (nth result-type 2))]
      (is (= [[:bindings :document] [:notices :document]]
             (nth (second matches-case) 2))
          "observe! result carries delivered notices, not only a snapshot"))))

(deftest dataspace-source-forms-fail-closed
  (is (thrown-with-msg?
       clojure.lang.ExceptionInfo #"not declared in namespace :capabilities"
       (sema/analyze
        "(ns app (:capabilities #{:entropy/draw}))
         (defn publish [x :document] (assert! x))
         (defn main [] 0)")))
  (is (thrown-with-msg?
       clojure.lang.ExceptionInfo #"assert! requires an assertion document"
       (sema/analyze
        "(ns app (:capabilities #{:dataspace/transact}))
         (defn publish [] (assert!))")))
  (is (thrown-with-msg?
       clojure.lang.ExceptionInfo #"type mismatch"
       (sema/analyze
        "(ns app (:capabilities #{:dataspace/transact}))
         (defn publish [] (assert! (quot 1 0)))
         (defn main [] 0)")))
  (is (thrown-with-msg?
       clojure.lang.ExceptionInfo #"outside pure-product profile"
       (sema/analyze
        "(defn publish [x :document] (assert! x))"
        {:language-profile :pure-product}))))

(deftest cljs-fallback-is-kept-in-lockstep-with-catalog
  "CLJS cannot read the classpath resource; forgetting the fallback
   silently drops named dataspace/transact on that backend."
  (let [src (slurp (io/file "src/kotoba/compiler/frontend.cljc"))]
    (is (re-find #":dataspace/transact 24" src)
        "capability-registry-cljs-fallback must include wire id 24")))

(deftest undeclared-dataspace-capability-is-rejected
  (is (thrown-with-msg?
       clojure.lang.ExceptionInfo
       #"not declared in namespace :capabilities"
       (sema/analyze
        "(ns app (:capabilities #{:entropy/draw}))
         (defn publish [x] (cap-call :dataspace/transact x))
         (defn main [] 0)"))))

(deftest page-fault-evidence-operations-are-a-closed-kernel-surface
  (let [result (sema/analyze
                "(defn main []
                   (let [handler (kernel-page-fault-handler-address)
                         selector (kernel-read-cs)]
                     (kernel-load-idt handler 10)))")]
    (is (= :i64 (:result result)))
    (is (hir/valid? result))))

(deftest recoverable-page-fault-operations-have-sealed-arities
  (let [result (sema/analyze
                "(defn main []
                   (let [handler (kernel-page-fault-recovery-handler-address)
                         configured (kernel-configure-page-fault-recovery 4096 12272)
                         probe (kernel-probe-recoverable-guard-write)]
                     (+ handler configured probe)))")]
    (is (= :i64 (:result result)))
    (is (hir/valid? result))))

(deftest double-fault-ist-operations-have-sealed-arities
  (let [result (sema/analyze
                "(defn main []
                   (let [handler (kernel-double-fault-handler-address)
                         configured (kernel-configure-double-fault-ist 4096 12288)
                         loaded (kernel-load-gdt-tss 8192 10)
                         probe (kernel-probe-double-fault)]
                     (+ handler configured loaded probe)))")]
    (is (= :i64 (:result result)))
    (is (hir/valid? result))))

(deftest public-sema-facade-owns-consumer-entry-points
  (is (contains? sema/forbidden-heads 'eval))
  (is (every? pos? [sema/max-functions sema/max-expression-nodes
                    sema/max-lowered-nodes sema/max-bindings
                    sema/max-list-items sema/max-namespace-capabilities
                    sema/max-namespace-docstring-chars
                    sema/max-function-docstring-chars]))
  (is (map? (sema/kernel-region-report
             (sema/analyze "(defn main [] 42)"))))
  (with-redefs [sema/max-functions 1]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"function count"
                          (sema/analyze
                           "(defn helper [] 1) (defn main [] 42)")))))

(defn- result-of
  "The declared result type of `p` in SRC. `main` must be zero-arity, so the
  function under test is a helper beside it."
  [src]
  (let [r (sema/analyze (str src "\n(defn main [] 0)"))]
    (->> (:functions r) (filter #(= 'p (:name %))) first :result)))

(deftest string-predicates-are-bool-like-every-other-predicate
  ;; Profile 5 (compiler ADR 0191) typed comparisons and predicates as `:bool`
  ;; so `and`/`or`/`not` compose. It carried the arithmetic and generic
  ;; predicates and left `string=?` and `string-contains?` at `:i64`, in the
  ;; same frontend where the later `string-index-contains` returns `:bool`.
  (testing "a :bool-declared function may return one"
    (is (= :bool (result-of "(defn p [a :string b :string] :bool (string=? a b))")))
    (is (= :bool (result-of "(defn p [a :string] :bool (string-contains? a \"x\"))"))))
  (testing "and they compose, which is the whole reason profile 5 exists"
    (is (= :bool (result-of
                  "(defn p [a :string] :bool (and (string=? a \"x\") (string-contains? a \"y\")))"))))
  (testing "not, over a string predicate"
    (is (= :bool (result-of "(defn p [a :string b :string] :bool (not (string=? a b)))"))))
  (testing "an i64-declared function may no longer return one — this is the break"
    (is (thrown? clojure.lang.ExceptionInfo
                 (result-of "(defn p [a :string b :string] :i64 (string=? a b))"))))
  (testing "the migration ADR 0191 names is available: (if p 1 0)"
    (is (= :i64 (result-of
                 "(defn p [a :string b :string] :i64 (if (string=? a b) 1 0))")))))

(defn- function-named
  [result name]
  (->> (:functions result) (filter #(= name (:name %))) first))

(defn- form-tree [form]
  (tree-seq coll? seq form))

(defn- body-heads [form]
  (into [] (comp (filter seq?) (map first)) (form-tree form)))

(deftest option-some?-widens-from-option-i64-to-option-T
  ;; Bare `option-some?` (and the `some?` / `nil?` desugars that become it) is
  ;; typed `:option-i64`. Decision cores that store `[:option :string]` on a
  ;; record therefore have to write `option-some?-of` at every site — the same
  ;; tax `option-or` already pays by rewriting to `option-value-of`. This pass
  ;; is that rewrite: HIR still carries the typed `-of` form native admits.
  (testing "option-some? on [:option :string] is :bool and lowers to -of"
    (let [result (sema/analyze
                  (str "(defn p [v [:option :string]] :bool (option-some? v))\n"
                       "(defn main [] 0)"))
          p (function-named result 'p)]
      (is (hir/valid? result))
      (is (= :bool (:result p)))
      (is (some #{'option-some?-of} (body-heads (:body p))))
      (is (not-any? #{'option-some?} (body-heads (:body p))))))
  (testing "option-value on [:option :string] lowers to option-value-of"
    (let [p (function-named
             (sema/analyze
              (str "(defn p [v [:option :string]] :string (option-value v \"none\"))\n"
                   "(defn main [] 0)"))
             'p)]
      (is (= :string (:result p)))
      (is (some #{'option-value-of} (body-heads (:body p))))
      (is (not-any? #{'option-value} (body-heads (:body p))))))
  (testing "some? and nil? follow, because they desugar to option-some?"
    (let [some-p (function-named
                  (sema/analyze
                   (str "(defn p [v [:option :string]] :bool (some? v))\n"
                        "(defn main [] 0)"))
                  'p)
          nil-p (function-named
                 (sema/analyze
                  (str "(defn p [v [:option :string]] :bool (nil? v))\n"
                       "(defn main [] 0)"))
                 'p)]
      (is (= :bool (:result some-p)))
      (is (some #{'option-some?-of} (body-heads (:body some-p))))
      (is (= :bool (:result nil-p)))
      (is (some #{'option-some?-of} (body-heads (:body nil-p))))))
  (testing "and of two record option-string fields is :bool, without (if … true false)"
    (let [p (function-named
             (sema/analyze
              "(ns example.actor
                 (:schemas {:example/actor
                            [:record :example/actor
                             [[:endpoint [:option :string]]
                              [:region [:option :string]]]]})
                 (:export [p]))
               (defn p [a [:ref :example/actor]] :bool
                 (and (option-some? (record-get a :endpoint))
                      (option-some? (record-get a :region))))")
             'p)]
      (is (= :bool (:result p)))
      (is (some #{'option-some?-of} (body-heads (:body p))))
      (is (not-any? #{'option-some?} (body-heads (:body p))))
      (is (not-any? true? (form-tree (:body p)))
          "the (if pred true false) wrap is the stale self-restriction this removes")))
  (testing "legacy :option-i64 keeps the bare form — KIR execute still uses it"
    (let [p (function-named
             (sema/analyze
              (str "(defn p [v :option-i64] :bool (option-some? v))\n"
                   "(defn main [] 0)"))
             'p)]
      (is (= :bool (:result p)))
      (is (some #{'option-some?} (body-heads (:body p))))
      (is (not-any? #{'option-some?-of} (body-heads (:body p))))))
  (testing "rewrite leak still fails closed: option-some? remains option-i64-only"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo
                          #"expected option-i64"
                          (sema/analyze
                           "(defn p [v :i64] :bool (option-some? v))\n(defn main [] 0)")))))
