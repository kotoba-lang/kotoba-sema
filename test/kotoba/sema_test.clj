(ns kotoba.sema-test
  (:require [clojure.test :refer [deftest is testing]]
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
  (is (some? (clojure.java.io/resource
              "kotoba/lang/capability-catalog.edn")))
  (is (some? (clojure.java.io/resource
              "kotoba/lang/guest-grammar.edn")))
  (is (seq sema/capability-registry))
  (is (seq sema/source-operation-registry)))

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

(deftest atomic-kernel-table-primitive-is-bounded-and-typed
  (let [hir (sema/analyze
             "(defn swap [base length index expected desired] (kernel-compare-exchange-u32 base length index expected desired)) (defn main [] 0)")
        swap (first (filter #(= 'swap (:name %)) (:functions hir)))]
    (is (= :i64 (:result swap)))
    (is (= '(kernel-compare-exchange-u32 base length index expected desired)
           (:body swap))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"arity mismatch"
        (sema/analyze
         "(defn main [] (kernel-compare-exchange-u32 4096 64 0 0))"))))

(deftest scheduler-domain-publication-is-a-typed-kernel-primitive
  (let [hir (sema/analyze
             "(defn publish [domain] (kernel-publish-current-domain domain)) (defn main [] 0)")
        publish (first (filter #(= 'publish (:name %)) (:functions hir)))]
    (is (= :i64 (:result publish)))
    (is (= '(kernel-publish-current-domain domain) (:body publish))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"arity mismatch"
        (sema/analyze
         "(defn main [] (kernel-publish-current-domain))"))))

(deftest value-runtime-capability-table-is-kernel-private
  (let [hir (sema/analyze
             "(defn table [] (kernel-value-runtime-capability-table)) (defn main [] 0)")
        table (first (filter #(= 'table (:name %)) (:functions hir)))]
    (is (= :i64 (:result table)))
    (is (= '(kernel-value-runtime-capability-table) (:body table)))))

(deftest value-runtime-provider-regions-are-kernel-private
  (let [hir (sema/analyze
              "(defn queue [] (kernel-value-provider-queue))
              (defn arena [] (kernel-value-runtime-arena))
              (defn scratch [] (kernel-value-runtime-cas-scratch))
              (defn main [] 0)")
        by-name (into {} (map (juxt :name identity) (:functions hir)))]
    (is (= :i64 (:result (get by-name 'queue))))
    (is (= '(kernel-value-provider-queue) (:body (get by-name 'queue))))
    (is (= :i64 (:result (get by-name 'arena))))
    (is (= '(kernel-value-runtime-arena) (:body (get by-name 'arena))))
    (is (= :i64 (:result (get by-name 'scratch))))
    (is (= '(kernel-value-runtime-cas-scratch) (:body (get by-name 'scratch))))))

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
