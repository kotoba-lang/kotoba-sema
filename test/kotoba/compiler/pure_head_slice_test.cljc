(ns kotoba.compiler.pure-head-slice-test
  "ADR-544 step 1 first slice: `lam` and `app` admitted as desugaring source
  heads that lower onto the existing fn / application machinery. `rel query
  perform handle ref` stay rejected until their semantics land."
  (:require [clojure.test :refer [deftest is testing]]
            [kotoba.sema :as sema]))

(defn- analyze-or-throw [src]
  (try
    {:ok (sema/analyze src)}
    (catch Exception e
      {:threw (ex-message e)
       :code (get-in (ex-data e) [:kotoba.error/code])})))

(deftest lam-and-app-desugar-to-fn-and-application
  (testing "a lam bound to a local and applied via app compiles"
    (let [r (analyze-or-throw
             "(ns demo (:export [main])) (defn main [] :i64 (let [g (lam [x] x)] (app g 7)))")]
      (is (:ok r) (pr-str r))
      (is (= :i64 (get-in r [:ok :result]))) ; typed i64
      )))

(deftest lam-is-a-fn-value
  (testing "a lam in a let behaves as an fn value (capture + call)"
    (let [r (analyze-or-throw
             "(ns demo (:export [main])) (defn main [] :i64 (let [y 9 g (lam [x] (+ x y))] (app g 1)))")]
      (is (:ok r) (pr-str r)))))

(deftest rel-query-perform-handle-ref-stay-rejected
  (testing "the other pure heads have no lowering in this slice"
    (doseq [[head src] [["rel" "(ns a (:export [main])) (defn main [] :i64 (rel x))"]
                        ["query" "(ns a (:export [main])) (defn main [] :i64 (query x))"]
                        ["perform" "(ns a (:export [main])) (defn main [] :i64 (perform x))"]
                        ["handle" "(ns a (:export [main])) (defn main [] :i64 (handle x))"]
                        ["ref" "(ns a (:export [main])) (defn main [] :i64 (ref x))"]]]
      (let [r (analyze-or-throw src)]
        (is (and (:threw r) (some? (:code r)))
            (str head " should be rejected in this slice: " r))))))