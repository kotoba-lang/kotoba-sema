;; Admission and typing for reading a `:bytes` value.
;;
;; Until these operations, `bytes-operations` held one entry — a constructor
;; for the canonical empty value — so a guest could take a `:bytes` parameter,
;; hand it straight back, and observe nothing about it. Binary input was inert
;; inside the language.
;;
;; This namespace covers the FRONTEND half only: what is admitted, what is
;; rejected, and with which message. Execution lives in kotoba-kir and has its
;; own tests; a source form that analyzes here is not yet a form that runs.

(ns kotoba.compiler.bytes-read-operations-test
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [kotoba.compiler.frontend :as frontend]))

(defn- analyze [source]
  (frontend/analyze source))

(defn- rejection [source]
  (try (analyze source) ::admitted
       (catch clojure.lang.ExceptionInfo e (.getMessage e))))

(deftest reads-are-admitted
  (testing "length of a bytes parameter"
    (is (some? (analyze "(ns p (:export [f])) (defn f [b :bytes] :i64 (bytes-length b))"))))
  (testing "indexed read"
    (is (some? (analyze "(ns p (:export [f])) (defn f [b :bytes i :i64] :i64 (bytes-u8-at b i))"))))
  (testing "composed with the arithmetic a caller would actually write"
    ;; The shape a dequantiser needs: read a byte, split it into nibbles.
    (is (some? (analyze (str "(ns p (:export [lo hi]))"
                             "(defn lo [b :bytes i :i64] :i64 (bit-and (bytes-u8-at b i) 15))"
                             "(defn hi [b :bytes i :i64] :i64"
                             "  (bit-and (u64-shift-right (bytes-u8-at b i) 4) 15))"))))))

(deftest results-are-i64
  ;; A byte is a small integer here; there is no narrower scalar, and both
  ;; reads must be usable directly in i64 arithmetic without a conversion.
  (is (some? (analyze (str "(ns p (:export [f]))"
                           "(defn f [b :bytes] :i64 (+ (bytes-length b) (bytes-u8-at b 0)))")))))

(deftest the-first-argument-must-be-bytes
  (doseq [[label source] {"string" "(ns p (:export [f])) (defn f [s :string] :i64 (bytes-length s))"
                          "i64" "(ns p (:export [f])) (defn f [n :i64] :i64 (bytes-u8-at n 0))"}]
    (testing label
      (let [message (rejection source)]
        (is (not= ::admitted message))
        (is (str/includes? (str message) "expected bytes")
            (str "rejected, but not for the reason claimed: " message))))))

(deftest the-index-must-be-an-integer
  (let [message (rejection (str "(ns p (:export [f]))"
                                "(defn f [b :bytes s :string] :i64 (bytes-u8-at b s))"))]
    (is (not= ::admitted message))
    (is (str/includes? (str message) "expected i64") message)))

(deftest arity-is-checked
  (doseq [source ["(ns p (:export [f])) (defn f [b :bytes] :i64 (bytes-u8-at b))"
                  "(ns p (:export [f])) (defn f [b :bytes i :i64] :i64 (bytes-length b i))"]]
    (is (= "bytes operation arity mismatch" (rejection source)))))

(deftest the-empty-constructor-still-rejects-operands
  ;; Adding entries to the table must not loosen the one that was there.
  (is (= "bytes-empty does not accept operands"
         (rejection "(ns p (:export [f])) (defn f [b :bytes] :bytes (bytes-empty b))"))))
