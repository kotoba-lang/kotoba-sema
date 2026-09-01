(ns kotoba.compiler.affine-test
  "A wrong `true` here silently mutates a value somebody still holds, so most
  of these assert refusals."
  (:require [clojure.test :refer [deftest is testing]]
            [kotoba.compiler.affine :as aff]))

;; ── the shape a struct of arrays writes ─────────────────────────────────────

(deftest a-shadowing-update-chain-is-linear
  ;; The order book's whole access pattern: allocate once, write by index,
  ;; each write shadowing the handle before it.
  (is (aff/linear-let-chain?
       '(let [v (vector-i64-new 1024)
              v (vector-assoc v 0 7)
              v (vector-assoc v 1 9)]
          (vector-at v 0))
       'v)))

(deftest reading-between-writes-is-still-linear
  (is (aff/linear-let-chain?
       '(let [v (vector-i64-new 8)
              v (vector-assoc v 0 (+ 1 2))
              v (vector-assoc v 1 3)]
          (vector-count v))
       'v)))

;; ── the refusals, one per way a live value could be corrupted ───────────────

(deftest two-uses-on-one-path-are-not-linear
  ;; The second use sees what the first consumed.
  (testing "both in the same initialiser"
    (is (not (aff/linear? '(vector-assoc v 0 (vector-at v 1)) 'v))))
  (testing "both in the body"
    (is (not (aff/linear? '(+ (vector-at v 0) (vector-at v 1)) 'v)))))

(deftest a-bare-reference-is-not-linear
  ;; Returning the handle, or handing it to something that is not a vector
  ;; operation, puts it somewhere this analysis cannot see.
  (is (not (aff/linear? 'v 'v)))
  (is (not (aff/linear? '(some-function v) 'v)))
  (is (not (aff/linear? '[v] 'v))))

(deftest storing-the-handle-into-itself-is-not-linear
  ;; `(vector-assoc v 0 v)` is the handle reaching an element slot, where a
  ;; later in-place write would be visible through a value nobody expected to
  ;; change.
  (is (not (aff/linear? '(vector-assoc v 0 v) 'v))))

(deftest a-view-consumes-its-parent
  ;; `vector-drop` returns a view of a suffix. Treating it as a read would
  ;; make the one operation that ALIASES the safe one -- a view whose parent
  ;; is later written in place is a view of something else.
  (is (contains? aff/consuming 'vector-drop))
  (is (not (contains? aff/reading 'vector-drop))))

(deftest a-chain-with-no-rebinding-is-not-a-chain
  ;; Nothing to lower in place: there is no consumed handle.
  (is (not (aff/linear-let-chain?
            '(let [v (vector-i64-new 4)] (vector-at v 0)) 'v))))

(deftest an-escaping-body-refuses-the-whole-chain
  (is (not (aff/linear-let-chain?
            '(let [v (vector-i64-new 4)
                   v (vector-assoc v 0 1)]
               (some-function v))
            'v))))

(deftest a-name-used-twice-in-one-initialiser-refuses
  (is (not (aff/linear-let-chain?
            '(let [v (vector-i64-new 4)
                   v (vector-assoc v (vector-at v 0) 1)]
               (vector-count v))
            'v))))

;; ── the analysis says nothing about unrelated names ─────────────────────────

(deftest another-binding-does-not-make-this-one-non-linear
  (is (aff/linear-let-chain?
       '(let [w (vector-i64-new 2)
              v (vector-i64-new 4)
              v (vector-assoc v 0 1)]
          (vector-at v 0))
       'v)))
