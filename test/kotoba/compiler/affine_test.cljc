(ns kotoba.compiler.affine-test
  "A wrong `true` here silently mutates a value somebody still holds, so most
  of these assert refusals."
  (:require [clojure.test :refer [deftest is testing]]
            [kotoba.compiler.affine :as aff]))

;; ── the shape a struct of arrays writes ─────────────────────────────────────

(deftest a-threaded-let-is-linear
  ;; Distinct names, because Kotoba refuses a rebound one: `amu check` on a
  ;; `let` that binds `v` twice answers `duplicate let binding` (measured
  ;; 2026-09-01, amu e96dd8c6). The first version of this analysis looked for
  ;; exactly that shape and would have been a gate nothing could pass.
  (is (aff/linear-let-thread?
       '(let [a (vector-new 1 2 3)
              b (vector-assoc a 0 9)]
          (vector-at b 0))
       '[a b])))

(deftest a-longer-thread-is-linear
  (is (aff/linear-let-thread?
       '(let [a (vector-new 0 0 0)
              b (vector-assoc a 0 7)
              c (vector-assoc b 1 9)]
          (vector-count c))
       '[a b c])))

(deftest a-name-read-after-being-consumed-is-not-linear
  ;; `a` is consumed by `b` and then read again. An in-place store would be
  ;; visible through a handle somebody still holds.
  (is (not (aff/linear-let-thread?
            '(let [a (vector-new 1 2 3)
                   b (vector-assoc a 0 9)]
               (+ (vector-at b 0) (vector-at a 0)))
            '[a b]))))

;; ── the shape Kotoba actually uses ──────────────────────────────────────────

(deftest a-parameter-threaded-through-tail-recursion-is-linear
  ;; `let` cannot rebind, so a loop threads the handle through a parameter.
  ;; `v` appears in both arms of the `if` and only one arm runs, so this is
  ;; ONE use per path -- which the analysis only sees if alternatives are
  ;; counted as alternatives rather than summed.
  (is (aff/linear-parameter?
       '(if (>= i n)
          (vector-at v 0)
          (go (vector-assoc v 0 i) (+ i 1) n))
       'v)))

(deftest two-uses-in-one-arm-is-still-not-linear
  ;; The maximum over arms must not hide a sum inside one of them.
  (is (not (aff/linear-parameter?
            '(if (>= i n)
               (+ (vector-at v 0) (vector-at v 1))
               (go (vector-assoc v 0 i) (+ i 1) n))
            'v))))

(deftest a-use-in-the-test-counts-on-every-path
  ;; The condition runs whichever arm is taken, so a use there plus a use in
  ;; an arm is two uses on one path.
  (is (not (aff/linear-parameter?
            '(if (> (vector-at v 0) n)
               0
               (go (vector-assoc v 0 i) (+ i 1) n))
            'v))))

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

(deftest a-single-binding-is-not-a-thread
  ;; Nothing to lower in place: no handle is consumed.
  (is (not (aff/linear-let-thread?
            '(let [a (vector-new 1 2)] (vector-at a 0)) '[a]))))

(deftest an-escaping-body-refuses-the-whole-thread
  (is (not (aff/linear-let-thread?
            '(let [a (vector-new 1 2)
                   b (vector-assoc a 0 1)]
               (some-function b))
            '[a b]))))

(deftest a-name-used-twice-in-one-initialiser-refuses
  (is (not (aff/linear-let-thread?
            '(let [a (vector-new 1 2)
                   b (vector-assoc a (vector-at a 0) 1)]
               (vector-count b))
            '[a b]))))

;; ── the analysis says nothing about unrelated names ─────────────────────────

(deftest an-unrelated-binding-does-not-make-this-one-non-linear
  (is (aff/linear-let-thread?
       '(let [w (vector-new 9)
              a (vector-new 1 2)
              b (vector-assoc a 0 1)]
          (vector-at b 0))
       '[a b])))

(deftest the-bang-form-consumes-like-the-one-it-replaces
  ;; It was missing from `consuming`, which made every linear program fail the
  ;; gate that exists to admit it -- and fail with a message saying the handle
  ;; was used more than once when it was used exactly once.
  (is (contains? aff/consuming 'vector-assoc!))
  (is (aff/linear-parameter?
       '(if (>= i n)
          (vector-at v 0)
          (go (vector-assoc! v 0 i) (+ i 1) n))
       'v))
  (is (not (aff/linear-parameter?
            '(+ (vector-at v 1) (vector-at (vector-assoc! v 0 i) 0))
            'v))))

;; The gate calls `linear?`, not the two predicates above. Those were tested
;; in isolation and passed, while `check-affine-writes!` -- the only caller --
;; consulted neither, so nothing here covered the decision that is actually
;; made. Measured 2026-09-01: `amu check` refused a correctly threaded
;; program, naming the handle as "used more than once", because `sym-uses`
;; counted the `let` BINDER as a use and `position-ok?` read the bare name in
;; the binding vector as an escape. Two independent reasons, both of which
;; made every let-bound handle unadmittable. These pin the live path.

(deftest a-let-binder-is-not-a-use-of-the-name
  (let [form '(do (let [v (vector-alloc 4)
                        a (vector-assoc! v 0 1)
                        b (vector-assoc! a 1 2)]
                    (vector-at b 0)))]
    (testing "the threaded handles are admitted"
      (is (aff/linear? form 'v))
      (is (aff/linear? form 'a)))))

(deftest a-let-bound-handle-written-twice-is-refused
  (is (not (aff/linear? '(do (let [v (vector-alloc 4)
                                   a (vector-assoc! v 0 1)
                                   b (vector-assoc! v 1 2)]
                               (vector-at b 0)))
                        'v))))

(deftest a-let-bound-handle-read-after-being-consumed-is-refused
  (is (not (aff/linear? '(do (let [v (vector-alloc 4)
                                   a (vector-assoc! v 0 1)]
                               (vector-at v 0)))
                        'v))))

(deftest a-let-bound-handle-that-escapes-is-refused
  ;; Not a vector operation, so the analysis cannot see who keeps it.
  (is (not (aff/linear? '(do (let [v (vector-alloc 4)
                                   a (vector-assoc! v 0 1)]
                               (keeper v)))
                        'v))))

;; ── fused read-modify-write: `v[k] += delta` has no other expression ───────
;;
;; `lvl-qty[k] += qty` (superproject ADR-2609010500; `torihiki.book/slab/add!`,
;; two call sites) has no expression in Kotoba except
;; `(vector-assoc! v k (+ (vector-at v k) delta))` -- two separate calls,
;; which `sym-uses` counted as two uses and `position-ok?` counted as an
;; escape (the value argument mentions `v`). Both refused it correctly under
;; the OLD rule, because the old rule could not tell this shape apart from an
;; unrelated double use. Measured on unmodified `kotoba-sema` (2026-09-01,
;; before this file's `fused-rmw?`): `kotoba.sema/analyze` on
;;
;;     (defn add! [v :vector-i64 k :i64 delta :i64] :vector-i64
;;       (vector-assoc! v k (+ (vector-at v k) delta)))
;;
;; throws `vector-assoc! requires a linear handle: v is used more than once
;; on some path through add!, or reaches somewhere this cannot see` --
;; `sema/analyze` is the same entry point `kotoba.sema-test` uses, so this is
;; the live path, not a hypothetical one.

(deftest a-fused-read-then-write-at-the-same-index-is-one-use
  (is (aff/linear? '(vector-assoc! v k (+ (vector-at v k) delta)) 'v))
  (testing "the f64 sibling, since the rule is data-driven off consuming/reading"
    (is (aff/linear? '(vector-f64-assoc! v k (+ (vector-f64-at v k) delta)) 'v)))
  (testing "threaded through the tail-recursive parameter shape Kotoba uses"
    (is (aff/linear-parameter?
         '(if (>= i n)
            (vector-at v 0)
            (go (vector-assoc! v i (+ (vector-at v i) delta)) (+ i 1) n delta))
         'v))))

(deftest a-fused-write-at-one-index-does-not-license-a-read-at-another
  ;; A fused write at k1 proves nothing about a read at a DIFFERENT index --
  ;; admitting this would mean an in-place store at k1 could be visible
  ;; through whatever the mismatched read at k2 feeds.
  (is (not (aff/linear? '(vector-assoc! v k1 (+ (vector-at v k2) delta)) 'v))))

(deftest a-second-mention-of-the-handle-inside-the-update-is-not-fused
  ;; `fused-read-in-value` requires the qualifying read to be the ONLY
  ;; mention of `v` in the value expression. `(some reading-call-at-idx? ...)`
  ;; alone would have missed this: it only asks whether a qualifying read is
  ;; PRESENT, not whether anything else also mentions `v`.
  (is (not (aff/linear? '(vector-assoc! v k (+ (vector-at v k) (vector-count v))) 'v))))

(deftest a-handle-read-after-a-fused-write-consumed-it-is-still-refused
  (is (not (aff/linear? '(do (vector-assoc! v k (+ (vector-at v k) delta))
                             (vector-at v 0))
                        'v))))

(deftest two-fused-writes-on-one-path-are-still-two-uses
  ;; Each call is individually fused -- one use each -- but a path that runs
  ;; both is two uses of the same live handle, which is exactly what the
  ;; gate exists to refuse: the second write is unaware the first happened.
  (is (not (aff/linear? '(do (vector-assoc! v k1 (+ (vector-at v k1) d1))
                             (vector-assoc! v k2 (+ (vector-at v k2) d2)))
                        'v))))

(deftest the-index-argument-cannot-itself-be-the-handle
  ;; Degenerate self-index: `fused-read-in-value` alone would not catch this,
  ;; because the extra occurrence of `v` is in the OUTER form's index
  ;; position, not inside the value expression it inspects.
  (is (not (aff/linear? '(vector-assoc! v v (+ (vector-at v v) delta)) 'v))))

(deftest a-fused-call-is-not-mistaken-for-a-plain-assoc-when-the-value-is-not-a-call
  ;; `(vector-assoc! v 0 i)` -- the existing bang-form shape, value is a bare
  ;; symbol, not a compound read+op expression. `fused-rmw?` must fall
  ;; through to the plain count (which already admits this) rather than
  ;; misfire on it.
  (is (aff/linear-parameter?
       '(if (>= i n)
          (vector-at v 0)
          (go (vector-assoc! v 0 i) (+ i 1) n))
       'v)))
