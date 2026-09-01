(ns kotoba.compiler.affine
  "Is this vector binding used LINEARLY — at most once on every path, with a
  consuming update as its last use?

  ## Why the question is worth asking

  `vector-assoc` allocates. The native host says so in its own words: *every
  operation that changes an element allocates rather than mutates*, and
  `checked_vector_assoc` is a `memmove` of the whole vector followed by a bump
  into an arena that is never reclaimed. Two consequences, both measured
  rather than reasoned about:

  - one element write costs O(length)
  - the number of writes a vector may ever receive is
    `arena / length` — **a 16,384-item vector, the longest KIR admits, can be
    updated four times in the life of a program** (65,536 / 16,384)

  An order book is a struct of arrays with about a million slots per field and
  a write on every order. Both numbers are wrong for it by orders of
  magnitude, and neither is a safety property: `surface-status.edn` classifies
  the whole native vector entry `:implemented-partial`, and its `:state` entry
  says plainly that **the invariant is AMBIENT, not mutation itself**.

  ## What linearity buys, and why it is not a new semantics

  If a vector handle is dead after an update, updating it in place and
  allocating a copy are indistinguishable to every observer. So this analysis
  does not change what a program MEANS. It decides when the backend may lower
  `vector-assoc` to a store instead of a copy, which is why the answer has to
  be conservative: a wrong `true` here silently mutates a value somebody still
  holds.

  ## What conservative means here

  `false` for anything not obviously linear. The shapes admitted are the ones
  a struct-of-arrays actually writes:

      (let [v (vector-i64-new n)
            v (vector-assoc v 0 x)      ; shadows — the old v is dead
            v (vector-assoc v 1 y)]
        (vector-at v 0))

  A binding that is READ after being consumed, referenced twice on one path,
  returned, passed to a function, or captured is refused. Escape analysis for
  literals already exists next door in `kotoba.native.vector-region`; this is
  the same posture applied to the update path rather than to construction.

  ## Why it lives in the frontend

  It first landed in `kotoba-native`, next door to
  `kotoba.native.vector-region`, which is a similar-looking escape analysis.
  That was the wrong home: this reads SOURCE forms, `kotoba-sema` is what
  holds source, and a backend repo is not on `kotoba-sema`'s dependency path
  -- so the gate could never have been consulted from where the decision is
  made. Moved rather than duplicated."
  (:require [clojure.set :as set]))

(def consuming
  "Operations that make the vector they are given dead.

  `vector-drop` is here with the assoc family: it returns a view of a suffix,
  and a view whose parent is later written in place is a view of something
  else. Admitting it as non-consuming would make the one operation that
  ALIASES the safe one."
  '#{vector-assoc vector-f64-assoc vector-conj vector-f64-conj
     vector-drop vector-f64-drop})

(def reading
  "Operations that observe without consuming."
  '#{vector-count vector-f64-count vector-at vector-f64-at
     vector-get vector-f64-get nth})

(defn- sym-uses
  "How many times `target` appears as a bare symbol in `form`.

  Counted rather than detected, because `at most once` is the question and
  `appears at all` is a different one — a binding used twice on one path
  cannot be consumed by either use."
  [form target]
  (cond
    (= form target) 1
    (seq? form) (reduce + 0 (map #(sym-uses % target) form))
    (vector? form) (reduce + 0 (map #(sym-uses % target) form))
    (map? form) (reduce + 0 (map #(+ (sym-uses (key %) target)
                                     (sym-uses (val %) target)) form))
    (set? form) (reduce + 0 (map #(sym-uses % target) form))
    :else 0))

(defn- consuming-call?
  [form target]
  (and (seq? form)
       (contains? consuming (first form))
       (= target (second form))))

(defn- reading-call?
  [form target]
  (and (seq? form)
       (contains? reading (first form))
       (= target (second form))))

(defn- position-ok?
  "`target` may appear only as the FIRST argument of a vector operation.

  Anywhere else — an argument to something that is not a vector operation, a
  return value, an element being stored — is an escape: the handle reaches
  code this analysis cannot see, and code it cannot see may hold it."
  [form target]
  (cond
    (= form target) false
    (seq? form)
    (if (or (consuming-call? form target) (reading-call? form target))
      ;; The first argument is the vector; every other argument must not
      ;; mention it. `(vector-assoc v 0 v)` stores the handle into itself.
      (every? #(zero? (sym-uses % target)) (drop 2 form))
      (every? #(position-ok? % target) form))
    (vector? form) (every? #(position-ok? % target) form)
    (map? form) (every? #(and (position-ok? (key %) target)
                              (position-ok? (val %) target)) form)
    (set? form) (every? #(position-ok? % target) form)
    :else true))

(defn linear?
  "True when `target` may be updated in place inside `form`.

  Three conditions, and each of them is a way a wrong `true` would corrupt a
  live value:

  1. **at most one use** — two uses on one path means the second sees what the
     first consumed
  2. **every use is in vector-operation position** — anywhere else the handle
     escapes to code this cannot see
  3. **a consumed binding is not read afterwards** — enforced by 1, and stated
     because it is the property that matters"
  [form target]
  (and (<= (sym-uses form target) 1)
       (position-ok? form target)))

(defn- binding-pairs [bindings] (partition 2 bindings))

(defn linear-let-chain?
  "True when every rebinding of `name` in a `let` consumes the previous one.

  The shape a struct of arrays writes:

      (let [v (vector-i64-new n)
            v (vector-assoc v 0 x)
            v (vector-assoc v 1 y)]
        (vector-at v 0))

  Each `v` shadows the last, so the previous handle is unreachable the moment
  the new one exists — which is exactly the condition for the store to be
  in place. A binding that is read between two updates is still linear; one
  that is read AFTER its last update is too. What is not linear is a form that
  mentions the name twice in one initialiser, or anywhere outside a vector
  operation."
  [form name]
  (and (seq? form) (= 'let (first form)) (vector? (second form))
       (let [pairs (binding-pairs (second form))
             body (drop 2 form)
             inits (map second pairs)
             ;; Bindings OF this name. Two or more means at least one is a
             ;; consuming update of the one before it, which is the only shape
             ;; with anything to lower in place -- a single binding is a
             ;; construction nobody has written to yet.
             binds (filter #(= name (first %)) pairs)]
         (and (<= 2 (count binds))
              ;; Every initialiser that mentions the name must consume it, and
              ;; must do so linearly.
              (every? (fn [init]
                        (or (zero? (sym-uses init name))
                            (linear? init name)))
                      inits)
              (every? #(linear? % name) body)))))
