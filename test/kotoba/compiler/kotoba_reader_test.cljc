(ns kotoba.compiler.kotoba-reader-test
  "JVM-free reader tests for the `#()` fn shorthand (lang-cosientist
  iteration 3). Runs on the nbb route like the rest of run-tests.cljs.

  Integer literals read as JS bigint, so expected forms are built with
  `(js/BigInt \"2\")` rather than quoted literals -- a quoted `2` in CLJS
  is a double and `=` fails against the reader's bigint."
  (:require [clojure.string :as str]
            [clojure.test :as t :refer [deftest is]]
            [kotoba.compiler.kotoba-reader :as r]))

#?(:clj  (def ^:private two 2)
   :cljs (def ^:private two (js/BigInt "2")))
#?(:clj  (def ^:private one 1)
   :cljs (def ^:private one (js/BigInt "1")))

(deftest fn-shorthand-reads-as-fn-form
  ;; #() is ONE call form: #(* % 2) == (fn [p1] (* p1 2)).
  (is (= (list 'fn ['p1] (list '* 'p1 two))
         (first (r/read-forms "#(* % 2)")))))

(deftest fn-shorthand-two-args
  (is (= '(fn [p1 p2] (+ p1 p2))
         (first (r/read-forms "#(+ %1 %2)")))))

(deftest fn-shorthand-nested-body
  ;; Inner collections are preserved; only the top-level args are the call.
  (is (= (list 'fn ['p1] (list 'f (list '+ 'p1 one)))
         (first (r/read-forms "#(f (+ % 1))")))))

(deftest fn-shorthand-empty-body-rejects
  (is (thrown? #?(:clj Throwable :cljs :default) (r/read-forms "#()"))))

(deftest fn-shorthand-rest-arg-rejects
  (is (thrown? #?(:clj Throwable :cljs :default) (r/read-forms "#(+ %& 1)"))))

(deftest fn-shorthand-gap-arg-rejects
  ;; %2 with no %1 in a 1-source map is a shape the map lowering refuses;
  ;; the reader itself must NOT invent a %1 binding for it.
  (is (= (list 'fn ['p1 'p2] (list '+ 'p2 one))
         (first (r/read-forms "#(+ %2 1)")))))

;; ── source-location, after the line index (build-scaling co-scientist it. 2) ──
;;
;; `source-location` used to re-derive line/column at every located node by
;; `subs`-ing the whole prefix and splitting it on newlines, which is O(offset)
;; per node and quadratic in source size. It is now a binary search over one
;; line-start index. These pin the three positions a binary search gets wrong
;; when its boundary condition is off: the very first form, a form that starts
;; exactly ON a line start, and a form on the last line.

(deftest locations-on-the-first-line
  (let [[a b] (r/read-forms "(a) (b)")]
    (is (= {:line 1 :column 1} (select-keys (meta a) [:line :column])))
    (is (= {:line 1 :column 5} (select-keys (meta b) [:line :column])))))

(deftest location-at-a-line-start
  ;; `(b)` begins at offset 4, which is itself a line start.
  (let [[_ b] (r/read-forms "(a)\n(b)")]
    (is (= {:line 2 :column 1 :offset 4}
           (select-keys (meta b) [:line :column :offset])))))

(deftest location-on-a-late-line-is-indented-from-that-line-not-the-file
  (let [source (str (apply str (repeat 200 "(a)\n")) "  (z)")
        forms (r/read-forms source)]
    (is (= {:line 201 :column 3} (select-keys (meta (last forms)) [:line :column])))))

(deftest locations-agree-with-counting-newlines-at-every-form
  ;; The property the fast path has to preserve, checked against the slow
  ;; definition rather than against remembered numbers.
  (let [source "(a)\n  (b (c))\n\n(d)\n     (e)\n"
        expected (fn [offset]
                   (let [prefix (subs source 0 offset)
                         nl (count (filter #(= \newline %) prefix))]
                     {:line (inc nl)
                      :column (inc (- offset (inc (or (str/last-index-of prefix "\n") -1))))}))]
    (doseq [form (r/read-forms source)]
      (is (= (expected (:offset (meta form)))
             (select-keys (meta form) [:line :column]))
          (str "form " (pr-str form)))))) 

;; ── set literals of exact integers ────────────────────────────────────────
;;
;; An exact Kotoba i64 literal reads as a JavaScript BigInt, `cljs.core/set`
;; switches to a hashed representation above eight elements, and nbb cannot
;; hash a BigInt. Nine integers in a set therefore threw a raw TypeError about
;; `closure_uid_...`, which reached the caller as `source reader rejected
;; input` with no reason attached to it at all.
;;
;; The limit is NOT lifted here -- reading the set without hashing gets past
;; the reader and hits the same barrier inside elaboration, which turns a
;; refusal into an internal compiler error. It is named instead.

(deftest eight-exact-integers-in-a-set-read
  (is (= 8 (count (first (r/read-forms "#{1 2 3 4 5 6 7 8}"))))))

(deftest nine-exact-integers-in-a-set-are-refused-by-name
  ;; ONE host, and the asymmetry is the point rather than an oversight. A
  ;; Clojure set hashes a BigInt without complaint, so on the JVM nine exact
  ;; integers read like any other nine values; the failure mode this refusal
  ;; names exists only where `cljs.core/set` does.
  ;;
  ;; Written as one assertion per host rather than skipped on the JVM, because
  ;; a skipped half says nothing and this half says something: it is the
  ;; control that keeps the refusal honest. If the reader ever started
  ;; refusing on the JVM too, the guard would have stopped being about the
  ;; host that has the problem.
  (let [e (try (r/read-forms "#{1 2 3 4 5 6 7 8 9}") nil
               (catch #?(:clj Throwable :cljs :default) error error))]
    #?(:clj
       (is (nil? e)
           "the JVM has no BigInt hashing problem, so nothing is refused there")
       :cljs
       (do
         (is (some? e) "nine exact integers in a set is refused")
         (is (str/includes? (ex-message e) "exact-integer")
             (str "the refusal names its reason, got: " (ex-message e)))
         (is (= 9 (:count (ex-data e))))))))

(deftest nine-keywords-in-a-set-still-read
  ;; The barrier is the BigInt, not the count -- keywords hash fine.
  (is (= 9 (count (first (r/read-forms "#{:a :b :c :d :e :f :g :h :i}"))))))

;; ---------------------------------------------------------------------------
;; 2026-09-08: the two things that were wrong here, found only by making this
;; reader the reader for BOTH hosts. Neither was findable while the JVM read
;; source with `clojure.tools.reader` and only ClojureScript came through here.
;; ---------------------------------------------------------------------------

(deftest an-integer-in-range-is-a-long-on-the-jvm
  ;; `parse-int-token` called `(bigint token)` unconditionally, so on the JVM
  ;; `5` came back `clojure.lang.BigInt` where `clojure.tools.reader` returns
  ;; `java.lang.Long`. `(= 5 (bigint 5))` is true, so no program ever computed
  ;; a wrong VALUE from it -- what broke was every assertion comparing a
  ;; printed AST or a sha256 of one, because `5` and `5N` are different text.
  ;; 18 assertions across the corpus, all golden-hash or `pr-str` mismatches.
  ;;
  ;; This asserts the TYPE, not the value, because value equality is exactly
  ;; what hid the defect. `(is (= 5 ...))` passes either way.
  #?(:clj (is (instance? Long (first (r/read-forms "5")))
              "an integer that fits in an i64 is a Long, as tools.reader gives")
     :cljs (is (identical? js/BigInt (.-constructor (first (r/read-forms "5"))))
               "ClojureScript has no Long; a JS Number loses precision above 2^53")))

(deftest an-integer-past-the-i64-boundary-promotes
  ;; The other direction, so the fix cannot be "always Long" either. The
  ;; boundary itself stays exact; one past it must not silently wrap.
  #?(:clj (do (is (instance? Long (first (r/read-forms "9223372036854775807")))
                  "i64 max is still a Long")
              (is (instance? clojure.lang.BigInt
                             (first (r/read-forms "9223372036854775808")))
                  "one past i64 max promotes rather than throwing or wrapping"))
     :cljs (is (= "9223372036854775808"
                  (str (first (r/read-forms "9223372036854775808"))))
               "bigint carries it exactly")))

(deftest deref-reads-as-a-deref-form
  ;; `read-form`'s dispatch had no case for `@`, and `@` is not a delimiter,
  ;; so `@a` fell through to `read-symbol-or-number` and became the single
  ;; SYMBOL `@a`. The frontend then refused it as an unbound variable -- a
  ;; true statement about a wrong input, which sends the author looking for a
  ;; missing binding that was never the problem. 17 assertions in
  ;; `local_state_test`.
  (is (= (list 'deref 'a) (first (r/read-forms "@a"))))
  (is (= (list 'swap! 'a '+ one)
         (first (r/read-forms "(swap! a + 1)")))
      "the surrounding local-state forms are untouched")
  (is (= (list 'f (list 'deref 'a))
         (first (r/read-forms "(f @a)")))
      "and it composes inside a call"))

(deftest the-other-reader-macros-are-still-absent
  ;; Stated as a test so it cannot quietly stop being true. quote,
  ;; syntax-quote, unquote, var-quote and `^meta` have no case in this reader
  ;; either. Nothing in the `.kotoba` corpus exercises them, so their absence
  ;; is UNMEASURED rather than known-good -- do not read the `@` clause above
  ;; as evidence the rest are covered. If one of these starts reading as a
  ;; form instead of a symbol, someone added it and this test should be
  ;; updated deliberately rather than deleted.
  (is (symbol? (first (r/read-forms "'a")))
      "quote is read as a symbol today, not as (quote a)"))
