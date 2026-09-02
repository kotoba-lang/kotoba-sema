(ns kotoba.compiler.guest-grammar-vendor-test
  "This repository carries a BYTE COPY of kotoba-lang's `lang/guest-grammar.edn`
  at `resources/kotoba/lang/guest-grammar.edn`, and it owns the frontend the
  file is supposed to describe. Two things can go wrong, and both had.

  ## Why the existing check could not see either

  kotoba-lang's `local-and-sibling-vendors-match-authority` compares its
  authority against `../amu`, `../kotoba`, `../kotoba-sema` and `../grammar`.
  Those paths exist only inside the west monorepo layout, each is guarded with
  `(when (.isFile ...))`, and an absent path is reported `:missing` and
  tolerated. In a single-repository clone it compares exactly one copy -- the
  authority's own -- and reports green.

  Measured 2026-09-03 on the four mains, before the resync wave: amu's copy was
  one change behind (580 lines against 601) and kotoba's two copies were two
  hundred lines behind. Three of four had drifted, and the check written to
  find drift said nothing. ADR-2608136000's shape: a check that could not run
  returns the value of a check that ran and found nothing wrong.

  ## What this file checks instead

  1. The copy this repository ships is byte-identical to the authority of the
     2026-09-03 wave, by pinned sha256. That literal is pinned in FOUR
     repositories (kotoba-lang, amu, kotoba, here), so an authority edit that
     is not carried to all four goes red in the ones left behind -- including
     in a clone with no sibling to compare against.
  2. The copy AGREES WITH THE FRONTEND. `:admitted-builtins` must name exactly
     the heads `kernel-memory-operations`, `slice-value-operations` and
     `kernel-privileged-operations` admit. This is the check no other
     repository can make, because the frontend lives here.

  Measured 2026-09-03: the authority named THREE kernel heads
  (`kernel-load-u8`, `kernel-store-u8`, `kernel-boot-info`) while this
  frontend admitted 114 -- 115 since fwstore's `kernel-uefi-alloc-region`.
  Nothing here, in amu or in kotoba-lang reads
  `:admitted-builtins`, and nothing anywhere reads it to decide what the
  COMPILER admits -- the tables below do that. Its one reader is
  `kotoba.grammar/admitted-heads` in kotoba-lang/kotoba's vendored loader,
  where a missing head is reported as `:unknown-form`. So the understatement
  cost one repository 112 false `:unknown-form` reports and nothing failed,
  through eight widenings of the tables it describes.

  ## The one thing this file cannot do

  Only one copy of `kotoba/lang/guest-grammar.edn` is on this repository's
  classpath: its own. None of `artifact`, `kotoba-hir` or `kotoba-kir` carries
  one. So the `COMPARED` count here is 1 and the cross-repository half is done
  by the pinned digest, not by a comparison. amu and kotoba each see two and
  three copies respectively and compare them across their pins."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.set :as set]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [kotoba.compiler.frontend :as frontend]
            [kotoba.sema :as sema]))

(def authority-grammar-sha256
  "sha256 of kotoba-lang `lang/guest-grammar.edn` at the 2026-09-03 resync
  wave. Change it only as part of that wave, in all four repositories."
  "6e1202fd23bc5a2ed6ef432114585c1813f5143d643eb4c8ee9a00b6e798b922")

(def ^:private resource-path "kotoba/lang/guest-grammar.edn")

(defn- sha256-hex [^bytes bs]
  (let [d (.digest (java.security.MessageDigest/getInstance "SHA-256") bs)]
    (apply str (map #(format "%02x" %) d))))

(defn- classpath-copies
  "Every copy of the grammar resource on this classpath, as [url bytes]. Not
  `io/resource`, which answers with the FIRST and so cannot see a second."
  []
  (->> (enumeration-seq (.getResources (clojure.lang.RT/baseLoader) resource-path))
       (mapv (fn [url]
               [(str url)
                (with-open [in (.openStream url)]
                  (.readAllBytes in))]))))

(defn- head-names [x]
  (into #{} (map name) x))

(defn- frontend-kernel-heads []
  ;; Through the same public accessor a CONSUMER has to use
  ;; (`kotoba.sema/kernel-operation-heads`), not the three tables directly.
  ;; The tables are still asserted below, because this repository owns them
  ;; and an accessor that silently lost a family would otherwise pass.
  (head-names sema/kernel-operation-heads))

(defn- grammar-kernel-heads [grammar]
  (into #{} (filter #(or (str/starts-with? % "kernel-")
                         (str/starts-with? % "slice-")))
        (head-names (:admitted-builtins grammar))))

(deftest the-vendored-copy-is-the-authority-of-the-resync-wave
  (let [copies (classpath-copies)]
    (println (format "COMPARED\t%d\tclasspath copies of %s" (count copies) resource-path))
    (is (pos? (count copies))
        "the grammar resource is not on the classpath at all; this run measured
         nothing, which is not the same as finding nothing wrong")
    (doseq [[url bytes] copies]
      (let [actual (sha256-hex bytes)]
        (is (= authority-grammar-sha256 actual)
            (str "vendored grammar drifted from the authority\n"
                 "  copy     " url "\n"
                 "  expected " authority-grammar-sha256 "\n"
                 "  actual   " actual "\n"
                 "Resync from kotoba-lang lang/guest-grammar.edn and carry the"
                 " digest to kotoba-lang, amu, kotoba-sema and kotoba together."))))))

(deftest the-grammar-names-exactly-the-kernel-heads-this-frontend-admits
  (let [grammar (edn/read-string (slurp (io/resource resource-path)))
        declared (grammar-kernel-heads grammar)
        admitted (frontend-kernel-heads)
        missing (set/difference admitted declared)
        extra (set/difference declared admitted)]
    (println (format "SCANNED\t%d\tkernel heads admitted by the frontend (%d declared by the grammar)"
                     (count admitted) (count declared)))
    (is (pos? (count admitted))
        "the frontend admits no kernel head at all; the tables were not read")
    (is (empty? missing)
        (str "the frontend admits heads the authority does not name: "
             (pr-str (sort missing))))
    (is (empty? extra)
        (str "the authority names heads the frontend does not admit: "
             (pr-str (sort extra))))
    (testing "the accessor is the union of the three tables, so a family
              dropped from it -- or a table emptied by a bad merge -- is not a
              pass"
      (is (= admitted
             (head-names (concat (keys frontend/kernel-memory-operations)
                                 (keys frontend/slice-value-operations)
                                 (keys frontend/kernel-privileged-operations))))))
    (testing "and the tables are non-empty"
      (is (= 53 (count frontend/kernel-memory-operations)))
      (is (= 8 (count frontend/slice-value-operations)))
      ;; fwstore: 54 since .
      (is (= 54 (count frontend/kernel-privileged-operations))))))
