(ns kotoba.sema
  "Stable public entry points for Kotoba source semantic analysis."
  (:require [kotoba.compiler.frontend :as frontend]
            [kotoba.compiler.schema :as schema]))

(def analyze
  "Analyze Kotoba source and return a validated HIR envelope."
  frontend/analyze)

(def read-forms
  "Read Kotoba source using the admitted reader profile."
  frontend/read-forms)

(def validate-schema-table!
  "Validate a named schema table and return it."
  schema/validate-table!)

(def schema-identities
  "Return stable nominal content identities for a schema table."
  schema/identities)

(def capability-registry frontend/capability-registry)
(def source-operation-registry frontend/source-operation-registry)
(def capability-id->name frontend/capability-id->name)
(def forbidden-heads frontend/forbidden-heads)
(def max-functions frontend/max-functions)
(def max-expression-nodes frontend/max-expression-nodes)
(def max-lowered-nodes frontend/max-lowered-nodes)
(def max-bindings frontend/max-bindings)
(def max-list-items frontend/max-list-items)
(def max-namespace-capabilities frontend/max-namespace-capabilities)
(def max-namespace-docstring-chars frontend/max-namespace-docstring-chars)
(def max-function-docstring-chars frontend/max-function-docstring-chars)
(def kernel-region-report frontend/kernel-region-report)
