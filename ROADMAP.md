# Roadmap

1. Typed hash-consed AST, symbols, contexts, immutable snapshots, diagnostics.
2. CDCL SAT with watched literals, VSIDS, restarts, clause learning, cores.
3. Congruence closure and Nelson–Oppen theory combination.
4. Exact rationals plus simplex/cuts for LRA/LIA and difference logic. LRA,
   difference logic, branch-and-bound QF_LIA, and bounded Boolean-QF_LIA
   foundations plus nonzero constant-divisor Euclidean div/mod are
   implemented; cutting planes and full shared-theory exchange remain.
5. Bit-blasting, arrays, algebraic datatypes, strings/sequences, floating point.
   Finite enumerations plus arbitrary-arity same-sort recursive datatypes with
   arity-indexed Go+ constructor vectors, bounded selector proofs,
   recognizers, graph acyclicity, exact n-ary models, and SMT-LIB execution are
   implemented. Mixed-sort Bool/Int/Real/bit-vector/Self fields, scalar product
   constructors, sort-refining selector cursors, exact models, context-indexed
   GoSMT construction, and SMT-LIB execution are implemented. Target-indexed
   cross-declaration references, productive mutually recursive groups,
   cross-sort acyclicity/models, and SMT-LIB `declare-datatypes` are
   implemented. Unary `par` families now monomorphize lazily into distinct
   concrete identities across scalar, datatype, and nested parametric
   arguments; qualified constructors, indexed recognizers, exact scalar
   selector models, exhaustive Bool/Int/Real/bit-vector/datatype `match` for
   both constructor-determined and unconstrained terms, and
   typed/SMT-LIB `update-field` agree with pinned Z3. Updates rebuild the
   selector's owning constructor, preserve every other constructor, work from
   symbolic recognizer evidence, and retain exact models. Multi-parameter
   families and mutually parametric groups remain.
6. Quantifiers, E-matching, MBQI, nonlinear arithmetic, transcendental bounds.
7. SMT-LIB 2.7 commands, models, proofs, cores, options, statistics.
8. Tactics/probes, Optimize/MaxSMT, fixedpoint/Horn clauses, portfolio solving.
9. Z3 differential farm, SMT-COMP corpus, proof/model validation, fuzz/race.
10. Per-family 2× throughput and 50% allocation reductions, independent consumer,
    versioned GoForge/pkg.go.dev release.

Performance is gated separately for construction, simplification, SAT, each
theory, incremental traces, parsing, model extraction, and optimization. No
aggregate score can compensate for a workload family below either target.
