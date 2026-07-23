# Roadmap

1. Typed hash-consed AST, symbols, contexts, immutable snapshots, diagnostics.
2. CDCL SAT with watched literals, VSIDS, restarts, clause learning, cores.
3. Congruence closure and Nelson–Oppen theory combination.
4. Exact rationals plus simplex/cuts for LRA/LIA and difference logic. LRA,
   difference logic, branch-and-bound QF_LIA, and bounded Boolean-QF_LIA
   foundations plus nonzero constant-divisor Euclidean div/mod are
   implemented; cutting planes and full shared-theory exchange remain.
5. Bit-blasting, arrays, algebraic datatypes, strings/sequences, floating point.
   Finite enumerations plus unary- and binary-self-recursive datatypes with
   indexed Go+ constructor witnesses, field-indexed selectors, recognizers,
   graph acyclicity, exact branching models, and SMT-LIB execution are
   implemented. Mixed-field/arity-above-two, mutually recursive, and
   parametric datatypes remain the next datatype layer.
6. Quantifiers, E-matching, MBQI, nonlinear arithmetic, transcendental bounds.
7. SMT-LIB 2.7 commands, models, proofs, cores, options, statistics.
8. Tactics/probes, Optimize/MaxSMT, fixedpoint/Horn clauses, portfolio solving.
9. Z3 differential farm, SMT-COMP corpus, proof/model validation, fuzz/race.
10. Per-family 2× throughput and 50% allocation reductions, independent consumer,
    versioned GoForge/pkg.go.dev release.

Performance is gated separately for construction, simplification, SAT, each
theory, incremental traces, parsing, model extraction, and optimization. No
aggregate score can compensate for a workload family below either target.
