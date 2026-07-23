# GoSMT

GoSMT is a native Go+/Go SMT solver and compatibility project pinned against
Microsoft Z3 4.16.0 (`ddb49568d3520e99799e364fb22f35fc67d887b1`, MIT).
It does not bind to Z3: differential tests use Z3 as an oracle while released
artifacts remain pure generated Go.

The essential, solver-neutral surface lives in `goforge.dev/goplus/std/smt`:
sorted terms, exhaustive results, context-indexed models and proofs, checked
incremental scopes, temporary assumptions, minimized unsat cores, and native
Boolean, integer-difference, general exact-linear-integer, exact-linear-real,
and typed unary/binary EUF
solving, including finite, arbitrary-arity same-sort, mixed-sort, mutually
recursive, unary/multi-parameter, and mutually parametric algebraic datatypes
with exhaustive
Bool/Int/Real/bit-vector/datatype pattern matching—including constructor
selection from branch constraints—and typed field updates, plus Euclidean integer
division/modulo by nonzero constants,
plus bounded complete Boolean QF_DT branching and sound conjunctive
combination while those signatures remain
disjoint and fixed-point shared equality exchange for unary Real→Real EUF.
Strings include exact ground regular-language membership, constructive
symbolic, shared-conjunction, and bounded non-conjunctive witnesses,
equality-forced and singleton-intersection contradiction proofs, constructive
single-unknown, uniquely delimited, adjacent-symbol, repeated-symbol, and
canonically split bounded word equations with exact ground-equality
and code-point-length equality/inequality interaction, plus globally
backtracked shared-symbol systems with inline storage through eight equations
and exact overflow under a shared resource limit. Length, regex, and general
string-predicate constraints likewise remain inline through four entries per
family before exact overflow. The façade recognizes one-symbol
prefix/suffix equations directly. Compact relational length terms preserve
`len(x) = len(y)`, `<`, and `<=` without generic AST materialization, including
Boolean-nested constraints during bounded backtracking. Affine combinations
of lengths support exact addition, subtraction, and constant scaling, plus
regex-coupled candidate
selection including bounded Boolean predicates and string disequalities, the
core SMT-LIB regex, and globally backtracked contains/prefix/suffix constraints
algebra, and context-indexed GoSMT construction. The standard library keeps
regexes element-sort indexed and small Boolean-regex formulas in an inline
postfix representation.
Function arguments and results retain Go+ sort indices. The
solver-neutral SMT-LIB syntax lives
in `goforge.dev/goplus/std/smtlib`. This module adds Z3-shaped contexts,
SMT-LIB execution, theories, tactics, optimization, fixedpoint, compatibility,
and portfolio engineering.

This repository is at foundation stage; see [COMPATIBILITY.md](COMPATIBILITY.md)
for the versioned scope and [ROADMAP.md](ROADMAP.md) for the non-negotiable path
to broad Z3 functionality. Unsupported theories return `unknown`; they are not
silently approximated.
