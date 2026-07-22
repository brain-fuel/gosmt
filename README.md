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
solving, plus sound conjunctive combination while those signatures remain
disjoint and fixed-point shared equality exchange for unary Real→Real EUF.
Function arguments and results retain Go+ sort indices. The
solver-neutral SMT-LIB syntax lives
in `goforge.dev/goplus/std/smtlib`. This module adds Z3-shaped contexts,
SMT-LIB execution, theories, tactics, optimization, fixedpoint, compatibility,
and portfolio engineering.

This repository is at foundation stage; see [COMPATIBILITY.md](COMPATIBILITY.md)
for the versioned scope and [ROADMAP.md](ROADMAP.md) for the non-negotiable path
to broad Z3 functionality. Unsupported theories return `unknown`; they are not
silently approximated.
