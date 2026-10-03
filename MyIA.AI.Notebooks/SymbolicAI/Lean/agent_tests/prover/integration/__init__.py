"""LeanDojo v2 integration stubs (c.76 feasibility verdict).

This package is the future home of runtime tactic-loop tools that bridge the
`agent_tests/prover/` static-analyzer pipeline with `lean_dojo.Dojo` (the
interactive theorem-proving environment of LeanDojo v2).

Cycle c.76 verdict (issue #18915): RECOVERABLE-LOCAL. LeanDojo v2.2.0 +
Lean toolchain v4.11.0 install in <5 min on a CPU machine, and the API
surface (Dojo, LeanGitRepo, trace) is importable. The actual integration
into `agent_tests/prover/tools.py` is deferred — see #18915 for the
follow-up scope.
"""
