# argumentation_lib — vendored shim layer for Argument Analysis notebooks
#
# Provides the public API consumed by CoursIA notebooks, decoupled from
# the EPITA `argumentation_analysis` internals.  All heavy imports are
# lazy; importing this module alone must succeed without the EPITA package.
#
# Phase B.1 — shims only.  Core vendoring (agents, runner) comes in B.2.
# See #2137 Phase B scope and acceptance criteria.

__version__ = "0.1.0"

# -- lazy re-exports (B.2 will populate these) --
