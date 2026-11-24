"""Contract tests for the declared local deviation on the EPITA copy of
`argumentation_lib/_belief_revision_handler.py` (issue #23163, defect signal
c.6784603097).

Upstream declares ``REVISION_METHODS = {"dalal", "levi"}`` (class attribute)
but never consults it: an unknown ``method`` string passed to ``revise()`` was
silently routed through the Levi pattern and echoed verbatim in the ``method``
key of the result dict (committed notebook output, ``Argumentation-06c``
cell [7]). A caller with a misspelled method name had no way to know.

The declared local deviation (NOT-VERBATIM, documented in the module header
and in `argumentation_lib/NOTICE-EPITA` -- "Adaptations locales declarees",
same mechanism as `_adf_handler.py` 2026-10-29) validates ``method`` at the
very top of ``revise()``, BEFORE the try block, so the refusal raises without
touching the JVM.

That placement is what makes these tests **JVM-free by construction**: the
instance is built without ``__init__`` (same pattern as ``test_adf_handler.py``),
carries none of the Java class handles, and the validated code path never
reaches one. The module itself still hard-imports ``jpype`` (that optionality
was only ever added to `_adf_handler.py`), so the import happens inside each
test with a skip guard: on the CPU-only CI job (no ``jpype`` wheels) these
tests skip rather than break collection.

The notebook `Argumentation-06c-Revision-Croyances-Python.ipynb` exercises the
same path on a real JVM (dalal/levi convergence still holds, unknown method
refused) and renders its outputs.
"""
from __future__ import annotations

import os
import sys

# Make `argumentation_lib` importable (../argumentation_lib relative to tests/).
_TESTS_DIR = os.path.dirname(os.path.abspath(__file__))
_ARG_ANALYSIS_DIR = os.path.dirname(_TESTS_DIR)
if _ARG_ANALYSIS_DIR not in sys.path:
    sys.path.insert(0, _ARG_ANALYSIS_DIR)

import pytest  # noqa: E402


def _load_handler_class():
    """Import the handler class, skipping the leg when jpype is absent.

    The module imports ``jpype`` at top level (only `_adf_handler.py` ever got
    the optional-import treatment), so a module-level import would fail at
    COLLECTION on the CPU-only CI job and take the whole job down with it.
    """
    try:
        from argumentation_lib._belief_revision_handler import (
            BeliefRevisionHandler,
        )
    except ModuleNotFoundError as exc:  # pragma: no cover - runner-dependent
        pytest.skip(f"jpype absent on this runner: {exc}")
    return BeliefRevisionHandler


def _handler_without_jvm():
    """An instance that never touched `__init__` (no JVM required).

    The validation guarded by these tests sits before any use of the Java
    class handles, so a bare instance is enough to observe it. If the
    validation ever moved after the first JVM call, these tests would fail
    with ``AttributeError`` instead of ``ValueError`` -- which is the point.
    """
    cls = _load_handler_class()
    return cls.__new__(cls)


def test_revise_rejects_unknown_method():
    handler = _handler_without_jvm()
    with pytest.raises(ValueError, match="inconnu") as excinfo:
        handler.revise(["p"], "q", method="inconnu")
    # The message names the accepted methods, so the caller can self-correct.
    message = str(excinfo.value)
    assert "dalal" in message and "levi" in message


def test_revise_rejects_non_string_method():
    handler = _handler_without_jvm()
    # A non-string method is an out-of-set value, not a TypeError: the guard
    # must refuse it the same way as a misspelled name.
    with pytest.raises(ValueError):
        handler.revise(["p"], "q", method=None)


def test_revision_methods_is_the_declared_pair():
    cls = _load_handler_class()
    # Pin the declared surface exactly: silently widening the set (or
    # narrowing it) is a behavior change that must go through NOTICE-EPITA.
    assert cls.REVISION_METHODS == {"dalal", "levi"}
