"""Contract test for the C186d -> C186f import alias in argumentation_lib.

Before the alias, importing the AF layer raised at module load:

    ModuleNotFoundError: No module named 'argumentation_lib.tweety_initializer'

because the verbatim upstream copy `_af_handler.py` imports the sibling as
``.tweety_initializer`` while the delivered module is ``_tweety_initializer``
(sub-tranche C186f). The alias registered by the shim layer
(``sys.modules.setdefault`` in ``argumentation_lib/__init__.py``) is the
re-routing point the verbatim file's DEPENDENCY NOTICE announces. This file
holds that contract: import path, alias identity, and package-import safety
without a JVM.
"""
from __future__ import annotations

import os
import sys
from pathlib import Path

# Make `argumentation_lib` importable (../argumentation_lib relative to tests/).
_TESTS_DIR = os.path.dirname(os.path.abspath(__file__))
_ARG_ANALYSIS_DIR = os.path.dirname(_TESTS_DIR)
if _ARG_ANALYSIS_DIR not in sys.path:
    sys.path.insert(0, _ARG_ANALYSIS_DIR)

import argumentation_lib


def test_alias_registered_at_package_import():
    """The alias module IS the delivered C186f module (same object)."""
    assert "argumentation_lib.tweety_initializer" in sys.modules
    assert (
        sys.modules["argumentation_lib.tweety_initializer"]
        is sys.modules["argumentation_lib._tweety_initializer"]
    )


def test_af_layer_imports_after_alias():
    """The import the G.9 fingerprint documented as failing now succeeds."""
    from argumentation_lib._af_handler import AFHandler  # noqa: F401

    handler_cls = argumentation_lib.get_af_handler_symbol()
    assert handler_cls.__name__ == "AFHandler"


def test_lazy_accessor_agrees():
    """The public lazy accessor returns the same class as the direct import."""
    direct = argumentation_lib.get_af_handler_symbol()
    assert direct is sys.modules["argumentation_lib._af_handler"].AFHandler


def test_package_import_stands_alone(tmp_path: Path):
    """Importing the package alone must stay JVM-free and side-effect safe.

    Regression guard for the alias: it eagerly imports `_tweety_initializer`
    at package load. That module imports `jpype` (stdlib-safe without a JVM)
    — the package import must neither start a JVM nor raise without one.
    """
    import subprocess

    probe = (
        "import sys; sys.path.insert(0, r'"
        + str(_ARG_ANALYSIS_DIR)
        + "'); import argumentation_lib, jpype; "
        "print(argumentation_lib.__version__, jpype.isJVMStarted())"
    )
    out = subprocess.run(
        [sys.executable, "-c", probe],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=120,
    )
    assert out.returncode == 0, out.stderr
    version, jvm = out.stdout.split()
    assert version == argumentation_lib.__version__
    assert jvm == "False"
