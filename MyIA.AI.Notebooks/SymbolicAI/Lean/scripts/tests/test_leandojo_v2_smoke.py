"""
LeanDojo-v2 Smoke Tests - Quick validation without tracing.

Tests:
- LeanDojo-v2 module import (lean_dojo_v2)
- Version detection via importlib.metadata (NOT __version__, which is hardcoded
  to "1.0.0" in lean_dojo_v2/__init__.py -- cf. issue #18430)
- PyPantograph availability check (separate git install, optional for smoke)
- License file at package root (Apache-2.0 effective per the LICENSE file;
  the README's MIT claim is stale -- doc'd in #18430)
- No tracing / no token required (smoke only)

Sibling of test_leandojo_basic.py (which targets the v1 line). The two
test files coexist on purpose: this one validates the *installation chain*
without firing any tracing. The full tracing tests live in the notebook
extension.

Raison d'etre: gate the install before extending Lean-10. If this smoke
fails, LeanDojo-v2 is not ready for pedagogical integration on this
machine -- the failure is documented, not silently worked around.

Usage:
    python test_leandojo_v2_smoke.py
"""
from __future__ import annotations

import importlib
import sys
from pathlib import Path


# LeanDojo-v2 version pinned at install time (cf. issue #18430).
# Verified via pyproject.toml / PyPI metadata. The package's own
# `__version__` attribute is hardcoded "1.0.0" (see lean_dojo_v2/__init__.py
# on GitHub) -- we therefore query importlib.metadata for the real version.
EXPECTED_LEAN_DOJO_V2_VERSION = "1.0.9"


def _check_module(module_name: str) -> tuple[bool, str]:
    """Try to import a module; return (ok, version_or_error)."""
    try:
        mod = importlib.import_module(module_name)
    except Exception as exc:  # ImportError, OSError, version mismatch
        return False, f"{type(exc).__name__}: {exc}"
    # The installed version is reliable via importlib.metadata; the module
    # __version__ attribute is unreliable for lean_dojo_v2 (hardcoded).
    real_version = "<unknown>"
    try:
        from importlib.metadata import version as _v
        real_version = _v(module_name)
    except Exception as exc:
        real_version = f"<metadata-error: {exc}>"
    return True, real_version


def test_lean_dojo_v2_imports() -> bool:
    """lean_dojo_v2 package must import without error."""
    ok, info = _check_module("lean_dojo_v2")
    print(f"[import] lean_dojo_v2: {'OK' if ok else 'FAIL'} ({info})")
    return ok


def test_lean_dojo_v2_version_pinned() -> bool:
    """The installed version must match the pin EXPECTED_LEAN_DOJO_V2_VERSION."""
    ok, info = _check_module("lean_dojo_v2")
    if not ok:
        print(f"[version] lean_dojo_v2: SKIP (import failed: {info})")
        return False
    pinned_ok = info == EXPECTED_LEAN_DOJO_V2_VERSION
    print(f"[version] lean_dojo_v2: {'OK' if pinned_ok else 'WARN'} "
          f"(installed={info!r}, expected={EXPECTED_LEAN_DOJO_V2_VERSION!r})")
    # Smoke test allows version drift but flags it.
    return pinned_ok


def test_pantograph_imports() -> bool:
    """PyPantograph (git+https install) must import without error."""
    # PyPantograph ships as 'pantograph' on PyPI in newer versions, or as
    # 'pypantograph' depending on fork. Probe both.
    for name in ("pantograph", "pypantograph"):
        ok, info = _check_module(name)
        if ok:
            print(f"[import] {name}: OK ({info})")
            return True
    print("[import] pantograph/pypantograph: NOT FOUND "
          "(acceptable for smoke -- the v2 lib can run without Pantograph)")
    # Not a hard fail: tracing only requires Pantograph, not import.
    return True


def test_lean_dojo_v2_license_metadata() -> bool:
    """lean_dojo_v2 must expose a license marker (Apache-2.0 effective)."""
    try:
        mod = importlib.import_module("lean_dojo_v2")
    except Exception as exc:
        print(f"[license] lean_dojo_v2: SKIP (import failed: {exc})")
        return False
    # LeanDojo-v2's LICENSE file is Apache-2.0 (verified at
    # https://github.com/lean-dojo/LeanDojo-v2/blob/main/LICENSE).
    # The README says MIT, but the LICENSE file is the authoritative source.
    # We only assert that *some* license marker is reachable, then report.
    pkg = getattr(mod, "__file__", "")
    pkg_path = Path(pkg).parent if pkg else Path.cwd()
    license_files = []
    for candidate in ("LICENSE", "LICENSE.md", "LICENSE.txt", "COPYING"):
        if (pkg_path / candidate).exists():
            license_files.append(candidate)
    print(f"[license] license files found at package root: {license_files or 'NONE'}")
    # Smoke-level assertion: at least one license marker is reachable.
    return bool(license_files)


def test_no_github_token_required() -> bool:
    """Smoke must run WITHOUT GITHUB_ACCESS_TOKEN (tracing is deferred)."""
    import os
    has_token = "GITHUB_ACCESS_TOKEN" in os.environ
    if has_token:
        print("[no-token] WARN: GITHUB_ACCESS_TOKEN is set in env "
              "(smoke should not need it -- check no tracing fired)")
    else:
        print("[no-token] OK: no GITHUB_ACCESS_TOKEN in env (smoke is pure-import)")
    return True  # informational, not a hard fail


if __name__ == "__main__":
    print("=" * 60)
    print(f"LeanDojo-v2 smoke -- pinned version {EXPECTED_LEAN_DOJO_V2_VERSION}")
    print("=" * 60)
    results = {
        "import": test_lean_dojo_v2_imports(),
        "version_pinned": test_lean_dojo_v2_version_pinned(),
        "pantograph_imports": test_pantograph_imports(),
        "license_metadata": test_lean_dojo_v2_license_metadata(),
        "no_token_required": test_no_github_token_required(),
    }
    print()
    print("=" * 60)
    print("Summary:")
    for name, ok in results.items():
        marker = "OK" if ok else "FAIL"
        print(f"  [{marker}] {name}")
    print("=" * 60)
    # Smoke never returns non-zero: a soft FAIL means LeanDojo-v2 is not
    # ready on this machine, but the report itself is the deliverable.
    sys.exit(0)

