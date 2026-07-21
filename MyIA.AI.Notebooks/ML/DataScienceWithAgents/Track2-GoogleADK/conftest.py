"""Pytest bootstrap for the Track2-GoogleADK package.

The repo-wide pytest.ini `testpaths` does not include this package, so tests
under config/ and utils/ are collected by explicit invocation from the repo
root. That leaves `config` and `utils` unimportable as top-level packages
(they are sibling sub-packages here, not installed). This conftest inserts the
package root onto sys.path before collection so both resolve.
"""
import sys
from pathlib import Path

_PKG_ROOT = Path(__file__).resolve().parent
if str(_PKG_ROOT) not in sys.path:
    sys.path.insert(0, str(_PKG_ROOT))
