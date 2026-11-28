"""Fixtures partagees par les tests de qc-mcp-lite.

La fixture `_reset_rate_limit_state` isolait chaque test du limiteur de debit
REEL du serveur (`server._rate_limit`), qui appelle `time.sleep(~60 s)` des que
la fenetre de 60 s est pleine. Elle vit ici, et non dans un module de test,
pour que TOUS les modules du dossier en heritent -- y compris ceux ajoutes
apres la scission du module de tests, qui a franchi le plafond des 800 lignes
impose aux scripts neufs (cliquet `scripts/tests/test_script_size_ratchet.py`).
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

import pytest

from server import _call_timestamps


@pytest.fixture(autouse=True)
def _reset_rate_limit_state():
    """Reset the module-global rate-limit deque before each test.

    ``_rate_limit()`` appends to the module-global ``_call_timestamps`` deque
    without clearing it. Tests that exercise the real ``_api_post`` (they mock
    ``requests.post`` but still call ``_rate_limit``) therefore accumulate
    timestamps across the suite. Once 10 calls fall inside the 60s window, the
    real ``time.sleep(~60s)`` fires -- hanging the full suite (~60s per excess
    call, observed: 13 tests = 61.67s; the whole suite hung >2min before this).
    Clearing the deque per test isolates each test from the live rate limiter.
    """
    _call_timestamps.clear()
    yield
