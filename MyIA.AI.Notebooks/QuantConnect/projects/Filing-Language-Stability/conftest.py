# Marqueurs pytest declares pour ce projet.
#
# Le smoke SEC reel (tests/test_smoke_sec_real.py) est marque
# ``@pytest.mark.smoke`` ; on declare ici pour eviter le warning
# ``PytestUnknownMarkWarning`` et pour permettre aux outils de tri
# (``-m 'not smoke'``) de l'exclure proprement.

import pytest


def pytest_configure(config):
    config.addinivalue_line(
        "markers",
        "smoke: smoke test reseau reel (skip par defaut, declenche via "
        "PYTEST_RUN_SMOKE=1).",
    )
