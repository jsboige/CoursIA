"""Helpers partages par les tests de qc-mcp-lite.

Ils vivaient dans `test_server.py`, qui a franchi le plafond des 800 lignes
impose aux scripts neufs par le cliquet de taille
(`scripts/tests/test_script_size_ratchet.py`). Le prefixe `_` les sort de la
collecte pytest : ce module n'est qu'un support d'import, comme
`scripts/tests/_bash_resolution.py` dans le meme genre.

Import relatif (`from ._qc_helpers import ...`) : le dossier porte un
`__init__.py`, donc
pytest importe ses modules comme `tests.test_server` et non comme des modules
de premier niveau.
"""
from unittest.mock import MagicMock

_DUMMY_ENV = {"QC_API_USER_ID": "test", "QC_API_ACCESS_TOKEN": "testtoken"}


def _mock_api_response(json_data: dict) -> MagicMock:
    """Create a mock response with json() and raise_for_status()."""
    mock = MagicMock()
    mock.json.return_value = json_data
    mock.raise_for_status = MagicMock()
    return mock
