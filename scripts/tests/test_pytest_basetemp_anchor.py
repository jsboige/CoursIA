"""Le scratch pytest doit vivre dans le workspace, pas a la racine du volume.

Contrat : sans `--basetemp` explicite, pytest ecrit ses `tmp_path` sous
`<rootdir>/.tmp/pytest`. Reglage porte par `conftest.py` a la racine du depot
(mandat user de rangement du volume, 27/10/2026).
"""

import importlib.util
import types
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def _load_root_conftest():
    """Charge `conftest.py` de la racine du depot comme module."""
    spec = importlib.util.spec_from_file_location(
        "coursia_root_conftest", ROOT / "conftest.py"
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class _FakeConfig:
    """Fausse config pytest : seuls les attributs reellement lus sont requis."""

    def __init__(self, rootpath, basetemp=None):
        self.rootpath = Path(rootpath)
        self.option = types.SimpleNamespace(basetemp=basetemp)
        self._basetemp = basetemp

    def getoption(self, name, default=None):
        if name == "basetemp":
            return self._basetemp if self._basetemp is not None else default
        return default


def test_sans_option_explicite_le_basetemp_est_ancre_dans_le_workspace(tmp_path):
    conftest = _load_root_conftest()
    config = _FakeConfig(tmp_path)
    conftest.pytest_configure(config)
    assert Path(config.option.basetemp) == tmp_path / ".tmp" / "pytest"


def test_un_basetemp_explicite_prime_sur_l_ancrage(tmp_path):
    conftest = _load_root_conftest()
    config = _FakeConfig(tmp_path, basetemp="D:/tmp/explicite")
    conftest.pytest_configure(config)
    assert config.option.basetemp == "D:/tmp/explicite"


def test_le_conftest_de_la_racine_est_present():
    assert (ROOT / "conftest.py").is_file()
