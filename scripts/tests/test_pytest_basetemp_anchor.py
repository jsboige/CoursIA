"""Le scratch pytest doit vivre hors du volume partage et hors du depot.

Contrat : sans `--basetemp` explicite, pytest ecrit ses `tmp_path` sous
`%LOCALAPPDATA%/CoursIA/pytest/<projet>/run-<pid>/`, un dossier par session,
supprime a la fin de la session (mandat user de rangement du volume,
27/10/2026).

**Hors de tout arbre git** : le ledger de dette refuse un repertoire d'etat
a l'interieur d'un arbre git (`REPO_PATH_REFUSED`) -- les tests du ledger
utilisent `tmp_path` comme repertoire d'etat, donc un scratch ancre dans le
depot ferait echouer 32 de ces tests (mesure : 32 failed / 107 passed avec
l'ancrage dans le depot, 1 failed / 138 passed hors arbre git).
"""

import importlib.util
import os
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


def test_sans_option_explicite_le_scratch_est_hors_de_l_arbre_git(tmp_path,
                                                                  monkeypatch):
    monkeypatch.setenv("LOCALAPPDATA", str(tmp_path / "localappdata"))
    conftest = _load_root_conftest()
    config = _FakeConfig(tmp_path / "projet")
    conftest.pytest_configure(config)
    basetemp = Path(config.option.basetemp)
    assert basetemp.is_relative_to(tmp_path / "localappdata")
    assert basetemp.name.startswith("run-")
    assert basetemp.parent.name == "projet"


def test_le_scratch_est_unique_par_session(tmp_path, monkeypatch):
    """pytest VIDE le `--basetemp` : deux sessions concurrentes ne peuvent
    pas partager le meme dossier."""
    monkeypatch.setenv("LOCALAPPDATA", str(tmp_path / "localappdata"))
    conftest = _load_root_conftest()
    first = _FakeConfig(tmp_path / "projet")
    second = _FakeConfig(tmp_path / "projet")
    conftest.pytest_configure(first)
    # Une autre session : un autre pid (simule) => un autre dossier.
    monkeypatch.setattr(os, "getpid", lambda: 424242)
    conftest.pytest_configure(second)
    assert first.option.basetemp != second.option.basetemp


def test_un_basetemp_explicite_prime_sur_l_ancrage(tmp_path, monkeypatch):
    monkeypatch.setenv("LOCALAPPDATA", str(tmp_path / "localappdata"))
    conftest = _load_root_conftest()
    config = _FakeConfig(tmp_path, basetemp="D:/tmp/explicite")
    conftest.pytest_configure(config)
    assert config.option.basetemp == "D:/tmp/explicite"


def test_le_scratch_de_la_session_est_supprime(tmp_path, monkeypatch):
    monkeypatch.setenv("LOCALAPPDATA", str(tmp_path / "localappdata"))
    conftest = _load_root_conftest()
    config = _FakeConfig(tmp_path / "projet")
    conftest.pytest_configure(config)
    scratch = Path(config.option.basetemp)
    scratch.mkdir(parents=True, exist_ok=True)
    (scratch / "marqueur").write_text("x", encoding="utf-8")
    session = types.SimpleNamespace(config=config)
    conftest.pytest_sessionfinish(session, 0)
    assert not scratch.exists()


def test_le_conftest_de_la_racine_est_present():
    assert (ROOT / "conftest.py").is_file()
