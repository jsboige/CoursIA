"""`get` n'ecrit un secret que dans un chemin ignore par une regle VERSIONNEE.

Revue Hermes du 22/09 sur #17425 : la doc promettait que l'organe nomme la source
de l'ignorance (`git check-ignore -v`), le code ne lisait que le code retour
(`-q`). Un chemin ignore par le seul `.git/info/exclude` -- local au clone --
passait donc pour protege. La mesure est desormais celle de l'organe de
couverture des secrets (`scripts/ci/check_secret_paths_ignored.py`, #17442).
"""

from __future__ import annotations

import importlib.util
import subprocess
from pathlib import Path

import pytest

_MODULE_PATH = Path(__file__).resolve().parents[1] / "agent_keyring.py"


def _load_module():
    spec = importlib.util.spec_from_file_location("agent_keyring_ignore_under_test", _MODULE_PATH)
    mod = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod


def _git(repo: Path, *args: str) -> None:
    subprocess.run(["git", *args], cwd=repo, check=True, capture_output=True)


@pytest.fixture()
def repo(tmp_path, monkeypatch):
    _git(tmp_path, "init", "-q")
    (tmp_path / ".gitignore").write_text("versionne/*\n!versionne/visible.env\n", encoding="utf-8")
    _git(tmp_path, "add", ".gitignore")
    _git(tmp_path, "-c", "user.email=t@t", "-c", "user.name=t", "commit", "-q", "-m", "init")
    (tmp_path / ".git" / "info").mkdir(parents=True, exist_ok=True)
    (tmp_path / ".git" / "info" / "exclude").write_text("local-seulement/\n", encoding="utf-8")
    monkeypatch.chdir(tmp_path)
    return tmp_path


def test_regle_versionnee_protege(repo):
    statut, source = _load_module()._git_ignored(repo / "versionne" / "a.env")
    assert statut == "VERSIONNEE" and source == ".gitignore"


def test_exclude_local_ne_protege_pas_le_depot(repo):
    statut, source = _load_module()._git_ignored(repo / "local-seulement" / "a.env")
    assert statut == "LOCALE"
    assert source.replace("\\", "/").endswith(".git/info/exclude")


def test_chemin_non_ignore(repo):
    assert _load_module()._git_ignored(repo / "ailleurs" / "a.env")[0] == "NON_IGNORE"


def test_motif_de_negation_n_est_pas_une_protection(repo):
    assert _load_module()._git_ignored(repo / "versionne" / "visible.env")[0] == "NON_IGNORE"


def test_hors_depot_est_non_mesure(repo, tmp_path_factory):
    dehors = tmp_path_factory.mktemp("dehors") / "a.env"
    assert _load_module()._git_ignored(dehors) is None
