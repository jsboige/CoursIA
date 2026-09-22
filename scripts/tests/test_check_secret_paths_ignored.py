"""Tests de `scripts/ci/check_secret_paths_ignored.py`.

Deux familles, et les deux sont necessaires :

* **unitaires** sur le decoupage de `git check-ignore -v` -- dont le cas Windows
  `D:/CoursIA/.git/info/exclude:24:...`, ou la source contient elle-meme un `:` ;
* **bout en bout** sur des depots temoins, ou la MEME arborescence est rendue
  `DEFAUT` ou `CLEAN` selon que la regle vit dans `.git/info/exclude` (local) ou
  dans un `.gitignore` suivi. C'est la paire discriminante : sans elle, un organe
  qui refuserait tout passerait aussi le test « rouge avant, vert apres ».
"""

from __future__ import annotations

import importlib.util
import subprocess
from pathlib import Path

import pytest

ORGANE = Path(__file__).resolve().parents[1] / "ci" / "check_secret_paths_ignored.py"


@pytest.fixture(scope="module")
def mod():
    spec = importlib.util.spec_from_file_location("check_secret_paths_ignored", ORGANE)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def _depot(racine: Path, regle_versionnee: bool, regle_locale: bool) -> Path:
    """Bâtit un depot temoin ou `.secrets/` est couvert par l'une, l'autre, ou aucune."""
    subprocess.run(["git", "init", "-q", str(racine)], check=True)
    subprocess.run(["git", "config", "user.email", "t@t"], cwd=racine, check=True)
    subprocess.run(["git", "config", "user.name", "t"], cwd=racine, check=True)
    (racine / "README.md").write_text("temoin\n", encoding="utf-8")
    (racine / ".gitignore").write_text(
        ".secrets/\n" if regle_versionnee else "# aucune regle de repertoire\n",
        encoding="utf-8",
    )
    if regle_locale:
        excl = racine / ".git" / "info"
        excl.mkdir(parents=True, exist_ok=True)
        (excl / "exclude").write_text("/.secrets/\n", encoding="utf-8")
    subprocess.run(["git", "add", "README.md", ".gitignore"], cwd=racine, check=True)
    subprocess.run(["git", "commit", "-qm", "temoin"], cwd=racine, check=True)
    return racine


SONDES = (".secrets/sonde",)
CONTROLES = ("README.md",)


# --------------------------------------------------------------------------- unitaires

def test_decoupe_une_ligne_standard(mod):
    v = mod.parse_ligne_check_ignore(".gitignore:390:.secrets/\t.secrets/master.env")
    assert v == {
        "source": ".gitignore",
        "ligne": 390,
        "motif": ".secrets/",
        "chemin": ".secrets/master.env",
    }


def test_decoupe_une_source_qui_contient_deux_points(mod):
    """Un chemin Windows porte un `:` -- un split par la GAUCHE tronquerait la source."""
    v = mod.parse_ligne_check_ignore(
        "D:/CoursIA/.git/info/exclude:24:/.secrets/\t.secrets/master.env"
    )
    assert v["source"] == "D:/CoursIA/.git/info/exclude"
    assert v["ligne"] == 24


def test_une_ligne_sans_tabulation_ne_se_decoupe_pas(mod):
    assert mod.parse_ligne_check_ignore("pas une sortie de check-ignore") is None


def test_une_source_suivie_est_versionnee(mod):
    assert mod.source_est_versionnee(".gitignore", frozenset({".gitignore"})) is True


def test_une_source_non_suivie_est_locale(mod):
    assert (
        mod.source_est_versionnee("D:/CoursIA/.git/info/exclude", frozenset({".gitignore"}))
        is False
    )


# ------------------------------------------------------------------- bout en bout

def test_une_regle_locale_seule_est_un_defaut(mod, tmp_path):
    r = _depot(tmp_path / "local", regle_versionnee=False, regle_locale=True)
    rapport = mod.analyser(r, SONDES, CONTROLES)
    assert rapport["verdict"] == "DEFAUT"
    assert rapport["sensibles"][0]["statut"] == "LOCALE"


def test_une_regle_versionnee_est_clean(mod, tmp_path):
    """CONTROLE POSITIF : la meme arborescence doit passer au vert."""
    r = _depot(tmp_path / "versionnee", regle_versionnee=True, regle_locale=True)
    rapport = mod.analyser(r, SONDES, CONTROLES)
    assert rapport["verdict"] == "CLEAN"
    assert rapport["sensibles"][0]["source"] == ".gitignore"


def test_aucune_regle_du_tout_est_un_defaut(mod, tmp_path):
    r = _depot(tmp_path / "rien", regle_versionnee=False, regle_locale=False)
    rapport = mod.analyser(r, SONDES, CONTROLES)
    assert rapport["verdict"] == "DEFAUT"
    assert rapport["sensibles"][0]["statut"] == "NON_IGNORE"


def test_le_controle_positif_doit_rester_visible(mod, tmp_path):
    """Si README.md ressort ignore, la mesure ne vaut rien -- et le vert serait pire."""
    r = _depot(tmp_path / "casse", regle_versionnee=True, regle_locale=False)
    (r / ".gitignore").write_text(".secrets/\nREADME.md\n", encoding="utf-8")
    subprocess.run(["git", "add", ".gitignore"], cwd=r, check=True)
    subprocess.run(["git", "commit", "-qm", "casse"], cwd=r, check=True)
    rapport = mod.analyser(r, SONDES, CONTROLES)
    assert rapport["verdict"] == "INSTRUMENT_CASSE"


def test_un_secret_deja_suivi_est_un_defaut(mod, tmp_path):
    """Une regle arrivee apres le `git add` ne retire rien de l'index."""
    r = _depot(tmp_path / "suivi", regle_versionnee=True, regle_locale=False)
    (r / ".secrets").mkdir()
    (r / ".secrets" / "master.env").write_text("K=v\n", encoding="utf-8")
    subprocess.run(["git", "add", "-f", ".secrets/master.env"], cwd=r, check=True)
    subprocess.run(["git", "commit", "-qm", "oups"], cwd=r, check=True)
    rapport = mod.analyser(r, SONDES, CONTROLES)
    assert rapport["verdict"] == "SUIVI"
    assert ".secrets/master.env" in rapport["secrets_deja_suivis"]


def test_hors_depot_rend_unknown_pas_un_vert(mod, tmp_path):
    """« je n'ai pas pu mesurer » ne se confond jamais avec « rien a signaler »."""
    with pytest.raises(mod.MesureImpossible):
        mod.analyser(tmp_path / "pas-un-depot", SONDES, CONTROLES)
