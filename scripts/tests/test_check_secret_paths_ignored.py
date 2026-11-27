"""Tests de `scripts/ci/check_secret_paths_ignored.py`.

Trois familles, et les trois sont necessaires :

* **unitaires** sur le decoupage de `git check-ignore -v` -- dont le cas Windows
  `D:/CoursIA/.git/info/exclude:24:...`, ou la source contient elle-meme un `:` ;
* **bout en bout** sur des depots temoins, ou la MEME arborescence est rendue
  `DEFAUT` ou `CLEAN` selon que la regle vit dans `.git/info/exclude` (local) ou
  dans un `.gitignore` suivi. C'est la paire discriminante : sans elle, un organe
  qui refuserait tout passerait aussi le test « rouge avant, vert apres » ;
* **bout en bout sur la famille scratch** (artefacts a la racine du depot) :
  memes trois etats, plus le cas « deja suivi », qui est le seul que la regle
  d'ignore ne peut pas rattraper.
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


# Motifs livres par la PR : ce sont eux que le depot doit porter pour que la
# famille scratch soit protegee. Les recopier ici evite un test qui passerait
# avec n'importe quel jeu de motifs.
MOTIFS_SCRATCH = "/scratchpad_*\n/[A-Z]*AppDataLocalTemp*\n"


def _depot_scratch(racine: Path, motifs: str) -> Path:
    """Depot temoin ou la famille scratch est couverte par `motifs` (versionne)."""
    subprocess.run(["git", "init", "-q", str(racine)], check=True)
    subprocess.run(["git", "config", "user.email", "t@t"], cwd=racine, check=True)
    subprocess.run(["git", "config", "user.name", "t"], cwd=racine, check=True)
    (racine / "README.md").write_text("temoin\n", encoding="utf-8")
    (racine / ".gitignore").write_text(".secrets/\n" + motifs, encoding="utf-8")
    subprocess.run(["git", "add", "README.md", ".gitignore"], cwd=racine, check=True)
    subprocess.run(["git", "commit", "-qm", "temoin"], cwd=racine, check=True)
    return racine


SONDES = (".secrets/sonde",)
CONTROLES = ("README.md",)


def _analyser_secrets(mod, r):
    """Mesure la famille SECRETS isolee.

    Les tests de cette famille ne doivent pas dependre des motifs scratch :
    ceux-ci ont leurs propres tests, et un depot temoin qui ne porte que
    `.secrets/` rendrait leur verdict DEFAUT pour une raison etrangere au
    secret mesure.
    """
    return mod.analyser(
        r, SONDES, CONTROLES, chemins_scratch=(), controles_positifs_scratch=()
    )


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


def test_un_nom_scratch_est_reconnu_a_la_racine(mod):
    assert mod.est_nom_scratch_racine("scratchpad_c540_dossier_19540.md") is True
    assert mod.est_nom_scratch_racine("C\uf03aUsersjsboiAppDataLocalTemppool_c422.json") is True


def test_un_prefixe_hors_racine_n_est_pas_un_scratch(mod):
    """La profondeur est discriminante : `scratchpad_*` plus profond peut designer
    un livrable. Un faux positif ici ferait echouer le depot pour rien."""
    assert mod.est_nom_scratch_racine("docs/scratchpad_c540.md") is False
    assert mod.est_nom_scratch_racine("docs/pool_c422.json") is False


# ------------------------------------------------------------------- bout en bout

def test_une_regle_locale_seule_est_un_defaut(mod, tmp_path):
    r = _depot(tmp_path / "local", regle_versionnee=False, regle_locale=True)
    rapport = _analyser_secrets(mod, r)
    assert rapport["verdict"] == "DEFAUT"
    assert rapport["sensibles"][0]["statut"] == "LOCALE"


def test_une_regle_versionnee_est_clean(mod, tmp_path):
    """CONTROLE POSITIF : la meme arborescence doit passer au vert."""
    r = _depot(tmp_path / "versionnee", regle_versionnee=True, regle_locale=True)
    rapport = _analyser_secrets(mod, r)
    assert rapport["verdict"] == "CLEAN"
    assert rapport["sensibles"][0]["source"] == ".gitignore"


def test_aucune_regle_du_tout_est_un_defaut(mod, tmp_path):
    r = _depot(tmp_path / "rien", regle_versionnee=False, regle_locale=False)
    rapport = _analyser_secrets(mod, r)
    assert rapport["verdict"] == "DEFAUT"
    assert rapport["sensibles"][0]["statut"] == "NON_IGNORE"


def test_le_controle_positif_doit_rester_visible(mod, tmp_path):
    """Si README.md ressort ignore, la mesure ne vaut rien -- et le vert serait pire."""
    r = _depot(tmp_path / "casse", regle_versionnee=True, regle_locale=False)
    (r / ".gitignore").write_text(".secrets/\nREADME.md\n", encoding="utf-8")
    subprocess.run(["git", "add", ".gitignore"], cwd=r, check=True)
    subprocess.run(["git", "commit", "-qm", "casse"], cwd=r, check=True)
    rapport = _analyser_secrets(mod, r)
    assert rapport["verdict"] == "INSTRUMENT_CASSE"


def test_un_secret_deja_suivi_est_un_defaut(mod, tmp_path):
    """Une regle arrivee apres le `git add` ne retire rien de l'index."""
    r = _depot(tmp_path / "suivi", regle_versionnee=True, regle_locale=False)
    (r / ".secrets").mkdir()
    (r / ".secrets" / "master.env").write_text("K=v\n", encoding="utf-8")
    subprocess.run(["git", "add", "-f", ".secrets/master.env"], cwd=r, check=True)
    subprocess.run(["git", "commit", "-qm", "oups"], cwd=r, check=True)
    rapport = _analyser_secrets(mod, r)
    assert rapport["verdict"] == "SUIVI"
    assert ".secrets/master.env" in rapport["chemins_sensibles_deja_suivis"]


def test_hors_depot_rend_unknown_pas_un_vert(mod, tmp_path):
    """« je n'ai pas pu mesurer » ne se confond jamais avec « rien a signaler »."""
    with pytest.raises(mod.MesureImpossible):
        mod.analyser(tmp_path / "pas-un-depot", SONDES, CONTROLES)


def test_une_negation_gagnante_designore_le_secret(mod, tmp_path):
    """Une regle `!motif` gagnante rend `check-ignore` rc=0 (mesure issue #17708)
    mais INCLUT le fichier au lieu de l'exclure : sans le tri du motif, le secret
    serait classe VERSIONNEE -- vert sur un fichier stageable. Controle positif :
    le meme depot sans la negation passe au vert (le repertoire reste ignore)."""
    r = _depot(tmp_path / "negation", regle_versionnee=True, regle_locale=False)
    # git ne peut re-inclure un fichier d'un repertoire exclu qu'avec des regles
    # de contenu : on re-ecrit le .gitignore en `.secrets/*` + exception `!...`,
    # forme qui devient reelle si la regle de repertoire est un jour raffinee.
    (r / ".gitignore").write_text(".secrets/*\n!.secrets/sonde\n", encoding="utf-8")
    subprocess.run(["git", "add", ".gitignore"], cwd=r, check=True)
    subprocess.run(["git", "commit", "-qm", "negation"], cwd=r, check=True)
    rapport = _analyser_secrets(mod, r)
    assert rapport["verdict"] == "DEFAUT"
    assert rapport["sensibles"][0]["statut"] == "NON_IGNORE"


def test_sans_la_negation_le_depot_reste_vert(mod, tmp_path):
    """Controle positif de la paire : `.secrets/*` seul (sans `!`) reste CLEAN,
    donc le DEFAUT ci-dessus vient bien du `!`, pas d'un bruit du motif `*`."""
    r = _depot(tmp_path / "sans-negation", regle_versionnee=True, regle_locale=False)
    (r / ".gitignore").write_text(".secrets/*\n", encoding="utf-8")
    subprocess.run(["git", "add", ".gitignore"], cwd=r, check=True)
    subprocess.run(["git", "commit", "-qm", "sans-negation"], cwd=r, check=True)
    rapport = _analyser_secrets(mod, r)
    assert rapport["verdict"] == "CLEAN"
    assert rapport["sensibles"][0]["statut"] == "VERSIONNEE"


# ---------------------------------------------------------------- famille scratch

def test_la_famille_scratch_est_couverte_par_une_regle_versionnee(mod, tmp_path):
    """CONTROLE POSITIF : les motifs livres couvrent les deux familles mesurees."""
    r = _depot_scratch(tmp_path / "scratch-ok", MOTIFS_SCRATCH)
    rapport = mod.analyser(r, SONDES, CONTROLES)
    assert rapport["verdict"] == "CLEAN"
    assert all(v["statut"] == "VERSIONNEE" for v in rapport["scratch"])
    assert rapport["scratch"][0]["source"] == ".gitignore"


def test_sans_la_regle_scratch_le_depot_rouge(mod, tmp_path):
    """Le cas du clone reel : rien ne protege les artefacts de scratch."""
    r = _depot_scratch(tmp_path / "scratch-nu", "")
    rapport = mod.analyser(r, SONDES, CONTROLES)
    assert rapport["verdict"] == "DEFAUT"
    assert rapport["defauts_scratch"]


def test_une_regle_scratch_locale_seule_est_un_defaut(mod, tmp_path):
    """Une regle dans `.git/info/exclude` rend le `git status` propre sur CE clone
    et sur aucun autre : c'est le defaut que l'organe existe pour attraper."""
    r = _depot_scratch(tmp_path / "scratch-local", "")
    excl = r / ".git" / "info"
    excl.mkdir(parents=True, exist_ok=True)
    (excl / "exclude").write_text(MOTIFS_SCRATCH, encoding="utf-8")
    rapport = mod.analyser(r, SONDES, CONTROLES)
    assert rapport["verdict"] == "DEFAUT"
    assert rapport["scratch"][0]["statut"] == "LOCALE"


def test_un_artefact_scratch_deja_suivi_est_un_defaut(mod, tmp_path):
    """Une regle d'ignore ne retire rien de l'index : le fichier deja suivi reste
    suivi. C'est le seul etat que la regle ne peut pas rattraper."""
    r = _depot_scratch(tmp_path / "scratch-suivi", MOTIFS_SCRATCH)
    (r / "scratchpad_c540_dossier_19540.md").write_text("x\n", encoding="utf-8")
    subprocess.run(["git", "add", "-f", "scratchpad_c540_dossier_19540.md"], cwd=r, check=True)
    subprocess.run(["git", "commit", "-qm", "oups"], cwd=r, check=True)
    rapport = mod.analyser(r, SONDES, CONTROLES)
    assert rapport["verdict"] == "SUIVI"
    assert "scratchpad_c540_dossier_19540.md" in rapport["chemins_scratch_deja_suivis"]


def test_le_controle_positif_scratch_doit_rester_visible(mod, tmp_path):
    """Un motif trop large (genre `/C*`) rendrait `COURSE_CATALOG.generated.json`
    invisible : la mesure ne vaudrait plus rien."""
    r = _depot_scratch(tmp_path / "scratch-casse", "/C*\n")
    rapport = mod.analyser(r, SONDES, CONTROLES)
    assert rapport["verdict"] == "INSTRUMENT_CASSE"
