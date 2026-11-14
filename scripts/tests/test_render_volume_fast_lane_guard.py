"""Tests de l'absorption de la garde de volume de rendu (#25510, T-A/3).

Le garde absorbe est `Render volume delta (#11656 advisory)`, issu du
workflow `render-volume-delta-advisory.yml`. Il mesure la **perte de volume
de RENDU** d'un carnet entre le merge-base et la tete -- le cas fondateur
(#11656 / #11351) : des carnets qui gardent `outputs: [...]` mesureur mais
ont perdu 96-99 % de leur volume rendu, ce qu'aucun detecteur de seuil
ABSOLU ne voit.

Ces tests couvrent :
  - le VERDICT CIBLE : un finding `LOST_MIME` de famille `image` fait
    echouer la garde (rc 1) -- c'est le cas #26032 (une PNG de 40 Ko
    disparue de la cellule 10, PR gate vert) ;
  - l'ABSTENTION : sans ancetre commun, la garde s'abstient en le disant
    (rc 2) au lieu de fabriquer un « rien de perdu » ;
  - l'ERREUR STRUCTURELLE : un carnet non mesure ne vaut pas « rien de
    perdu » (rc 2) ;
  - l'EXEMPTION des carnets neufs ;
  - le RENOMMAGE : un carnet renomme est MESURE (les deux chemins sont
    passes a l'organe natif), jamais exempt ;
  - l'ECHEC DE `git diff` : il rend rc 2, jamais « aucun carnet modifie » ;
  - le PLAFOND : il se nomme, il ne tronque plus ;
  - la NON-REIMPLEMENTATION : la mesure est celle de l'organe natif
    `check_render_volume_delta.py`, appele comme bibliotheque ;
  - le REGISTRE : nom byte-identique au job rendu, perimetre, bornage,
    `blocking=False` (etape 1 de la tranche).

Les tests du registre et de l'identite sont relus par les organes
`check_absorbed_check_run_identity.py` et `check_absorbed_path_parity.py`.
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
if str(CI_DIR) not in sys.path:
    sys.path.insert(0, str(CI_DIR))

import run_render_volume_guard as rvg  # noqa: E402
from fast_lane_registry import TRANCHE46  # noqa: E402

NOTEBOOK = "MyIA.AI.Notebooks/Demo/demo.ipynb"
IMAGE_BYTES = 4096
TEXT_BYTES = 4096


def _notebook(image: bool = False, text: bool = False,
              cell_id: str = "cell-1", text_size: int = 0) -> dict:
    """Carnet minimal avec une sortie image (et/ou texte) mesurable.

    `text_size` gonfle la cellule de code : c'est ce qui permet de
    fabriquer un carnet dont la similarite de contenu avec sa version de
    base reste au-dessus du seuil de detection de renommage de git
    (`-M50%`).
    """
    data: dict[str, str] = {}
    if image:
        data["image/png"] = "x" * IMAGE_BYTES
    if text:
        data["text/plain"] = "y" * TEXT_BYTES
    source = "print('demo')\n"
    if text_size:
        source = "# " + "a" * text_size + "\n" + source
    return {
        "cells": [
            {
                "cell_type": "code",
                "execution_count": 1,
                "id": cell_id,
                "metadata": {},
                "outputs": ([{"output_type": "display_data", "data": data,
                              "metadata": {}}] if data else []),
                "source": [source],
            }
        ],
        "metadata": {
            "kernelspec": {"display_name": "Python 3", "language": "python",
                           "name": "python3"},
            "language_info": {"name": "python", "version": "3.11.0"},
        },
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _git(repo: Path, *args: str) -> subprocess.CompletedProcess:
    return subprocess.run(["git", *args], cwd=repo, capture_output=True,
                          text=True, encoding="utf-8", errors="replace",
                          check=True)


def _write_notebook(repo: Path, notebook: dict, path: str = NOTEBOOK) -> None:
    target = repo / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(notebook), encoding="utf-8")


def _build_repo(repo: Path, base_notebook: dict, head_notebook: dict) -> Path:
    """Depot jetable : `main` porte la base, `feature` porte la tete.

    Le merge-base `main`/HEAD est alors le commit de base -- exactement la
    situation d'une PR.
    """
    _git(repo, "init", "-b", "main")
    _git(repo, "config", "user.email", "test@example.invalid")
    _git(repo, "config", "user.name", "Test")
    _write_notebook(repo, base_notebook)
    _git(repo, "add", NOTEBOOK)
    _git(repo, "commit", "-m", "base")
    _git(repo, "checkout", "-b", "feature")
    _write_notebook(repo, head_notebook)
    _git(repo, "add", NOTEBOOK)
    _git(repo, "commit", "-m", "head")
    return repo


@pytest.fixture()
def repo(tmp_path, monkeypatch):
    """Cas de reference : la base porte une image, la tete ne la porte plus."""
    _build_repo(tmp_path, _notebook(image=True), _notebook(image=False))
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(rvg, "REPO_ROOT", tmp_path)
    return tmp_path


# --- le verdict cible -------------------------------------------------------

def test_une_perte_d_image_est_le_verdict_cible(repo, capsys):
    rc = rvg.main(["--base-ref", "main"])
    out = capsys.readouterr().out
    assert rc == 1, out
    assert "CIBLE" in out
    assert "LOST_MIME" in out
    assert NOTEBOOK in out


def test_aucune_perte_ne_donne_pas_de_verdict(repo, capsys):
    """Controle NEGATIF : le garde ne rouge pas sur une PR qui garde son image."""
    _write_notebook(repo, _notebook(image=True))
    _git(repo, "add", NOTEBOOK)
    _git(repo, "commit", "-m", "head: image conservee")
    rc = rvg.main(["--base-ref", "main"])
    out = capsys.readouterr().out
    assert rc == 0, out
    assert "CIBLE" not in out


def test_une_famille_non_image_ne_fait_pas_echouer_la_garde(tmp_path,
                                                             monkeypatch,
                                                             capsys):
    """La CIBLE est `image` : une famille `text` disparue est RAPPORTEE, pas
    bloquante -- elle est plus large que le cas vise et ferait du bruit."""
    _build_repo(tmp_path, _notebook(text=True), _notebook())
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(rvg, "REPO_ROOT", tmp_path)
    rc = rvg.main(["--base-ref", "main"])
    out = capsys.readouterr().out
    assert rc == 0, out
    assert "CIBLE" not in out
    assert "LOST_MIME" in out


def test_le_carnet_neuf_est_exempt(repo, capsys):
    """Un carnet AJOUTE par la PR n'a rien a perdre : il est exempt."""
    _git(repo, "checkout", "-b", "nouveau", "main")
    _write_notebook(repo, _notebook(image=True), "MyIA.AI.Notebooks/Demo/neuf.ipynb")
    _git(repo, "add", "MyIA.AI.Notebooks/Demo/neuf.ipynb")
    _git(repo, "commit", "-m", "carnet neuf")
    rc = rvg.main(["--base-ref", "main", "--head-ref", "nouveau"])
    out = capsys.readouterr().out
    assert rc == 0, out
    assert "CIBLE" not in out


# --- abstention et erreur structurelle --------------------------------------

def test_abstention_sans_ancetre_commun(repo, capsys):
    """Pas de merge-base -> abstention EXPLICITE (rc 2), jamais un « rien de
    perdu »."""
    _git(repo, "checkout", "--orphan", "orpheline")
    _write_notebook(repo, _notebook(image=False))
    _git(repo, "add", NOTEBOOK)
    _git(repo, "commit", "-m", "branche sans ancetre commun")
    rc = rvg.main(["--base-ref", "main", "--head-ref", "orpheline"])
    out = capsys.readouterr().out
    assert rc == 2, out
    assert "ABSTENTION" in out
    assert "CIBLE" not in out


def test_un_carnet_absent_de_l_arbre_de_travail_est_une_erreur(repo, capsys):
    """Un carnet non mesure ne vaut pas « rien de perdu » : rc 2."""
    (repo / NOTEBOOK).unlink()
    rc = rvg.main(["--base-ref", "main"])
    out = capsys.readouterr().out
    assert rc == 2, out
    assert "ERREUR" in out


def test_aucun_carnet_modifie_ne_donne_pas_de_verdict(repo, capsys):
    """Un PR qui ne touche aucun carnet n'a rien a mesurer : rc 0, sans bruit."""
    _git(repo, "checkout", "-b", "script", "main")
    (repo / "outillage.py").write_text("x = 1\n", encoding="utf-8")
    _git(repo, "add", "outillage.py")
    _git(repo, "commit", "-m", "hors carnet")
    rc = rvg.main(["--base-ref", "main", "--head-ref", "script"])
    out = capsys.readouterr().out
    assert rc == 0, out


# --- la mesure vient de l'organe natif ---------------------------------------

def test_la_mesure_vient_de_l_organe_natif(repo, monkeypatch, capsys):
    """Organe-first : le wrapper APPELLE `check_render_volume_delta`, il ne
    reecrit pas la detection."""
    calls: list[str] = []
    original = rvg.rvd.scan_notebook

    def spy(path, base_ref, head_ref=None, **kwargs):
        calls.append(str(path))
        return original(path, base_ref, head_ref, **kwargs)

    monkeypatch.setattr(rvg.rvd, "scan_notebook", spy)
    rvg.main(["--base-ref", "main"])
    assert calls, "l'organe natif n'a pas ete appele"
    # L'organe natif attend un chemin RELATIF a la racine du depot : c'est
    # lui qu'il passe a `git show <ref>:<chemin>`.
    assert Path(calls[0]).as_posix() == NOTEBOOK


def test_le_rapport_json_expose_les_findings(repo, capsys):
    rc = rvg.main(["--base-ref", "main", "--json"])
    out = capsys.readouterr().out
    assert rc == 1
    report = json.loads(out)
    assert report["target"]
    assert report["target"][0]["kind"] == "LOST_MIME"
    assert report["target"][0]["mime_family"] == "image"


# --- le renommage est mesure ------------------------------------------------

def _build_repo_with_rename(repo: Path, renamed: str, text_size: int = 0) -> Path:
    """Depot jetable : `main` porte le carnet a son ANCIEN chemin, la
    branche `feature` le porte a son NOUVEL chemin, sans image.

    Le carnet garde ses identifiants de cellules : c'est ce qui permet de
    reconnaitre le renommage quand git ne le voit plus.
    """
    _git(repo, "init", "-b", "main")
    _git(repo, "config", "user.email", "test@example.invalid")
    _git(repo, "config", "user.name", "Test")
    _write_notebook(repo, _notebook(image=True, cell_id="cell-demo",
                                    text_size=text_size))
    _git(repo, "add", NOTEBOOK)
    _git(repo, "commit", "-m", "base")
    _git(repo, "checkout", "-b", "feature")
    (repo / Path(renamed).parent).mkdir(parents=True, exist_ok=True)
    _git(repo, "mv", NOTEBOOK, renamed)
    _write_notebook(repo, _notebook(image=False, cell_id="cell-demo",
                                    text_size=text_size), renamed)
    _git(repo, "add", renamed)
    _git(repo, "commit", "-m", "renomme, image perdue")
    return repo


def test_un_carnet_renomme_detecte_par_git_est_mesure(tmp_path, monkeypatch,
                                                       capsys):
    """Renommage que git VOIT (`R`) : les DEUX chemins sont mesures.

    C'est le cas des descentes en sous-series : le carnet garde l'essentiel
    de son contenu, git le voit comme un renommage, et l'organe compare
    l'ancien chemin a la base au nouveau chemin a la tete.

    CONTROLE NEGATIF : `--name-only` fait repasser ce test en rc 0
    (le chemin de base est perdu, le carnet est lu comme neuf, exempt).
    """
    renamed = "MyIA.AI.Notebooks/Demo/sub/demo.ipynb"
    _build_repo_with_rename(tmp_path, renamed, text_size=8000)
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(rvg, "REPO_ROOT", tmp_path)

    rc = rvg.main(["--base-ref", "main"])
    out = capsys.readouterr().out
    assert rc == 1, out
    assert "CIBLE" in out
    assert "LOST_MIME" in out
    assert renamed in out
    assert "renomme" in out


def test_un_carnet_renomme_non_detecte_par_git_est_mesure(tmp_path,
                                                           monkeypatch, capsys):
    """Renommage que git ne voit PLUS (`D` + `A`) : il est quand meme mesure.

    Mesure (13/11) : un carnet dont la sortie image a disparu tombe a
    ~1 % de similarite de contenu. `git diff -M50%` le rend alors `D` +
    `A` -- et l'ancien filtre `MR` le sortait de la liste : le carnet
    n'etait pas mesure DU TOUT. Les identifiants de cellules (nbformat
    4.5) survivent au renommage ET a la re-execution : ils servent
    d'oracle d'appariement.
    """
    renamed = "MyIA.AI.Notebooks/Demo/sub/demo.ipynb"
    _build_repo_with_rename(tmp_path, renamed, text_size=0)
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(rvg, "REPO_ROOT", tmp_path)

    rc = rvg.main(["--base-ref", "main"])
    out = capsys.readouterr().out
    assert rc == 1, out
    assert "CIBLE" in out
    assert "LOST_MIME" in out
    assert renamed in out


def test_un_carnet_neuf_ne_sest_pas_apparie(tmp_path, monkeypatch, capsys):
    """CONTROLE NEGATIF de l'appariement : deux carnets sans rapport ne sont
    PAS apparies.

    L'appariement par identifiants de cellules ne doit pas transformer un
    ajout legitime en renommage mesure : sans cela, un carnet neuf serait
    compare a un carnet supprime, et une fausse perte de rendu serait
    rapportee.
    """
    _git(tmp_path, "init", "-b", "main")
    _git(tmp_path, "config", "user.email", "test@example.invalid")
    _git(tmp_path, "config", "user.name", "Test")
    _write_notebook(tmp_path, _notebook(image=True, cell_id="cell-ancien"))
    _git(tmp_path, "add", NOTEBOOK)
    _git(tmp_path, "commit", "-m", "base")
    _git(tmp_path, "checkout", "-b", "feature")
    _git(tmp_path, "rm", NOTEBOOK)
    _write_notebook(tmp_path, _notebook(image=True, cell_id="cell-neuf"),
                    "MyIA.AI.Notebooks/Demo/neuf.ipynb")
    _git(tmp_path, "add", "-A")
    _git(tmp_path, "commit", "-m", "remplacement")
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(rvg, "REPO_ROOT", tmp_path)

    rc = rvg.main(["--base-ref", "main"])
    out = capsys.readouterr().out
    assert rc == 0, out
    assert "CIBLE" not in out


def test_le_renommage_passe_les_deux_chemins_a_l_organe_natif(tmp_path,
                                                                monkeypatch):
    """L'organe natif recoit le chemin de BASE et le chemin de TETE."""
    renamed = "MyIA.AI.Notebooks/Demo/sub/demo.ipynb"
    _build_repo_with_rename(tmp_path, renamed, text_size=8000)
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(rvg, "REPO_ROOT", tmp_path)

    calls: list[tuple[str, str | None]] = []
    original = rvg.rvd.scan_notebook

    def spy(path, base_ref, head_ref=None, **kwargs):
        calls.append((str(path), kwargs.get("head_path")))
        return original(path, base_ref, head_ref, **kwargs)

    monkeypatch.setattr(rvg.rvd, "scan_notebook", spy)
    rvg.main(["--base-ref", "main"])
    assert calls, "l'organe natif n'a pas ete appele"
    base_path, head_path = calls[0]
    assert Path(base_path).as_posix() == NOTEBOOK, "le chemin de base a change"
    assert Path(head_path).as_posix() == renamed, "le chemin de tete a change"


# --- l'echec de git n'est pas un « rien a signaler » -------------------------

def test_un_echec_de_git_diff_rend_rc_2(repo, monkeypatch, capsys):
    """Un `git diff` en echec n'est PAS « aucun carnet modifie ».

    Sans ce rc 2, une PR dont le diff n'a pas pu etre lu publie un
    « [OK] rien a signaler » en rc 0 : un vert muet sur une mesure qui
    n'a pas eu lieu.

    Le merge-base, lui, reste resolvable : c'est bien l'echec du DIFF
    qui est mesure ici, pas l'abstention de l'ancre.
    """
    reel = rvg.git

    def git_casse_diff(*args: str):
        if "diff" in args:
            return subprocess.CompletedProcess(["git", *args], 128, "",
                                               "fatal: bad revision\n")
        return reel(*args)

    monkeypatch.setattr(rvg, "git", git_casse_diff)
    rc = rvg.main(["--base-ref", "main"])
    out = capsys.readouterr().out
    assert rc == 2, out
    assert "ABSTENTION" in out
    assert "aucun carnet" in out


def test_un_echec_de_git_diff_est_signale_en_json(repo, monkeypatch, capsys):
    """Le meme echec, en JSON : l'abstention est lisible par la machine."""
    reel = rvg.git

    def git_casse_diff(*args: str):
        if "diff" in args:
            return subprocess.CompletedProcess(["git", *args], 128, "",
                                               "fatal: bad revision\n")
        return reel(*args)

    monkeypatch.setattr(rvg, "git", git_casse_diff)
    rc = rvg.main(["--base-ref", "main", "--json"])
    out = capsys.readouterr().out
    assert rc == 2, out
    report = json.loads(out)
    assert report["abstained"] is True


# --- le plafond se nomme, il ne tronque pas ----------------------------------

def test_le_plafond_ne_tronque_plus_il_se_nomme(tmp_path, monkeypatch,
                                                 capsys):
    """Une fournee de serie entiere passe sous le plafond : tous les carnets
    sont mesures, et le franchissement est dit.

    La version precedente tronquait (`notebooks[:MAX_NOTEBOOKS]`) SANS LE
    DIRE : la moitie de la fournee passait pour « rien a signaler ».
    """
    paths = [f"MyIA.AI.Notebooks/Demo/n{i}.ipynb" for i in range(3)]
    _git(tmp_path, "init", "-b", "main")
    _git(tmp_path, "config", "user.email", "test@example.invalid")
    _git(tmp_path, "config", "user.name", "Test")
    for path in paths:
        _write_notebook(tmp_path, _notebook(image=True), path)
    _git(tmp_path, "add", ".")
    _git(tmp_path, "commit", "-m", "base")
    _git(tmp_path, "checkout", "-b", "feature")
    for path in paths:
        _write_notebook(tmp_path, _notebook(image=False), path)
    _git(tmp_path, "add", ".")
    _git(tmp_path, "commit", "-m", "tete")
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(rvg, "REPO_ROOT", tmp_path)
    # Plafond ramene a 1 : les trois carnets sont au-dela.
    monkeypatch.setattr(rvg, "MAX_NOTEBOOKS", 1)

    rc = rvg.main(["--base-ref", "main"])
    out = capsys.readouterr().out
    assert rc == 1, out
    assert "PLAFOND" in out
    # Les TROIS carnets ont ete mesures : aucun n'a ete ecarte.
    cibles = [ligne for ligne in out.splitlines() if ligne.startswith("  - CIBLE")]
    assert len(cibles) == 3, out


def test_au_dela_du_plafond_le_rapport_json_nomme_le_total(tmp_path,
                                                            monkeypatch,
                                                            capsys):
    """Le rapport JSON expose le total mesure et le franchissement."""
    paths = [f"MyIA.AI.Notebooks/Demo/n{i}.ipynb" for i in range(2)]
    _git(tmp_path, "init", "-b", "main")
    _git(tmp_path, "config", "user.email", "test@example.invalid")
    _git(tmp_path, "config", "user.name", "Test")
    for path in paths:
        _write_notebook(tmp_path, _notebook(image=True), path)
    _git(tmp_path, "add", ".")
    _git(tmp_path, "commit", "-m", "base")
    _git(tmp_path, "checkout", "-b", "feature")
    for path in paths:
        _write_notebook(tmp_path, _notebook(image=False), path)
    _git(tmp_path, "add", ".")
    _git(tmp_path, "commit", "-m", "tete")
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(rvg, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(rvg, "MAX_NOTEBOOKS", 1)

    rc = rvg.main(["--base-ref", "main", "--json"])
    assert rc == 1
    report = json.loads(capsys.readouterr().out)
    assert report["notebooks_total"] == 2
    assert report["above_cap"] is True
    assert len(report["scanned"]) == 2


# --- le registre -------------------------------------------------------------

def test_le_garde_est_declare_dans_le_registre():
    assert len(TRANCHE46) == 1
    guard = TRANCHE46[0]
    assert guard.name == "Render volume delta (#11656 advisory)"
    assert guard.source == "render-volume-delta-advisory.yml"
    assert guard.absorbed is True
    # Etape 1 de la tranche : le verdict est signale, jamais bloquant.
    assert guard.blocking is False
    assert guard.needs_base is True
    assert guard.diff_bounded is True
    # rc=2 (abstention / erreur structurelle) est NEUTRE, jamais un vert.
    assert 2 in guard.warn_rc


def test_le_nom_est_byte_identique_au_job_source():
    """Le nom rendu du job source fait foi : le registre l'adopte mot pour
    mot (controle positif d'identite, `check_absorbed_check_run_identity.py`)."""
    from check_unique_check_run_names import _load_yaml, _parse_workflow

    workflow = Path(__file__).resolve().parents[2] / ".github" / "workflows" \
        / "render-volume-delta-advisory.yml"
    data = _parse_workflow(workflow.read_text(encoding="utf-8"), _load_yaml())
    assert data is not None, "workflow source illisible"
    rendered = [job.get("name") or key
                for key, job in data.get("jobs", {}).items()]
    assert TRANCHE46[0].name in rendered


def test_le_perimetre_couvre_les_actifs_et_l_organe():
    paths = TRANCHE46[0].paths
    assert "MyIA.AI.Notebooks/**/*.ipynb" in paths
    assert "scripts/notebook_tools/check_render_volume_delta.py" in paths
    assert "scripts/ci/run_render_volume_guard.py" in paths


def test_le_garde_est_selectionne_par_son_perimetre():
    import fast_lane

    guard = TRANCHE46[0]
    assert fast_lane.guard_applies(guard, [NOTEBOOK]) is True
    assert fast_lane.guard_applies(guard, ["scripts/ci/fast_lane.py"]) is False


def test_l_argv_porte_le_bornage_de_la_base():
    """L'organe de bornage (`check_absorbed_argv_scope.py`) voit le jeton
    explicite ET la valeur `{base_ref}` : la base vient de la lane."""
    import fast_lane

    argv = TRANCHE46[0].argv
    assert "--base-ref" in argv
    index = argv.index("--base-ref")
    assert argv[index + 1] == "{base_ref}"
    resolved = fast_lane.substitute(argv, {"base_ref": "origin/main"})
    assert resolved[resolved.index("--base-ref") + 1] == "origin/main"
