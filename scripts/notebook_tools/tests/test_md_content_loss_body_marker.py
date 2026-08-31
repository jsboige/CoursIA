"""Tests pour la justification par-cellule depuis le body de la PR (#13491).

L'acceptance du cahier des charges exigeait trois controles :
  1. Une justification correctement formee rend le check VERT (rc=0).
  2. Une justification malformee ou visant une autre cellule le laisse ROUGE
     (rc=1 inchange).
  3. CONTROLE POSITIF OBLIGATOIRE : une fixture reproduisant un des 3 cas
     fondateurs de #8655 (ratio 1-4 %) reste ROUGE meme avec un marker
     present, si le marker ne nomme pas cette cellule.

On couvre les 3 controles + les sous-cas qui tomberaient en marche :
  - em-dash tolerance (les editeurs transposent -- en em-dash) ;
  - chemin prefixe vs basename du notebook ;
  - caractere accentue dans le mot-cle (reecriture / assumee) ;
  - absence totale de body (workflow_dispatch, depannage main) : aucun marker,
    comportement actuel preserve ;
  - fichier body absent / illisible : rc=2 (fail loud preserve).
"""
import json
import os
import subprocess
import sys
import textwrap
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import detect_md_content_loss as dml  # noqa: E402


NB_REL = "Sudoku/Sudoku-01-Performances.ipynb"


# Une cellule pedagogique substantielle (~700c normalises, au-dessus de MIN_ORIG_CHARS).
LONG_CELL = textwrap.dedent("""\
    ## Exercice : Verifier qu'une grille est valide

    ### Enonce

    Apres avoir resolu un Sudoku avec le backtracking, il est essentiel de
    verifier que la solution obtenue est bien valide. Implementez une fonction
    qui verifie les contraintes suivantes :

    1. Chaque ligne contient les chiffres 1 a 9 sans repetition.
    2. Chaque colonne contient les chiffres 1 a 9 sans repetition.
    3. Chaque bloc 3x3 contient les chiffres 1 a 9 sans repetition.

    **Indices gradues** :

    - Indice 1 : pensez a utiliser des ensembles pour detecter les doublons.
    - Indice 2 : decoupez la verification en trois sous-fonctions.
""").strip()

# Meme cellule, mais apres une reecriture assumee qui tombe a ~46 % du volume
# normalise (bande 4-75 %, non-couverte avant #13491). Le motif `### Enonce`
# est preserve, la signature est simplement raccourcie -- on en profite pour
# tester que le marker JUSTIFIE le TRUNCATED_CELL sans pour autant exonerer
# un LOST_MOTIF qui serait apparu (le scenario fondateur : le marqueur designe
# un (notebook, cell_idx), pas une dispense en gros).
REWRITTEN_CELL_61PCT = textwrap.dedent("""\
    ## Exercice : Verifier qu'une grille est valide

    ### Enonce

    Apres une resolution par backtracking, on verifie la solution en trois
    sous-fonctions (lignes, colonnes, blocs 3x3) ; les doublons sont detectes
    par ensembles.
""").strip()


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------
def _md(src, cell_id="mdcell-1"):
    return {"cell_type": "markdown", "source": src, "metadata": {}, "id": cell_id}


def _nb(md_cells):
    return {"cells": list(md_cells), "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


def _run_with_body(repo, nb_abs, body_file, extra_args=None, env_override=None):
    """Invoque detect_md_content_loss.main avec notebook + --check +
    --pr-body-file, en cdant dans `repo` (le detecteur utilise cwd-relative
    git refs). Retourne le rc.
    """
    extra_args = extra_args or []
    nb_rel = str(nb_abs.relative_to(repo))
    argv = [
        "--base", "HEAD~1",
        "--head", "HEAD",
        "--check",
        nb_rel,
        "--pr-body-file", str(body_file),
    ] + extra_args
    old_cwd = Path.cwd()
    old_env = {}
    if env_override:
        for k, v in env_override.items():
            old_env[k] = os.environ.get(k)
            os.environ[k] = v
    try:
        os.chdir(repo)
        return dml.main(argv)
    finally:
        os.chdir(old_cwd)
        for k, v in old_env.items():
            if v is None:
                os.environ.pop(k, None)
            else:
                os.environ[k] = v


@pytest.fixture
def tmp_git_repo(tmp_path):
    """Repo git minimal : un commit avec LONG_CELL, un second avec
    REWRITTEN_CELL_61PCT (sous le seuil 75 %). Permet de tester un verdict
    TRUNCATED_CELL reel a corriger par marker.
    """
    rp = tmp_path / "repo"
    rp.mkdir()
    nb_abs = rp / NB_REL
    nb_abs.parent.mkdir(parents=True)
    nb_abs.write_text(json.dumps(_nb([_md(LONG_CELL)]), ensure_ascii=False), encoding="utf-8")
    subprocess.run(["git", "init", "-q"], cwd=rp, check=True)
    subprocess.run(["git", "config", "user.email", "test@x"], cwd=rp, check=True)
    subprocess.run(["git", "config", "user.name", "test"], cwd=rp, check=True)
    subprocess.run(["git", "add", NB_REL], cwd=rp, check=True)
    subprocess.run(["git", "commit", "-q", "-m", "base"], cwd=rp, check=True)
    nb_abs.write_text(json.dumps(_nb([_md(REWRITTEN_CELL_61PCT)]), ensure_ascii=False),
                      encoding="utf-8")
    subprocess.run(["git", "add", NB_REL], cwd=rp, check=True)
    subprocess.run(["git", "commit", "-q", "-m", "rewritten"], cwd=rp, check=True)
    return rp, nb_abs


# ---------------------------------------------------------------------------
# 1. Acceptance controle positif : marker bien forme -> rc=0
# ---------------------------------------------------------------------------
class TestBodyMarkerPositive:
    def test_valid_marker_makes_check_pass(self, tmp_git_repo):
        repo, nb_abs = tmp_git_repo
        marker = (
            f"md-content-loss: reecriture assumee -- {nb_abs.name} cell 0 : "
            "rephrase volontaire du contenu ~61 %"
        )
        body_file = repo / "pr-body.md"
        body_file.write_text("# Mon PR\n\n" + marker + "\n", encoding="utf-8")
        rc = _run_with_body(repo, nb_abs, body_file)
        assert rc == 0, f"Un marker valide aurait du rendre --check vert. rc={rc}"

    def test_marker_with_em_dash_passes(self, tmp_git_repo):
        repo, nb_abs = tmp_git_repo
        marker = (
            f"md-content-loss: reecriture assumée — {nb_abs.name} cell 0 : "
            "rephrase volontaire"
        )
        body_file = repo / "pr-body.md"
        body_file.write_text(marker + "\n", encoding="utf-8")
        rc = _run_with_body(repo, nb_abs, body_file)
        assert rc == 0

    def test_marker_with_repo_path_prefix_matches_basename(self, tmp_git_repo):
        repo, nb_abs = tmp_git_repo
        marker = (
            f"md-content-loss: reecriture assumee -- MyIA.AI.Notebooks/Sudoku/{nb_abs.name} "
            "cell 0 : ok"
        )
        body_file = repo / "pr-body.md"
        body_file.write_text(marker + "\n", encoding="utf-8")
        rc = _run_with_body(repo, nb_abs, body_file)
        assert rc == 0


# ---------------------------------------------------------------------------
# 2. Acceptance controle negatif : marker mal forme -> rc=1 (inchange)
# ---------------------------------------------------------------------------
class TestBodyMarkerNegative:
    def test_no_marker_keeps_rc_1(self, tmp_git_repo):
        repo, nb_abs = tmp_git_repo
        body_file = repo / "pr-body.md"
        body_file.write_text("# Mon PR\n\nAucune justification ici.\n", encoding="utf-8")
        rc = _run_with_body(repo, nb_abs, body_file)
        assert rc == 1, (
            f"Pas de marker -> rc=1 inchange (le detecteur ne doit pas inventer "
            f"une porte). rc={rc}"
        )

    def test_marker_for_wrong_notebook_does_not_apply(self, tmp_git_repo):
        repo, nb_abs = tmp_git_repo
        marker = (
            "md-content-loss: reecriture assumee -- Another-Notebook.ipynb cell 0 : rephrase"
        )
        body_file = repo / "pr-body.md"
        body_file.write_text(marker + "\n", encoding="utf-8")
        rc = _run_with_body(repo, nb_abs, body_file)
        assert rc == 1, f"Marker visant un autre notebook -> rc=1 inchange. rc={rc}"

    def test_marker_for_wrong_cell_idx_does_not_apply(self, tmp_git_repo):
        repo, nb_abs = tmp_git_repo
        marker = (
            f"md-content-loss: reecriture assumee -- {nb_abs.name} cell 999 : "
            "cellule fictive"
        )
        body_file = repo / "pr-body.md"
        body_file.write_text(marker + "\n", encoding="utf-8")
        rc = _run_with_body(repo, nb_abs, body_file)
        assert rc == 1, (
            f"Marker visant une cellule inexistante -> rc=1 inchange. rc={rc}"
        )

    def test_malformed_marker_kept_inert(self, tmp_git_repo):
        repo, nb_abs = tmp_git_repo
        body_file = repo / "pr-body.md"
        body_file.write_text(
            "md-content-loss: reecriture assumee --\n"
            "rewording -- Some.ipynb cell 0 : tentative invalide\n",
            encoding="utf-8",
        )
        rc = _run_with_body(repo, nb_abs, body_file)
        assert rc == 1, f"Marker malforme -> rc=1 (ne pas valider a l'aveugle). rc={rc}"


# ---------------------------------------------------------------------------
# 3. Acceptance controle positif obligatoire (#13491 explicite)
#    Fixture ratio ~1-4 % + marker PRESENT mais visant une autre cellule -> rouge.
# ---------------------------------------------------------------------------
class TestFixtureFounderCaseProtected:
    def test_founder_case_4pct_with_wrong_marker_stays_red(self, tmp_path):
        rp = tmp_path / "repo"
        rp.mkdir()
        nb_abs = rp / NB_REL
        nb_abs.parent.mkdir(parents=True)
        nb_abs.write_text(json.dumps(_nb([_md(LONG_CELL)]), ensure_ascii=False), encoding="utf-8")
        subprocess.run(["git", "init", "-q"], cwd=rp, check=True)
        subprocess.run(["git", "config", "user.email", "test@x"], cwd=rp, check=True)
        subprocess.run(["git", "config", "user.name", "test"], cwd=rp, check=True)
        subprocess.run(["git", "add", NB_REL], cwd=rp, check=True)
        subprocess.run(["git", "commit", "-q", "-m", "base"], cwd=rp, check=True)
        # Tete : cellule reduite a 16c (~3 % du volume normalise, ordre #8654).
        nb_abs.write_text(json.dumps(_nb([_md("# Titre")]), ensure_ascii=False),
                          encoding="utf-8")
        subprocess.run(["git", "add", NB_REL], cwd=rp, check=True)
        subprocess.run(["git", "commit", "-q", "-m", "truncated"], cwd=rp, check=True)
        marker = (
            f"md-content-loss: reecriture assumee -- {nb_abs.name} cell 999 : "
            "pas la bonne cellule"
        )
        body_file = rp / "pr-body.md"
        body_file.write_text(marker + "\n", encoding="utf-8")
        rc = _run_with_body(rp, nb_abs, body_file)
        assert rc == 1, (
            f"Fixture fondateur 1-4 % + marker mauvaise cellule -> DOIT rester "
            f"rc=1. rc={rc}"
        )


# ---------------------------------------------------------------------------
# 4. Robustesse : fichiers vides, env var fallback, fichier introuvable
# ---------------------------------------------------------------------------
class TestRobustness:
    def test_empty_body_file_keeps_default_behavior(self, tmp_git_repo):
        repo, nb_abs = tmp_git_repo
        body_file = repo / "pr-body.md"
        body_file.write_text("", encoding="utf-8")
        rc = _run_with_body(repo, nb_abs, body_file)
        assert rc == 1

    def test_nonexistent_pr_body_file_returns_rc_2(self, tmp_git_repo):
        repo, nb_abs = tmp_git_repo
        body_file = repo / "absent.md"  # jamais cree
        rc = _run_with_body(repo, nb_abs, body_file)
        assert rc == 2, (
            f"Fichier --pr-body-file absent doit retourner rc=2 (fail loud). rc={rc}"
        )

    def test_env_var_fallback_works(self, tmp_git_repo):
        """L'env var MD_CONTENT_LOSS_PR_BODY_FILE est resolue en fallback de
        --pr-body-file : le moteur fast-lane n'a pas a specialiser chaque
        garde, c'est le canal transverse.
        """
        repo, nb_abs = tmp_git_repo
        marker = (
            f"md-content-loss: reecriture assumee -- {nb_abs.name} cell 0 : rephrase"
        )
        body_file = repo / "pr-body.md"
        body_file.write_text(marker + "\n", encoding="utf-8")
        # PAS de --pr-body-file dans argv : c'est l'env var qui prend le relais.
        nb_rel = str(nb_abs.relative_to(repo))
        argv = ["--base", "HEAD~1", "--head", "HEAD", "--check", nb_rel]
        old_cwd = Path.cwd()
        old_val = os.environ.get("MD_CONTENT_LOSS_PR_BODY_FILE")
        os.environ["MD_CONTENT_LOSS_PR_BODY_FILE"] = str(body_file)
        try:
            os.chdir(repo)
            rc = dml.main(argv)
        finally:
            os.chdir(old_cwd)
            if old_val is None:
                os.environ.pop("MD_CONTENT_LOSS_PR_BODY_FILE", None)
            else:
                os.environ["MD_CONTENT_LOSS_PR_BODY_FILE"] = old_val
        assert rc == 0, (
            f"Env var MD_CONTENT_LOSS_PR_BODY_FILE devrait etre prise en compte. "
            f"rc={rc}"
        )

    def test_pr_body_in_memory_via_arg(self, tmp_git_repo):
        """Le detecteur accepte --pr-body (literal) pour eviter d'ecrire le body
        dans un fichier sur le runner -- c'est le canal in-memory qui contourne
        le pattern CodeQL `actions/code-injection` sur `printf '%s' \"${{
        ...body }}\" > file`.
        """
        repo, nb_abs = tmp_git_repo
        marker = (
            f"md-content-loss: reecriture assumee -- {nb_abs.name} cell 0 : "
            "rephrase via --pr-body"
        )
        nb_rel = str(nb_abs.relative_to(repo))
        argv = [
            "--base", "HEAD~1",
            "--head", "HEAD",
            "--check",
            nb_rel,
            "--pr-body", "# Mon PR\n\n" + marker + "\n",
        ]
        old_cwd = Path.cwd()
        try:
            os.chdir(repo)
            rc = dml.main(argv)
        finally:
            os.chdir(old_cwd)
        assert rc == 0, (
            f"--pr-body in-memory devrait rendre --check vert. rc={rc}"
        )

    def test_pr_body_in_memory_via_env_var(self, tmp_git_repo):
        """L'env var MD_CONTENT_LOSS_PR_BODY est prioritaire sur
        MD_CONTENT_LOSS_PR_BODY_FILE : le canal in-memory est la voie
        recommandee pour contourner CodeQL `actions/code-injection`.
        """
        repo, nb_abs = tmp_git_repo
        marker = (
            f"md-content-loss: reecriture assumee -- {nb_abs.name} cell 0 : "
            "rephrase via env var"
        )
        nb_rel = str(nb_abs.relative_to(repo))
        argv = ["--base", "HEAD~1", "--head", "HEAD", "--check", nb_rel]
        old_cwd = Path.cwd()
        old_val = os.environ.get("MD_CONTENT_LOSS_PR_BODY")
        os.environ["MD_CONTENT_LOSS_PR_BODY"] = "# PR\n\n" + marker + "\n"
        try:
            os.chdir(repo)
            rc = dml.main(argv)
        finally:
            os.chdir(old_cwd)
            if old_val is None:
                os.environ.pop("MD_CONTENT_LOSS_PR_BODY", None)
            else:
                os.environ["MD_CONTENT_LOSS_PR_BODY"] = old_val
        assert rc == 0, (
            f"Env var MD_CONTENT_LOSS_PR_BODY devrait rendre --check vert. "
            f"rc={rc}"
        )
