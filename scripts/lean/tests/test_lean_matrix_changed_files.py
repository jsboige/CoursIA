#!/usr/bin/env python3
"""Non-regression du job `changes` de ``lean-ci-matrix.yml`` (#22065).

Le trou : les deux lectures de l'API du job etaient repliees en silence
(``|| echo -n "" > "$out"``). Un 403 de quota rendait la liste des
fichiers modifies VIDE, donc ``any=false``, donc le build Lean etait
``skipped`` -- et ``skipped`` se replie en vert : un build qui n'a pas eu
lieu s'affichait comme fait (instance #21999, run 39814286963).

Ces tests verrouillent quatre choses :

  1. une lecture d'API en echec **ne peut pas** produire une liste vide
     silencieuse -- l'appelant sort en erreur et **n'ecrit aucun fichier**
     de sortie ;
  2. le workflow lui-meme ne peut pas reintroduire le repli muet ;
  3. git local repond D'ABORD (zero quota d'API, #22065) : quand git
     repond, l'API n'est jamais consultee ; une erreur git declenche le
     repli, jamais une liste vide ; les deux sources en echec restent
     bruyantes ;
  4. le checkout du job emporte les deux parents (``fetch-depth: 2``) --
     sans lui, la lecture git serait structurellement inerte.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from lean_matrix_changed_files import (  # noqa: E402
    ApiError,
    SELF_COVER,
    main,
)

WORKFLOW = REPO / ".github" / "workflows" / "lean-ci-matrix.yml"


def _boom(*_args, **_kwargs):
    raise ApiError("gh api a echoue (rc=1) : API rate limit exceeded (HTTP 403)")


def test_1_echec_api_ne_produit_aucun_fichier(tmp_path, monkeypatch):
    """Le cas mesure (#21999) : 403 -> pas de liste vide, sortie non nulle."""
    monkeypatch.setattr("lean_matrix_changed_files._gh_api", _boom)
    monkeypatch.setattr("lean_matrix_changed_files.time.sleep", lambda _s: None)
    out = tmp_path / "changed.txt"
    rc = main([
        "--event", "pull_request", "--repo", "jsboige/CoursIA",
        "--pr", "21999", "--out", str(out), "--sleep", "0",
    ])
    assert rc == 1
    assert not out.exists(), "un echec de l'API ne doit ecrire aucun fichier"


def test_2_echec_api_apres_les_tentatives_reste_echec(tmp_path, monkeypatch):
    """Meme apres une nouvelle tentative, l'echec reste bruyant."""
    calls = {"n": 0}

    def _always_fail(*_args, **_kwargs):
        calls["n"] += 1
        raise ApiError("HTTP 403")

    monkeypatch.setattr("lean_matrix_changed_files._gh_api", _always_fail)
    monkeypatch.setattr("lean_matrix_changed_files.time.sleep", lambda _s: None)
    out = tmp_path / "changed.txt"
    rc = main([
        "--event", "pull_request", "--repo", "jsboige/CoursIA",
        "--pr", "21999", "--out", str(out), "--retries", "2", "--sleep", "0",
    ])
    assert rc == 1
    assert not out.exists()
    assert calls["n"] == 3, "2 tentatives + 1 = 3 appels"


def test_3_reussite_ecrit_la_liste(tmp_path, monkeypatch):
    monkeypatch.setattr(
        "lean_matrix_changed_files._gh_api",
        lambda *a, **k: "a.lean\nb.lean\n",
    )
    out = tmp_path / "changed.txt"
    rc = main([
        "--event", "pull_request", "--repo", "jsboige/CoursIA",
        "--pr", "21999", "--out", str(out),
    ])
    assert rc == 0
    assert out.read_text(encoding="utf-8").splitlines() == ["a.lean", "b.lean"]


def test_4_la_nouvelle_tentative_rattrape_le_403(tmp_path, monkeypatch):
    """Le 403 de quota est transitoire : le rejeu du job a reussi sur
    l'instance mesuree. Une tentative suffit a ne pas perdre le build."""
    calls = {"n": 0}

    def _fail_then_ok(*_args, **_kwargs):
        calls["n"] += 1
        if calls["n"] == 1:
            raise ApiError("HTTP 403")
        return "a.lean\n"

    monkeypatch.setattr("lean_matrix_changed_files._gh_api", _fail_then_ok)
    monkeypatch.setattr("lean_matrix_changed_files.time.sleep", lambda _s: None)
    out = tmp_path / "changed.txt"
    rc = main([
        "--event", "pull_request", "--repo", "jsboige/CoursIA",
        "--pr", "21999", "--out", str(out), "--sleep", "0",
    ])
    assert rc == 0
    assert out.read_text(encoding="utf-8").splitlines() == ["a.lean"]


def test_5_push_nouvelle_branche_donne_le_self_cover(tmp_path, monkeypatch):
    monkeypatch.setattr(
        "lean_matrix_changed_files._gh_api",
        lambda *a, **k: pytest.fail("aucun appel API sur une nouvelle branche"),
    )
    out = tmp_path / "changed.txt"
    rc = main([
        "--event", "push", "--repo", "jsboige/CoursIA",
        "--before", "0000000000000000000000000000000000000000",
        "--sha", "abc123", "--out", str(out),
    ])
    assert rc == 0
    assert out.read_text(encoding="utf-8").splitlines() == [SELF_COVER]


def test_6_workflow_dispatch_donne_le_self_cover(tmp_path, monkeypatch):
    monkeypatch.setattr(
        "lean_matrix_changed_files._gh_api",
        lambda *a, **k: pytest.fail("aucun appel API en workflow_dispatch"),
    )
    out = tmp_path / "changed.txt"
    rc = main([
        "--event", "workflow_dispatch", "--repo", "jsboige/CoursIA",
        "--out", str(out),
    ])
    assert rc == 0
    assert out.read_text(encoding="utf-8").splitlines() == [SELF_COVER]


def test_7_le_workflow_ne_peut_plus_ecraser_la_liste_en_silence():
    """Garde de non-regression sur le workflow lui-meme : le repli muet
    (``|| echo -n "" > "$out"``) ne doit plus apparaitre dans le CODE.

    Les lignes de commentaire sont ignorees : le workflow documente le
    trou ferme, et un commentaire n'est pas une commande.
    """
    lines = WORKFLOW.read_text(encoding="utf-8").splitlines()
    code = [ln for ln in lines if not ln.lstrip().startswith("#")]
    text = "\n".join(code)
    assert 'echo -n "" > "$out"' not in text, (
        "le workflow reintroduit le repli muet : un echec de l'API "
        "produirait une liste vide et un faux vert"
    )
    assert "|| echo -n" not in text, (
        "le workflow reintroduit un repli muet sur l'echec de l'API"
    )


def test_8_le_workflow_appelle_le_lecteur_echouant():
    """Le job doit appeler le lecteur en Python, pas refaire l'appel en
    shell (le shell peut reintroduire le repli muet)."""
    text = WORKFLOW.read_text(encoding="utf-8")
    assert "scripts/lean/lean_matrix_changed_files.py" in text


# --- Couche git d'abord, API en repli (#22065, 2026-11-15) ---------------


def _run_git(cwd: Path, *args: str) -> str:
    proc = subprocess.run(
        ["git", *args],
        cwd=cwd,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    assert proc.returncode == 0, f"git {args} a echoue : {proc.stderr}"
    return proc.stdout


def test_9_git_repond_l_api_n_est_jamais_consultee(tmp_path, monkeypatch):
    """Git d'abord : quand git repond, la lecture API -- donc le quota
    d'installation partage -- n'est pas consommee (le rouge mesure de
    #26004 ne tient plus)."""
    monkeypatch.setattr(
        "lean_matrix_changed_files._git_pull_request_files",
        lambda _sha: ["x.lean", "y.lean"],
    )
    monkeypatch.setattr(
        "lean_matrix_changed_files._gh_api",
        lambda *a, **k: pytest.fail(
            "l'API ne doit pas etre consultee quand git repond"
        ),
    )
    out = tmp_path / "changed.txt"
    rc = main([
        "--event", "pull_request", "--repo", "jsboige/CoursIA",
        "--pr", "26004", "--sha", "a" * 40, "--out", str(out),
    ])
    assert rc == 0
    assert out.read_text(encoding="utf-8").splitlines() == ["x.lean", "y.lean"]


def test_10_git_decline_repli_sur_l_api(tmp_path, monkeypatch):
    """Git ne peut pas repondre (parent absent, hors depot...) : la
    lecture retombe sur l'API d'origine."""
    monkeypatch.setattr(
        "lean_matrix_changed_files._git_pull_request_files",
        lambda _sha: None,
    )
    monkeypatch.setattr(
        "lean_matrix_changed_files._gh_api",
        lambda *a, **k: "a.lean\n",
    )
    out = tmp_path / "changed.txt"
    rc = main([
        "--event", "pull_request", "--repo", "jsboige/CoursIA",
        "--pr", "26004", "--sha", "a" * 40, "--out", str(out),
    ])
    assert rc == 0
    assert out.read_text(encoding="utf-8").splitlines() == ["a.lean"]


def test_11_git_et_api_echouent_sortie_non_nulle(tmp_path, monkeypatch):
    """Le rouge mesure (#26004) ne doit pas devenir un faux vert : git ET
    l'API tombent -> aucun fichier ecrit, sortie non nulle."""
    monkeypatch.setattr(
        "lean_matrix_changed_files._git_pull_request_files",
        lambda _sha: None,
    )
    monkeypatch.setattr("lean_matrix_changed_files._gh_api", _boom)
    monkeypatch.setattr("lean_matrix_changed_files.time.sleep", lambda _s: None)
    out = tmp_path / "changed.txt"
    rc = main([
        "--event", "pull_request", "--repo", "jsboige/CoursIA",
        "--pr", "26004", "--sha", "a" * 40,
        "--out", str(out), "--sleep", "0",
    ])
    assert rc == 1
    assert not out.exists(), "git et API en echec : aucun fichier de sortie"


def test_12_reussite_git_diff_vide_liste_vide_legitime(tmp_path, monkeypatch):
    """Une REUSSITE git sur un diff vide vaut liste vide (commit de
    fusion sans changement face a sa base) : le fichier est ecrit vide,
    l'API n'est pas consultee -- seule une erreur git declencherait le
    repli, jamais un diff vide reussi."""
    repo = tmp_path / "repo"
    repo.mkdir()
    monkeypatch.chdir(repo)
    _run_git(repo, "init", "-q")
    _run_git(repo, "config", "user.email", "ci@example.com")
    _run_git(repo, "config", "user.name", "CI")
    (repo / "base.txt").write_text("base\n", encoding="utf-8")
    _run_git(repo, "add", "base.txt")
    _run_git(repo, "commit", "-q", "-m", "base")
    _run_git(repo, "checkout", "-q", "-b", "feature")
    _run_git(repo, "commit", "-q", "--allow-empty", "-m", "vide")
    _run_git(repo, "checkout", "-q", "-")
    _run_git(repo, "merge", "-q", "--no-ff", "-m", "fusion", "feature")
    merge_sha = _run_git(repo, "rev-parse", "HEAD").strip()

    monkeypatch.setattr(
        "lean_matrix_changed_files._gh_api",
        lambda *a, **k: pytest.fail(
            "git a repondu (vide) : l'API ne doit pas etre consultee"
        ),
    )
    out = tmp_path / "changed.txt"
    rc = main([
        "--event", "pull_request", "--repo", "jsboige/CoursIA",
        "--pr", "26004", "--sha", merge_sha, "--out", str(out),
    ])
    assert rc == 0
    assert out.exists(), "une reussite git ecrit le fichier, meme vide"
    assert out.read_text(encoding="utf-8") == ""


def test_13_push_git_repond_l_api_n_est_jamais_consultee(
    tmp_path, monkeypatch
):
    """push : avant et apres presents localement -> diff git, zero
    appel API."""
    monkeypatch.setattr(
        "lean_matrix_changed_files._git_push_files",
        lambda _before, _sha: ["m.lean"],
    )
    monkeypatch.setattr(
        "lean_matrix_changed_files._gh_api",
        lambda *a, **k: pytest.fail(
            "l'API ne doit pas etre consultee quand git repond"
        ),
    )
    out = tmp_path / "changed.txt"
    rc = main([
        "--event", "push", "--repo", "jsboige/CoursIA",
        "--before", "b" * 40, "--sha", "c" * 40, "--out", str(out),
    ])
    assert rc == 0
    assert out.read_text(encoding="utf-8").splitlines() == ["m.lean"]


def test_14_push_git_decline_repli_sur_le_compare_api(tmp_path, monkeypatch):
    """push : un objet absent localement (profondeur 2, force-push...)
    -> compare API d'origine."""
    monkeypatch.setattr(
        "lean_matrix_changed_files._git_push_files",
        lambda _before, _sha: None,
    )
    monkeypatch.setattr(
        "lean_matrix_changed_files._gh_api",
        lambda *a, **k: "p.lean\n",
    )
    out = tmp_path / "changed.txt"
    rc = main([
        "--event", "push", "--repo", "jsboige/CoursIA",
        "--before", "b" * 40, "--sha", "c" * 40, "--out", str(out),
    ])
    assert rc == 0
    assert out.read_text(encoding="utf-8").splitlines() == ["p.lean"]


def test_15_vrai_depot_commit_de_fusion_a_deux_parents(tmp_path, monkeypatch):
    """Controle positif sur un vrai depot : un commit de fusion M(base,
    feature) a bien deux parents, et le lecteur sert ``git diff HEAD^1
    HEAD`` -- exactement les fichiers de la branche, pas ceux de la base
    (qui a bouge entre temps), sans consulter l'API."""
    repo = tmp_path / "repo"
    repo.mkdir()
    monkeypatch.chdir(repo)
    _run_git(repo, "init", "-q")
    _run_git(repo, "config", "user.email", "ci@example.com")
    _run_git(repo, "config", "user.name", "CI")
    (repo / "base.txt").write_text("base\n", encoding="utf-8")
    _run_git(repo, "add", "base.txt")
    _run_git(repo, "commit", "-q", "-m", "base")
    _run_git(repo, "checkout", "-q", "-b", "feature")
    (repo / "a.lean").write_text("a\n", encoding="utf-8")
    (repo / "sub").mkdir()
    (repo / "sub" / "b.lean").write_text("b\n", encoding="utf-8")
    _run_git(repo, "add", ".")
    _run_git(repo, "commit", "-q", "-m", "feature")
    _run_git(repo, "checkout", "-q", "-")
    # La base bouge APRES le branchement : le diff au premier parent
    # doit rendre la branche, pas ce mouvement de base.
    (repo / "base.txt").write_text("base-modifiee\n", encoding="utf-8")
    _run_git(repo, "add", "base.txt")
    _run_git(repo, "commit", "-q", "-m", "base bouge")
    _run_git(repo, "merge", "-q", "--no-ff", "-m", "fusion", "feature")
    merge_sha = _run_git(repo, "rev-parse", "HEAD").strip()
    parents = _run_git(
        repo, "rev-list", "--parents", "-n", "1", "HEAD"
    ).split()
    assert len(parents) == 3, "le commit de fusion de test doit avoir 2 parents"

    monkeypatch.setattr(
        "lean_matrix_changed_files._gh_api",
        lambda *a, **k: pytest.fail(
            "git repond : l'API ne doit pas etre consultee"
        ),
    )
    out = tmp_path / "changed.txt"
    rc = main([
        "--event", "pull_request", "--repo", "jsboige/CoursIA",
        "--pr", "26004", "--sha", merge_sha, "--out", str(out),
    ])
    assert rc == 0
    assert sorted(out.read_text(encoding="utf-8").splitlines()) == [
        "a.lean", "sub/b.lean",
    ]


def test_16_head_local_discordant_git_decline(tmp_path, monkeypatch):
    """Hors Actions (HEAD local != sha de l'evenement), git ne doit
    JAMAIS servir le diff local : c'est le garde-fou qui empeche de
    repondre depuis un checkout sans rapport. Repli API."""
    repo = tmp_path / "repo"
    repo.mkdir()
    monkeypatch.chdir(repo)
    _run_git(repo, "init", "-q")
    _run_git(repo, "config", "user.email", "ci@example.com")
    _run_git(repo, "config", "user.name", "CI")
    (repo / "base.txt").write_text("base\n", encoding="utf-8")
    _run_git(repo, "add", "base.txt")
    _run_git(repo, "commit", "-q", "-m", "base")
    (repo / "autre.txt").write_text("x\n", encoding="utf-8")
    _run_git(repo, "add", "autre.txt")
    _run_git(repo, "commit", "-q", "-m", "autre")

    sha_discordant = "d" * 40
    api_args: list[str] = []

    def _fake_gh_api(args, **_kwargs):
        api_args.extend(args)
        return "via-api.lean\n"

    monkeypatch.setattr("lean_matrix_changed_files._gh_api", _fake_gh_api)
    out = tmp_path / "changed.txt"
    rc = main([
        "--event", "pull_request", "--repo", "jsboige/CoursIA",
        "--pr", "26004", "--sha", sha_discordant, "--out", str(out),
    ])
    assert rc == 0
    assert out.read_text(encoding="utf-8").splitlines() == ["via-api.lean"]
    assert any("pulls" in a for a in api_args), "le repli doit passer par l'API"


def test_17_le_workflow_checkout_emporte_les_deux_parents():
    """Sans ``fetch-depth: 2`` au checkout du job `changes`, le parent 1
    (base) manque localement : la lecture git serait structurellement
    inerte et le correctif ne servirait a rien."""
    text = WORKFLOW.read_text(encoding="utf-8")
    assert "fetch-depth: 2" in text, (
        "le checkout du job changes doit etre de profondeur 2 pour que "
        "git diff HEAD^1 HEAD soit possible"
    )


def test_18_deplacement_hors_d_un_lake_remonte_les_deux_chemins(
    tmp_path, monkeypatch
):
    """Un fichier deplace d'un lake vers un autre doit faire remonter
    l'ancien ET le nouveau chemin (``--no-renames``) : sinon le lake qui
    a perdu le fichier n'est pas rebati, et sa casse passe inapercue."""
    repo = tmp_path / "repo"
    repo.mkdir()
    monkeypatch.chdir(repo)
    _run_git(repo, "init", "-q")
    _run_git(repo, "config", "user.email", "ci@example.com")
    _run_git(repo, "config", "user.name", "CI")
    (repo / "lakeA").mkdir()
    (repo / "lakeA" / "M.lean").write_text(
        "theorem t : 1 = 1 := rfl\n" * 20, encoding="utf-8"
    )
    _run_git(repo, "add", ".")
    _run_git(repo, "commit", "-q", "-m", "base")
    _run_git(repo, "checkout", "-q", "-b", "feature")
    (repo / "lakeB").mkdir()
    _run_git(repo, "mv", "lakeA/M.lean", "lakeB/M.lean")
    _run_git(repo, "commit", "-q", "-m", "deplacement")
    _run_git(repo, "checkout", "-q", "-")
    _run_git(repo, "merge", "-q", "--no-ff", "-m", "fusion", "feature")
    merge_sha = _run_git(repo, "rev-parse", "HEAD").strip()

    monkeypatch.setattr(
        "lean_matrix_changed_files._gh_api",
        lambda *a, **k: pytest.fail(
            "git repond : l'API ne doit pas etre consultee"
        ),
    )
    out = tmp_path / "changed.txt"
    rc = main([
        "--event", "pull_request", "--repo", "jsboige/CoursIA",
        "--pr", "26004", "--sha", merge_sha, "--out", str(out),
    ])
    assert rc == 0
    assert sorted(out.read_text(encoding="utf-8").splitlines()) == [
        "lakeA/M.lean", "lakeB/M.lean",
    ]
