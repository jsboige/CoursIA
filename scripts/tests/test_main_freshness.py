"""Tests de la garde de fraicheur du tirage (coordination/main_freshness.py).

Incidents fondateurs (mesures du 2026-11-14) : un tirage servi sur un main
local en retard de 605 commits (« sature, tout est livre » -- faux), et un
avertissement de picker perime lu puis ignore. La garde REFUSE. Ces tests
pinnnent :

* le controle positif : main en retard -> refus, remede `git pull --ff-only` ;
* le controle positif : module du tirage divergent d'origin/main -> refus ;
* le controle NEGATIF : un clone a jour, organes conformes, PASSE ;
* l'echappatoire explicite `--allow-stale` -- dite dans la sortie JSON ;
* le clone pas sur main (worktree) : la mesure porte sur le main local ;
* la mesure impossible : fail-closed, jamais un vert sur un fetch rate ;
* le cablage dans tapis_rapide.main (refus = sortie 4, sans repli picker).

Aucun test ne touche le reseau : l'origin est un depot nu local (file://),
comme test_session_hygiene.py.
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

# cf. test_session_hygiene.py : subprocess git paralleles vs RLIMIT_NPROC sur
# le runner WSL self-hosted.
os.environ.setdefault("GIT_OPTIONAL_LOCKS", "0")
pytestmark = [
    pytest.mark.skipif(
        os.environ.get("CI") == "true"
        and os.environ.get("RUNNER_OS") == "Linux"
        and os.environ.get("PYTEST_XDIST_WORKER") is not None,
        reason="RLIMIT_NPROC sous xdist WSL self-hosted (cf. #17496)",
    ),
]

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import gh_bulk
from coordination import gh_selection
from coordination import main_freshness as mf
from coordination import tapis_origami
from coordination import tapis_rapide as tr

_ENV_GIT = {
    "GIT_OPTIONAL_LOCKS": "0",
    "GIT_PACK_THREADS": "1",
    "GIT_REV_LIST_THREADS": "1",
}


def _git(*args: str, cwd: Path) -> str:
    proc = subprocess.run(["git", *args], cwd=str(cwd), capture_output=True, text=True,
                          encoding="utf-8", errors="replace", timeout=60, check=False,
                          env={**os.environ, **_ENV_GIT})
    if proc.returncode != 0:
        raise RuntimeError(f"git {args} (cwd={cwd}) rc={proc.returncode}: {proc.stderr}")
    return proc.stdout.strip()


def _mini_depot(tmp_path: Path, name: str = "clone") -> tuple[Path, Path]:
    """Depot nu local (origin) + clone portant les modules du tirage en factices."""
    origin, clone = tmp_path / "origin.git", tmp_path / name
    _git("init", "--bare", "--initial-branch=main", "--quiet", str(origin), cwd=tmp_path)
    _git("init", "--initial-branch=main", "--quiet", str(clone), cwd=tmp_path)
    _git("config", "user.email", "test@example.com", cwd=clone)
    _git("config", "user.name", "test", cwd=clone)
    _git("config", "commit.gpgsign", "false", cwd=clone)
    _git("remote", "add", "origin", str(origin), cwd=clone)
    for rel in mf.ORGANES:
        cible = clone / rel
        cible.parent.mkdir(parents=True, exist_ok=True)
        cible.write_text(f"# {rel}\n", encoding="utf-8")
    _git("add", *mf.ORGANES, cwd=clone)
    _git("commit", "-m", "organes du tirage", "--quiet", cwd=clone)
    _git("push", "-q", "-u", "origin", "main", cwd=clone)
    return clone, origin


def _avancer_origin(tmp_path: Path, origin: Path, n: int = 1) -> None:
    """Un second clone fait avancer origin/main de n commits."""
    clone2 = tmp_path / "clone2"
    _git("clone", "--quiet", str(origin), str(clone2), cwd=tmp_path)
    for i in range(n):
        (clone2 / f"avance{i}.md").write_text(f"avance {i}\n", encoding="utf-8")
        _git("add", f"avance{i}.md", cwd=clone2)
        _git("commit", "-m", f"avance {i}", "--quiet", cwd=clone2)
    _git("push", "-q", "origin", "main", cwd=clone2)


# --- controle NEGATIF : un clone a jour passe -------------------------------


def test_clone_a_jour_passe(tmp_path):
    """Clone frais, organes conformes : la garde ne refuse rien."""
    clone, _ = _mini_depot(tmp_path)
    v = mf.garder(clone, run=mf.run_defaut)
    assert v["ok"] is True, f"un clone a jour doit passer, causes : {v}"
    assert v["refuse"] is False and v["outre_passe"] is False
    assert v["ecart"] == 0 and v["organes_divergents"] == []
    assert v["raisons"] == []


# --- controle positif : main en retard ---------------------------------------


def test_main_en_retard_refuse_avec_remede(tmp_path):
    """Incident po-2024 (14/11) : 605 commits de retard -> refus + remede."""
    clone, origin = _mini_depot(tmp_path)
    _avancer_origin(tmp_path, origin, n=3)
    v = mf.garder(clone, run=mf.run_defaut)
    assert v["refuse"] is True and v["ok"] is False
    assert v["ecart"] == 3, f"3 commits d'avance attendus, lu {v['ecart']}"
    assert [r["code"] for r in v["raisons"]] == ["MAIN_PERIME"]
    assert "3 commit" in v["raisons"][0]["motif"]
    assert "pull --ff-only" in v["raisons"][0]["remede"]


# --- controle positif : organe divergent -------------------------------------


def test_organe_divergent_refuse_puis_repasse(tmp_path):
    """Incident po-2028 (14/11) : l'organe differe d'origin/main -> refus.

    Controle negatif jumeau dans le meme test : le fichier remis a son
    contenu d'origin/main, le refus tombe.
    """
    clone, _ = _mini_depot(tmp_path)
    chemin = clone / "scripts/coordination/gh_bulk.py"
    chemin.write_text("# modifie localement, divergent d'origin/main\n", encoding="utf-8")
    v = mf.garder(clone, run=mf.run_defaut)
    assert v["refuse"] is True
    assert v["organes_divergents"] == ["scripts/coordination/gh_bulk.py"]
    assert v["raisons"][0]["code"] == "ORGANE_DIVERGENT"
    chemin.write_text("# scripts/coordination/gh_bulk.py\n", encoding="utf-8")
    v2 = mf.garder(clone, run=mf.run_defaut)
    assert v2["refuse"] is False and v2["ok"] is True, f"causes residuelles : {v2}"


# --- echappatoire explicite ---------------------------------------------------


def test_allow_stale_outrepasse_et_se_dit_dans_le_json(tmp_path):
    """--allow-stale leve le refus ET le dit : `outre_passe: true` en JSON."""
    clone, origin = _mini_depot(tmp_path)
    _avancer_origin(tmp_path, origin, n=1)
    v = mf.garder(clone, allow_stale=True, run=mf.run_defaut)
    assert v["refuse"] is False and v["ok"] is False
    assert v["outre_passe"] is True
    assert '"outre_passe": true' in json.dumps(v)


# --- clone pas sur main -------------------------------------------------------


def test_clone_pas_sur_main_mesure_le_main_local(tmp_path):
    """Un worktree/branche feature : la reference mesuree reste refs/heads/main."""
    clone, _ = _mini_depot(tmp_path)
    _git("checkout", "-q", "-b", "feature/x", cwd=clone)
    v = mf.garder(clone, run=mf.run_defaut)
    assert v["refuse"] is False
    assert v["branche"] == "feature/x"
    assert v["ref_mesure"] == "refs/heads/main" and v["ecart"] == 0


def test_clone_sans_main_mesure_sur_head(tmp_path):
    """Clone sans branche main (cas degenerre) : mesure sur HEAD, nommee."""
    clone, _ = _mini_depot(tmp_path)
    _git("checkout", "-q", "--detach", cwd=clone)
    _git("branch", "-D", "main", cwd=clone)
    v = mf.garder(clone, run=mf.run_defaut)
    assert v["ref_mesure"] == "HEAD" and v["ecart"] == 0
    assert v["refuse"] is False


def test_worktree_frais_passe_malgre_main_partage_en_retard(tmp_path):
    """Incident po-2028 (15/11) : worktree frais refuse a cause du main partage.

    La lane tirait depuis un worktree cree sur un origin/main a jour ; le
    `main` du clone principal (partage, qu'elle ne doit pas toucher) avait
    381 commits de retard, et la garde refusait sur lui. Le HEAD qui
    execute est a jour : la garde passe et nomme HEAD. Controle jumeau :
    le clone principal, lui, sur son main en retard, reste refuse.
    """
    clone, origin = _mini_depot(tmp_path)
    _avancer_origin(tmp_path, origin, n=3)
    _git("fetch", "-q", "origin", "main", cwd=clone)
    wt = tmp_path / "wt"
    _git("worktree", "add", "-q", "--detach", str(wt), "origin/main", cwd=clone)
    v = mf.garder(wt, run=mf.run_defaut)
    assert v["refuse"] is False and v["ok"] is True, f"causes : {v}"
    assert v["ref_mesure"] == "HEAD" and v["ecart"] == 0
    v_principal = mf.garder(clone, run=mf.run_defaut)
    assert v_principal["refuse"] is True
    assert v_principal["ecart"] == 3
    assert [r["code"] for r in v_principal["raisons"]] == ["MAIN_PERIME"]


# --- mesure impossible : fail-closed -----------------------------------------


def test_fetch_impossible_refuse_fail_closed(tmp_path):
    """Un fetch rate ne se publie jamais comme un vert : refus, cause nommee."""
    def _run_casse(argv, timeout):
        if "fetch" in argv:
            return 128, "", "fatal: unable to access : reseau coupe"
        raise AssertionError(f"seul le fetch devait etre tente, vu : {argv}")

    v = mf.garder(tmp_path / "inexistant", run=_run_casse)
    assert v["refuse"] is True and v["ok"] is False and v["ecart"] is None
    assert [r["code"] for r in v["raisons"]] == ["MESURE_IMPOSSIBLE"]
    assert "fetch" in v["raisons"][0]["motif"]


# --- echappatoire pytest : la garde ne touche ni reseau ni depot reel --------


def test_garde_inactive_sous_pytest_sans_run_injecte(tmp_path, monkeypatch):
    """Sans run injecte sous pytest, la garde passe sans rien toucher.

    C'est la couture qui garde les tests existants de tapis_rapide (fixture
    forbid_shell_escape) hors de tout subprocess -- meme couture que le
    journal de tirage de pick_idle_grain.py.
    """
    monkeypatch.delenv("MAIN_FRESHNESS_FORCE", raising=False)
    v = mf.garder(tmp_path / "peu-importe", run=None)
    assert v["ok"] is True and v["refuse"] is False
    assert v.get("passe") == "pytest"


def test_main_freshness_force_outre_l_echappatoire(tmp_path, monkeypatch):
    """MAIN_FRESHNESS_FORCE=1 : la garde mesure vraiment (ici : echec nomme)."""
    monkeypatch.setenv("MAIN_FRESHNESS_FORCE", "1")
    v = mf.garder(tmp_path / "inexistant", run=None)
    assert v["refuse"] is True
    assert v["raisons"][0]["code"] == "MESURE_IMPOSSIBLE"


# --- cablage dans tapis_rapide.main ------------------------------------------


def test_tapis_refuse_le_tirage_sur_main_perime(monkeypatch, capsys):
    """Le refus de garde se rend par la sortie 4, remede sur stderr, JSON sur stdout."""
    verdict = {"ok": False, "refuse": True, "outre_passe": False, "ecart": 605,
               "raisons": [{"code": "MAIN_PERIME",
                            "motif": "le main local est en retard de 605 commit(s) sur origin/main",
                            "remede": "git pull --ff-only"}]}
    monkeypatch.setattr(mf, "garder", lambda depot, allow_stale=False: dict(verdict))
    rc = tr.main(["--lane", "myia-po-2024:CoursIA-2"])
    assert rc == 4, "le refus de fraicheur doit se rendre par la sortie 4 (pas le 3 du repli)"
    capture = capsys.readouterr()
    assert "TIRAGE REFUSE [MAIN_PERIME]" in capture.err
    assert "605" in capture.err and "pull --ff-only" in capture.err
    assert "pick_idle_grain" not in capture.err, "le refus ne doit PAS imprimer le repli picker"
    assert json.loads(capture.out)["ecart"] == 605


def test_tapis_propage_allow_stale_et_le_dit_dans_le_rapport(monkeypatch, capsys):
    """--allow-stale atteint la garde, et le rapport JSON porte l'outre-passe."""
    vu = {}

    def _garder(depot, allow_stale=False):
        vu["allow_stale"] = allow_stale
        return {"ok": False, "refuse": False, "outre_passe": True, "raisons": [
            {"code": "MAIN_PERIME", "motif": "le main local est en retard de 2 commit(s)",
             "remede": "git pull --ff-only"}]}

    monkeypatch.setattr(mf, "garder", _garder)
    # La voie LEGERE est le defaut (#27225) : elle lit les metadonnees du pool,
    # les citations et les PRs. Ces trois lectures sont MOCKEES : ce test ne
    # touche pas le reseau (le module le dit), et un quota epuoussé ne doit
    # pas le faire echouer.
    monkeypatch.setattr(gh_selection, "lire_metadonnees_issues",
                        lambda *a, **k: ([], 0.0))
    monkeypatch.setattr(gh_bulk, "lire_citations_mergees", lambda *a, **k: {})
    monkeypatch.setattr(gh_bulk, "lire_prs_ouvertes", lambda *a, **k: [])
    monkeypatch.setattr(tapis_origami, "mesurer",
                        lambda *a, **k: (set(), {"measured": False, "active": False}))
    rc = tr.main(["--lane", "L", "--allow-stale", "--json"])
    assert rc == 0
    assert vu["allow_stale"] is True, "--allow-stale doit atteindre la garde"
    rapport = json.loads(capsys.readouterr().out)
    assert rapport["fraicheur"]["outre_passe"] is True


def test_rejeu_lecture_ne_passe_pas_la_garde(tmp_path, monkeypatch, capsys):
    """Un rejeu --lecture est un diagnostic hors ligne : pas de garde, pas de cle."""
    def _garder(*a, **k):
        raise AssertionError("la garde ne s'applique pas a un rejeu --lecture")

    monkeypatch.setattr(mf, "garder", _garder)
    dossier = tmp_path / "lecture"
    dossier.mkdir()
    (dossier / "issues.json").write_text("[]", encoding="utf-8")
    (dossier / "prs_ouvertes.json").write_text("[]", encoding="utf-8")
    monkeypatch.setattr(tr.gh_bulk, "charger_depuis",
                        lambda *a, **k: gh_bulk.Lecture(issues=[], prs=[], citations={}))
    rc = tr.main(["--lane", "L", "--lecture", str(dossier), "--json"])
    assert rc == 0
    assert "fraicheur" not in json.loads(capsys.readouterr().out)
