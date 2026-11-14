"""Temoins de l'alignement budget / parallelisme de l'organe d'attestation
Lean (#26480, dispatch coordinateur du 14/11).

Trois defauts distincts, trois temoins :

1. **le diagnostic se perdait** : `build_lake()` ne recopiait pas
   `budget_violation` du payload de `lean_exec`, et l'echec etait presente
   comme un `timeout` muet -- un depassement de concurrence se lisait comme
   un depassement de temps ;
2. **le couple (jobs, budget) n'etait pas aligne** : l'organe laissait
   `lean_exec` sur ses defauts implicites (`budget = 2` places reservees,
   `jobs = cpu // 4`), deux grandeurs qui se contredisent. L'organe passe
   maintenant les deux explicitement, avec le budget couvrant les
   compilations ET le scheduler `lake` ;
3. **le dry-run ne posait ni `ok` ni `reason`** : `main()` affichait
   « raison inconnue » et rendait rc=1, si bien qu'un dry-run reussi se
   lisait comme un echec.

Les fonctions testees sont **pures** (aucun Lake, aucun toolchain,
aucun appel reseau) : le temoin ne depend pas de l'etat de la machine.
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "scripts" / "lean"))

import attest_local_build as alb  # noqa: E402


LAKE = {"lake": "decisiontheory", "project-path": "lakes/decisiontheory"}


# --- 1. la violation de budget est propagee, et elle nomme la cause -------

def test_build_lake_propage_la_violation_de_budget(monkeypatch, tmp_path):
    """`budget_violation` est recopie et la raison la NOMME.

    Sur le code casse, le champ etait absent et la raison disait seulement
    « lake build a echoue (exit_code=...) » : la cause reelle (concurrence)
    disparaitrait au profit d'une lecture « lent ».
    """
    violation = "4 compilations lean > parallélisme accordée 3 (places reservees 4)"
    monkeypatch.setattr(
        alb,
        "run_lake_build",
        lambda *a, **k: {
            "exit_code": 124,
            "status": "timeout",
            "jobs": 3,
            "budget_violation": violation,
            "granted_jobs": 3,
        },
    )
    monkeypatch.setattr(alb, "prepare_lake", lambda *a, **k: {"ok": True})
    (tmp_path / "lakes" / "decisiontheory").mkdir(parents=True)

    result = alb.build_lake(LAKE, tmp_path, tmp_path, timeout=30.0)

    assert result["budget_violation"] == violation
    assert result["ok"] is False
    assert "budget" in result["reason"].lower()
    assert violation in result["reason"]


def test_build_lake_sans_violation_raison_generique(monkeypatch, tmp_path):
    """Controle negatif : sans violation, la raison reste la raison de
    l'echec de build (le champ porte None, pas une cause inventee)."""
    monkeypatch.setattr(
        alb,
        "run_lake_build",
        lambda *a, **k: {"exit_code": 1, "status": "error", "jobs": 3},
    )
    monkeypatch.setattr(alb, "prepare_lake", lambda *a, **k: {"ok": True})
    (tmp_path / "lakes" / "decisiontheory").mkdir(parents=True)

    result = alb.build_lake(LAKE, tmp_path, tmp_path, timeout=30.0)

    assert result["budget_violation"] is None
    assert result["ok"] is False
    assert "exit_code=1" in result["reason"]


def test_attest_nome_la_violation_au_niveau_du_lot(monkeypatch, tmp_path):
    """Le verdict du LOT nomme la violation : c'est lui que l'agent lit."""
    monkeypatch.setattr(alb, "current_login", lambda: "myia-ai-01")
    monkeypatch.setattr(alb, "pr_head", lambda repo, pr: "a" * 40)
    monkeypatch.setattr(alb, "pr_files", lambda repo, pr: ["x.lean"])
    monkeypatch.setattr(alb, "lakes_for", lambda files: [LAKE])
    monkeypatch.setattr(
        alb,
        "build_lake",
        lambda *a, **k: {
            "lake": "decisiontheory",
            "ok": False,
            "exit_code": 124,
            "status": "timeout",
            "budget_violation": "4 compilations lean > parall\u00e9lisme accord\u00e9e 3",
        },
    )
    # Le worktree est un dossier temporaire vide que l'organe supprime
    # lui-meme juste apres l'avoir cree : on le remplace par un dossier
    # sous `tmp_path` pour ne rien laisser dans le depot.
    worktree = tmp_path / "wt"
    worktree.mkdir()
    monkeypatch.setattr(alb.tempfile, "mkdtemp", lambda *a, **k: str(worktree))
    monkeypatch.setattr(
        alb,
        "_run",
        lambda cmd, **k: subprocess.CompletedProcess(
            args=cmd, returncode=0, stdout="", stderr=""
        ),
    )
    monkeypatch.setattr(alb, "cleanup_worktree", lambda wt: None)

    result = alb.attest(12345, "jsboige/CoursIA", 30.0, dry_run=False)

    assert result["ok"] is False
    assert "violation du budget" in result["reason"]
    assert "4 compilations lean" in result["reason"]


# --- 2. le couple (jobs, budget) est aligne et passe explicitement -------

def test_raison_alignement_refuse_un_budget_trop_petit():
    """Un budget qui ne couvre pas les compilations ET le scheduler est
    refuse : il sous-compte l'occupation reelle du cap machine-wide."""
    raison = alb.raison_alignement_budget(jobs=3, budget=2)
    assert raison
    assert "scheduler" in raison


def test_raison_alignement_refuse_un_budget_trop_grand():
    """Un budget qui reserve des places que le run n'occupera pas refuse
    des runs a tort sous un cap serre."""
    raison = alb.raison_alignement_budget(jobs=3, budget=9)
    assert raison


def test_raison_alignement_accepte_le_couple_justes():
    assert alb.raison_alignement_budget(jobs=3, budget=4) == ""
    assert alb.raison_alignement_budget(jobs=1, budget=2) == ""


def test_argv_passe_le_budget_explicite(tmp_path):
    """Le budget est passe a `lean_exec` en argument : sa valeur implicite
    (2 places) ne couvre pas le parallelisme accorde par defaut."""
    argv = alb._lean_exec_argv(
        ["lake", "build"],
        lake_dir=tmp_path,
        timeout=30.0,
        stdout_file=tmp_path / "out.txt",
        stderr_file=tmp_path / "err.txt",
        budget=4,
    )
    assert "--budget" in argv
    assert argv[argv.index("--budget") + 1] == "4"
    # le payload reste le dernier element : c'est lui que l'organe lance
    assert argv[-2:] == ["lake", "build"]


def test_run_lake_build_pose_le_parallelisme_demande(monkeypatch, tmp_path):
    """`LEAN_EXEC_JOBS` est pose dans l'environnement de l'enfant : c'est
    la seule voie par laquelle `lean_exec` lit le parallelisme demande."""
    capture = {}

    def fake_run(cmd, *, cwd=None, timeout=None, env=None):
        capture["cmd"] = cmd
        capture["env"] = env
        return subprocess.CompletedProcess(
            args=cmd, returncode=0,
            stdout=json.dumps({"exit_code": 0, "status": "ok", "jobs": 3}),
            stderr="",
        )

    monkeypatch.setattr(alb, "_run", fake_run)

    payload = alb.run_lake_build(tmp_path, timeout=30.0, jobs=3, budget=4)

    assert capture["env"]["LEAN_EXEC_JOBS"] == "3"
    assert payload["status"] == "ok"


def test_attest_refuse_un_couple_incoherent_avant_toute_construction(monkeypatch):
    """Un couple incoherent est refuse AVANT toute construction : l'organe
    ne construit pas avec un budget qui sous-compte son occupation."""
    monkeypatch.setattr(alb, "current_login", lambda: "myia-ai-01")
    construit = []
    monkeypatch.setattr(alb, "pr_head", lambda repo, pr: construit.append(1) or "a" * 40)

    with pytest.raises(alb.OrganError) as exc:
        alb.attest(1, "jsboige/CoursIA", 30.0, dry_run=False, jobs=3, budget=2)

    assert "incoherent" in str(exc.value)
    assert not construit


# --- 3. le dry-run pose ok et reason --------------------------------------

def _dry_run_env(monkeypatch, verdicts):
    """Prepare un dry-run : login, PR et verdict de cache donnes."""
    monkeypatch.setattr(alb, "current_login", lambda: "myia-ai-01")
    monkeypatch.setattr(alb, "pr_head", lambda repo, pr: "b" * 40)
    monkeypatch.setattr(alb, "pr_files", lambda repo, pr: ["x.lean"])
    monkeypatch.setattr(alb, "lakes_for", lambda files: [LAKE])
    monkeypatch.setattr(
        alb, "check_cache_compatibility", lambda lake_dir, pivot: verdicts
    )


def test_dry_run_reussi_vert_et_raison_nommee(monkeypatch):
    """Un dry-run reussi est VERT et nomme les lakes : avant le correctif,
    `ok` restait absent, `main()` affichait « raison inconnue » et rendait
    rc=1."""
    _dry_run_env(monkeypatch, {"ok": True, "reason": "", "checks": []})

    result = alb.attest(4242, "jsboige/CoursIA", 30.0, dry_run=True)

    assert result["ok"] is True
    assert result["reason"]
    assert "decisiontheory" in result["reason"]
    assert result["dry_run"] is True


def test_dry_run_en_echec_nomme_le_lake_et_sa_raison(monkeypatch):
    """Un dry-run en echec nomme le lake fautif et la raison du cache."""
    _dry_run_env(
        monkeypatch,
        {"ok": False, "reason": "lake-manifest.json different du cache", "checks": []},
    )

    result = alb.attest(4242, "jsboige/CoursIA", 30.0, dry_run=True)

    assert result["ok"] is False
    assert "decisiontheory" in result["reason"]
    assert "lake-manifest.json" in result["reason"]


def test_main_dry_run_reussi_rend_rc_zero(monkeypatch, capsys):
    """Le code de retour suit le verdict : 0 pour un dry-run reussi.

    Avant le correctif, le dry-run rendait 1 quel que soit le verdict -- un
    succes se lisait comme un echec.
    """
    _dry_run_env(monkeypatch, {"ok": True, "reason": "", "checks": []})

    rc = alb.main(["4242", "--dry-run"])

    sortie = capsys.readouterr().out
    assert rc == 0
    assert "raison inconnue" not in sortie
    assert "dry-run" in sortie


def test_main_dry_run_en_echec_rend_rc_un(monkeypatch, capsys):
    _dry_run_env(
        monkeypatch,
        {"ok": False, "reason": "cache chaud absent", "checks": []},
    )

    rc = alb.main(["4242", "--dry-run"])

    sortie = capsys.readouterr().out
    assert rc == 1
    assert "raison inconnue" not in sortie
    assert "cache chaud" in sortie
