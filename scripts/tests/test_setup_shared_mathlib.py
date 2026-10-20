"""Tests du cycle Apply/rollback de setup_shared_mathlib.ps1 (#21454).

Le defaut fondateur : dans Invoke-Apply, un membre rollbacke par -Build etait
retire de $stateMembers mais restait present dans $existing charge avant la
boucle -- la fusion d'etat finale le REINTRODUISAIT, et share-state.json
declarait des membres qui n'avaient plus de jonction (mesure po-2027,
2026-10-19 : 24 membres declares, 18 jonctions / 6 absents sur le disque).

Les tests executent le VRAI script sur une fixture git minimale (3 projets
fictifs, un seul groupe, un shim lake.cmd sur PATH) :

- test_rollback_member_not_reintroduced_by_state_merge : deux Apply -Build
  successifs ; au second, deux membres echouent -> rollback. Acceptances #21454 :
  le membre rollbacke est ABSENT du fichier (2), l'etat est conforme au disque
  (1), le membre sans backup est marque needsProvision (correctif 2).
- test_interrupted_run_preserves_treated_members_trace : un Apply -Build ou le
  shim du membre B echoue ET detruit le dossier du membre C -- le script meurt
  au traitement de C (exit != 0). Correctif 3 : l'etat persiste apres CHAQUE
  membre, donc le fichier existe malgre l'interruption, contient les membres
  traites, et le membre rollbacke (B) n'y figure plus comme jonctionne.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
from pathlib import Path
from types import SimpleNamespace

import pytest

# Junctions NTFS + pwsh (script #Requires -Version 7.0) : surface Windows-only,
# comme test_manage_self_hosted_runner.py (#12704). Les runners Linux sautent.
requires_windows = pytest.mark.skipif(
    os.name != "nt" or shutil.which("pwsh") is None,
    reason="junctions NTFS + pwsh requis (#21454)",
)

REPO_ROOT = Path(__file__).resolve().parents[2]
SCRIPT = REPO_ROOT / "scripts" / "lean" / "setup_shared_mathlib.ps1"

BACKUP_SUFFIX = ".bak-2611"
FAKE_REV = "1234567890abcdef1234567890abcdef12345678"


def _run(cmd: list[str], cwd: Path) -> None:
    proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True,
                          encoding="utf-8", errors="replace")
    assert proc.returncode == 0, f"{cmd} failed:\n{proc.stdout}\n{proc.stderr}"


def _make_project(root: Path, name: str, *, with_checkout: bool) -> Path:
    # with_checkout=False ne crée PAS le répertoire mathlib (même pas vide) :
    # un répertoire vide serait backupé par l'Apply (hadBackup=True) et le
    # membre ne serait plus le cas « sans checkout » que les tests visent.
    proj = root / name
    proj.mkdir(parents=True, exist_ok=True)
    if with_checkout:
        ml = proj / ".lake" / "packages" / "mathlib"
        ml.mkdir(parents=True, exist_ok=True)
        (ml / "Mathlib.lean").write_text("-- fake mathlib\n", encoding="utf-8")
        (ml / f"marker-{name}.txt").write_text(name, encoding="utf-8")
    (proj / "lake-manifest.json").write_text(
        json.dumps({"packages": [{"name": "mathlib", "rev": FAKE_REV}]}), encoding="utf-8"
    )
    (proj / "lean-toolchain").write_text("tc-test\n", encoding="utf-8")
    return proj


def _write_shim(root: Path, lines: list[str]) -> None:
    """Ecrit un shim lake.cmd (CRLF) dans <root>/tools (prepended au PATH)."""
    tools = root / "tools"
    tools.mkdir(exist_ok=True)
    body = "\r\n".join(["@echo off", *lines]) + "\r\n"
    (tools / "lake.cmd").write_bytes(body.encode("ascii"))


def _run_apply(root: Path) -> subprocess.CompletedProcess:
    env = os.environ.copy()
    env["PATH"] = str(root / "tools") + os.pathsep + env["PATH"]
    return subprocess.run(
        ["pwsh", "-NoProfile", "-NonInteractive", "-File", str(SCRIPT),
         "-Mode", "Apply", "-Build"],
        cwd=root, env=env, capture_output=True, text=True, encoding="utf-8",
        errors="replace", timeout=300,
    )


def _read_state(root: Path, group_dir: str) -> dict:
    path = root / ".mathlib-cache" / group_dir / "share-state.json"
    assert path.exists(), f"share-state.json absent : {path}"
    return json.loads(path.read_text(encoding="utf-8-sig"))


@pytest.fixture()
def fixture_repo(tmp_path: Path) -> SimpleNamespace:
    """Depot git minimal : 3 projets, un seul groupe, donneur = projA.

    projA porte un VRAI mini-depot git dans son checkout mathlib (HEAD = la rev
    du manifest) : c'est ce qui rend le cache valide au second Apply
    (Test-CacheValid fait un rev-parse HEAD dans le cache, #18584). projA porte
    aussi le plus gros .lake/build -> donneur deterministe.
    """
    root = tmp_path / "repo"
    root.mkdir()
    _run(["git", "init", "-q"], root)

    proj_a = _make_project(root, "projA", with_checkout=True)
    _make_project(root, "projB", with_checkout=True)
    _make_project(root, "projC", with_checkout=False)

    # Vrai depot dans le checkout du donneur ; le manifest declare sa HEAD.
    ml_a = proj_a / ".lake" / "packages" / "mathlib"
    _run(["git", "init", "-q"], ml_a)
    _run(["git", "add", "-A"], ml_a)
    _run(["git", "-c", "user.email=t@t", "-c", "user.name=t", "commit", "-qm", "fake mathlib"], ml_a)
    head = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=ml_a, capture_output=True, text=True,
        encoding="utf-8", errors="replace", check=True
    ).stdout.strip()
    for name in ("projA", "projB", "projC"):
        (root / name / "lake-manifest.json").write_text(
            json.dumps({"packages": [{"name": "mathlib", "rev": head}]}), encoding="utf-8"
        )

    # Poids .lake/build du donneur (non commite) : projA candidat le plus gros.
    build_a = ml_a / ".lake" / "build"
    build_a.mkdir(parents=True, exist_ok=True)
    (build_a / "artifact.bin").write_bytes(b"x" * (4 * 1024 * 1024))
    return SimpleNamespace(root=root, group_dir=f"tc-test-{head[:8]}")


@requires_windows
def test_rollback_member_not_reintroduced_by_state_merge(
    fixture_repo: SimpleNamespace,
) -> None:
    root, group_dir = fixture_repo.root, fixture_repo.group_dir
    # Phase 1 : tout reussit -> 3 membres jonctionnes, etat [projA, projB, projC].
    _write_shim(root, ["exit /b 0"])
    proc1 = _run_apply(root)
    assert proc1.returncode == 0, f"phase 1 stdout tail:\n{proc1.stdout[-1500:]}"
    state1 = _read_state(root, group_dir)
    assert sorted(m["relPath"] for m in state1["members"]) == ["projA", "projB", "projC"]
    assert state1.get("rolledBack", []) == []

    # Phase 2 : projB et projC echouent -> rollback. C'est ici que le defaut
    # #21454 jouait : projB/projC restent dans $existing et la fusion les
    # reintroduisait.
    _write_shim(root, [
        'echo %CD% | findstr /C:"projB" >nul && exit /b 1',
        'echo %CD% | findstr /C:"projC" >nul && exit /b 1',
        "exit /b 0",
    ])
    proc2 = _run_apply(root)
    assert proc2.returncode == 0, f"phase 2 stdout tail:\n{proc2.stdout[-1500:]}"

    # Acceptance 2 : le membre rollbacke est ABSENT du fichier.
    state2 = _read_state(root, group_dir)
    members = {m["relPath"]: m for m in state2["members"]}
    assert list(members) == ["projA"], f"membres apres rollback : {list(members)}"
    assert members["projA"]["isDonor"] is True

    rolled = {m["relPath"]: m for m in state2["rolledBack"]}
    assert set(rolled) == {"projB", "projC"}
    # projB avait un backup -> restaure physique, pas de reprovisionnement.
    assert rolled["projB"]["needsProvision"] is False
    # projC n'avait pas de checkout -> rollback laisse mathlib ABSENT.
    assert rolled["projC"]["needsProvision"] is True

    # Acceptance 1 : l'etat dit ce que le disque dit.
    ml_a = root / "projA" / ".lake" / "packages" / "mathlib"
    # Jonction vers le cache : on y voit le contenu du checkout du donneur.
    assert (ml_a / "Mathlib.lean").exists()
    assert (ml_a / "marker-projA.txt").exists()
    ml_b = root / "projB" / ".lake" / "packages" / "mathlib"
    # Restaure PHYSIQUE depuis le bak (le marqueur de projB, pas celui du donneur).
    assert (ml_b / "marker-projB.txt").exists()
    assert not (ml_b.parent / ("mathlib" + BACKUP_SUFFIX)).exists()
    # projC : ni jonction ni copie.
    assert not (root / "projC" / ".lake" / "packages" / "mathlib").exists()


@requires_windows
def test_interrupted_run_preserves_treated_members_trace(
    fixture_repo: SimpleNamespace,
) -> None:
    root, group_dir = fixture_repo.root, fixture_repo.group_dir
    # Phase 1 : tout reussit -> etat [projA, projB, projC].
    _write_shim(root, ["exit /b 0"])
    proc1 = _run_apply(root)
    assert proc1.returncode == 0, f"phase 1 stdout tail:\n{proc1.stdout[-1500:]}"
    assert sorted(m["relPath"] for m in _read_state(root, group_dir)["members"]) == [
        "projA", "projB", "projC"
    ]

    # Phase 2 : projB echoue ET remplace projC par un FICHIER -- au tour de
    # projC, le repoint `New-Item -ItemType Junction` ne peut pas creer la
    # chaine de repertoires a travers un fichier : erreur terminante, le script
    # meurt au milieu du groupe (exit != 0). (New-Item Junction cree les
    # repertoires parents manquants : un simple rmdir ne suffit pas a faire
    # echouer -- constate en faisant tourner le test.)
    proj_c = root / "projC"
    _write_shim(root, [
        f'echo %CD% | findstr /C:"projB" >nul && (rmdir /s /q "{proj_c}" & echo x > "{proj_c}" & exit /b 1)',
        "exit /b 0",
    ])
    proc2 = _run_apply(root)
    assert proc2.returncode != 0, "le run devait mourir au traitement de projC"

    # Correctif 3 : malgre l'interruption, l'etat existe (persiste apres chaque
    # membre), projA y figure, et projB -- rollbacke juste avant l'interruption
    # -- n'y est plus reintroduit. projC (dossier detruit, plus de jonction) est
    # retire par le filtre disque : le fichier ne declare aucun fantome.
    state = _read_state(root, group_dir)
    members = sorted(m["relPath"] for m in state["members"])
    assert members == ["projA"], f"membres apres interruption : {members}"
    rolled = sorted(m["relPath"] for m in state["rolledBack"])
    assert rolled == ["projB"]
    # projB restaure physique depuis son bak.
    assert (root / "projB" / ".lake" / "packages" / "mathlib" / "marker-projB.txt").exists()


@requires_windows
def test_reprovisioned_member_pruned_and_createdat_preserved(
    fixture_repo: SimpleNamespace,
) -> None:
    """Reserves #21462 : elagage de rolledBack + createdAt preserve.

    Un membre rollbacke puis RE-APPROVISIONNE par un Apply ulterieur ne doit
    plus rester dans rolledBack (le rappel du Rollback affichait un
    needsProvision perime apres reprovisionnement effectif), et le createdAt
    du groupe ne doit pas glisser a chaque save.
    """
    root, group_dir = fixture_repo.root, fixture_repo.group_dir

    # Phase 1 : tout reussit -> creation du groupe, createdAt de reference.
    _write_shim(root, ["exit /b 0"])
    proc1 = _run_apply(root)
    assert proc1.returncode == 0, f"phase 1 stdout tail:\n{proc1.stdout[-1500:]}"
    state1 = _read_state(root, group_dir)
    created_ref = state1["createdAt"]
    assert state1.get("rolledBack", []) == []

    # Phase 2 : projB seul echoue -> rollback, entre dans rolledBack.
    _write_shim(root, [
        'echo %CD% | findstr /C:"projB" >nul && exit /b 1',
        "exit /b 0",
    ])
    proc2 = _run_apply(root)
    assert proc2.returncode == 0, f"phase 2 stdout tail:\n{proc2.stdout[-1500:]}"
    state2 = _read_state(root, group_dir)
    assert sorted(m["relPath"] for m in state2["members"]) == ["projA", "projC"]
    assert sorted(m["relPath"] for m in state2["rolledBack"]) == ["projB"]
    # createdAt preserve des le deuxieme save.
    assert state2["createdAt"] == created_ref

    # Phase 3 : tout reussit -> projB re-junctionne (re-approvisionne).
    _write_shim(root, ["exit /b 0"])
    proc3 = _run_apply(root)
    assert proc3.returncode == 0, f"phase 3 stdout tail:\n{proc3.stdout[-1500:]}"
    state3 = _read_state(root, group_dir)
    assert sorted(m["relPath"] for m in state3["members"]) == ["projA", "projB", "projC"]
    # Le correctif : l'entree rollback de projB est ELAGUEE (membre de nouveau
    # jonctionne = re-approvisionne ; le rappel du Rollback ne doit plus le
    # montrer needsProvision).
    assert state3.get("rolledBack", []) == [], (
        f"rolledBack apres reprovisionnement : {state3.get('rolledBack')}"
    )
    # createdAt toujours celui de la creation du groupe.
    assert state3["createdAt"] == created_ref
    # Verite disque : projB jonctionne vers le cache (marqueur du donneur).
    assert (root / "projB" / ".lake" / "packages" / "mathlib" / "marker-projA.txt").exists()
