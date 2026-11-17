"""Tests du payload de build remis a l'organe canonique (#26699, #15666).

Le payload `lake build <cibles>` est construit **au point de la remise** a
`scripts/lean/lean_exec.py`, et nulle part ailleurs : une liste de commande
posee hors de la main de l'organe est une voie directe, que le garde
`scripts/lean/check_lake_direct_invocation.py` refuse (forme 2 : jeton
`lake` dans un literal de liste).

Ce fichier verifie le CONTRAT de la remise :
- le payload cible est `lake build <cibles>` ;
- le payload du lac entier est `lake build` (mode `all`) ;
- l'argv construit par l'organe contient bien ce payload, apres le `--` ;
- les KWARGS que `attest()` passe a `build_lake` sont ceux que la VRAIE
  signature de `build_lake` accepte (F1 de #26704 : `build_cache_dir` au
  lieu de `project_cache_dir` levait un `TypeError` a chaque attestation,
  et aucun test n'exercitait la chaine reelle jusqu'a ce point d'appel) ;
- ce fichier ne lance aucun processus : l'execution est neutralisee.

Aucun lake, aucun reseau, aucune machine.
"""

import inspect
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import attest_local_build  # noqa: E402
from attest_local_build import _lean_exec_argv, run_lake_build  # noqa: E402


class _FakeProc:
    """Resultat d'execution neutre : l'organe n'a rien lance."""

    returncode = 0
    stdout = "{}"
    stderr = ""


def _capture_payload(monkeypatch) -> list:
    """Capture le payload remis a l'organe, sans lancer quoi que ce soit."""
    captured: dict = {}

    def fake_argv(payload, **kwargs):
        captured["payload"] = list(payload)
        return ["fake-organe"]

    monkeypatch.setattr(attest_local_build, "_lean_exec_argv", fake_argv)
    monkeypatch.setattr(attest_local_build, "_run", lambda *a, **k: _FakeProc())
    return captured


def test_le_payload_cible_est_remis_a_l_organe(monkeypatch, tmp_path):
    captured = _capture_payload(monkeypatch)
    run_lake_build(tmp_path, timeout=1.0, targets=["Demo.Alpha", "Demo.Delta"])
    assert captured["payload"] == ["lake", "build", "Demo.Alpha", "Demo.Delta"]


def test_le_payload_du_lac_entier_ne_porte_aucune_cible(monkeypatch, tmp_path):
    captured = _capture_payload(monkeypatch)
    run_lake_build(tmp_path, timeout=1.0, targets=[])
    assert captured["payload"] == ["lake", "build"]


def test_une_cible_absente_porte_le_meme_payload(monkeypatch, tmp_path):
    """`targets=None` (mode `all`) et `targets=[]` sont le meme lac entier."""
    captured = _capture_payload(monkeypatch)
    run_lake_build(tmp_path, timeout=1.0, targets=None)
    assert captured["payload"] == ["lake", "build"]


def test_l_argv_de_l_organe_porte_le_payload_apres_le_separateur(tmp_path):
    """L'organe recoit la commande dans son payload, apres le `--`."""
    argv = _lean_exec_argv(
        ["lake", "build", "Demo.Alpha"],
        lake_dir=tmp_path,
        timeout=60.0,
        stdout_file=tmp_path / "stdout.txt",
        stderr_file=tmp_path / "stderr.txt",
    )
    # Le separateur `--` precede le payload : rien n'est execute avant lui.
    separateur = argv.index("--")
    assert argv[separateur + 1:] == ["lake", "build", "Demo.Alpha"]


def test_le_point_d_appel_de_build_lake_passe_des_kwargs_que_la_signature_accepte(
    monkeypatch, tmp_path
):
    """F1 de #26704 : la CHAINE REELLE `attest()` -> `build_lake()` est exercee.

    Le test ne moque pas `build_lake` : il **capture** les arguments que le
    point d'appel lui passe, puis les lie a la VRAIE signature. Un kwarg faux
    (`build_cache_dir` au lieu de `project_cache_dir`) leve alors un
    `TypeError` ici, avant toute compilation -- c'est le trou de couverture
    qui a laisse passer F1 jusqu'a la PR.
    """
    vraie_build_lake = attest_local_build.build_lake
    captured: dict = {}

    def faux_build_lake(*args, **kwargs):
        captured["args"] = args
        captured["kwargs"] = kwargs
        # La liaison est le VERIT : elle leve le TypeError si un kwarg est faux.
        inspect.signature(vraie_build_lake).bind(*args, **kwargs)
        return {"ok": True, "lake": "demo_lean", "errors": [], "jobs": 0}

    monkeypatch.setattr(attest_local_build, "build_lake", faux_build_lake)
    monkeypatch.setattr(
        attest_local_build,
        "current_login",
        lambda: attest_local_build.attestation.ATTESTATION_AUTHOR,
    )
    monkeypatch.setattr(
        attest_local_build, "pr_head", lambda repo, pr: "0" * 40
    )
    monkeypatch.setattr(
        attest_local_build,
        "pr_files",
        lambda repo, pr: [
            "MyIA.AI.Notebooks/SymbolicAI/Lean/demo/demo_lean/Demo/Alpha.lean"
        ],
    )
    monkeypatch.setattr(
        attest_local_build, "manifest_at_head", lambda repo, head: {}
    )
    monkeypatch.setattr(
        attest_local_build,
        "select_lakes",
        lambda files, head_manifest, base_manifest: [
            {
                "lake": "demo_lean",
                "project-path": "MyIA.AI.Notebooks/SymbolicAI/Lean/demo/demo_lean",
            }
        ],
    )
    monkeypatch.setattr(
        attest_local_build, "_pivot_candidates", lambda base, head: []
    )
    monkeypatch.setattr(
        attest_local_build,
        "resolve_cache_pivot",
        lambda lake_dir, candidates: {"ok": True, "pivot": str(tmp_path)},
    )
    monkeypatch.setattr(
        attest_local_build, "_worktree_path", lambda pr: tmp_path / "wt"
    )
    monkeypatch.setattr(
        attest_local_build, "_clear_stale_worktree", lambda path: None
    )
    monkeypatch.setattr(
        attest_local_build, "_run", lambda *a, **k: _FakeProc()
    )
    monkeypatch.setattr(
        attest_local_build.attest_build_targets,
        "resolve_targets",
        lambda *a, **k: {"ok": True, "targets": ["Demo.Alpha"]},
    )
    monkeypatch.setattr(
        attest_local_build, "post_attestation", lambda repo, pr, body: "1"
    )
    monkeypatch.setattr(
        attest_local_build, "cleanup_worktree", lambda path: None
    )

    attest_local_build.attest(
        pr=4242,
        repo="jsboige/CoursIA",
        timeout=1.0,
        dry_run=False,
        cache_root=tmp_path / "cache",
    )

    assert captured, "le point d'appel de build_lake n'a pas ete atteint"
    assert "project_cache_dir" in captured["kwargs"], (
        "le cache de build du projet doit etre passe sous le nom declare "
        "par la signature de build_lake"
    )
    assert "build_cache_dir" not in captured["kwargs"], (
        "build_cache_dir n'existe pas dans la signature de build_lake : "
        "l'appel aurait leve un TypeError a chaque attestation"
    )
    assert captured["kwargs"]["project_cache_dir"].name == "demo_lean"


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(pytest.main([__file__, "-v"]))
