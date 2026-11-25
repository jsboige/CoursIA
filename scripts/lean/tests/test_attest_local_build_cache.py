"""Tests for the build-cache helpers of scripts/lean/attest_local_build.py (#26699).

Couvre le cache de build du PROJET :
- `preserve_project_build` : le `.lake/build` quitte le worktree et vient au
  cache, avec l'empreinte du contexte (toolchain + manifeste) ;
- `restore_project_build` : il y revient dans un worktree neuf ;
- un contexte different (toolchain, manifeste) **ecrase** le cache au lieu
  de le reutiliser (fail-closed) ;
- un cache absent ne fait rien ;
- `seed_project_build_from_pivot` (#27516) : premier essai d'une PR, le
  `.lake/build` du pivot prechauffe est **copie** dans le worktree -- copie,
  pas deplacement : le pivot garde son build pour les PRs suivantes.

Fixtures synthetiques sous ``tmp_path``. Aucun lake, aucun reseau.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from attest_local_build import (  # noqa: E402
    REPO_ROOT,
    build_cache_dir,
    build_cache_root,
    preserve_project_build,
    restore_project_build,
    seed_project_build_from_pivot,
)


def _make_lake(root: Path, toolchain: str = "leanprover/lean4:v4.33.0",
               manifest: str = '{"packages": []}') -> Path:
    lake = root / "demo"
    lake.mkdir(parents=True, exist_ok=True)
    (lake / "lean-toolchain").write_text(toolchain + "\n", encoding="utf-8")
    (lake / "lake-manifest.json").write_text(manifest, encoding="utf-8")
    return lake


def _fake_build(lake: Path) -> Path:
    build = lake / ".lake" / "build"
    (build / "lib" / "lean" / "Demo").mkdir(parents=True, exist_ok=True)
    (build / "lib" / "lean" / "Demo" / "Alpha.olean").write_bytes(b"OLEAN")
    return build


def test_le_cache_vit_hors_du_depot(tmp_path):
    root = build_cache_root(tmp_path / "cache")
    assert root == tmp_path / "cache"
    # Le defaut est a cote du depot (meme volume que les worktrees), jamais
    # dedans : un cache n'est jamais commite.
    default = build_cache_root()
    assert default.name == "attest-lean-cache"
    # L'invariant est « HORS de l'arbre du depot », pas « aucun composant ne
    # porte le nom du depot » : sur un runner CI, le checkout vit dans
    # `/home/runner/work/CoursIA/CoursIA`, dont le parent se nomme deja
    # `CoursIA` -- l'assertion par sous-chaine y echouait a tort.
    assert default.parent == REPO_ROOT.parent
    assert default != REPO_ROOT
    assert REPO_ROOT not in default.parents


def test_le_repertoire_du_cache_est_par_pr_et_par_lake(tmp_path):
    root = build_cache_root(tmp_path / "cache")
    path = build_cache_dir(root, 25585, "conway_lean")
    assert path == tmp_path / "cache" / "pr-25585" / "conway_lean"


def test_preserve_puis_restore_ramene_le_build(tmp_path):
    lake = _make_lake(tmp_path / "wt1")
    _fake_build(lake)
    cache = build_cache_dir(build_cache_root(tmp_path / "cache"), 25585, "demo")

    kept = preserve_project_build(cache, lake)
    assert kept["preserved"], kept
    # Le build a quitte le worktree...
    assert not (lake / ".lake" / "build").exists()
    # ... et il est dans le cache, avec son empreinte.
    assert (cache / "build" / "lib" / "lean" / "Demo" / "Alpha.olean").is_file()
    meta = json.loads((cache / "meta.json").read_text(encoding="utf-8"))
    assert meta["toolchain"] == "leanprover/lean4:v4.33.0"
    assert meta["manifest_sha256"]

    # Un essai suivant, dans un worktree neuf : le build revient.
    lake2 = _make_lake(tmp_path / "wt2")
    back = restore_project_build(cache, lake2)
    assert back["restored"], back
    assert (lake2 / ".lake" / "build" / "lib" / "lean" / "Demo" / "Alpha.olean").is_file()
    # Le cache a bien ete vide de son build (deplace, pas copie).
    assert not (cache / "build").exists()


def test_une_toolchain_differente_ecrase_le_cache(tmp_path):
    lake = _make_lake(tmp_path / "wt1")
    _fake_build(lake)
    cache = build_cache_dir(build_cache_root(tmp_path / "cache"), 25585, "demo")
    preserve_project_build(cache, lake)

    # L'essai suivant porte une autre toolchain : le cache ne vaut rien.
    lake2 = _make_lake(tmp_path / "wt2", toolchain="leanprover/lean4:v4.34.0")
    back = restore_project_build(cache, lake2)
    assert not back["restored"]
    assert "ecrase" in back["reason"]
    assert not (lake2 / ".lake" / "build").exists()
    assert not cache.exists()


def test_un_manifeste_different_ecrase_le_cache(tmp_path):
    lake = _make_lake(tmp_path / "wt1")
    _fake_build(lake)
    cache = build_cache_dir(build_cache_root(tmp_path / "cache"), 25585, "demo")
    preserve_project_build(cache, lake)

    lake2 = _make_lake(tmp_path / "wt2", manifest='{"packages": [{"name": "mathlib"}]}')
    back = restore_project_build(cache, lake2)
    assert not back["restored"]
    assert not cache.exists()


def test_sans_cache_le_restore_ne_fait_rien(tmp_path):
    lake = _make_lake(tmp_path / "wt1")
    cache = build_cache_dir(build_cache_root(tmp_path / "cache"), 25585, "demo")
    back = restore_project_build(cache, lake)
    assert not back["restored"]
    assert not (lake / ".lake" / "build").exists()


def test_preserve_sans_build_ne_fait_rien(tmp_path):
    lake = _make_lake(tmp_path / "wt1")
    cache = build_cache_dir(build_cache_root(tmp_path / "cache"), 25585, "demo")
    kept = preserve_project_build(cache, lake)
    assert not kept["preserved"]


def test_le_seed_depuis_le_pivot_copie_sans_le_vider(tmp_path):
    # #27516 : pivot prechauffe (build du projet present), worktree de
    # premiere attestation (cache par-PR vide).
    pivot = _make_lake(tmp_path / "pivot")
    _fake_build(pivot)
    lake = _make_lake(tmp_path / "wt1")

    seeded = seed_project_build_from_pivot(pivot, lake)
    assert seeded["seeded"], seeded
    # Le build est dans le worktree...
    assert (lake / ".lake" / "build" / "lib" / "lean" / "Demo" / "Alpha.olean").is_file()
    # ... et le pivot le garde aussi : COPIE, pas deplacement -- le pivot
    # doit resservir les PRs suivantes, et preserve_project_build (qui
    # DEPLACE le .lake/build du worktree) ne doit rien lui arracher.
    assert (pivot / ".lake" / "build" / "lib" / "lean" / "Demo" / "Alpha.olean").is_file()

    # Le seed parti du pivot finit conserve dans le cache par-PR : au
    # deuxieme essai, restore reprend la main (le seed ne re-copie pas).
    cache = build_cache_dir(build_cache_root(tmp_path / "cache"), 25585, "demo")
    kept = preserve_project_build(cache, lake)
    assert kept["preserved"], kept
    lake2 = _make_lake(tmp_path / "wt2")
    back = restore_project_build(cache, lake2)
    assert back["restored"], back
    again = seed_project_build_from_pivot(pivot, lake2)
    assert not again["seeded"]
    assert "deja present" in again["reason"]


def test_le_seed_sans_build_au_pivot_ne_fait_rien(tmp_path):
    # Un pivot jamais prechauffe sur son build propre (cache_get seul) ne
    # fournit rien : le seed est un non-evenement explicite.
    pivot = _make_lake(tmp_path / "pivot")
    lake = _make_lake(tmp_path / "wt1")
    seeded = seed_project_build_from_pivot(pivot, lake)
    assert not seeded["seeded"]
    assert "pivot" in seeded["reason"]
    assert not (lake / ".lake" / "build").exists()
    assert not (pivot / ".lake").exists()


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(pytest.main([__file__, "-v"]))
