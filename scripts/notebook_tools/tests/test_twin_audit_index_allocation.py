#!/usr/bin/env python3
"""Plancher d'allocation du prefixe d'audit twin (#22299).

Le garde d'integrite (`test_audit_index_unique_and_no_identical_duplicates_per_pair`)
exige que le prefixe `NNNN` d'un fichier d'audit soit unique PAR PAIRE. Or
`_next_audit_index` ne lit que le repertoire **local** : deux branches issues du
meme `origin/main` y voient le meme disque, calculent le meme max et emettent le
meme prefixe. Le garde ne rougit qu'APRES le merge -- c'est-a-dire quand le
travail est deja fait, dans une PR qui n'est plus celle qu'on peut corriger.
Cinq paires mesurees le 2026-10-24.

Le correctif ajoute un **plancher lu sur la ref d'integration** :
`_audit_floor(repo_root, registry_dir, name, ref)` rend le plus grand index deja
publie pour la paire sur `ref`, et `_write_audit_file(..., floor=N)` alloue
`max(max_local + 1, N + 1)`.

Trois proprietes sont testees ici, avec un vrai depot git (pas un mock : la
lecture passe par `git ls-tree`, un faux `subprocess.run` testerait le mock) :

    1. le plancher lit vraiment la ref (et non le disque) ;
    2. il **degrade en 0** (et n'empeche jamais d'ecrire) sur ref absente,
       ref illisible, ou registre hors depot -- c'est un garde, pas une mesure ;
    3. `_write_audit_file` place l'index au-dessus du plancher meme quand le
       max local est plus bas, et garde le comportement historique sans plancher.

Run:
    pytest scripts/notebook_tools/tests/test_twin_audit_index_allocation.py
"""
from __future__ import annotations

import importlib.util
import subprocess
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent.parent
SCRIPT = SCRIPT_DIR / "check_twin_parity.py"

PAIR_NAME = "Probas-13 Crowdsourcing"
PAIR_SLUG = "probas-13-crowdsourcing"


def _load_module():
    spec = importlib.util.spec_from_file_location("check_twin_parity", SCRIPT)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


ctp = _load_module()


def _git(repo: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=repo, capture_output=True, text=True,
        encoding="utf-8", errors="replace", check=True,
    ).stdout


def _init_repo(repo: Path) -> None:
    _git(repo, "init", "-q")
    _git(repo, "config", "user.email", "t@t")
    _git(repo, "config", "user.name", "t")
    _git(repo, "config", "commit.gpgsign", "false")


def _publish_audit(repo: Path, registry: Path, index: int, lane: str) -> None:
    """Ecrit un fichier d'audit sur DISQUE (pas encore commite)."""
    d = registry / PAIR_SLUG
    d.mkdir(parents=True, exist_ok=True)
    (d / f"{index:04d}-2026-10-20-{lane}.yaml").write_text(
        "date: \"2026-10-20\"\nby: myia-po-2024:CoursIA\n", encoding="utf-8",
        newline="",
    )


def _repo_with_published_indexes(tmp_path: Path, indexes: list[int]) -> tuple[Path, Path]:
    """Mini-depot dont la ref `main` porte `indexes` pour la paire."""
    repo = tmp_path / "repo"
    repo.mkdir()
    registry = repo / "scripts" / "notebook_tools" / "twin_pairs.d"
    registry.mkdir(parents=True)
    _init_repo(repo)
    # Un commit initial sans registre : la ref existe avant le premier audit.
    (repo / "README.md").write_text("init\n", encoding="utf-8")
    _git(repo, "add", "README.md")
    _git(repo, "commit", "-qm", "init")
    _git(repo, "branch", "-M", "main")
    for i in indexes:
        _publish_audit(repo, registry, i, "myia-po-2025-CoursIA")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-qm", "audits")
    return repo, registry


# --- 1. le plancher lit la ref ------------------------------------------------

def test_audit_indexes_at_ref_reads_published_indexes(tmp_path):
    """`_audit_indexes_at_ref` rend les prefixes commites sur la ref."""
    repo, registry = _repo_with_published_indexes(tmp_path, [1, 2, 3])
    got = ctp._audit_indexes_at_ref(repo, "main", registry, PAIR_NAME)
    assert got == {1, 2, 3}, (
        f"indexes publies sur main attendus {{1, 2, 3}}, obtenu {got}. "
        f"La lecture passe par `git ls-tree -r --name-only main -- "
        f"<reg_rel>/{PAIR_SLUG}/` ; un ensemble vide ici signifie que le chemin "
        f"relatif ou le slug ne correspondent pas a l'arbre."
    )


def test_audit_floor_is_max_published_not_present_on_disk(tmp_path):
    """Le plancher suit la ref, meme quand un index plus haut est sur disque.

    C'est le point du correctif : un audit **local non commite** (index 9) ne
    doit pas influencer le plancher (3), et l'index publie le plus haut non
    plus ne doit pas etre deduit du disque.
    """
    repo, registry = _repo_with_published_indexes(tmp_path, [1, 2, 3])
    _publish_audit(repo, registry, 9, "myia-po-2024-CoursIA-2")  # non commite
    assert ctp._audit_floor(repo, registry, PAIR_NAME, "main") == 3


# --- 2. degradation en 0 : un garde, pas une mesure ---------------------------

def test_audit_floor_is_zero_for_unreadable_ref_and_none(tmp_path):
    """Ref absente / illisible / None -> 0 : ne jamais bloquer une ecriture."""
    repo, registry = _repo_with_published_indexes(tmp_path, [1])
    cases = {
        "ref inconnue": ctp._audit_floor(repo, registry, PAIR_NAME, "nope/nope"),
        "ref None": ctp._audit_floor(repo, registry, PAIR_NAME, None),
        "ref vide": ctp._audit_floor(repo, registry, PAIR_NAME, ""),
    }
    for label, value in cases.items():
        assert value == 0, f"{label} : plancher attendu 0, obtenu {value}"


def test_audit_indexes_at_ref_empty_when_registry_outside_repo(tmp_path):
    """Registre hors depot -> ensemble vide (le `relative_to` echoue)."""
    repo, _ = _repo_with_published_indexes(tmp_path, [1])
    outside = tmp_path / "ailleurs" / "twin_pairs.d"
    outside.mkdir(parents=True)
    assert ctp._audit_indexes_at_ref(repo, "main", outside, PAIR_NAME) == set()


# --- 3. allocation au-dessus du plancher --------------------------------------

def _audit_dict() -> dict:
    return {"date": "2026-10-25", "by": "myia-po-2024:CoursIA",
            "python": {"blob_sha": "0" * 40},
            "csharp": {"blob_sha": "1" * 40}}


def test_write_audit_file_allocates_above_floor(tmp_path):
    """max local = 2, plancher publie = 7 -> l'index ecrit est 8.

    Sans plancher, l'index serait 3, et deux branches issues du meme main
    ecriraient toutes deux `0003` -- le doublon que le garde refuse apres
    merge (5 paires mesurees le 2026-10-24).
    """
    repo, registry = _repo_with_published_indexes(tmp_path, [1, 2])
    path = ctp._write_audit_file(registry, PAIR_NAME, _audit_dict(), floor=7)
    assert path.name.startswith("0008-"), (
        f"index attendu 0008 (7 + 1), obtenu {path.name} ; sans plancher "
        f"l'allocation retombe sur max local + 1 = 0003."
    )


def test_write_audit_file_keeps_local_allocation_without_floor(tmp_path):
    """Sans plancher (floor=0) : comportement historique, max local + 1."""
    repo, registry = _repo_with_published_indexes(tmp_path, [1, 2])
    path = ctp._write_audit_file(registry, PAIR_NAME, _audit_dict())
    assert path.name.startswith("0003-"), (
        f"index attendu 0003 (max local 0002 + 1), obtenu {path.name} : le "
        f"plancher ne doit jamais s'appliquer quand il vaut 0."
    )


def test_write_audit_file_floor_below_local_max_is_ignored(tmp_path):
    """Plancher plus bas que le max local : c'est le local qui gagne."""
    repo, registry = _repo_with_published_indexes(tmp_path, [1, 2])
    path = ctp._write_audit_file(registry, PAIR_NAME, _audit_dict(), floor=1)
    assert path.name.startswith("0003-"), (
        f"index attendu 0003, obtenu {path.name} : `max(local + 1, floor + 1)` "
        f"ne doit jamais RETROGRADER un index deja pris sur disque."
    )


# --- 4. cablage CLI ----------------------------------------------------------

def test_cli_exposes_allocation_floor_flags():
    """Les deux flags existent et le defaut est `origin/main`.

    Test de cablage volontairement pauvre : il n'appelle pas `_main` (qui
    ecrirait un registre), il verifie que le plancher est atteignable depuis
    la ligne de commande -- sans lui, `--update` continuerait d'emettre des
    prefixes issus du seul disque local.
    """
    r = subprocess.run(
        [sys.executable, str(SCRIPT), "--help"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    assert r.returncode == 0, f"--help a echoue : {r.stderr[-400:]}"
    for flag in ("--allocate-against", "--no-allocate-against"):
        assert flag in r.stdout, f"{flag} absent de --help : flag non cable"
    assert "origin/main" in r.stdout, "defaut origin/main non documente"
