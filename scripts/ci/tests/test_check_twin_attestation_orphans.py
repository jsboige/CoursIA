#!/usr/bin/env python3
"""Temoins de la garde des attestations orphelines (#27969).

La garde doit :
- **laisser vert** une attestation dont le sha est le blob du jumeau a la tete
  de la revision (cas normal : attestation emise en derniere operation) ;
- **laisser vert** une attestation dont le sha est un blob deja present sur la
  base (etat anterieur legitime) ;
- **rougir** une attestation qui cite un blob qui n'existe ni sur la base ni a
  la tete : c'est l'orphelin qui rougeira `main` apres le squash ;
- **rougir** une attestation prise a la TETE de la branche quand `main` bouge
  ensuite sur le meme carnet : le squash ecrira un troisieme blob (variante
  mesuree sur #28094, rejoue le 23/11) ;
- **ne jamais examiner** une attestation deja presente sur la base (heritage
  herite, pas un motif de refus) ;
- **rendre un incident** (rc 2), jamais un verdict, quand l'instrument ne peut
  pas lire.

Les tests sont hermetiques : ils construisent un depot git jetable, pas une
copie du depot (un test qui depend du reseau ou de `main` ne prouve rien).

Run: python -m pytest scripts/ci/tests/test_check_twin_attestation_orphans.py -q
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts" / "ci"))

import check_twin_attestation_orphans as organ  # noqa: E402

REGISTRY = "scripts/notebook_tools/twin_pairs.d"
PY_NOTEBOOK = "MyIA.AI.Notebooks/Serie/A-01-Python.ipynb"
CS_NOTEBOOK = "MyIA.AI.Notebooks/Serie/A-01-CSharp.ipynb"
PAIR = "serie-a-01"


def _git(repo: Path, *args: str) -> str:
    proc = subprocess.run(["git", *args], cwd=repo, capture_output=True,
                          text=True, encoding="utf-8", errors="replace")
    assert proc.returncode == 0, f"git {' '.join(args)} : {proc.stderr}"
    return proc.stdout


def _write(path: Path, contenu: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(contenu, encoding="utf-8")


def _repo(tmp_path: Path) -> Path:
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q", "-b", "main")
    _git(repo, "config", "user.email", "t@example.invalid")
    _git(repo, "config", "user.name", "t")
    _write(repo / PY_NOTEBOOK, '{"cells": []}\n')
    _write(repo / CS_NOTEBOOK, '{"cells": []}\n')
    _write(repo / REGISTRY / f"{PAIR}.yaml",
           f'- name: "Serie A 01"\n'
           f'  family: Serie\n'
           f'  python: {PY_NOTEBOOK}\n'
           f'  csharp: {CS_NOTEBOOK}\n')
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "base")
    return repo


def _attestation(repo: Path, index: int, py_sha: str, cs_sha: str, jour: str = "2026-11-22") -> str:
    rel = f"{REGISTRY}/{PAIR}/{index:04d}-{jour}-lane.yaml"
    _write(repo / rel,
           f"date: '{jour}'\n"
           f"by: lane\n"
           f"python_sha: {py_sha}\n"
           f"csharp_sha: {cs_sha}\n"
           f"content_python_sha: {'0' * 64}\n"
           f"content_csharp_sha: {'0' * 64}\n")
    return rel


def _blob(repo: Path, path: str, ref: str = "HEAD") -> str:
    return _git(repo, "ls-tree", ref, "--", path).split()[2]


def _run(repo: Path, base: str = "main", head: str = "HEAD") -> int:
    return organ.main(["--base", base, "--head", head, "--repo-root", str(repo)])


def _branche(repo: Path) -> Path:
    """Les commits de la PR se font HORS de `main` : `main` reste la base."""
    _git(repo, "checkout", "-q", "-b", "branche")
    return repo


def test_attestation_sur_la_tete_passe(tmp_path):
    repo = _branche(_repo(tmp_path))
    _write(repo / PY_NOTEBOOK, '{"cells": ["modifie"]}\n')
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "modification du carnet")
    _attestation(repo, 1, _blob(repo, PY_NOTEBOOK), _blob(repo, CS_NOTEBOOK))
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "attestation")
    assert _run(repo) == 0


def test_attestation_sur_un_etat_anterieur_de_la_base_passe(tmp_path):
    repo = _branche(_repo(tmp_path))
    py_principal = _blob(repo, PY_NOTEBOOK)
    cs_principal = _blob(repo, CS_NOTEBOOK)
    _write(repo / PY_NOTEBOOK, '{"cells": ["modifie"]}\n')
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "modification du carnet")
    # l'attestation cite l'etat ANTERIEUR (deja sur la base) : legitime
    _attestation(repo, 1, py_principal, cs_principal)
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "attestation")
    assert _run(repo) == 0


def test_attestation_orpheline_rougit(tmp_path):
    repo = _branche(_repo(tmp_path))
    cs_principal = _blob(repo, CS_NOTEBOOK)
    # etat intermediaire : le blob existe dans l'historique de la branche,
    # il n'est ni sur la base ni le blob de la tete
    _write(repo / PY_NOTEBOOK, '{"cells": ["intermediaire"]}\n')
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "etat intermediaire")
    sha_intermediaire = _blob(repo, PY_NOTEBOOK)
    _write(repo / PY_NOTEBOOK, '{"cells": ["final"]}\n')
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "etat final")
    _attestation(repo, 1, sha_intermediaire, cs_principal)
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "attestation orpheline")
    assert _run(repo) == 1


def test_une_attestation_intermediaire_orpheline_ne_rougit_pas(tmp_path):
    """`main` ne lit que la DERNIERE attestation d'une paire : une attestation
    intermediaire orpheline ne rougit rien, elle est un avertissement.

    Cas fondateur (#27335) : 0034-0036 orphelines, puis 0037 aux blobs de la
    tete -- la PR est legitime et ne doit pas etre refusee.
    """
    repo = _branche(_repo(tmp_path))
    cs_principal = _blob(repo, CS_NOTEBOOK)
    _write(repo / PY_NOTEBOOK, '{"cells": ["intermediaire"]}\n')
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "etat intermediaire")
    sha_intermediaire = _blob(repo, PY_NOTEBOOK)
    _write(repo / PY_NOTEBOOK, '{"cells": ["final"]}\n')
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "etat final")
    # 0001 : orpheline, mais INTERMEDIAIRE
    _attestation(repo, 1, sha_intermediaire, cs_principal)
    # 0002 : la derniere attestation de la paire, aux blobs de la tete
    _attestation(repo, 2, _blob(repo, PY_NOTEBOOK), _blob(repo, CS_NOTEBOOK))
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "attestations")
    assert _run(repo) == 0


def test_une_attestation_de_la_base_n_est_jamais_examinee(tmp_path):
    repo = _repo(tmp_path)
    cs_principal = _blob(repo, CS_NOTEBOOK)
    _write(repo / PY_NOTEBOOK, '{"cells": ["intermediaire"]}\n')
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "etat intermediaire")
    sha_intermediaire = _blob(repo, PY_NOTEBOOK)
    _write(repo / PY_NOTEBOOK, '{"cells": ["final"]}\n')
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "etat final")
    _attestation(repo, 1, sha_intermediaire, cs_principal)
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "attestation orpheline")
    # cette attestation est desormais dans la BASE : la revision examinee
    # n'en ajoute aucune -> rien a examiner -> vert
    _git(repo, "checkout", "-q", "-b", "branche")
    _write(repo / "MyIA.AI.Notebooks/Serie/autre.txt", "contenu\n")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "changement sans attestation")
    assert _run(repo) == 0


def test_base_introuvable_rend_un_incident(tmp_path):
    repo = _repo(tmp_path)
    assert _run(repo, base="ref-inexistante") == 2


def test_attestation_prise_a_la_tete_que_main_bouge_avant_le_squash_rougit(tmp_path):
    """La variante du 23/11 : attestation a la TETE de la branche, `main` bouge
    ensuite sur le meme carnet -- le squash ecrira un TROISIEME blob.

    Instance mesuree (#28094) : rejeu de la garde sur la tete de la PR
    (`5f6191fd8492`), avec la base = `main` juste avant son squash
    (`7f8ba531f481`) -> **3 refus bloquants** (`csharp_sha` ORPHAN) sur
    `csp-2-consistency`, `csp-6-hybridization` et `csp-8-temporal` : exactement
    les paires qui ont rouge sur `main` le 23/11, re-scellees par #28188.

    Le cas ne se voyait pas sur la branche : le test de branche est vert (le
    blob atteste EST celui de la tete) et la porte n'existait pas encore
    (#27969 ouvert). Le carnet porte ici six lignes pour que les deux cotes
    modifient une ligne LOINTAINTE l'une de l'autre : la fusion est propre et
    ecrit bien un troisieme blob, ni celui de la tete ni celui de la base.
    """
    base = ('{"cells": []}\n{"a": 1}\n{"b": 1}\n'
            '{"c": 1}\n{"d": 1}\n{"e": 1}\n')
    repo = _repo(tmp_path)
    _write(repo / PY_NOTEBOOK, base)
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "carnet a six lignes")
    repo = _branche(repo)
    # la branche modifie le carnet, puis atteste SON propre etat (la tete)
    _write(repo / PY_NOTEBOOK, base.replace('{"a": 1}', '{"a": 2}'))
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "modification du carnet sur la branche")
    _attestation(repo, 1, _blob(repo, PY_NOTEBOOK), _blob(repo, CS_NOTEBOOK))
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "attestation a la tete")
    # `main` bouge ensuite sur le meme carnet (front-matter, navigation) :
    # la fusion ecrira un troisieme blob, different de l'etat atteste.
    _git(repo, "checkout", "-q", "main")
    _write(repo / PY_NOTEBOOK, base.replace('{"e": 1}', '{"e": 2}'))
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "main bouge sur le carnet")
    _git(repo, "checkout", "-q", "branche")
    assert _run(repo) == 1
