#!/usr/bin/env python3
"""Rebaseline chirurgical du registre de jumeaux (#8570).

Avant : `--update` (meme avec un selecteur) re-serialisait le registre entier
via `yaml.safe_dump`. Mesure firsthand sur les 116 paires -- rebaseliner UNE
paire produisait `1108 insertions(+), 658 deletions(-)` et supprimait les **67
lignes de commentaire** du fichier, dont l'en-tete de 15 lignes qui documente
le schema et le vocabulaire `parity_level`. Consequences :

  * le vrai changement (4 lignes) devenait irreviewable -- motif poison-catalogue
    applique au registre ;
  * la documentation du registre disparaissait silencieusement ;
  * `update_pair()` conservait par-dessus le marche `date`/`by` de l'audit
    PRECEDENT, donc l'entree affirmait « auditee par X le <date d'avant> » avec
    des SHAs d'aujourd'hui -- la tracabilite mentait.

C'est pourquoi la remediation CI prescrivait l'edition manuelle. Depuis #8570
l'ecriture est chirurgicale et la provenance est horodatee : la commande courte
redevient la bonne.

Ces tests couvrent :
    1. les commentaires du registre survivent a un `--update --pair`
    2. le diff se limite au bloc `last_audit` de la paire ciblee
    3. un rebaseline sans changement de valeur est un no-op byte-identique
    4. `--by` inscrit l'auteur et la date est remise a aujourd'hui
    5. les autres paires restent byte-identiques

Run:
    pytest scripts/notebook_tools/tests/test_check_twin_parity_surgical.py
"""
from __future__ import annotations

import datetime as dt
import importlib.util
import shutil
from pathlib import Path

import pytest

SCRIPT_DIR = Path(__file__).resolve().parent.parent
SCRIPT = SCRIPT_DIR / "check_twin_parity.py"
REGISTRY = SCRIPT_DIR / "twin_pairs.yaml"


def _load_module():
    spec = importlib.util.spec_from_file_location("check_twin_parity", SCRIPT)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


ctp = _load_module()


@pytest.fixture
def registry_backup():
    """Sauvegarde + restauration du registre autour de chaque test."""
    if not REGISTRY.exists():
        pytest.skip(f"registre introuvable : {REGISTRY}")
    backup = REGISTRY.with_suffix(".yaml.bak.c8570")
    shutil.copy2(REGISTRY, backup)
    try:
        yield REGISTRY
    finally:
        shutil.copy2(backup, REGISTRY)
        backup.unlink(missing_ok=True)


def _first_pair_name(raw: str) -> str:
    for line in raw.splitlines():
        if line.startswith("- name:"):
            return line.split(":", 1)[1].strip().strip("\"'")
    pytest.skip("registre sans entree exploitable")


def test_comments_survive_surgical_rebaseline(registry_backup):
    """Le bug fondateur : `safe_dump` supprimait les 67 commentaires."""
    raw = REGISTRY.read_text(encoding="utf-8")
    name = _first_pair_name(raw)
    before = sum(1 for line in raw.splitlines() if line.lstrip().startswith("#"))
    assert before > 0, "le registre doit porter son en-tete documentaire"

    new_raw, _ = ctp.surgical_rebaseline(raw, {name: {"by": "test-lane"}})
    after = sum(1 for line in new_raw.splitlines() if line.lstrip().startswith("#"))
    assert after == before, "un rebaseline ne doit supprimer aucun commentaire"


def test_diff_limited_to_target_block(registry_backup):
    """Seules les lignes changees de la paire ciblee bougent."""
    raw = REGISTRY.read_text(encoding="utf-8")
    name = _first_pair_name(raw)

    new_raw, touched = ctp.surgical_rebaseline(
        raw, {name: {"by": "sentinelle-c8570", "date": "1999-01-01"}}
    )
    assert touched == 1

    before, after = raw.splitlines(), new_raw.splitlines()
    assert len(before) == len(after), "aucune ligne ajoutee ni supprimee"
    changed = [i for i, (b, a) in enumerate(zip(before, after)) if b != a]
    assert len(changed) == 2, f"attendu 2 lignes (date + by), obtenu {len(changed)}"
    assert all("sentinelle-c8570" in after[i] or "1999-01-01" in after[i]
               for i in changed)


def test_noop_is_byte_identical(registry_backup):
    """Rebaseliner vers les valeurs deja en place ne produit aucun churn.

    Sans cette garantie, un rebaseline sur une paire a jour normaliserait le
    quoting (le registre melange 'x' et "x") et polluerait le diff.
    """
    raw = REGISTRY.read_text(encoding="utf-8")
    name = _first_pair_name(raw)
    import yaml

    entry = next(p for p in yaml.safe_load(raw) if p["name"] == name)
    audit = entry["last_audit"]

    new_raw, touched = ctp.surgical_rebaseline(
        raw,
        {name: {"date": str(audit["date"]), "by": audit["by"],
                "python_sha": audit["python_sha"], "csharp_sha": audit["csharp_sha"]}},
    )
    assert touched == 0
    assert new_raw == raw, "un no-op doit etre byte-identique"


def test_update_pair_stamps_fresh_provenance():
    """`by` et `date` sont rafraichis : la tracabilite ne doit pas mentir."""
    pair = {
        "python": "does/not/exist-a.ipynb",
        "csharp": "does/not/exist-b.ipynb",
        "last_audit": {"date": "2020-01-01", "by": "auditeur-precedent"},
    }
    audit, _ = ctp.update_pair(Path("."), pair, by="myia-ai-01:CoursIA")
    assert audit["by"] == "myia-ai-01:CoursIA", "--by doit primer sur l'ancien auteur"
    assert audit["date"] == dt.date.today().isoformat(), (
        "la date doit etre celle du rebaseline, pas celle de l'audit precedent"
    )


def test_other_pairs_untouched(registry_backup):
    """Rebaseliner une paire ne doit rien changer aux 115 autres."""
    import yaml

    raw = REGISTRY.read_text(encoding="utf-8")
    name = _first_pair_name(raw)
    new_raw, _ = ctp.surgical_rebaseline(raw, {name: {"by": "sentinelle-c8570"}})

    before = {p["name"]: p["last_audit"] for p in yaml.safe_load(raw)}
    after = {p["name"]: p["last_audit"] for p in yaml.safe_load(new_raw)}
    assert set(before) == set(after), "aucune paire ajoutee ni perdue"
    for other in before:
        if other != name:
            assert before[other] == after[other], f"paire {other} modifiee a tort"
