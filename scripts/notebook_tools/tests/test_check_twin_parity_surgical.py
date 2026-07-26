#!/usr/bin/env python3
"""Rebaseline chirurgical du registre de jumeaux (#8570, porte sur #8542).

Avant #8570 : `--update` (meme avec un selecteur) re-serialisait le registre
entier via `yaml.safe_dump`. Mesure firsthand sur les 116 paires -- rebaseliner
UNE paire produisait `1108 insertions(+), 658 deletions(-)` et supprimait les
**67 lignes de commentaire** du fichier, dont l'en-tete qui documente le schema
et le vocabulaire `parity_level`. Consequences :

  * le vrai changement (4 lignes) devenait irreviewable -- motif poison-catalogue
    applique au registre ;
  * la documentation du registre disparaissait silencieusement ;
  * `update_pair()` conservait par-dessus le marche `date`/`by` de l'audit
    PRECEDENT, donc l'entree affirmait « auditee par X le <date d'avant> » avec
    des SHAs d'aujourd'hui -- la tracabilite mentait.

Depuis #8570 l'ecriture est chirurgicale et la provenance est horodatee.
Depuis #8542 (Option C) le registre est un **repertoire** `twin_pairs.d/`, un
fichier par paire, et la documentation vit dans `_schema.yaml`. La cible du
rebaseline est donc le raw d'UN fichier d'entree -- exactement ce que la boucle
`--update` passe a `surgical_rebaseline` (cf `_pair_file` + boucle `reg_path.is_dir()`).

Ces tests couvrent :
    1. les commentaires d'un fichier d'entree survivent au rebaseline
    2. le diff se limite au bloc `last_audit` de la paire ciblee
    3. un rebaseline sans changement de valeur est un no-op byte-identique
    4. `--by` inscrit l'auteur et la date est remise a aujourd'hui
    5. les fichiers des autres paires restent byte-identiques
    6. `_schema.yaml` (la documentation) n'est jamais une cible de rebaseline

Note de conception -- **pas de `pytest.skip` sur registre absent**. Un registre
introuvable est precisement la panne que ces tests doivent attraper : #8586 a
repointe le loader vers `twin_pairs.d/` en laissant ce module sur l'ancien
`twin_pairs.yaml`, et les gardes sont passees en SKIP silencieux (`sss.s`).
La suite restait verte pendant que la couverture s'evaporait. Un test qui skippe
est pire qu'un test qui echoue : il ne signale rien. D'ou `pytest.fail`.

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
REGISTRY_DIR = SCRIPT_DIR / "twin_pairs.d"
SCHEMA_FILE = REGISTRY_DIR / "_schema.yaml"


def _load_module():
    spec = importlib.util.spec_from_file_location("check_twin_parity", SCRIPT)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


ctp = _load_module()


def _entry_files() -> list[Path]:
    """Fichiers de paires du registre (hors documentation `_`-prefixee).

    Echoue -- ne skippe pas -- si le registre est introuvable ou vide : c'est
    la regression #8586 elle-meme.
    """
    if not REGISTRY_DIR.is_dir():
        pytest.fail(
            f"registre introuvable : {REGISTRY_DIR}. "
            "Si le registre a demenage, ce module doit suivre : un skip ici "
            "rendrait la suite verte sans rien garder (regression #8586)."
        )
    files = [f for f in sorted(REGISTRY_DIR.glob("*.yaml"))
             if not f.name.startswith("_")]
    if not files:
        pytest.fail(f"registre vide : aucun fichier de paire dans {REGISTRY_DIR}")
    return files


@pytest.fixture
def registry_backup():
    """Sauvegarde + restauration du REPERTOIRE de registre autour de chaque test."""
    files = _entry_files()
    backup = REGISTRY_DIR.with_name(REGISTRY_DIR.name + ".bak.c8570")
    if backup.exists():
        shutil.rmtree(backup)
    shutil.copytree(REGISTRY_DIR, backup)
    try:
        yield files
    finally:
        shutil.rmtree(REGISTRY_DIR)
        shutil.move(str(backup), str(REGISTRY_DIR))


def _pair_name(path: Path) -> str:
    for line in path.read_text(encoding="utf-8").splitlines():
        stripped = line.lstrip("- ").rstrip()
        if stripped.startswith("name:"):
            return stripped.split(":", 1)[1].strip().strip("\"'")
    pytest.fail(f"fichier de paire sans `name:` exploitable : {path}")


def test_comments_survive_surgical_rebaseline():
    """Le bug fondateur : `safe_dump` supprimait les commentaires.

    Raw craft pour que la garde soit deterministe -- elle ne doit pas dependre
    de quel fichier d'entree porte, ce jour-la, un commentaire.
    """
    raw = (
        "# en-tete documentaire de l'entree\n"
        "- name: Paire-Temoin\n"
        "  python: a.ipynb\n"
        "  csharp: b.ipynb\n"
        "  # commentaire interne, au milieu du bloc\n"
        "  last_audit:\n"
        "    date: '2020-01-01'\n"
        "    by: auditeur-precedent\n"
    )
    before = sum(1 for line in raw.splitlines() if line.lstrip().startswith("#"))
    assert before == 2

    new_raw, touched = ctp.surgical_rebaseline(raw, {"Paire-Temoin": {"by": "test-lane"}})
    after = sum(1 for line in new_raw.splitlines() if line.lstrip().startswith("#"))
    assert touched == 1
    assert after == before, "un rebaseline ne doit supprimer aucun commentaire"
    assert "# en-tete documentaire de l'entree" in new_raw
    assert "  # commentaire interne, au milieu du bloc" in new_raw


def test_diff_limited_to_target_block(registry_backup):
    """Seules les lignes changees de la paire ciblee bougent."""
    pfile = registry_backup[0]
    raw = pfile.read_text(encoding="utf-8")
    name = _pair_name(pfile)

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
    import yaml

    pfile = registry_backup[0]
    raw = pfile.read_text(encoding="utf-8")
    name = _pair_name(pfile)

    data = yaml.safe_load(raw)
    entry = data[0] if isinstance(data, list) else data
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


def test_other_pair_files_untouched(registry_backup):
    """Rebaseliner une paire ne doit rien changer aux 115 autres FICHIERS.

    Rejoue la boucle de production (`--update` en mode repertoire) : lire le
    fichier de la paire, `surgical_rebaseline`, reecrire ce fichier-la seul.
    """
    files = registry_backup
    assert len(files) > 1, "registre trop petit pour tester l'isolation"

    target = files[0]
    name = _pair_name(target)
    others_before = {f: f.read_bytes() for f in files[1:]}

    new_raw, _ = ctp.surgical_rebaseline(
        target.read_text(encoding="utf-8"), {name: {"by": "sentinelle-c8570"}}
    )
    target.write_text(new_raw, encoding="utf-8")

    assert "sentinelle-c8570" in target.read_text(encoding="utf-8")
    for f, content in others_before.items():
        assert f.read_bytes() == content, f"fichier {f.name} modifie a tort"


def test_pair_file_resolves_from_name(registry_backup):
    """`name` -> fichier : le mapping dont depend l'ecriture file-per-entry.

    En mode repertoire la boucle `--update` retrouve le fichier via `_pair_file`.
    Si ce mapping derive, le rebaseline n'ecrit nulle part -- en silence.
    """
    for pfile in registry_backup:
        name = _pair_name(pfile)
        assert ctp._pair_file(REGISTRY_DIR, name) == pfile, (
            f"'{name}' resout vers {ctp._pair_file(REGISTRY_DIR, name).name}, "
            f"mais son entree vit dans {pfile.name}"
        )


def test_schema_file_is_never_a_rebaseline_target(registry_backup):
    """La documentation (`_schema.yaml`) est hors du champ du rebaseline.

    C'est la ou vivent, depuis #8542, les lignes de commentaire que le bug
    fondateur supprimait. Aucun `name` de paire ne doit y resoudre, et le
    chargeur doit l'ignorer.
    """
    if not SCHEMA_FILE.exists():
        pytest.fail(f"documentation du registre absente : {SCHEMA_FILE}")
    comments = sum(1 for line in SCHEMA_FILE.read_text(encoding="utf-8").splitlines()
                   if line.lstrip().startswith("#"))
    assert comments > 0, "_schema.yaml doit porter la documentation du registre"

    for pfile in registry_backup:
        assert ctp._pair_file(REGISTRY_DIR, _pair_name(pfile)) != SCHEMA_FILE

    loaded_names = {p["name"] for p in ctp.load_registry(REGISTRY_DIR)}
    assert loaded_names == {_pair_name(f) for f in registry_backup}
