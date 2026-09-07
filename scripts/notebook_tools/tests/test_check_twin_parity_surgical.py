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
import sys
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
    de quel fichier d'entree porte, ce jour-la, un commentaire. Depuis #9399,
    un rebaseline d'une paire legacy qui drift migre vers la forme append-only
    `audits:` ; la garantie porte toujours : aucun commentaire n'est supprime.
    """
    raw = (
        "# en-tete documentaire de l'entree\n"
        "- name: Paire-Temoin\n"
        "  family: Test\n"
        "  python: a.ipynb\n"
        "  csharp: b.ipynb\n"
        "  parity_level: full\n"
        "  # commentaire interne, au milieu du bloc\n"
        "  last_audit:\n"
        "    date: '2020-01-01'\n"
        "    by: auditeur-precedent\n"
        "    python_sha: a1b2c3d4e5f6a1b2c3d4e5f6a1b2c3d4e5f6a1b2\n"
        "    csharp_sha: 0f1e2d3c4b5a0f1e2d3c4b5a0f1e2d3c4b5a0f1e\n"
    )
    before = sum(1 for line in raw.splitlines() if line.lstrip().startswith("#"))
    assert before == 2

    # SHA python change -> declenche la migration legacy -> audits:.
    new_raw, touched = ctp.surgical_rebaseline(raw, {"Paire-Temoin": {
        "date": "2026-08-04", "by": "test-lane",
        "python_sha": "b2c3d4e5f6a1b2c3d4e5f6a1b2c3d4e5f6a1b2c3",
        "csharp_sha": "0f1e2d3c4b5a0f1e2d3c4b5a0f1e2d3c4b5a0f1e",
    }})
    after = sum(1 for line in new_raw.splitlines() if line.lstrip().startswith("#"))
    assert touched == 1
    assert after == before, "un rebaseline ne doit supprimer aucun commentaire"
    assert "# en-tete documentaire de l'entree" in new_raw
    assert "  # commentaire interne, au milieu du bloc" in new_raw


def test_diff_limited_to_target_block():
    """Seul le bloc d'audit de la paire ciblee bouge ; le reste est intact.

    Depuis #9399 (volet a, migration at-rest), le registre est en forme
    append-only `audits:`. Un rebaseline qui drift APPEND une nouvelle entree ;
    TOUS les enregistrements precedents survivent verbatim. La garantie
    chirurgicale (#8570) est preservee : aucune cle top-level hors audit
    (name/family/python/csharp/parity_level/known_differences) ne change
    (anti-regression : on ne jette pas l'historique d'audit).

    Note : ce test exerce `surgical_rebaseline` comme FONCTION PURE sur un
    raw inline fabrique, independamment de l'etat du registre reel (migre en
    file-per-audit, #14911 : les paires reelles n'ont plus de `audits:` inline).
    La garantie de isolation file-per-audit (un audit = un fichier, rien
    n'ecrase l'historique) est couverte par test_twin_registry_integrity.
    """
    import yaml

    raw = (
        "- name: Paire-Temoin\n"
        "  family: Test\n"
        "  python: a.ipynb\n"
        "  csharp: b.ipynb\n"
        "  parity_level: full\n"
        "  audits:\n"
        "    - date: \"2026-01-01\"\n"
        "      by: auditeur-precedent\n"
        "      python_sha: a1b2c3d4e5f6a1b2c3d4e5f6a1b2c3d4e5f6a1b2\n"
        "      csharp_sha: 0f1e2d3c4b5a0f1e2d3c4b5a0f1e2d3c4b5a0f1e\n"
        "    - date: \"2026-02-01\"\n"
        "      by: auditeur-second\n"
        "      python_sha: b2c3d4e5f6a1b2c3d4e5f6a1b2c3d4e5f6a1b2c3\n"
        "      csharp_sha: 1f2e3d4c5b6a1f2e3d4c5b6a1f2e3d4c5b6a1f2e\n"
        "  known_differences:\n"
        "    - 'sibling qui ne doit pas bouger'\n"
    )
    before = yaml.safe_load(raw)[0]
    old_audit = ctp._latest_audit(before)
    before_audits = before["audits"]

    # SHA python change -> append a new entry (registry is audits: since the
    # #9399 volet a at-rest migration).
    new_raw, touched = ctp.surgical_rebaseline(
        raw, {"Paire-Temoin": {"date": "1999-01-01", "by": "sentinelle-c8570",
                               "python_sha": "f" * 40,
                               "csharp_sha": old_audit["csharp_sha"]}}
    )
    assert touched == 1
    after = yaml.safe_load(new_raw)[0]

    # Aucune cle top-level hors audit n'a bouge.
    for key in ("name", "family", "python", "csharp", "parity_level", "known_differences"):
        assert before.get(key) == after.get(key), f"cle non-audit modifiee : {key}"

    # Forme append-only ; tout l'historique survit, le sentinel est appende.
    assert "last_audit" not in after, "le singleton legacy doit etre remplace"
    audits = after["audits"]
    assert isinstance(audits, list) and len(audits) == len(before_audits) + 1
    assert audits[:-1] == before_audits, "les enregistrements precedents doivent survivre verbatim"
    assert audits[-1]["python_sha"] == "f" * 40, "le nouvel enregistrement doit etre dernier"
    assert audits[-1]["by"] == "sentinelle-c8570"


def test_noop_is_byte_identical():
    """Rebaseliner vers les valeurs deja en place ne produit aucun churn.

    Sans cette garantie, un rebaseline sur une paire a jour normaliserait le
    quoting (le registre melange 'x' et "x") et polluerait le diff.

    Le candidat noop doit porter les MEMES cles de comparaison que le dernier
    audit (#9581) : si celui-ci a des `content_*_sha` (rebaseline outil récent)
    et que le candidat ne les a pas, `_cmp_pair_shas` compare content-sha vs
    blob-sha -> faux drift -> append parasite. Un vrai rebaseline recalcule
    toujours les deux familles de SHAs ; le test doit faire pareil.

    Exerce `surgical_rebaseline` en fonction pure sur un raw inline fabrique
    (le registre reel est migre file-per-audit, #14911).
    """
    import yaml

    raw = (
        "- name: Paire-Noop\n"
        "  family: Test\n"
        "  python: a.ipynb\n"
        "  csharp: b.ipynb\n"
        "  audits:\n"
        "    - date: \"2026-01-01\"\n"
        "      by: lane:CoursIA\n"
        "      python_sha: aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n"
        "      csharp_sha: bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n"
        "      content_python_sha: cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc\n"
        "      content_csharp_sha: dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd\n"
    )
    data = yaml.safe_load(raw)
    entry = data[0]
    audit = ctp._latest_audit(entry)

    noop = {"date": str(audit["date"]), "by": audit["by"],
            "python_sha": audit["python_sha"], "csharp_sha": audit["csharp_sha"]}
    for k in ("content_python_sha", "content_csharp_sha"):
        if k in audit:
            noop[k] = audit[k]

    new_raw, touched = ctp.surgical_rebaseline(raw, {"Paire-Noop": noop})
    assert touched == 0
    assert new_raw == raw, "un no-op doit etre byte-identique"


def test_update_pair_stamps_fresh_provenance():
    """`by` et `date` sont rafraichis : la tracabilite ne doit pas mentir."""
    pair = {
        "python": "does/not/exist-a.ipynb",
        "csharp": "does/not/exist-b.ipynb",
        "last_audit": {"date": "2020-01-01", "by": "auditeur-precedent"},
    }
    audit, _, _ = ctp.update_pair(Path("."), pair, by="myia-ai-01:CoursIA")
    assert audit["by"] == "myia-ai-01:CoursIA", "--by doit primer sur l'ancien auteur"
    assert audit["date"] == dt.date.today().isoformat(), (
        "la date doit etre celle du rebaseline, pas celle de l'audit precedent"
    )


def test_other_pair_files_untouched(tmp_path):
    """Rebaseliner une paire ne doit rien changer aux FICHIERS des autres paires.

    Rejoue la boucle de production (`--update` en mode repertoire) : lire le
    fichier de la paire, `surgical_rebaseline`, reecrire ce fichier-la seul.
    Ici on fabrique un registre synthetique (`tmp_path`) pour verifier la
    garantie d'isolation sans dependre de l'etat du registre reel (migre en
    file-per-audit, #14911 : les cours file-per-audit ne touchent plus du tout
    les autres paires -- un audit s'ecrit dans son propre `<pair>/`).
    """
    reg = tmp_path / "twin_pairs.d"
    reg.mkdir()
    # 3 paires inline (chaque fichier porte son propre `audits:`).
    for idx, name in enumerate(("Alpha", "Beta", "Gamma"), start=1):
        (reg / f"pair-{name.lower()}.yaml").write_text(
            f"- name: {name}\n"
            f"  family: Test\n"
            f"  python: a{idx}.ipynb\n"
            f"  csharp: b{idx}.ipynb\n"
            f"  audits:\n"
            f"    - date: \"2026-01-01\"\n"
            f"      by: lane:CoursIA\n"
            f"      python_sha: {name.lower() * 40}\n"
            f"      csharp_sha: {name.upper() * 40}\n",
            encoding="utf-8",
        )
    target = reg / "pair-alpha.yaml"
    others = {f: f.read_bytes() for f in reg.glob("*.yaml") if f != target}
    assert len(others) >= 2, "trop peu de paires pour tester l'isolation"

    # Entree complete (SHA python change) -> append un enregistrement.
    new_raw, _ = ctp.surgical_rebaseline(
        target.read_text(encoding="utf-8"),
        {"Alpha": {"date": "1999-01-01", "by": "sentinelle-c8570",
                   "python_sha": "f" * 40, "csharp_sha": "e" * 40}},
    )
    ctp.write_registry_text(target, new_raw)

    assert "sentinelle-c8570" in target.read_text(encoding="utf-8")
    for f, content in others.items():
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


def test_write_preserves_lf_on_every_platform(tmp_path):
    """La garantie chirurgicale doit survivre a l'ECRITURE, pas seulement au calcul.

    Les tests ci-dessus verifient `surgical_rebaseline` au niveau de la chaine :
    ils passent sur toutes les plateformes, y compris quand le fichier ecrit sur
    disque est integralement reecrit. `Path.write_text` ouvre avec
    `newline=None`, qui traduit `\\n` en `os.linesep` -- donc en CRLF sous
    Windows. Le calcul restait chirurgical, l'ecriture ne l'etait pas, et le
    diff affichait le fichier entier (#8709, #8713 : `-16` lignes pour un
    changement de deux).
    """
    target = tmp_path / "pair.yaml"
    original = "- name: X\n  last_audit:\n    date: \"2020-01-01\"\n"
    target.write_bytes(original.encode("utf-8"))

    new_raw, _ = ctp.surgical_rebaseline(original, {"X": {"date": "2026-01-01"}})
    ctp.write_registry_text(target, new_raw)

    written = target.read_bytes()
    assert b"\r\n" not in written, (
        "le registre doit rester en LF : un CRLF fait apparaitre chaque ligne "
        "inchangee comme modifiee et noie la ligne reellement auditee"
    )
    # La garantie LF est relative au TEXTE CALCULE (la migration #9399 ajoute
    # legitimement des lignes) : l'ecriture ne doit ni traduire les LF en CRLF,
    # ni en ajouter/supprimer vs ce que surgical_rebaseline a calcule.
    assert written.decode("utf-8").count("\n") == new_raw.count("\n")


def test_registry_blobs_are_lf_only():
    """Aucun blob de registre versionne ne doit etre en CRLF.

    Backstop du test precedent : meme si un ecrivain contourne
    `write_registry_text`, le registre **dans git** reste homogene.

    On interroge l'index (`git ls-files --eol`, colonne `i/`) et non le working
    tree : avec `core.autocrlf=true` -- la configuration par defaut de la moitie
    de la flotte -- le working tree est legitimement en CRLF alors que le blob
    est en LF. Tester les octets sur disque ferait echouer ce test sur toutes
    les machines Windows correctement configurees, pour un registre sain. C'est
    aussi ce qui explique que le defaut ait pu voyager : la ou `autocrlf` est
    actif il est invisible, la ou il ne l'est pas il committe du CRLF.
    """
    import subprocess

    out = subprocess.run(
        ["git", "ls-files", "--eol", str(REGISTRY_DIR)],
        capture_output=True, text=True, encoding="utf-8", errors="replace", cwd=SCRIPT_DIR,
    )
    if out.returncode != 0:
        pytest.skip("hors depot git")
    crlf = [line.split("\t")[-1] for line in out.stdout.splitlines()
            if line.startswith("i/crlf")]
    assert not crlf, f"blobs de registre en CRLF : {', '.join(crlf)}"


# --- Forme append-only `audits:` (#9399 volet a) ---
#
# Le singleton `last_audit:` etait un aimant a collision : deux audits
# concurrents de la meme paire ecrivaient les memes lignes -> CONFLICT git, ou
# pire, ecrasement silencieux du plus recent par le plus ancien (#9171, #9237,
# #9245, + 4e manifestation invisible). La liste append-only `audits:` fait que
# chaque audit ajoute une entree distincte : rien n'ecrase plus rien.


def test_legacy_migration_preserves_reason_and_history():
    """La migration legacy -> audits: preserve `reason` et l'enregistrement ancien.

    `reason` est un texte libre long de justification d'audit. Le rejeter
    reviendrait a jetter l'historique d'audit -> anti-regression (#9399 critere 4).
    On preserve byte-faithful via re-indentation mecanique (pas de re-quoting).
    """
    raw = (
        "- name: Paire-R\n"
        "  last_audit:\n"
        "    date: \"2026-08-01\"\n"
        "    by: lane-prev:CoursIA\n"
        "    python_sha: aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n"
        "    csharp_sha: bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n"
        "    reason: \"Markdown-only fix: cell 13 cited N=1000 but caps at 500.\"\n"
    )
    new_raw, touched = ctp.surgical_rebaseline(
        raw, {"Paire-R": {"date": "2026-08-04", "by": "po-2023:CoursIA",
                          "python_sha": "c" * 40, "csharp_sha": "b" * 40}}
    )
    assert touched == 1
    import yaml
    entry = yaml.safe_load(new_raw)[0]
    assert "last_audit" not in entry and "audits" in entry
    audits = entry["audits"]
    assert len(audits) == 2
    # L'ancien enregistrement (item[0]) garde son reason + ses SHAs.
    assert audits[0]["reason"].startswith("Markdown-only fix"), "reason perdu !"
    assert audits[0]["python_sha"].startswith("a" * 8)
    # Le nouvel enregistrement (item[1]) porte le nouveau SHA.
    assert audits[1]["python_sha"] == "c" * 40


def test_concurrent_audits_never_silently_overwrite():
    """LE garant central de #9399 : deux audits ne s'ecrasent jamais silencieusement.

    Simule deux lanes auditant la meme paire depuis la meme base legacy :
    chacune migre -> audits:[old, sienne]. Apres les deux, l'ETAT REGROUPE les
    deux enregistrements -- aucun n'a ecrase l'autre. Avec le singleton, la 2e
    aurait silencieusement remplace la 1ere (inversion chronologique, 4e
    manifestation d'#9399). Ici les deux SHAs survivent.
    """
    base = (
        "- name: Paire-C\n"
        "  last_audit:\n"
        "    python_sha: 0a1b2c3d4e5f0a1b2c3d4e5f0a1b2c3d4e5f0a1b\n"
        "    csharp_sha: 1f2e3d4c5b6a1f2e3d4c5b6a1f2e3d4c5b6a1f2e\n"
    )
    audit_a = {"date": "2026-08-04", "by": "lane-a:CoursIA",
               "python_sha": "a" * 40, "csharp_sha": "b" * 40}
    audit_b = {"date": "2026-08-04", "by": "lane-b:CoursIA",
               "python_sha": "c" * 40, "csharp_sha": "d" * 40}
    # Chaque lane part de `base` (le scenario du merge 3-way concurrent).
    out_a, _ = ctp.surgical_rebaseline(base, {"Paire-C": audit_a})
    out_b, _ = ctp.surgical_rebaseline(base, {"Paire-C": audit_b})
    # La resolution du merge concurrent = on regroupe les entrees des deux cotes
    # (ce que fait un humain/agent en quelques secondes, sans perte de donnees).
    import yaml
    audits_a = yaml.safe_load(out_a)[0]["audits"]
    audits_b = yaml.safe_load(out_b)[0]["audits"]
    merged_entries = [audits_a[1], audits_b[1]]  # item[0] est le vieux, identique
    shas = {e["python_sha"] for e in merged_entries}
    assert shas == {"a" * 40, "c" * 40}, (
        "les deux audits doivent survivre au merge ; un ecrasement silencieux "
        "n'en laisserait qu'un"
    )
    # Preuve que rien n'a ete ecrase : chaque sortie contient encore le vieux
    # enregistrement de base (item[0]) -- l'historique est intact des deux cotes.
    assert audits_a[0]["python_sha"] == "0a1b2c3d4e5f0a1b2c3d4e5f0a1b2c3d4e5f0a1b"
    assert audits_b[0]["python_sha"] == "0a1b2c3d4e5f0a1b2c3d4e5f0a1b2c3d4e5f0a1b"


def test_append_only_noop_does_not_grow_list():
    """Re-auditer une paire deja a jour n'ajoute pas de doublon (anti-inflation).

    Sans cette garde, des `--update` successifs sans changement reel gonfleraient
    la liste indefiniment. Le no-op (SHAs inchanges) est byte-identical.
    """
    raw = (
        "- name: Paire-N\n"
        "  audits:\n"
        "    - date: \"2026-08-01\"\n"
        "      by: lane:CoursIA\n"
        "      python_sha: aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n"
        "      csharp_sha: bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n"
    )
    same = {"date": "2026-08-04", "by": "lane:CoursIA",
            "python_sha": "a" * 40, "csharp_sha": "b" * 40}
    out, touched = ctp.surgical_rebaseline(raw, {"Paire-N": same})
    assert touched == 0
    assert out == raw, "un no-op sur la forme append-only doit etre byte-identique"


# --- #10430 : indentation native 4 (audits: a indent 4) + coupure relative ---

_INDENT4_RAW = (
    "-   name: Indent4Pair\n"
    "    family: Test\n"
    "    python: a.ipynb\n"
    "    csharp: b.ipynb\n"
    "    parity_level: semantic\n"
    "    audits:\n"
    "    -   date: '2020-01-01'\n"
    "        by: old-auditor\n"
    "        python_sha: aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n"
    "        csharp_sha: bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n"
    "    known_differences:\n"
    "    - 'note sibling qui ne doit pas etre avalee par le bloc audit'\n"
)


def test_indent4_audits_header_now_recognized_10430():
    """Bug fondateur #10430 : `audits:` indent 4 etait invisible au regex \\s{2}.

    Avant le fix, surgical_rebaseline renvoyait touched=0 (header non reconnu)
    => no-op silencieux. Apres : le bloc est trouve, un SHA change declenche
    l'append, touched=1.
    """
    new = {"date": "2026-08-11", "by": "test-lane",
           "python_sha": "c" * 40,
           "csharp_sha": "b" * 40}  # csharp inchange, python change -> drift
    out, touched = ctp.surgical_rebaseline(_INDENT4_RAW, {"Indent4Pair": new})
    assert touched == 1, "audits: a indent 4 doit desormais etre reconnu (#10430)"
    # Append-only : le vieil enregistrement survive + un nouveau est ajoute.
    assert out.count("-   date:") + out.count("- date:") >= 2


def test_indent4_sibling_known_differences_not_consumed_10430():
    """La coupure doit etre RELATIVE a l'indent de la cle, pas un seuil absolu.

    Avec l'ancien `\\s{4,}\\S` pour les continuations, autoriser `audits:` a
    indent 4 aurait etrangle la cle sibling `known_differences:` (aussi a
    indent 4) dans le bloc audit -> faux drift + perte de la section. Le fix
    coupe au premier non-item non-plus-indent-que-la-cle.
    """
    new = {"date": "2026-08-11", "by": "test-lane",
           "python_sha": "c" * 40, "csharp_sha": "b" * 40}
    out, touched = ctp.surgical_rebaseline(_INDENT4_RAW, {"Indent4Pair": new})
    assert touched == 1
    assert "known_differences:" in out, "la cle sibling doit survivre"
    assert "note sibling qui ne doit pas etre avalee" in out, (
        "le contenu de known_differences ne doit pas etre corrompu"
    )


def test_indent2_regression_normal_style_still_works():
    """Regression : le style indent-2 (156 fichiers, la norme) reste reconnu.

    Le passage a \\s{2,} + coupure relative ne doit pas casser la majorite des
    registres. On verifie aussi qu'un sibling indent-2 (known_differences)
    n'est pas consume dans ce format la non plus.
    """
    raw = (
        "- name: Indent2Pair\n"
        "  family: Test\n"
        "  python: a.ipynb\n"
        "  csharp: b.ipynb\n"
        "  audits:\n"
        "    - date: '2020-01-01'\n"
        "      by: old-auditor\n"
        "      python_sha: aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n"
        "      csharp_sha: bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n"
        "  known_differences:\n"
        "    - 'sibling indent-2'\n"
    )
    new = {"date": "2026-08-11", "by": "test-lane",
           "python_sha": "c" * 40, "csharp_sha": "b" * 40}
    out, touched = ctp.surgical_rebaseline(raw, {"Indent2Pair": new})
    assert touched == 1
    assert "known_differences:" in out
    assert "sibling indent-2" in out


def test_append_preserves_indentationless_audit_items_12617():
    """Un item au meme niveau que ``audits:`` impose la meme marge a l'append.

    L'ancien rendu ajoutait quatre espaces absolus et melangeait deux styles de
    sequence dans ce bloc indent-4, ce qui produisait un YAML non parsable.
    """
    import yaml

    new = {"date": "2026-08-23", "by": "test-lane",
           "python_sha": "c" * 40, "csharp_sha": "b" * 40}
    out, touched = ctp.surgical_rebaseline(_INDENT4_RAW, {"Indent4Pair": new})

    assert touched == 1
    entry = yaml.safe_load(out)[0]
    assert len(entry["audits"]) == 2
    assert entry["audits"][1]["python_sha"] == "c" * 40
    assert "\n    - date: \"2026-08-23\"\n" in out
    assert "\n      date: \"2026-08-23\"\n" not in out


def test_append_preserves_indented_audit_items_12617():
    """Le style usuel item-indent = header-indent + 2 reste byte-coherent."""
    import yaml

    raw = (
        "- name: IndentedPair\n"
        "  audits:\n"
        "    - date: '2020-01-01'\n"
        "      by: old-auditor\n"
        "      python_sha: aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n"
        "      csharp_sha: bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n"
    )
    new = {"date": "2026-08-23", "by": "test-lane",
           "python_sha": "c" * 40, "csharp_sha": "b" * 40}
    out, touched = ctp.surgical_rebaseline(raw, {"IndentedPair": new})

    assert touched == 1
    entry = yaml.safe_load(out)[0]
    assert len(entry["audits"]) == 2
    assert entry["audits"][1]["python_sha"] == "c" * 40
    assert "\n    - date: \"2026-08-23\"\n" in out


def test_touched_zero_when_header_genuinely_absent():
    """Contrat dont depend la garde loud-failure (#10430) du chemin multi-fichiers.

    Quand une paire n'a AUCUN bloc audit (ni audits:, ni last_audit:),
    surgical_rebaseline renvoie touched=0. Le chemin CLI multi-fichiers
    distinguait avant ce cas d'un no-op legit uniquement par cette valeur ;
    on verifie le contrat unitairement.
    """
    raw = (
        "- name: NoAuditPair\n"
        "  family: Test\n"
        "  python: a.ipynb\n"
        "  csharp: b.ipynb\n"
    )
    new = {"date": "2026-08-11", "by": "test-lane",
           "python_sha": "c" * 40, "csharp_sha": "b" * 40}
    out, touched = ctp.surgical_rebaseline(raw, {"NoAuditPair": new})
    assert touched == 0
    assert out == raw, "aucun header => byte-identique (la CLI le signale en AVERTISSEMENT)"


def test_cli_first_audit_file_written_for_never_audited_pair(tmp_path):
    """Une paire jamais auditée recoit son PREMIER fichier d'audit (#14911).

    #10430 posait que la CLI devait exit 1 quand un bloc d'audit inline etait
    introuvable (scanner aveugle par regex). En forme file-per-audit (#14911),
    il n'y a plus de header inline a manquer : les audits sont des fichiers,
    donc `--update` sur une paire sans aucun audit ecrit legitimement son
    premier fichier (`0001-<date>-<lane>.yaml`) et sort 0. C'est le
    comportement nominal d'un premier audit, pas un echec.

    Le notebook existe dans git (sinon la paire serait `skipped`).
    """
    import subprocess

    repo = tmp_path / "repo"
    repo.mkdir()
    (repo / "a.ipynb").write_text("{}", encoding="utf-8")
    (repo / "b.ipynb").write_text("{}", encoding="utf-8")
    reg = repo / "twin_pairs.d"
    reg.mkdir()
    (reg / "_schema.yaml").write_text("# schema\n", encoding="utf-8")
    target = reg / "noauditpair.yaml"
    target.write_text(
        "- name: NoAuditPair\n"
        "  family: Test\n"
        "  python: a.ipynb\n"
        "  csharp: b.ipynb\n",
        encoding="utf-8",
    )
    # git init + commit pour que `_git_blob_sha` puisse rendre un SHA non-None
    # (sinon la CLI court-circuite en skipped -> 'Ignorees').
    _git_init_commit(repo)

    out = subprocess.run(
        [sys.executable, str(SCRIPT),
         "--repo-root", str(repo),
         "--registry", str(reg),
         "--update", "--pair", "NoAuditPair", "--by", "test-lane"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    # Pas de loud-fail : cette paire est auditée pour la premiere fois.
    assert "AVERTISSEMENT" not in out.stderr and "AVERTISSEMENT" not in out.stdout, (
        f"AVERTISSEMENT inattendu ; stdout={out.stdout!r} stderr={out.stderr!r}"
    )
    assert out.returncode == 0, (
        f"premier audit d'une paire sans audit doit sortir 0, "
        f"obtenu = {out.returncode}. stdout={out.stdout!r} stderr={out.stderr!r}"
    )
    # Un fichier d'audit 0001-<date>-<lane>.yaml a ete cree dans <slug>/.
    audit_dir = reg / "noauditpair"
    assert audit_dir.is_dir(), f"repertoire d'audit absent : {audit_dir}"
    files = sorted(audit_dir.glob("*.yaml"))
    assert len(files) == 1, f"un seul audit attendu, got {[f.name for f in files]}"
    assert files[0].name.startswith("0001-"), files[0].name
    # L'intention ne porte pas de bloc audits inline (elle n'en a jamais eu).
    assert "audits:" not in target.read_text(encoding="utf-8")


def test_cli_exit_zero_when_header_present_noop(tmp_path):
    """Compagnon du test precedent : un no-op legit (SHAs deja a jour) doit
    rester exit=0. La nouvelle regle exit=1 ne doit pas se declencher quand
    le scanner fait son travail correctement et trouve le bloc audit (meme
    si l'entree est deja a jour).
    """
    import subprocess

    repo = tmp_path / "repo"
    repo.mkdir()
    (repo / "a.ipynb").write_text("{}", encoding="utf-8")
    (repo / "b.ipynb").write_text("{}", encoding="utf-8")
    reg = repo / "twin_pairs.d"
    reg.mkdir()
    (reg / "_schema.yaml").write_text("# schema\n", encoding="utf-8")
    sha_a = "a" * 40
    sha_b = "b" * 40
    (reg / "okpair.yaml").write_text(
        f"- name: OkPair\n"
        f"  family: Test\n"
        f"  python: a.ipynb\n"
        f"  csharp: b.ipynb\n"
        f"  audits:\n"
        f"    - date: '2026-01-01'\n"
        f"      by: lane-prev:CoursIA\n"
        f"      python_sha: {sha_a}\n"
        f"      csharp_sha: {sha_b}\n",
        encoding="utf-8",
    )
    _git_init_commit(repo)

    out = subprocess.run(
        [sys.executable, str(SCRIPT),
         "--repo-root", str(repo),
         "--registry", str(reg),
         "--update", "--pair", "OkPair", "--by", "test-lane"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    # Pas d'AVERTISSEMENT loud-fail, pas d'exit non-zero.
    assert "AVERTISSEMENT" not in out.stderr, (
        f"AVERTISSEMENT inattendu sur stderr : {out.stderr!r}"
    )
    assert out.returncode == 0, (
        f"no-op legit doit garder exit=0 ; obtenu = {out.returncode}. "
        f"stdout={out.stdout!r} stderr={out.stderr!r}"
    )


def _git_init_commit(repo: Path):
    """Helper : initialise un repo git et commit tous les fichiers dans repo.

    Necessaire pour que `_git_blob_sha` (via `git show <ref>:path`) rende
    un SHA non-None ; sinon la CLI court-circuite toutes les paires en
    `skipped` (notebook absent de git) AVANT d'arriver au bloc loud-fail
    que ce test veut exercer.
    """
    import subprocess

    subprocess.run(["git", "init", "-q"], cwd=str(repo), check=True)
    subprocess.run(["git", "config", "user.email", "test@x"], cwd=str(repo), check=True)
    subprocess.run(["git", "config", "user.name", "test"], cwd=str(repo), check=True)
    subprocess.run(["git", "add", "-A"], cwd=str(repo), check=True)
    subprocess.run(
        ["git", "commit", "-q", "-m", "init for twin parity test"],
        cwd=str(repo), check=True,
    )
