"""Integrite structurelle du registre twin_pairs.d/ (#8057, file-per-entry #8542 Option C).

Historique : le registre etait un mono-fichier YAML `twin_pairs.yaml` (liste
append-only) sur lequel un merge driver `union` etait declare dans
`.gitattributes`. Les lanes y ajoutaient des entrees disjointes en fin de
fichier, ce qui produisait un conflit serie systematique (une seule PR
mergeable a la fois -- recurrences #8415 consolidation, #8476 re-apply, #8499
recovery tranche, #8505, #8526, #8492, toutes resolues a la main).

#8542 Option C supprime cette classe de conflit a la source : **un fichier par
paire** sous `twin_pairs.d/`. Deux PRs enregistrant des paires differentes
touchent des fichiers differents -- plus rien a fusionner. Cette suite de tests
est portee du mono-fichier vers le file-per-entry : les garanties
(comptage, doublons, schema, SHAs) sont preserves, le mode de defaillance
qu'elles couvraient (corruption silencieuse du merge union) disparait, et deux
nouveaux tests valident la structure file-per-entry elle-meme.

Le registre utilise des git blob SHAs (pas des hashes de contenu) : un notebook
edite (meme markdown-only) deplace son blob et doit etre re-audite via
`check_twin_parity.py --update --pair "<name>" --by "<lane>"`.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

import pytest

yaml = pytest.importorskip("yaml")

# Source unique de verite : le loader de check_twin_parity (evite de dupliquer
# la logique d'agregation du repertoire file-per-entry).
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_twin_parity import load_registry, _slug, _latest_audit  # noqa: E402

REGISTRY_DIR = Path(__file__).resolve().parents[1] / "twin_pairs.d"
SCHEMA = REGISTRY_DIR / "_schema.yaml"
SHA_RE = re.compile(r"^[0-9a-f]{40}$")
# Cles structurelles qu'une entree doit POSSEDER (sous-ensemble). L'enregistrement
# d'audit n'est pas liste ici : depuis #9399 volet (a) il peut prendre deux formes
# -- le singleton legacy `last_audit:` ou la liste append-only `audits:` -- et une
# entree valide possede l'UN des deux (cf `_has_audit_record` / `test_has_audit_record`).
REQUIRED_KEYS = {"name", "family", "python", "csharp", "parity_level"}
ALLOWED_KEYS = {
    "name", "family", "python", "csharp", "parity_level",
    "last_audit", "audits", "known_differences",
}
# Plancher d'entrees (post-migration #8542 : 116 paires sur origin/main). En
# mode file-per-entry, une entree perdue = un fichier supprime ; ce plancher le
# transforme en echec CI bruyant. A LEVER au fur et a mesure que le registre
# grossit (jamais baisser sans investiguer une perte, cf #8542 Constat 2).
MIN_ENTRIES = 116


def _entries() -> list:
    return load_registry(REGISTRY_DIR)


def _has_audit_record(entry: dict) -> bool:
    """Une entree valide possede un enregistrement d'audit sous l'une des deux
    formes (#9399) : le singleton legacy `last_audit:` ou la liste append-only
    `audits:` (non vide, chaque element un dict)."""
    if "last_audit" in entry and isinstance(entry["last_audit"], dict):
        return True
    audits = entry.get("audits")
    return isinstance(audits, list) and len(audits) > 0 and all(
        isinstance(a, dict) for a in audits
    )


def _all_audit_records(entry: dict) -> list:
    """Tous les enregistrements d'audit d'une entree (last_audit + chaque
    element de audits:). Sert a valider les SHAs PARTOUT, pas seulement le
    dernier -- un ancien enregistrement migre doit garder des SHAs valides
    (anti-regression : on ne jette pas l'historique, cf #9399 critere 4)."""
    records = []
    if isinstance(entry.get("last_audit"), dict):
        records.append(entry["last_audit"])
    for a in (entry.get("audits") or []):
        if isinstance(a, dict):
            records.append(a)
    return records


def _pair_files() -> list[Path]:
    """Tous les fichiers *.yaml non `_`-prefixes (un fichier = une paire)."""
    return sorted(p for p in REGISTRY_DIR.glob("*.yaml") if not p.name.startswith("_"))


class _DupKeyLoader(yaml.SafeLoader):
    """SafeLoader qui refuse les cles dupliquees au lieu de garder la derniere.

    Signaturait historique d'un merge union mal tombe (deux `python_sha:` dans
    un meme bloc) ; en file-per-entry c'est le signe d'une main-edit corrompue
    d'un fichier d'entree. PyYAML l'accepte silencieusement par defaut.
    """


def _no_duplicate_keys(loader, node, deep=False):
    mapping = {}
    for key_node, value_node in node.value:
        key = loader.construct_object(key_node, deep=deep)
        if key in mapping:
            raise yaml.constructor.ConstructorError(
                None, None, f"cle dupliquee dans le registre : {key!r}", key_node.start_mark
            )
        mapping[key] = loader.construct_object(value_node, deep=deep)
    return mapping


_DupKeyLoader.add_constructor(
    yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, _no_duplicate_keys
)


# --- Tests portes du mono-fichier (garanties preservees) ---


def test_registry_parses_as_list():
    assert len(_entries()) > 0


def test_no_duplicate_keys_anywhere():
    """Une cle dupliquee dans un fichier d'entree = structure corrompue."""
    for p in _pair_files():
        yaml.load(p.read_text(encoding="utf-8"), Loader=_DupKeyLoader)


def test_no_duplicate_pair_names():
    names = [e.get("name") for e in _entries()]
    dupes = sorted({n for n in names if names.count(n) > 1})
    assert not dupes, f"noms de paires dupliques : {dupes}"


def test_no_duplicate_notebook_paths():
    """Un notebook ne doit apparaitre que dans une seule paire."""
    seen: dict[str, str] = {}
    collisions = []
    for entry in _entries():
        for side in ("python", "csharp"):
            path = entry.get(side)
            if path in seen:
                collisions.append(f"{path} : {seen[path]} et {entry.get('name')}")
            else:
                seen[path] = entry.get("name", "?")
    assert not collisions, "notebooks enregistres deux fois : " + "; ".join(collisions)


def test_required_keys_present():
    missing = [
        f"{e.get('name', '?')} -> {sorted(REQUIRED_KEYS - set(e))}"
        for e in _entries()
        if not REQUIRED_KEYS.issubset(e)
    ]
    assert not missing, f"entrees incompletes : {missing}"


def test_has_audit_record():
    """Chaque entree porte un enregistrement d'audit (last_audit OU audits:, #9399).

    Les deux formes coexistent pendant la migration paresseuse a la volee : une
    entree n'en avoir AUCUNE est une corruption (paire enregistree sans jamais
    etre auditee -> DRIFT permanent non trace).
    """
    no_record = [
        e.get("name", "?") for e in _entries() if not _has_audit_record(e)
    ]
    assert not no_record, f"entrees sans enregistrement d'audit : {no_record}"


def test_audit_shas_are_git_blob_shas():
    """Les shas sont des blob SHA git (40 hex), pas des hashes de contenu.

    Valide les SHAs de TOUS les enregistrements (singleton last_audit + chaque
    element de la liste audits:) : un ancien enregistrement migre doit conserver
    des SHAs valides (#9399 critere 4 : on ne jette pas l'historique).
    """
    bad = []
    for entry in _entries():
        for audit in _all_audit_records(entry):
            for key in ("python_sha", "csharp_sha"):
                sha = audit.get(key)
                if not isinstance(sha, str) or not SHA_RE.match(sha):
                    bad.append(f"{entry.get('name', '?')}.{key} = {sha!r}")
    assert not bad, f"shas invalides : {bad}"


def test_registered_notebooks_exist_on_disk():
    repo_root = REGISTRY_DIR.resolve().parents[2]
    missing = [
        f"{e.get('name', '?')} -> {p}"
        for e in _entries()
        for p in (e.get("python"), e.get("csharp"))
        if p and not (repo_root / p).exists()
    ]
    assert not missing, f"notebooks introuvables : {missing}"


def test_entries_have_exact_key_set():
    """Chaque entree possede EXACTEMENT l'ensemble de cles canonique (ni plus, ni moins)."""
    bad = []
    for entry in _entries():
        keys = set(entry.keys())
        extra = keys - ALLOWED_KEYS
        missing = REQUIRED_KEYS - keys
        if extra or missing:
            name = entry.get("name", "?")
            if extra:
                bad.append(f"{name} -> cles inattendues: {sorted(extra)}")
            if missing:
                bad.append(f"{name} -> cles manquantes: {sorted(missing)}")
    assert not bad, "entrees au schema corrompu : " + "; ".join(bad)


def test_entry_count_floor():
    """Plancher anti-perte-silencieuse (une entree supprimee = un fichier manquant)."""
    n = len(_entries())
    assert n >= MIN_ENTRIES, (
        f"le registre a perdu des entrees : {n} < {MIN_ENTRIES} "
        f"(fichier d'entree supprime ou fusion accidentee ? cf #8542)"
    )


# --- Forme append-only `audits:` (#9399 volet a) ---


def test_audit_form_is_exclusive():
    """Une entree ne porte pas BOTH `last_audit` ET `audits` (source de verite unique).

    La migration (#9399) REMPLACE le singleton par la liste (l'ecrivain retire
    `last_audit:` quand il migre). Coexistence = main-edit corrompue ou migration
    a moitie faite -> le reader `_latest_audit` privilegierait `audits` et le
    `last_audit` residuel mentirait (SHAs potentiellement perimes).
    """
    both = [
        e.get("name", "?") for e in _entries()
        if "last_audit" in e and "audits" in e
    ]
    assert not both, f"entrees avec les deux formes d'audit : {both}"


def test_latest_audit_resolves_for_every_entry():
    """`_latest_audit` resout en un enregistrement a SHAs pour CHAQUE entree.

    Valide le reader polyvalent (#9399) sur le registre reel : quelle que soit la
    forme (legacy `last_audit` ou append-only `audits`), le dernier enregistrement
    porte des SHAs exploitables par le gate. Une entree dont le reader renvoie
    `{}` ou des SHAs absents -> DRIFT silencieux si la paire n'est pas checkee.
    """
    unresolved = []
    for entry in _entries():
        latest = _latest_audit(entry)
        if not isinstance(latest, dict) or not latest.get("python_sha") or not latest.get("csharp_sha"):
            unresolved.append(entry.get("name", "?"))
    assert not unresolved, f"entrees sans dernier audit resolu : {unresolved}"


def test_append_only_entries_well_formed():
    """Toute entree `audits:` est une liste non vide de dicts a SHAs valides.

    Un enregistrement d'audit (ancien ou nouveau) sans python_sha/csharp_sha est
    inutilisable par le gate (le reader renverrait None -> DRIFT bruyant, mais
    silencieux si la paire n'est pas checkee). On valide a l'inscription.
    """
    bad = []
    for entry in _entries():
        audits = entry.get("audits")
        if not isinstance(audits, list):
            continue
        for idx, rec in enumerate(audits):
            if not isinstance(rec, dict):
                bad.append(f"{entry.get('name', '?')}[{idx}] n'est pas un dict")
                continue
            for key in ("python_sha", "csharp_sha"):
                sha = rec.get(key)
                if not isinstance(sha, str) or not SHA_RE.match(sha):
                    bad.append(f"{entry.get('name', '?')}[{idx}].{key} = {sha!r}")
    assert not bad, f"entrees audits: mal formees : {bad}"


# --- Nouveaux tests : validation de la structure file-per-entry (#8542) ---


def test_one_file_per_pair_and_slug_roundtrip():
    """Chaque paire a son propre fichier `<slug(name)>.yaml`, contenant exactement
    cette paire (round-trip name -> slug -> fichier -> name)."""
    files = _pair_files()
    assert len(files) == len(_entries()), (
        f"{len(files)} fichiers pour {len(_entries())} entrees (un fichier par paire attendu)"
    )
    seen_files = set()
    for entry in _entries():
        name = entry.get("name", "?")
        expected = REGISTRY_DIR / f"{_slug(name)}.yaml"
        assert expected.exists(), f"fichier attendu manquant pour {name!r} : {expected.name}"
        seen_files.add(expected.name)
    assert len(seen_files) == len(files), "doublon de fichiers de paires"


def test_schema_file_present_and_excluded_from_pairs():
    """`_schema.yaml` est la documentation du repertoire (schema + provenance) :
    present, et correctement exclu du decompte de paires (parse a None/non-dict)."""
    assert SCHEMA.exists(), "_schema.yaml (doc schema + provenance) doit survivre (#8542)"
    data = yaml.safe_load(SCHEMA.read_text(encoding="utf-8"))
    assert not isinstance(data, dict), (
        "_schema.yaml doit etre de la documentation (comments), pas une paire ; "
        "sinon le loader `_`-skip doit etre durci."
    )
