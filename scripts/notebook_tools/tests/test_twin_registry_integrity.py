"""Integrite structurelle du registre twin_pairs.yaml (#8057).

Ces tests sont le filet de securite du merge `union` declare sur le registre
dans `.gitattributes`. Le registre est une liste append-only : les lanes y
ajoutent des entrees disjointes en fin de fichier, ce qui produisait un conflit
serie systematique (une seule PR mergeable a la fois -- 3e recurrence : #8415
consolidation, #8476 re-apply, #8499 recovery tranche).

`merge=union` concatene les deux cotes d'un hunk en conflit au lieu de poser des
marqueurs. Pour des appends disjoints c'est exactement le resultat voulu. Le
seul mode de defaillance est le rebaselinage concurrent de la *meme* entree :
l'union produirait alors deux lignes `python_sha:` dans un meme bloc, et
`yaml.safe_load` retient silencieusement la derniere. Ces tests transforment
cette corruption silencieuse en echec CI bruyant.
"""

from __future__ import annotations

import re
from pathlib import Path

import pytest

yaml = pytest.importorskip("yaml")

REGISTRY = Path(__file__).resolve().parents[1] / "twin_pairs.yaml"
SHA_RE = re.compile(r"^[0-9a-f]{40}$")
# Cle minimale qu'une entree doit posseder (sous-ensemble). Un merge union mal
# tombe peut aussi INJECTER des cles etrangeres (interlacement ligne a ligne) :
# ALLOWED_KEYS (ensemble exact) couvre ce second mode (cf test ci-dessous, #8542).
REQUIRED_KEYS = {"name", "family", "python", "csharp", "parity_level", "last_audit"}
ALLOWED_KEYS = {
    "name", "family", "python", "csharp", "parity_level",
    "last_audit", "known_differences",
}
# Plancher d'entrees (2026-07-25, 98 paires sur origin/main). Un merge union qui
# detruit/absorbe silencieusement une entree (interlacement) fait chuter le
# compte sous ce plancher -> echec CI bruyant. A LEVER au fur et a mesure que le
# registre grossit (jamais baisser sans investiguer une perte silencieuse, #8542).
MIN_ENTRIES = 98


def _entries() -> list:
    data = yaml.safe_load(REGISTRY.read_text(encoding="utf-8"))
    assert isinstance(data, list), "le registre doit etre une liste de paires"
    return data


class _DupKeyLoader(yaml.SafeLoader):
    """SafeLoader qui refuse les cles dupliquees au lieu de garder la derniere.

    C'est la signature exacte d'un merge union mal tombe (deux rebaselines
    concurrents de la meme entree). PyYAML l'accepte silencieusement par defaut.
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


def test_registry_parses_as_list():
    assert len(_entries()) > 0


def test_no_duplicate_keys_anywhere():
    """Mode de defaillance n1 du merge union : `python_sha` deux fois dans une entree."""
    yaml.load(REGISTRY.read_text(encoding="utf-8"), Loader=_DupKeyLoader)


def test_no_duplicate_pair_names():
    """Mode de defaillance n2 : la meme paire enregistree par deux lanes."""
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


def test_audit_shas_are_git_blob_shas():
    """Les shas sont des blob SHA git (40 hex), pas des hashes de contenu."""
    bad = []
    for entry in _entries():
        audit = entry.get("last_audit") or {}
        for key in ("python_sha", "csharp_sha"):
            sha = audit.get(key)
            if not isinstance(sha, str) or not SHA_RE.match(sha):
                bad.append(f"{entry.get('name', '?')}.{key} = {sha!r}")
    assert not bad, f"shas invalides : {bad}"


def test_registered_notebooks_exist_on_disk():
    repo_root = REGISTRY.resolve().parents[2]
    missing = [
        f"{e.get('name', '?')} -> {p}"
        for e in _entries()
        for p in (e.get("python"), e.get("csharp"))
        if p and not (repo_root / p).exists()
    ]
    assert not missing, f"notebooks introuvables : {missing}"


def test_entries_have_exact_key_set():
    """Mode de defaillance n3 du merge union (#8542, Constat 2) : l'interlacement
    ligne a ligne peut INJECTER des cles etrangeres dans une entree (les champs
    d'une paire appendee se retrouvent meles au bloc d'une autre). Le YAML peut
    encore parser, les cles requises peuvent encore etre presentes, aucune cle
    n'est dupliquee -- mais la structure est corrompue. Cet assert verifie que
    chaque entree possede EXACTEMENT l'ensemble de cles canonique (ni plus, ni
    moins), ce qu'aucun des tests precedents ne couvrait.
    """
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
    assert not bad, "entrees au schema corrompu (interlacement merge union ?) : " + "; ".join(bad)


def test_entry_count_floor():
    """Mode de defaillance n4 du merge union (#8542, Constat 2) : l'interlacement
    peut FUSIONNER ou ABSORBER silencieusement une entree entiere dans le bloc
    d'une autre, faisant chuter le compte total sans declencher d'erreur de parse
    ni de cle dupliquee. Le plancher MIN_ENTRIES (leve periodiquement a mesure que
    le registre grossit) transforme cette perte silencieuse en echec CI bruyant.
    """
    n = len(_entries())
    assert n >= MIN_ENTRIES, (
        f"le registre a perdu des entrees : {n} < {MIN_ENTRIES} "
        f"(interlacement merge union ou suppression accidentee ? cf #8542)"
    )
