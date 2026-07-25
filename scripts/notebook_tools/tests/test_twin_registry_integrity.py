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
REQUIRED_KEYS = {"name", "family", "python", "csharp", "parity_level", "last_audit"}


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
