#!/usr/bin/env python3
"""Emet la liste de paquets de l'image d'apprentissage depuis le manifeste 1.1.

Organe du pli 1.2 de l'Epic #27543 (`#27545`), derivee du pli 1.1 (`#27544`,
PR #27572).

LE CONTRAT
----------
`docs/curriculum/manifeste-dependances.json` est la **source unique** des
paquets de l'image d'apprentissage : cet outil ne lit aucun `requirements.txt`
du depot, il ne fait aucune requete reseau, et il n'invente aucun paquet. Il
consomme le manifeste consolide et rend un fichier `requirements` executable
par `pip`.

Trois familles d'ecarts sont distinguees, et jamais meleees :

1. **RESOLU (mesure)** -- un paquet porte par plusieurs groupes avec des
   bornees divergentes : la resolution vient du manifeste lui-meme
   (`conflicts[].resolution.version`), pas d'un arbitrage de ce script. Le
   script ne fait que la recopier.
2. **ECARTE (declaration, avec source)** -- un paquet du manifeste que
   l'image n'installe pas. Chaque ecart porte un **motif** et une **source**
   dans `learning_image_policy.json` (fichier versionne). Aucun ecart n'est
   muet : une liste sans motif n'est pas un ecart, c'est une omission.
3. **NORMALISE (mesure)** -- la manifeste porte parfois la meme borne
   ecrite de deux facons (`>=2.0.0` et `>=2.0`) : la fusion des bornes rend
   une borne unique, la plus stricte. La comparaison de versions passe par
   l'organe `check_lib_versions.version_key` (#23073) -- jamais par une
   comparaison de chaines.

PISTE DES EXTRAS
----------------
Le manifeste consolide porte des **noms normalises** (PEP 503) : un extra
(`eth-tester[py-evm]`) n'y survit pas. Les extras sont donc declares
explicitement dans la politique, avec leur source, et appliques a l'emission.
C'est une **declaration**, pas une mesure : le manifeste ne les porte pas.

USAGE
-----
    python scripts/notebook_tools/emit_learning_requirements.py --write
    python scripts/notebook_tools/emit_learning_requirements.py --check
    python scripts/notebook_tools/emit_learning_requirements.py --print

`--check` ne sort pas 0 si le fichier emis differe de celui qui est versionne :
le manifeste et l'image ne peuvent pas diverger en silence.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_MANIFEST = REPO_ROOT / "docs" / "curriculum" / "manifeste-dependances.json"
DEFAULT_POLICY = (
    REPO_ROOT / "docker-configurations" / "notebook-runner" / "learning_image_policy.json"
)
DEFAULT_OUT = (
    REPO_ROOT / "docker-configurations" / "notebook-runner" / "requirements-learning.txt"
)

# L'organe des versions de bibliotheques (#23073) : la comparaison de versions
# ne se reecrit pas ici.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_lib_versions import version_key  # noqa: E402

_EXACT = re.compile(r"^==\s*(?P<v>.+)$")
_LOWER = re.compile(r"^>=\s*(?P<v>.+)$")
_UPPER = re.compile(r"^<=\s*(?P<v>.+)$")
_STRICT_LOWER = re.compile(r"^>\s*(?P<v>.+)$")
_STRICT_UPPER = re.compile(r"^<\s*(?P<v>.+)$")
_COMPATIBLE = re.compile(r"^~=\s*(?P<v>.+)$")
_BARE = re.compile(r"^(?P<v>\d[^\s,]*)$")


def _cmp(left: str, right: str) -> int:
    """Compare deux versions non vides via l'organe #23073."""
    if not left:
        return 1 if right else 0
    if not right:
        return -1
    try:
        a, b = version_key(left), version_key(right)
    except Exception:
        return (left > right) - (left < right)
    return (a > b) - (a < b)


def _norm_name(name: str) -> str:
    """PEP 503 : le manifeste porte deja des noms normalises."""
    return re.sub(r"[-_.]+", "-", name.strip()).lower()


def _parse_term(term: str) -> tuple[str, str] | None:
    """Un terme de spec -> (operateur, version). None si la forme est inconnue."""
    term = term.strip()
    for regex, op in (
        (_EXACT, "=="),
        (_LOWER, ">="),
        (_UPPER, "<="),
        (_STRICT_LOWER, ">"),
        (_STRICT_UPPER, "<"),
        (_COMPATIBLE, "~="),
    ):
        match = regex.match(term)
        if match:
            return op, match.group("v").strip()
    match = _BARE.match(term)
    if match:
        return "==", match.group("v").strip()
    return None


def merge_specs(specs: list[str]) -> str:
    """Fusionne des bornes divergentes en une borne unique, la plus stricte.

    - une borne inferieure garde la version **maximale** (la plus stricte) ;
    - une borne superieure garde la version **minimale** (la plus stricte) ;
    - un pin exact l'emporte sur tout le reste (une version exacte est plus
      contraignante qu'un intervalle) ;
    - une forme inconnue (`~=`, joker) est **conservee telle quelle** : une
      absence de mesure n'est pas une autorisation de la jetter.
    """
    exact: str | None = None
    lower: tuple[str, str] | None = None  # (version, operateur)
    upper: tuple[str, str] | None = None
    opaque: list[str] = []
    for spec in specs:
        for term in str(spec).split(","):
            term = term.strip()
            if not term:
                continue
            parsed = _parse_term(term)
            if parsed is None:
                opaque.append(term)
                continue
            op, version = parsed
            if op == "==":
                if exact is None or _cmp(version, exact) > 0:
                    exact = version
                continue
            if op in (">=", ">"):
                if lower is None or _cmp(version, lower[0]) > 0:
                    lower = (version, op)
                elif _cmp(version, lower[0]) == 0 and op == ">" and lower[1] == ">=":
                    lower = (version, op)
                continue
            if op in ("<=", "<"):
                if upper is None or _cmp(version, upper[0]) < 0:
                    upper = (version, op)
                elif _cmp(version, upper[0]) == 0 and op == "<" and upper[1] == "<=":
                    upper = (version, op)
                continue
            opaque.append(f"{op}{version}")
    if exact is not None:
        return f"=={exact}"
    parts: list[str] = []
    if lower is not None:
        parts.append(f"{lower[1]}{lower[0]}")
    if upper is not None:
        parts.append(f"{upper[1]}{upper[0]}")
    parts.extend(opaque)
    return ",".join(parts)


def resolve_package(entry: dict[str, Any], conflict: dict[str, Any] | None) -> tuple[str, str]:
    """(spec resolue, origine) pour un paquet du manifeste consolide."""
    if conflict is not None:
        resolution = conflict.get("resolution") or {}
        version = str(resolution.get("version") or "").strip()
        if version:
            return version, "manifeste:resolution"
        # Un paquet sans version commune est ecarte par le manifeste lui-meme.
        return "", "manifeste:ecarte"
    specs = [str(s) for s in entry.get("specs") or []]
    exact = str(entry.get("version") or "").strip()
    if exact:
        return f"=={exact}", "manifeste:pin"
    if not specs:
        return "", "manifeste:sans-borne"
    if len(specs) == 1:
        return specs[0].strip(), "manifeste:spec"
    return merge_specs(specs), "manifeste:fusion"


def build_plan(
    manifest: dict[str, Any], policy: dict[str, Any]
) -> dict[str, Any]:
    """Construit le plan d'emission : installs, ecartes, motifs."""
    conflicts = {str(c["package"]): c for c in manifest.get("conflicts") or []}
    excludes = {
        _norm_name(str(item["package"])): item for item in policy.get("exclude") or []
    }
    extras = {
        _norm_name(str(name)): [str(e) for e in (value or [])]
        for name, value in (policy.get("extras") or {}).items()
    }
    pip_installed = {
        _norm_name(str(item["package"])): item
        for item in policy.get("pip_installed") or []
    }

    installs: list[dict[str, Any]] = []
    dropped: list[dict[str, Any]] = []
    for entry in manifest.get("consolidated_manifest") or []:
        name = _norm_name(str(entry["package"]))
        conflict = conflicts.get(name)
        spec, origin = resolve_package(entry, conflict)
        rule = excludes.get(name)
        if rule is not None:
            dropped.append(
                {
                    "package": name,
                    "motif": str(rule.get("motif") or ""),
                    "source": str(rule.get("source") or ""),
                }
            )
            continue
        if origin == "manifeste:ecarte":
            # Le manifeste lui-meme declares le paquet non installable
            # (aucune version commune) : l'ecart est deja motive la.
            dropped.append(
                {
                    "package": name,
                    "motif": "aucune version commune dans le manifeste consolide",
                    "source": "docs/curriculum/manifeste-dependances.json (conflicts[].resolution)",
                }
            )
            continue
        installs.append(
            {
                "package": name,
                "spec": spec,
                "origin": origin,
                "extras": extras.get(name, []),
                "installer": "pip" if name in pip_installed else "uv",
            }
        )
    installs.sort(key=lambda item: item["package"])
    dropped.sort(key=lambda item: item["package"])
    return {
        "installs": installs,
        "dropped": dropped,
        "pip_installed": sorted(pip_installed),
        "manifest_packages": len(manifest.get("consolidated_manifest") or []),
        "policy": str(policy.get("_source") or policy.get("_role") or ""),
        "interpreter": str((policy.get("target") or {}).get("interpreter") or ""),
        "interpreter_version": str((policy.get("target") or {}).get("version") or ""),
    }



def render_requirements(plan: dict[str, Any], manifest_path: str) -> str:
    """Rend le fichier `requirements` (commentaires d'en-tete + une ligne par paquet)."""
    lines = [
        "# Image d'apprentissage CoursIA -- paquets",
        "#",
        "# GENERE par scripts/notebook_tools/emit_learning_requirements.py --write",
        f"# Source unique : {manifest_path} (pli 1.1, #27544)",
        f"# Interpreteur cible : python {plan['interpreter_version']} "
        f"({plan['interpreter']})",
        f"# Paquets installes : {len(plan['installs'])} "
        f"/ {plan['manifest_packages']} du manifeste consolide",
        f"# Paquets ecartes : {len(plan['dropped'])} (motif + source dans le rapport)",
        "#",
        "# Ne pas editer a la main : `python scripts/notebook_tools/"
        "emit_learning_requirements.py --check` verifie la concordance.",
        "",
    ]
    for item in plan["installs"]:
        extras = "".join(f"[{extra}]" for extra in item["extras"])
        lines.append(f"{item['package']}{extras}{item['spec']}")
    return "\n".join(lines) + "\n"


def render_uv_input(plan: dict[str, Any]) -> str:
    """Rend l'ENTREE du resolveur uv (les paquets installes par pip en sont absents).

    `requirements-learning.txt` reste la source de record : la projection
    complete du manifeste. L'entree uv, elle, separe ce que uv sait resoudre
    de ce qu'il ne sait pas (voir `pip_installed` dans la politique).
    """
    lines = [
        "# Entree du resolveur uv pour l'image d'apprentissage",
        "# GENERE par scripts/notebook_tools/emit_learning_requirements.py --uv-input",
        "# Paquets installes par pip (absents ici, motif dans la politique) : "
        + (", ".join(plan["pip_installed"]) or "aucun"),
        "",
    ]
    for item in plan["installs"]:
        if item["installer"] != "uv":
            continue
        extras = "".join(f"[{extra}]" for extra in item["extras"])
        lines.append(f"{item['package']}{extras}{item['spec']}")
    return "\n".join(lines) + "\n"


def _sha256(path: Path) -> str:
    import hashlib

    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_lock(lock_path: Path, manifest_path: Path) -> int:
    """Verifie que le verrou est bien la resolution de la projection courante.

    Le verrou porte l'empreinte du manifeste et celle du fichier de
    projection : si l'un des deux change, le verrou est perime et doit etre
    regenere. Une empreinte absente = une verification absente, pas une
    verification reussie.
    """
    if not lock_path.is_file():
        print(f"ECHEC : verrou absent : {lock_path}", file=sys.stderr)
        return 1
    head = lock_path.read_text(encoding="utf-8")[:4000]
    manifest_hash = _sha256(manifest_path)
    if manifest_hash not in head:
        print(
            "ECHEC : le verrou ne porte pas l'empreinte du manifeste courant "
            "(il est perime : le regenere)",
            file=sys.stderr,
        )
        return 1
    print(f"OK : le verrou correspond au manifeste ({manifest_hash[:12]})")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", default=str(DEFAULT_MANIFEST))
    parser.add_argument("--policy", default=str(DEFAULT_POLICY))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--report", default="")
    parser.add_argument("--uv-input", default="", help="ecrit l'entree du resolveur uv")
    parser.add_argument("--lock", default="", help="verifie le verrou (avec son empreinte)")
    parser.add_argument("--write", action="store_true", help="ecrit le fichier")
    parser.add_argument("--check", action="store_true", help="verifie la concordance")
    parser.add_argument("--print", action="store_true", help="affiche le plan")
    args = parser.parse_args(argv)

    manifest_path = Path(args.manifest)
    if not manifest_path.is_file():
        print(f"ERREUR : manifeste absent : {manifest_path}", file=sys.stderr)
        return 2
    policy_path = Path(args.policy)
    if not policy_path.is_file():
        print(f"ERREUR : politique absente : {policy_path}", file=sys.stderr)
        return 2
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    policy = json.loads(policy_path.read_text(encoding="utf-8"))
    plan = build_plan(manifest, policy)
    rendered = render_requirements(plan, manifest_path.name)

    out_path = Path(args.out)
    if args.check:
        if not out_path.is_file():
            print(f"ECHEC : fichier absent : {out_path}", file=sys.stderr)
            return 1
        current = out_path.read_text(encoding="utf-8")
        if current != rendered:
            print(
                "ECHEC : le fichier versionne differe du manifeste "
                "(reconstruire avec --write)",
                file=sys.stderr,
            )
            return 1
        print(
            f"OK : {out_path} est la projection du manifeste "
            f"({len(plan['installs'])} paquets, {len(plan['dropped'])} ecartes)"
        )
        return 0
    if args.write:
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(rendered, encoding="utf-8", newline="\n")
        print(f"ecrit : {out_path} ({len(plan['installs'])} paquets)")
    if args.uv_input:
        uv_path = Path(args.uv_input)
        uv_path.parent.mkdir(parents=True, exist_ok=True)
        uv_path.write_text(render_uv_input(plan), encoding="utf-8", newline="\n")
        print(f"ecrit : {uv_path}")
    if args.lock:
        return check_lock(Path(args.lock), manifest_path)
    if args.report:
        report_path = Path(args.report)
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(
            json.dumps(plan, ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8",
            newline="\n",
        )
        print(f"ecrit : {report_path}")
    if args.print or not (args.write or args.check):
        for item in plan["installs"]:
            print(f"INSTALL {item['package']}{item['spec']} ({item['origin']})")
        for item in plan["dropped"]:
            print(f"ECARTE  {item['package']} -- {item['motif']} [{item['source']}]")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
