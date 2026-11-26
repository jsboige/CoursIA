#!/usr/bin/env python3
"""Certifie la navigation des variantes d'une famille contre le registre des jumeaux.

Pourquoi cet outil existe
-------------------------
L'EPIC #28763 (« cohérence multilangage des carnets ») demande que la navigation
annonce, avant ouverture, les variantes d'une même notion, avec le **type de
correspondance**, la **différence utile**, le **noyau** et les **liens** — et
qu'elle « n'annonce pas d'équivalence non démontrée ».

Le registre des jumeaux (`scripts/notebook_tools/twin_pairs.d/`) porte déjà la
preuve : pour chaque paire, `parity_level`, `bridge_verdict` et un enregistrement
d'audit. Mais la navigation (README de série, `index.qmd`, en-tête d'un carnet)
est de la **prose** : rien ne garantissait qu'une paire annoncée y soit
attestée, ni que le type de correspondance annoncé corresponde à l'attestation.
Un lien mort ou une équivalence affirmée sans preuve passaient inaperçus.

Ce tool relie les deux : il lit le registre, il lit les surfaces de navigation,
et il signale l'écart.

Les contrôles
-------------
1. `BROKEN_LINK`      — la cible annoncée n'existe pas sur le disque.
2. `UNATTESTED_PAIR`  — la navigation annonce une paire que le registre n'atteste
                        pas (équivalence annoncée sans démonstration).
3. `TYPE_MISMATCH`    — le type de correspondance annoncé diffère de celui que
                        l'attestation du registre permet de déduire.
4. `KERNEL_MISMATCH`  — le noyau annoncé diffère du kernelspec réel du carnet.
5. `MISSING_VARIANT`  — une notion existe d'un seul côté de la famille (variante
                        absente) : elle ne peut pas se dire « équivalence vérifiée ».

Le type de correspondance est **dérivé** du registre, jamais déclaré à la main :

    deux côtés + parity_level semantic/native-both + bridge_verdict SOTA-OK
        + un enregistrement d'audit  ->  « équivalence vérifiée »
    deux côtés + parity_level surface ->  « même progression »
    un seul côté                     ->  « complément »
    sinon                            ->  indéterminé (l'organe le signale)

Modes
-----
    python check_variant_navigation.py                 # surfaces par defaut
    python check_variant_navigation.py --json          # sortie machine
    python check_variant_navigation.py --check         # exit 1 si finding bloquant
    python check_variant_navigation.py --surface <f>   # une surface de plus
    python check_variant_navigation.py --all-families  # toutes les familles du registre
    python check_variant_navigation.py --list-families

Read-only : ne modifie aucun carnet, aucun registre, aucune documentation.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import unicodedata
from pathlib import Path

try:  # PyYAML est requis par le registre ; on l'importe via le module voisin.
    import yaml
except ImportError:  # pragma: no cover
    yaml = None

REPO_ROOT_DEFAULT = Path(__file__).resolve().parents[2]
REGISTRY_DEFAULT = "scripts/notebook_tools/twin_pairs.d"

# Familles de navigation couvertes par defaut : les deux familles de variantes
# de la serie Probas (inference probabiliste + theorie de la decision).
DEFAULT_FAMILIES = ("Probas/Infer.NET-PyMC", "Probas/DecisionTheory-Infer.NET-PyMC")

# Surfaces de navigation lues par defaut (relatives au depot).
DEFAULT_SURFACES = (
    "MyIA.AI.Notebooks/Probas/README.md",
    "MyIA.AI.Notebooks/Probas/index.qmd",
    "MyIA.AI.Notebooks/Probas/Infer/README.md",
    "MyIA.AI.Notebooks/Probas/PyMC/README.md",
    "MyIA.AI.Notebooks/Probas/DecisionTheory/README.md",
    "MyIA.AI.Notebooks/Probas/DecisionTheory/DecInfer/README.md",
    "MyIA.AI.Notebooks/Probas/DecisionTheory/DecPyMC/README.md",
)

SIDE_KEYS = ("python", "csharp", "rust")

# En-tete canonique d'une variante, dans une cellule markdown de carnet :
#   **Variante jumelle** : [Infer-01-Setup](../Infer/Infer-01-Setup.ipynb)
#   — correspondance : équivalence verifiee · noyau : `python3` (PyMC)
HEADER_RE = re.compile(
    r"^\*\*Variante jumelle\*\*\s*:\s*\[(?P<label>[^\]]+)\]\((?P<path>[^)]+)\)"
    r"(?P<rest>.*)$",
    re.MULTILINE,
)
CORRESPONDENCE_RE = re.compile(r"correspondance\s*:\s*(?P<value>[^·—\n]+)", re.IGNORECASE)
KERNEL_RE = re.compile(r"noyau\s*:\s*`(?P<value>[^`]+)`", re.IGNORECASE)

MD_LINK_RE = re.compile(r"\[(?P<label>[^\]]+)\]\((?P<target>[^)]+)\)")

TYPE_EQUIVALENCE = "équivalence vérifiée"
TYPE_PROGRESSION = "même progression"
TYPE_COMPLEMENT = "complément"


def strip_accents(text: str) -> str:
    return "".join(
        ch for ch in unicodedata.normalize("NFKD", text) if not unicodedata.combining(ch)
    )


def norm(text: str) -> str:
    return " ".join(strip_accents(text or "").lower().split())


# ---------------------------------------------------------------------------
# Registre
# ---------------------------------------------------------------------------


def load_registry(path: Path) -> list:
    """Charge le registre file-per-entry (meme contrat que check_twin_parity.py)."""
    if yaml is None:
        raise SystemExit("Erreur : PyYAML requis (pip install pyyaml).")
    if not path.exists():
        raise SystemExit(f"Erreur : registre introuvable : {path}")
    entries: list = []
    if path.is_dir():
        for f in sorted(path.glob("*.yaml")):
            if f.name.startswith("_"):
                continue
            data = yaml.safe_load(f.read_text(encoding="utf-8"))
            items = data if isinstance(data, list) else [data]
            for item in items:
                if not isinstance(item, dict):
                    continue
                item = dict(item)
                audits = _load_audits_from_files(path, f.stem)
                if audits:
                    item["audits"] = audits
                entries.append(item)
        return entries
    data = yaml.safe_load(path.read_text(encoding="utf-8"))
    if not isinstance(data, list):
        raise SystemExit("Erreur : le registre (fichier) doit etre une liste de paires.")
    return data


def _load_audits_from_files(registry_dir: Path, slug: str) -> list:
    """Reconstruit `audits:` depuis le sous-repertoire `<slug>/` (cf #14911)."""
    d = registry_dir / slug
    if not d.is_dir():
        return []
    audits = []
    for f in sorted(d.glob("*.yaml")):
        data = yaml.safe_load(f.read_text(encoding="utf-8"))
        if isinstance(data, dict):
            audits.append(data)
        elif isinstance(data, list):
            audits.extend(x for x in data if isinstance(x, dict))
    return audits


def has_audit(entry: dict) -> bool:
    return bool(entry.get("audits") or entry.get("last_audit"))


def sides_of(entry: dict) -> list:
    return [entry[k] for k in SIDE_KEYS if entry.get(k)]


def derive_correspondence(entry: dict) -> str | None:
    """Type de correspondance **deduit** de l'attestation du registre."""
    sides = sides_of(entry)
    if len(sides) < 2:
        return TYPE_COMPLEMENT
    level = entry.get("parity_level")
    if level == "surface":
        return TYPE_PROGRESSION
    if level in ("semantic", "native-both") and entry.get("bridge_verdict") == "SOTA-OK":
        if has_audit(entry):
            return TYPE_EQUIVALENCE
    return None


# ---------------------------------------------------------------------------
# Lecture des surfaces
# ---------------------------------------------------------------------------


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def parent_dir(path: str) -> str:
    """Repertoire parent d'un chemin, normalise en slashes (comparaison portable)."""
    return str(Path(path).parent).replace("\\", "/")


def resolve_target(base_dir: Path, target: str, repo_root: Path) -> str | None:
    """Resout un lien relatif vers un chemin repo-relative, ou None si non pertinent."""
    target = (target or "").strip()
    if not target or target.startswith(("http://", "https://", "mailto:", "#")):
        return None
    target = target.split("#", 1)[0]
    if not target:
        return None
    candidate = (base_dir / target).resolve()
    try:
        rel = candidate.relative_to(Path(repo_root).resolve())
    except ValueError:
        return None
    return rel.as_posix()


def scan_surface_pairs(surface: Path, dir_pairs: dict, repo_root: Path) -> list:
    """Paires de carnets annoncees par une surface (README / index.qmd).

    Une ligne de tableau qui lie **la meme notion** dans les deux repertoires
    d'une famille de variantes est une **annonce de paire** : elle doit etre
    attestee au registre.

    La correspondance se fait par **cle de notion** (le numero et le libelle
    apres le prefixe de famille), pas par simple proximite dans la ligne : une
    ligne lie souvent une notion *et* son extension (`01` et `01b`), qui ne
    sont pas deux variantes du meme carnet.
    """
    text = read_text(surface)
    base_dir = surface.parent
    claims = []
    for lineno, line in enumerate(text.splitlines(), start=1):
        if "|" not in line:
            continue
        targets = []
        for m in MD_LINK_RE.finditer(line):
            resolved = resolve_target(base_dir, m.group("target"), repo_root)
            if resolved and resolved.endswith(".ipynb"):
                targets.append(resolved)
        if len(targets) < 2:
            continue
        for dirs in dir_pairs.values():
            dpy, dcs = dirs
            left = [t for t in targets if parent_dir(t) == dpy]
            right = [t for t in targets if parent_dir(t) == dcs]
            for a in left:
                for b in right:
                    if notion_key(a, dirs) and notion_key(a, dirs) == notion_key(b, dirs):
                        claims.append(
                            {
                                "surface": surface.as_posix(),
                                "line": lineno,
                                "a": a,
                                "b": b,
                            }
                        )
    return claims


def scan_notebook_headers(notebook: Path) -> list:
    """En-tetes « Variante jumelle » d'un carnet."""
    try:
        nb = json.loads(read_text(notebook))
    except (json.JSONDecodeError, UnicodeDecodeError):
        return []
    headers = []
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "markdown":
            continue
        source = "".join(cell.get("source", []))
        for m in HEADER_RE.finditer(source):
            rest = m.group("rest")
            corr = CORRESPONDENCE_RE.search(rest)
            kern = KERNEL_RE.search(rest)
            headers.append(
                {
                    "notebook": notebook.as_posix(),
                    "label": m.group("label"),
                    "target": m.group("path"),
                    "correspondence": corr.group("value").strip() if corr else None,
                    "kernel": kern.group("value").strip() if kern else None,
                }
            )
    return headers


def notebook_kernel(notebook: Path) -> str | None:
    try:
        nb = json.loads(read_text(notebook))
    except (json.JSONDecodeError, UnicodeDecodeError):
        return None
    meta = nb.get("metadata", {})
    ks = (meta.get("kernelspec") or {}).get("name")
    if ks:
        return ks
    return (meta.get("language_info") or {}).get("name")


def notion_key(path: str, dirs: tuple) -> str | None:
    """Cle de notion = nom du fichier sans le prefixe de famille.

    `Infer-01-Setup.ipynb` et `PyMC-01-Setup.ipynb` partagent la cle
    `01-Setup` ; `DecInfer-01-Utility-Foundations` et
    `DecPyMC-01-Utility-Foundations` partagent `01-Utility-Foundations`.
    """
    for d in dirs:
        prefix = d.rsplit("/", 1)[-1]
        if path.startswith(d + "/"):
            name = path[len(d) + 1 :]
            for sep in ("-", "_"):
                if name.startswith(prefix + sep):
                    return name[len(prefix) + 1 :]
            return name
    return None


# ---------------------------------------------------------------------------
# Verification
# ---------------------------------------------------------------------------


def verify(repo_root: Path, registry_path: Path, families, surfaces, extra_surfaces):
    entries = load_registry(registry_path)
    fam_entries = [e for e in entries if e.get("family") in families]

    # Index : ensemble de deux cotes -> entree attestee.
    attested = {}
    dir_pairs = {}
    for e in fam_entries:
        sides = sides_of(e)
        if len(sides) >= 2:
            attested[frozenset(sides[:2])] = e
            dpy = str(Path(e["python"]).parent).replace("\\", "/")
            dcs = str(Path(e["csharp"]).parent).replace("\\", "/")
            dir_pairs[frozenset((dpy, dcs))] = (dpy, dcs)

    findings = []
    stats = {"pairs_announced": 0, "pairs_attested": 0, "headers": 0}

    # --- Surface A : en-tetes de variante dans les carnets -------------------
    notebook_dirs = sorted({d for pair in dir_pairs.values() for d in pair})
    for d in notebook_dirs:
        abs_dir = repo_root / d
        if not abs_dir.is_dir():
            continue
        for nb_path in sorted(abs_dir.glob("*.ipynb")):
            rel_nb = nb_path.relative_to(repo_root).as_posix()
            for header in scan_notebook_headers(nb_path):
                stats["headers"] += 1
                target = resolve_target(nb_path.parent, header["target"], repo_root)
                if target is None or not (repo_root / target).exists():
                    findings.append(
                        {
                            "kind": "BROKEN_LINK",
                            "surface": rel_nb,
                            "detail": f"cible inexistante : {header['target']}",
                        }
                    )
                    continue
                pair = frozenset((rel_nb, target))
                entry = attested.get(pair)
                if entry is None:
                    findings.append(
                        {
                            "kind": "UNATTESTED_PAIR",
                            "surface": rel_nb,
                            "detail": f"{rel_nb} <-> {target} : aucune entree de registre",
                        }
                    )
                    continue
                stats["pairs_attested"] += 1
                derived = derive_correspondence(entry)
                declared = header.get("correspondence")
                if declared is None:
                    findings.append(
                        {
                            "kind": "TYPE_MISMATCH",
                            "surface": rel_nb,
                            "detail": "type de correspondance absent de l'en-tete",
                        }
                    )
                elif norm(declared) != norm(derived or ""):
                    findings.append(
                        {
                            "kind": "TYPE_MISMATCH",
                            "surface": rel_nb,
                            "detail": (
                                f"annonce « {declared} » ; registre "
                                f"« {entry.get('name')} » -> « {derived or 'indetermine'} »"
                            ),
                        }
                    )
                kernel = notebook_kernel(nb_path)
                declared_kernel = header.get("kernel")
                if declared_kernel and kernel and declared_kernel != kernel:
                    findings.append(
                        {
                            "kind": "KERNEL_MISMATCH",
                            "surface": rel_nb,
                            "detail": f"annonce « {declared_kernel} » ; kernelspec « {kernel} »",
                        }
                    )

    # --- Surface B : tables de navigation des series ------------------------
    all_surfaces = list(surfaces) + list(extra_surfaces)
    for surf_rel in all_surfaces:
        surf = repo_root / surf_rel
        if not surf.exists():
            findings.append(
                {"kind": "BROKEN_LINK", "surface": surf_rel, "detail": "surface absente"}
            )
            continue
        for claim in scan_surface_pairs(surf, dir_pairs, repo_root):
            a, b = claim["a"], claim["b"]
            stats["pairs_announced"] += 1
            if frozenset((a, b)) in attested:
                stats["pairs_attested"] += 1
            else:
                findings.append(
                    {
                        "kind": "UNATTESTED_PAIR",
                        "surface": f"{claim['surface']}:{claim['line']}",
                        "detail": f"{a} <-> {b} : aucune entree de registre",
                    }
                )

    # --- Variantes absentes (une notion d'un seul cote) ---------------------
    missing = []
    for dirs in dir_pairs.values():
        dpy, dcs = dirs
        keys_py = set()
        keys_cs = set()
        for d, acc in ((dpy, keys_py), (dcs, keys_cs)):
            abs_dir = repo_root / d
            if not abs_dir.is_dir():
                continue
            for nb_path in sorted(abs_dir.glob("*.ipynb")):
                key = notion_key(nb_path.relative_to(repo_root).as_posix(), dirs)
                if key:
                    acc.add(key)
        for key in sorted(keys_py - keys_cs):
            missing.append(f"{dpy} : {key} sans pendant cote {dcs}")
        for key in sorted(keys_cs - keys_py):
            missing.append(f"{dcs} : {key} sans pendant cote {dpy}")
    for item in missing:
        findings.append({"kind": "MISSING_VARIANT", "surface": "famille", "detail": item})

    return findings, stats, fam_entries


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--repo-root", default=str(REPO_ROOT_DEFAULT))
    ap.add_argument("--registry", default=REGISTRY_DEFAULT)
    ap.add_argument("--family", action="append", default=[])
    ap.add_argument("--surface", action="append", default=[])
    ap.add_argument("--all-families", action="store_true")
    ap.add_argument("--list-families", action="store_true")
    ap.add_argument("--check", action="store_true", help="exit 1 si finding bloquant")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args(argv)

    repo_root = Path(args.repo_root).resolve()
    registry_path = Path(args.registry)
    if not registry_path.is_absolute():
        registry_path = repo_root / registry_path

    if args.list_families:
        entries = load_registry(registry_path)
        for fam in sorted({str(e.get("family")) for e in entries}):
            print(fam)
        return 0

    families = tuple(args.family) if args.family else DEFAULT_FAMILIES
    if args.all_families:
        entries = load_registry(registry_path)
        families = tuple(sorted({str(e.get("family")) for e in entries}))

    findings, stats, fam_entries = verify(
        repo_root, registry_path, families, DEFAULT_SURFACES, args.surface
    )

    blocking = [f for f in findings if f["kind"] != "MISSING_VARIANT"]
    if args.json:
        print(
            json.dumps(
                {
                    "families": list(families),
                    "entries": len(fam_entries),
                    "stats": stats,
                    "findings": findings,
                    "blocking": len(blocking),
                },
                ensure_ascii=False,
                indent=2,
            )
        )
    else:
        print(f"familles : {', '.join(families)}")
        print(f"entrees de registre : {len(fam_entries)}")
        print(
            "paires annoncees : {pairs_announced} | attestees : {pairs_attested} | "
            "en-tetes de variante : {headers}".format(**stats)
        )
        for f in findings:
            print(f"[{f['kind']}] {f['surface']} — {f['detail']}")
        if not findings:
            print("OK — aucune anomalie de navigation des variantes.")
    if args.check and blocking:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
