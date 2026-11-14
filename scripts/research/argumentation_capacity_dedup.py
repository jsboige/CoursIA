"""Deduplication et exposition licence des capacites de la plateforme Argumentation.

Grain #16457 (Axe 2, distillation-outil), sous-grain de #26422. Portee par #26423
(le catalogue en prose). Ce script rend la partie du catalogue *calculable* et
*re-verifiable*, sans re-faire le catalogue :

1. `check`  : controle de derive -- chaque chemin du manifeste
   (`docs/reference/argumentation-capacities.json`) doit exister dans l'arbre du
   repo etudiant. Un chemin absent = le catalogue a derivé de la realite = exit 1.
   C'est ce controle qui avait revele les 3 chemins faux du catalogue v1.

2. `dedup`  : calcule, a partir du manifeste + de l'arbre,
   (a) les capacites *vendorisees* (implantees a la fois dans la plateforme
       `argumentation_analysis/` et dans un projet etudiant numerote) ;
   (b) les capacites *ecarteles* (plateforme s'etendant sur >= 3 sous-arbres) ;
   (c) les capacites *multi-origines* (>= 2 projets etudiants) ;
   (d) les *modules dupliques* (un meme basename .py present dans >= 3 dossiers) ;
   (e) l'*exposition licence* des binaires vendorises (`libs/` + `ext_tools/`),
       en recomptant pour chacun la presence d'un fichier de licence a cote.

Le resultat est un rapport reproductible (JSON + Markdown), pas une prose a la main.

Regles appliquees :
- le manifeste est une source unique *curiee* ; l'arbre est *mesure* (fixture
  engage, ou `--tree` vers un snapshot plus frais) ;
- les licences des binaires sont *attribuees* (champ `license_attributed`) ;
  la seule fait mesurable est `license_file_present`, recomptee a chaque passage ;
- rien n'est invente : une capacite sans implémentation mesurée n'apparait pas.

Usage :
  python scripts/research/argumentation_capacity_dedup.py check
  python scripts/research/argumentation_capacity_dedup.py dedup \
      --out docs/reference/argumentation-capacites-dedup.md
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import defaultdict
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_MANIFEST = REPO_ROOT / "docs" / "reference" / "argumentation-capacities.json"
DEFAULT_TREE = REPO_ROOT / "scripts" / "tests" / "fixtures" / "argumentation_student_tree.json"
LICENSE_BASENAMES = {"license", "license.md", "license.txt", "license.mit",
                     "license.gpl", "license.gplv3", "license.lgpl", "licence", "licence.txt"}


def load_tree(path: Path) -> set[str]:
    data = json.loads(path.read_text(encoding="utf-8"))
    return {t["path"] for t in data.get("tree", []) if t.get("type") == "blob"}


def load_manifest(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def manifest_paths(manifest: dict) -> list[tuple[str, str]]:
    """Toutes les chemins absolus du manifeste, avec leur provenance (pour le rapport)."""
    out: list[tuple[str, str]] = []
    for cap in manifest["capabilities"]:
        for p in cap.get("platform", []):
            out.append((p, f"capacite {cap['id']}"))
        for proj, files in cap.get("projects", {}).items():
            for p in files:
                out.append((p, f"capacite {cap['id']} / {proj}"))
    for b in manifest.get("vendored_binaries", []):
        out.append((b["path"], "binaire vendorise"))
    return out


def cmd_check(manifest: dict, tree: set[str]) -> int:
    """Contrôle de dérive : tout chemin du manifeste doit exister dans l'arbre."""
    missing = sorted({p for p, _ in manifest_paths(manifest) if p not in tree})
    # les dossiers projet doivent contenir au moins un fichier
    for d in manifest.get("project_dirs", []):
        if not any(p.startswith(d + "/") for p in tree):
            missing.append(d + "/  (dossier projet sans fichier)")
    if missing:
        print("DERIVE : le manifeste cite des chemins absents de l'arbre :")
        for m in missing:
            print(f"  - {m}")
        return 1
    n = len(manifest_paths(manifest))
    print(f"OK : {n} chemins du manifeste presents dans l'arbre "
          f"({len(manifest['capabilities'])} capacites, "
          f"{len(manifest.get('vendored_binaries', []))} binaires).")
    return 0


def license_file_present(path: str, tree: set[str]) -> bool:
    d = path.rsplit("/", 1)[0]
    for cand in (d + "/LICENSE", d + "/LICENSE.md", d + "/LICENSE.txt",
                 d + "/LICENCE", d + "/LICENCE.txt", d + "/README-LICENSE.md"):
        if cand in tree:
            return True
    return False


def module_duplicates(tree: set[str], min_copies: int = 3) -> dict[str, list[str]]:
    """Un basename .py present dans >= min_copies dossiers distincts."""
    by_base: dict[str, set[str]] = defaultdict(set)
    for p in tree:
        if p.endswith(".py") and p.rsplit("/", 1)[-1] not in ("__init__.py", "conftest.py"):
            by_base[p.rsplit("/", 1)[-1]].add(p.rsplit("/", 1)[0])
    return {b: sorted(ds) for b, ds in by_base.items() if len(ds) >= min_copies}


def platform_subtrees(paths: list[str]) -> list[str]:
    """Sous-arbres plateforme distincts (2 premiers segments) couverts par une capacite."""
    return sorted({"/".join(p.split("/")[:2]) for p in paths if p})


def cmd_dedup(manifest: dict, tree: set[str], out_md: Path) -> int:
    caps = manifest["capabilities"]
    report: dict = {
        "source": manifest.get("source", {}),
        "vendorisees": [], "ecarteles": [], "multi_origines": [],
        "modules_dupliques": module_duplicates(tree),
        "exposition_licence": {},
    }

    for cap in caps:
        plat = cap.get("platform", [])
        projs = cap.get("projects", {})
        origins = [k for k, v in projs.items() if v]
        subtrees = platform_subtrees(plat)
        entry = {"id": cap["id"], "label": cap["label"], "portability": cap.get("portability"),
                 "platform_subtrees": subtrees, "project_origins": origins}
        if plat and origins:
            report["vendorisees"].append(entry)
        if len(subtrees) >= 3:
            report["ecarteles"].append(entry)
        if len(origins) >= 2:
            report["multi_origines"].append(entry)

    # exposition licence : recompte license_file_present + total par famille
    exp: dict[str, dict] = defaultdict(lambda: {"count": 0, "with_license": 0, "paths": []})
    for b in manifest.get("vendored_binaries", []):
        fam = b.get("family", "?")
        has = license_file_present(b["path"], tree)
        b["license_file_present"] = has
        exp[fam]["count"] += 1
        exp[fam]["with_license"] += 1 if has else 0
        exp[fam]["paths"].append(b["path"])
    report["exposition_licence"] = dict(exp)

    # ecrire le rapport JSON + Markdown
    out_json = out_md.with_suffix(".json")
    out_json.write_text(json.dumps(report, ensure_ascii=False, indent=2), encoding="utf-8")

    lines = [
        "# Argumentation EPITA 2025 — deduplication et exposition licence",
        "",
        f"**Mesuré** sur `{manifest['source'].get('repo','')}` "
        f"@ `{manifest['source'].get('ref','')[:12]}` "
        f"({manifest['source'].get('measured_at','')}) via l'organe "
        "`scripts/research/argumentation_capacity_dedup.py dedup`.",
        "",
        "Ce rapport est **reproductible** : il est calculé depuis le manifeste de capacités "
        "(`docs/reference/argumentation-capacities.json`) croisé à l'arbre réel du repo étudiant.",
        "",
        f"## 1. Capacités vendorisées ({len(report['vendorisees'])})",
        "",
        "Implantées à la fois dans la plateforme `argumentation_analysis/` **et** dans un projet étudiant numéroté — le projet est re-copié, pas appelé.",
        "",
        "| Capacité | Origine(s) projet | Sous-arbres plateforme |",
        "|---|---|---|",
    ]
    for e in report["vendorisees"]:
        lines.append(f"| {e['label']} | {', '.join(e['project_origins'])} | {', '.join(e['platform_subtrees'])} |")
    lines += ["", f"## 2. Capacités écartelées ({len(report['ecarteles'])})", "",
              "Une même capacité s'étend sur ≥ 3 sous-arbres de la plateforme (coût d'extraction).", ""]
    for e in report["ecarteles"]:
        lines.append(f"- **{e['label']}** — {len(e['platform_subtrees'])} sous-arbres : {', '.join(e['platform_subtrees'])}")
    lines += ["", f"## 3. Capacités multi-origines ({len(report['multi_origines'])})", "",
              "Produites par ≥ 2 projets étudiants (candidats d'extraction en boîte à outils partagée).", ""]
    for e in report["multi_origines"]:
        lines.append(f"- **{e['label']}** — {', '.join(e['project_origins'])}")
    lines += ["", f"## 4. Modules dupliqués ({len(report['modules_dupliques'])})", "",
              "Un même fichier `.py` présent dans ≥ 3 dossiers (hors `__init__.py`).", ""]
    for b, dirs in sorted(report["modules_dupliques"].items(), key=lambda kv: -len(kv[1])):
        lines.append(f"- `{b}` × {len(dirs)} : " + ", ".join(f"`{d}/`" for d in dirs))
    lines += ["", "## 5. Exposition licence des binaires vendorisés", "",
              "Binaires PE/JAR vendorisés dans le repo public. `licence` = **attribuée** (pas mesurée) ; "
              "`fichier de licence à côté` = **mesuré** à chaque passage.", ""]
    lines += ["| Famille | # binaires | avec fichier de licence |", "|---|---|---|"]
    for fam, v in sorted(report["exposition_licence"].items()):
        lines.append(f"| {fam} | {v['count']} | {v['with_license']} |")
    tot = sum(v["count"] for v in report["exposition_licence"].values())
    totlic = sum(v["with_license"] for v in report["exposition_licence"].values())
    lines += ["", f"**{tot} binaires vendorisés, dont {totlic} accompagnés d'un fichier de licence.**", ""]
    out_md.write_text("\n".join(lines), encoding="utf-8")
    print(f"rapport   : {out_md}")
    print(f"           {out_json}")
    print(f"vendorisees={len(report['vendorisees'])} ecarteles={len(report['ecarteles'])} "
          f"multi_origines={len(report['multi_origines'])} "
          f"modules_dup={len(report['modules_dupliques'])} binaires={tot} (licence={totlic})")
    return 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("command", choices=["check", "dedup"])
    ap.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    ap.add_argument("--tree", type=Path, default=DEFAULT_TREE)
    ap.add_argument("--out", type=Path,
                    default=REPO_ROOT / "docs" / "reference" / "argumentation-capacites-dedup.md")
    args = ap.parse_args(argv)
    manifest = load_manifest(args.manifest)
    tree = load_tree(args.tree)
    if args.command == "check":
        return cmd_check(manifest, tree)
    return cmd_dedup(manifest, tree, args.out)


if __name__ == "__main__":
    sys.exit(main())
