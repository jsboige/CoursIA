#!/usr/bin/env python3
"""Mesure de l'organe de distillation #19741 — dépôts lanyonai (solveurs physiques vérifiés).

Contexte : l'issue #19741 (chaîne de transcription-distillation Gorard / Lanyon AI)
demande, en étape 3, une mesure firsthand des dépôts `lanyonai` — licences,
déclaration de toolchain Lean/Mathlib, ce que la plus petite preuve établit
exactement, et si le code C correspondant se compile et s'exécute. Cet organe rend
la mesure re-exécutable à la demande (les dépôts amont évoluent) plutôt qu'un
constat figé dans un commentaire d'issue.

La mesure repose sur `gh api` (l'authentification est héritée de `gh auth`) —
pas de dépendance externe, pas de token en argument.

Usage :
    python scripts/research/measure_lanyonai.py                 # mesure complète par défaut
    python scripts/research/measure_lanyonai.py --repo BurgersEquation --proof inviscid_burgers_1d
    python scripts/research/measure_lanyonai.py --json           # sortie machine

Les six questions de l'étape 3 :
  1. la licence de chaque dépôt (ce qui conditionne toute réutilisation) ;
  2. la déclaration de toolchain (`lean-toolchain`, `lakefile`) — par dépôt ;
  3. ce que la preuve établit (compte de `def` / `theorem`, énoncés) ;
  4. l'intégrité de la preuve (`sorry`, `native_decide`, `axiom`) ;
  5. si la preuve relie le code au modèle (`implementation_mentions`) ;
  6. si le C livré calcule quelque chose (`has_main`, `main_is_stub`).

Les questions 1, 2 et 6 sont *par dépôt* ; 3, 4 et 5 portent sur une preuve
nommée. Le parsing est séparé du réseau : chaque fonction `parse_*` est pure et
testable hors ligne (`scripts/tests/test_measure_lanyonai.py`).
"""

from __future__ import annotations

import argparse
import base64
import json
import re
import subprocess
import sys
from dataclasses import dataclass, field


# Dépôts de la table de l'issue #19741 (étape 3). L'organe les mesure tous.
DEFAULT_REPOS = [
    "gkeyll",
    "AdvectionDiffusion",
    "BurgersEquation",
    "CompressibleEuler",
    "MaxwellEquations",
    "GeneralRelativisticMaxwell",
    "IdealMHD",
    "ElectrostaticVlasov",
    "LanyonScripts",
]

DEFAULT_ORG = "lanyonai"
DEFAULT_REPO = "BurgersEquation"
DEFAULT_PROOF = "inviscid_burgers_1d"

# Jetons signalant qu'une preuve relie le code au modèle formel. Un dépôt qui
# n'en porte aucun prouve les propriétés du schéma, pas la correspondance.
IMPLEMENTATION_MARKERS = (
    "implementation",
    "code_matches",
    "codeMatches",
    "cMatches",
    "toC",
    "Float",
)


def gh_api(path: str) -> dict:
    """Appeler `gh api` et renvoyer l'objet JSON (marqueur `__error__` si échec)."""
    try:
        out = subprocess.run(
            ["gh", "api", path],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=60,
            check=True,
        ).stdout
        return json.loads(out)
    except (subprocess.CalledProcessError, json.JSONDecodeError, FileNotFoundError) as exc:
        return {"__error__": str(exc)}


def fetch_file_text(org: str, repo: str, path: str) -> str:
    """Récupérer le contenu d'un fichier (base64) via l'API `contents`."""
    data = gh_api(f"repos/{org}/{repo}/contents/{path}")
    if "__error__" in data or "content" not in data:
        return ""
    try:
        return base64.b64decode(data["content"]).decode("utf-8", "replace")
    except Exception:
        return ""


def fetch_root_names(org: str, repo: str) -> list[str]:
    """Noms des entrées à la racine du dépôt ([] si illisible)."""
    data = gh_api(f"repos/{org}/{repo}/contents")
    if isinstance(data, dict) or "__error__" in data:
        return []
    try:
        return sorted(item["name"] for item in data)
    except Exception:
        return []


@dataclass
class RepoMeasurement:
    name: str
    license: str = "UNKNOWN"
    default_branch: str = "?"
    language: str = "?"
    size_kb: int = -1
    root_entries: list[str] = field(default_factory=list)

    @property
    def has_license_file(self) -> bool:
        return "LICENSE" in self.root_entries

    @property
    def has_lean_toolchain(self) -> bool:
        return "lean-toolchain" in self.root_entries

    @property
    def has_lakefile(self) -> bool:
        return bool({"lakefile.toml", "lakefile", "lakefile.lean", "lake-manifest.json"}
                    & set(self.root_entries))

    def to_dict(self) -> dict:
        return {
            "repo": self.name,
            "license": self.license,
            "license_file": self.has_license_file,
            "default_branch": self.default_branch,
            "language": self.language,
            "size_kb": self.size_kb,
            "has_lean_toolchain": self.has_lean_toolchain,
            "has_lakefile": self.has_lakefile,
            "root_entries": self.root_entries,
        }


@dataclass
class ProofMeasurement:
    repo: str
    proof: str
    lines: int = 0
    defs: int = 0
    theorems: int = 0
    theorem_names: list[str] = field(default_factory=list)
    imports: list[str] = field(default_factory=list)
    sorry_count: int = 0
    native_decide_count: int = 0
    axiom_count: int = 0
    implementation_mentions: list[str] = field(default_factory=list)

    def to_dict(self) -> dict:
        return {
            "repo": self.repo,
            "proof": self.proof,
            "lines": self.lines,
            "defs": self.defs,
            "theorems": self.theorems,
            "theorem_names": self.theorem_names,
            "imports": self.imports,
            "sorry_count": self.sorry_count,
            "native_decide_count": self.native_decide_count,
            "axiom_count": self.axiom_count,
            "implementation_mentions": self.implementation_mentions,
        }


@dataclass
class PrimitiveMeasurement:
    """Le fichier C correspondant à la preuve."""

    repo: str
    primitive: str
    lines: int = 0
    has_main: bool = False
    main_is_stub: bool | None = None
    static_inline_count: int = 0

    def to_dict(self) -> dict:
        return {
            "repo": self.repo,
            "primitive": self.primitive,
            "lines": self.lines,
            "has_main": self.has_main,
            "main_is_stub": self.main_is_stub,
            "static_inline_count": self.static_inline_count,
        }


def _strip_c_comments(text: str) -> str:
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
    return re.sub(r"//[^\n]*", "", text)


def parse_primitive(text: str, repo: str = "", primitive: str = "") -> PrimitiveMeasurement:
    """Mesurer un fichier C : taille, présence d'un `main`, et s'il est un pilote."""
    pm = PrimitiveMeasurement(repo=repo, primitive=primitive)
    pm.lines = len(text.splitlines())
    pm.static_inline_count = len(re.findall(r"\bstatic\s+inline\b", text))
    code = _strip_c_comments(text)
    match = re.search(r"^[ \t]*(?:int\s+)?main\s*\(", code, flags=re.M)
    if not match:
        return pm
    pm.has_main = True
    # Corps du main : jusqu'à l'accolade fermante en colonne 0.
    tail = code[match.end():]
    body_match = re.search(r"\{", tail)
    if not body_match:
        pm.main_is_stub = True
        return pm
    depth = 0
    body_chars: list[str] = []
    for ch in tail[body_match.start():]:
        if ch == "{":
            depth += 1
            if depth == 1:
                continue
        elif ch == "}":
            depth -= 1
            if depth == 0:
                break
        body_chars.append(ch)
    statements = [ln.strip() for ln in "".join(body_chars).splitlines() if ln.strip()]
    inert = {"return 0;", "return 0 ;", "return EXIT_SUCCESS;"}
    pm.main_is_stub = all(st in inert for st in statements)
    return pm


def parse_proof(text: str, repo: str = "", proof: str = "") -> ProofMeasurement:
    """Mesurer une preuve Lean : taille, déclarations, intégrité, renvois au code."""
    pm = ProofMeasurement(repo=repo, proof=proof)
    lines = text.splitlines()
    pm.lines = len(lines)
    pm.defs = sum(
        1
        for ln in lines
        if ln.startswith("def ") or ln.startswith("noncomputable def ")
        or ln.startswith("protected def ")
    )
    for ln in lines:
        s = ln.strip()
        if s.startswith("import "):
            pm.imports.append(s[len("import "):].strip())
        if s.startswith("theorem ") or s.startswith("protected theorem "):
            pm.theorems += 1
            pm.theorem_names.append(s.split("(", 1)[0].replace("theorem ", "").strip())
        if re.search(r"\bsorry\b", s):
            pm.sorry_count += 1
        if "native_decide" in s:
            pm.native_decide_count += 1
        if s.startswith("axiom "):
            pm.axiom_count += 1
    for marker in IMPLEMENTATION_MARKERS:
        if marker in text:
            pm.implementation_mentions.append(marker)
    return pm


def measure_repo(org: str, name: str) -> RepoMeasurement:
    data = gh_api(f"repos/{org}/{name}")
    if "__error__" in data:
        return RepoMeasurement(name=name, license="ERROR:" + data["__error__"][:60])
    lic = (data.get("license") or {}).get("spdx_id")
    return RepoMeasurement(
        name=name,
        license=lic or "NONE",
        default_branch=data.get("default_branch", "?"),
        language=str(data.get("language") or "?"),
        size_kb=data.get("size", -1),
        root_entries=fetch_root_names(org, name),
    )


def measure(org: str, repo: str, proof: str, repos: list[str]) -> dict:
    return {
        "org": org,
        "measured_by": "scripts/research/measure_lanyonai.py",
        "repos": [measure_repo(org, r).to_dict() for r in repos],
        "proof": parse_proof(
            fetch_file_text(org, repo, f"proofs/{proof}.lean"), repo, proof
        ).to_dict(),
        "primitive": parse_primitive(
            fetch_file_text(org, repo, f"implementations/{proof}.c"), repo, proof
        ).to_dict(),
    }


def render_text(report: dict) -> str:
    out = [f"Mesure lanyonai — org {report['org']} (organe: {report['measured_by']})"]
    out.append("\n[1] Licences et declaration de toolchain, par depot :")
    for r in report["repos"]:
        out.append(
            f"  {r['repo']:<28} licence={r['license']:<6} "
            f"fichier={'oui' if r['license_file'] else 'non':<3} "
            f"toolchain={'oui' if r['has_lean_toolchain'] else 'ABSENT':<6} "
            f"lakefile={'oui' if r['has_lakefile'] else 'ABSENT':<6} "
            f"lang={r['language']}"
        )
    p = report["proof"]
    out.append(
        f"\n[2] Preuve {p['repo']}/proofs/{p['proof']}.lean : "
        f"{p['lines']} lignes · {p['defs']} def · {p['theorems']} theorems"
    )
    out.append(f"    imports : {', '.join(p['imports']) or '(aucun lisible)'}")
    out.append(
        f"    integrite : sorry={p['sorry_count']} "
        f"native_decide={p['native_decide_count']} axiom={p['axiom_count']}"
    )
    mentions = ", ".join(p["implementation_mentions"]) or "AUCUNE"
    out.append(f"    renvois au code (implementation_mentions) : {mentions}")
    out.append("    theoremes :")
    for t in p["theorem_names"]:
        out.append(f"      - {t}")
    c = report.get("primitive") or {}
    if c:
        stub = {True: "STUB", False: "PILOTE", None: "SANS OBJET"}[c["main_is_stub"]]
        out.append(
            f"\n[3] Primitive {c['repo']}/implementations/{c['primitive']}.c : "
            f"{c['lines']} lignes · {c['static_inline_count']} static inline · "
            f"main={'oui' if c['has_main'] else 'non'} ({stub})"
        )
    return "\n".join(out)


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--org", default=DEFAULT_ORG)
    ap.add_argument("--repo", default=DEFAULT_REPO, help="dépôt portant la preuve cible")
    ap.add_argument("--proof", default=DEFAULT_PROOF, help="nom de la preuve (sans .lean)")
    ap.add_argument("--repos", default=",".join(DEFAULT_REPOS), help="liste de dépôts, virgules")
    ap.add_argument("--json", action="store_true", help="sortie JSON")
    args = ap.parse_args(argv)

    repos = [r.strip() for r in args.repos.split(",") if r.strip()]
    report = measure(args.org, args.repo, args.proof, repos)
    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    else:
        print(render_text(report))
    return 0


if __name__ == "__main__":
    sys.exit(main())
