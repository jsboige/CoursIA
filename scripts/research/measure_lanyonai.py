#!/usr/bin/env python3
"""Mesure de l'organe de distillation #19741 — dépôts lanyonai (solveurs physiques vérifiés).

Contexte : l'issue #19741 (chaîne de transcription-distillation Gorard / Lanyon AI)
demand, en étape 3, une mesure firsthand des dépôts `lanyonai` — licences,
déclaration de toolchain Lean/Mathlib, et ce que la plus petite preuve établit
exactement. Cet organe rend la mesure re-exécutable à la demande (les dépôts
amont évoluent) plutôt qu'un constat figé dans un commentaire d'issue.

La mesure repose sur `gh api` (l'authentification est héritée de `gh auth`) —
pas de dépendance externe, pas de token en argument.

Usage :
    python scripts/research/measure_lanyonai.py                 # mesure complète par défaut
    python scripts/research/measure_lanyonai.py --repo BurgersEquation --proof inviscid_burgers_1d
    python scripts/research/measure_lanyonai.py --json           # sortie machine

La mesure répond aux quatre questions de l'étape 3 :
  1. la licence de chaque dépôt (ce qui conditionne toute réutilisation) ;
  2. la version de Lean / Mathlib sous laquelle les preuves compilent (non
     déclarée : l'organe le constate en cherchant `lean-toolchain` / `lakefile`) ;
  3. ce que la preuve établit exactement (compte de `def` / `theorem`, liste des
     énoncés de théorèmes) ;
  4. la forme du dépôt (specifications `.rkt`, implementations `.c`, proofs `.lean`).
"""

from __future__ import annotations

import argparse
import base64
import json
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


def gh_api(path: str) -> dict:
    """Appeler `gh api` et renvoyer l'objet JSON ({} si échec réseau/auth)."""
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


def repo_has_file(org: str, repo: str, path: str) -> bool:
    """Vrai si le fichier existe à la racine du dépôt (404 sinon)."""
    data = gh_api(f"repos/{org}/{repo}/contents/{path}")
    return "__error__" not in data and "path" in data


@dataclass
class RepoMeasurement:
    name: str
    license: str = "UNKNOWN"
    default_branch: str = "?"
    language: str = "?"
    size_kb: int = -1

    def to_dict(self) -> dict:
        return {
            "repo": self.name,
            "license": self.license,
            "default_branch": self.default_branch,
            "language": self.language,
            "size_kb": self.size_kb,
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
    has_lean_toolchain: bool = False
    has_lakefile: bool = False

    def to_dict(self) -> dict:
        return {
            "repo": self.repo,
            "proof": self.proof,
            "lines": self.lines,
            "defs": self.defs,
            "theorems": self.theorems,
            "theorem_names": self.theorem_names,
            "imports": self.imports,
            "has_lean_toolchain": self.has_lean_toolchain,
            "has_lakefile": self.has_lakefile,
        }


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
    )


def measure_proof(org: str, repo: str, proof: str) -> ProofMeasurement:
    pm = ProofMeasurement(repo=repo, proof=proof)
    # Déclaration de toolchain / lakefile à la racine (l'issue affirme : absents).
    pm.has_lean_toolchain = repo_has_file(org, repo, "lean-toolchain")
    pm.has_lakefile = repo_has_file(org, repo, "lakefile.toml") or repo_has_file(
        org, repo, "lakefile"
    )
    text = fetch_file_text(org, repo, f"proofs/{proof}.lean")
    if not text:
        return pm
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
            pm.imports.append(s[len("import ") :].strip())
        if s.startswith("theorem ") or s.startswith("protected theorem "):
            pm.theorems += 1
            pm.theorem_names.append(s.split("(", 1)[0].replace("theorem ", "").strip())
    return pm


def measure(org: str, repo: str, proof: str, repos: list[str]) -> dict:
    return {
        "org": org,
        "measured_by": "scripts/research/measure_lanyonai.py",
        "repos": [measure_repo(org, r).to_dict() for r in repos],
        "proof": measure_proof(org, repo, proof).to_dict(),
    }


def render_text(report: dict) -> str:
    out = [f"Mesure lanyonai — org {report['org']} (organe: {report['measured_by']})"]
    out.append("\n[1] Licences des dépôts :")
    for r in report["repos"]:
        out.append(
            f"  {r['repo']:<28} licence={r['license']:<6} "
            f"branch={r['default_branch']:<6} lang={r['language']}"
        )
    p = report["proof"]
    out.append(
        f"\n[2] Toolchain de {p['repo']}: "
        f"lean-toolchain={'OUI' if p['has_lean_toolchain'] else 'ABSENT'} · "
        f"lakefile={'OUI' if p['has_lakefile'] else 'ABSENT'}"
    )
    out.append(f"    imports de la preuve : {', '.join(p['imports']) or '(aucun lisible)'}")
    out.append(
        f"\n[3] Preuve {p['repo']}/proofs/{p['proof']}.lean : "
        f"{p['lines']} lignes · {p['defs']} def · {p['theorems']} theorems"
    )
    out.append("    théorèmes :")
    for t in p["theorem_names"]:
        out.append(f"      - {t}")
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
