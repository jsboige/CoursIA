#!/usr/bin/env python
"""Qualification des carnets : difficulte (D1..D4) et dimension recherche (R0..R3).

L'organe lit le manifeste ``docs/curriculum/qualification/manifest.json``,
verifie sa coherence interne et **re-mesure** les signaux qu'il enregistre sur
l'arbre courant. Il ne calcule aucune valeur de difficulte ni de recherche :
ces deux axes sont **declares, justifies** (une ligne par carnet), l'organe
en controle la forme et la derivation.

Ce qu'il refuse (exit 1) :

- un carnet de la serie pilote absent du manifeste, ou une entree dont le
  fichier n'existe plus ;
- une valeur hors enumeration, une justification absente ou trop courte ;
- un niveau qui ne se derive pas de la regle documentee
  (``niveau = max(prerequis, autonomie)``) ;
- une **derive** : les mesures enregistrees ne correspondent plus a l'arbre
  (le carnet a change depuis sa qualification -- il faut le requalifier).

Ce qu'il signale sans faire echouer (avertissement) :

- une densite pedagogique sous le plancher de 1200 (#13410). C'est un
  **defaut a corriger** (enrichissement), pas une raison de requalifier :
  un carnet sous-dense n'est pas pour autant un carnet difficile.
- la **perte d'un signal** : un organe canonique (``pedagogy_density``,
  ``generate_catalog``) momentanement indisponible. La degradation est
  signalee, jamais avalee en silence.

Usage :

    python scripts/notebook_tools/curriculum_qualification.py --report
    python scripts/notebook_tools/curriculum_qualification.py --check
    python scripts/notebook_tools/curriculum_qualification.py --fields --json

Usage depuis un autre module (crochet du generateur, #24994) :

    from curriculum_qualification import load_manifest, qualification_for
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, field
from pathlib import Path

_TOOLS_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _TOOLS_DIR.parent.parent
if str(_TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(_TOOLS_DIR))

MANIFEST_RELPATH = "docs/curriculum/qualification/manifest.json"

DIFFICULTY_LEVELS = ("D1", "D2", "D3", "D4")
RESEARCH_LEVELS = ("R0", "R1", "R2", "R3")
CRITERIA = ("prerequis", "outillage", "autonomie")

#: Regle de derivation du niveau (voir ``docs/curriculum/qualification/
#: echelle-difficulte.md``) : le niveau est le plus contraignant des deux
#: criteres qui pessent sur le raisonnement demande -- les prerequis
#: (``prerequis``) et l'autonomie (``autonomie``). L'outillage est un **cout
#: d'acces** : il conditionne l'entree dans la serie, pas la difficulte du
#: contenu ; il est enregistre et signale, jamais promu au rang.
DIFFICULTY_RULE = "max(prerequis, autonomie)"

#: Une justification trop courte n'est pas une justification.
MIN_JUSTIFICATION_CHARS = 40


def _repo_root() -> Path:
    """La racine du depot (le parent de ``scripts/notebook_tools``)."""
    return _REPO_ROOT


def manifest_path() -> Path:
    """Le chemin absolu du manifeste."""
    return _repo_root() / MANIFEST_RELPATH


@dataclass
class Finding:
    """Une anomalie detectee sur le manifeste ou sur l'arbre."""

    kind: str  # 'structure' | 'couverture' | 'niveau' | 'derive'
    severity: str  # 'error' | 'warning'
    path: str
    message: str

    def as_dict(self) -> dict:
        return {
            "kind": self.kind,
            "severity": self.severity,
            "path": self.path,
            "message": self.message,
        }


@dataclass
class Qualification:
    """Une entree du manifeste, avec ses mesures et sa derivation."""

    path: str
    difficulte: str
    recherche: str
    criteres: dict
    justification: str
    mesures: dict
    derived_difficulty: str = ""
    drift: dict = field(default_factory=dict)

    def as_dict(self) -> dict:
        return {
            "path": self.path,
            "difficulte": self.difficulte,
            "recherche": self.recherche,
            "criteres": self.criteres,
            "justification": self.justification,
            "mesures": self.mesures,
            "derived_difficulty": self.derived_difficulty,
            "drift": self.drift,
        }


def derive_difficulty(criteres: dict) -> str:
    """Le niveau derive des criteres (``DIFFICULTY_RULE``)."""
    return "D%d" % max(int(criteres["prerequis"]), int(criteres["autonomie"]))


def load_manifest(path: Path | None = None) -> dict:
    """Charge le manifeste. Lève ``FileNotFoundError`` s'il est absent."""
    target = Path(path) if path else manifest_path()
    return json.loads(target.read_text(encoding="utf-8"))


def iter_entries(manifest: dict):
    """Parcourt les entrees ``(serie, notebook)`` du manifeste."""
    for serie in manifest.get("series", []):
        for entry in serie.get("notebooks", []):
            yield serie, entry


def qualification_for(manifest: dict, notebook_path: str) -> dict | None:
    """La qualification d'un carnet donne, ou ``None``.

    API destinee au crochet du generateur (#24994) : elle lit le manifeste
    et rend les deux champs, sans jamais les recalculer.
    """
    for _serie, entry in iter_entries(manifest):
        if entry.get("path") == notebook_path:
            return {
                "difficulte": entry.get("difficulte"),
                "recherche": entry.get("recherche"),
                "criteres": entry.get("criteres"),
                "justification": entry.get("justification"),
            }
    return None


# --------------------------------------------------------------------------
# Mesures : l'organe REUTILISE les organes existants, il n'en reinvente pas.
# --------------------------------------------------------------------------


#: Degradations constatees lors de la derniere mesure (organe indisponible).
#: L'organe ne les avale pas en silence : il les transforme en avertissement,
#: parce qu'un organe qui perd un signal doit le dire (CLAUDE.md section F).
_LAST_DEGRADED: list[str] = []


def _measure_notebook(path: Path) -> dict:
    """Mesure un carnet : exercices, cellules, densite, kernel, exigences.

    ``pedagogy_density`` et ``count_exercises`` sont les organes canoniques ;
    ils sont consommes tels quels. ``generate_catalog`` fournit ``kernel`` et
    ``exigences`` : son import est defensif, parce que ce fichier est porte
    par une autre lane (#24994) et que l'organe doit survivre a son evolution.
    """
    from count_exercises import count_exercises_in_notebook

    _LAST_DEGRADED.clear()

    try:
        from pedagogy_density import check_paths

        result = check_paths([path])
        verdict = None
        for bucket in (result.ok, result.below_threshold, result.exempt, result.unmeasured):
            for v in bucket:
                if v.path == str(path):
                    verdict = v
                    break
            if verdict is not None:
                break
    except Exception as exc:  # pragma: no cover - organe indisponible
        verdict = None
        _LAST_DEGRADED.append(f"pedagogy_density indisponible : {exc.__class__.__name__}")

    count = count_exercises_in_notebook(path)

    notebook = json.loads(path.read_text(encoding="utf-8"))
    code_cells = [c for c in notebook.get("cells", []) if c.get("cell_type") == "code"]
    md_cells = [c for c in notebook.get("cells", []) if c.get("cell_type") == "markdown"]

    mesures = {
        "exercices": count.count,
        "cellules_code": len(code_cells),
        "cellules_md": len(md_cells),
        "prose_chars": len("".join("".join(c.get("source", [])) for c in md_cells)),
        "densite": verdict.density if verdict is not None else None,
        "densite_plancher": verdict.threshold if verdict is not None else None,
        "kernel": None,
        "exigences": None,
    }

    try:
        import importlib.util

        spec = importlib.util.spec_from_file_location(
            "_catalog_gen", _TOOLS_DIR / "generate_catalog.py"
        )
        gencat = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(gencat)
        mesures["kernel"] = gencat.detect_kernel(notebook)
        req = gencat.detect_requirements(notebook)
        mesures["exigences"] = {
            "api": bool(req.get("requires_api")),
            "gpu": bool(req.get("requires_gpu")),
            "cloud": bool(req.get("requires_cloud")),
            "wsl": bool(req.get("requires_wsl")),
        }
    except Exception as exc:  # pragma: no cover - generate_catalog indisponible
        _LAST_DEGRADED.append(
            f"generate_catalog indisponible : {exc.__class__.__name__} "
            "(kernel et exigences non releves)"
        )

    return mesures


# --------------------------------------------------------------------------
# Verification
# --------------------------------------------------------------------------

#: Champs de mesure compares lors de la detection de derive. Le kernel et les
#: exigences ne sont compares que s'ils ont ete releves des deux cotes.
_DRIFT_FIELDS = ("exercices", "cellules_code", "cellules_md", "prose_chars", "densite")


def check_manifest(manifest: dict, root: Path | None = None) -> list[Finding]:
    """Verifie le manifeste contre lui-meme et contre l'arbre courant."""
    root = root or _repo_root()
    findings: list[Finding] = []
    degraded: set[str] = set()

    for serie in manifest.get("series", []):
        serie_path = serie.get("path", "")
        declared = {e.get("path") for e in serie.get("notebooks", [])}
        on_disk = {
            str(p.relative_to(root)).replace("\\", "/")
            for p in sorted((root / serie_path).glob("*.ipynb"))
        } if serie_path else set()

        for missing in sorted(on_disk - declared):
            findings.append(
                Finding(
                    "couverture",
                    "error",
                    missing,
                    "carnet present sur l'arbre et absent du manifeste : il n'est pas qualifie",
                )
            )
        for extra in sorted(declared - on_disk):
            findings.append(
                Finding(
                    "couverture",
                    "error",
                    extra,
                    "entree du manifeste sans carnet sur l'arbre (fichier deplace ou supprime ?)",
                )
            )

        for entry in serie.get("notebooks", []):
            nb_path = entry.get("path", "")
            diff = entry.get("difficulte")
            if diff not in DIFFICULTY_LEVELS:
                findings.append(
                    Finding("structure", "error", nb_path, f"difficulte invalide : {diff!r}")
                )
            research = entry.get("recherche")
            if research not in RESEARCH_LEVELS:
                findings.append(
                    Finding("structure", "error", nb_path, f"recherche invalide : {research!r}")
                )
            criteres = entry.get("criteres") or {}
            for crit in CRITERIA:
                value = criteres.get(crit)
                if not isinstance(value, int) or not (1 <= value <= 4):
                    findings.append(
                        Finding(
                            "structure",
                            "error",
                            nb_path,
                            f"critere {crit!r} absent ou hors 1..4 : {value!r}",
                        )
                    )
            justification = entry.get("justification") or ""
            if len(justification.strip()) < MIN_JUSTIFICATION_CHARS:
                findings.append(
                    Finding(
                        "structure",
                        "error",
                        nb_path,
                        f"justification absente ou trop courte (< {MIN_JUSTIFICATION_CHARS} caracteres)",
                    )
                )
            if all(isinstance(criteres.get(c), int) for c in ("prerequis", "autonomie")):
                derived = derive_difficulty(criteres)
                if diff in DIFFICULTY_LEVELS and derived != diff:
                    findings.append(
                        Finding(
                            "niveau",
                            "error",
                            nb_path,
                            f"niveau {diff} incompatible avec la regle {DIFFICULTY_RULE} "
                            f"(prerequis={criteres['prerequis']}, autonomie={criteres['autonomie']}) "
                            f"-> {derived}",
                        )
                    )

            # Derive : le carnet a-t-il change depuis sa qualification ?
            absolute = root / nb_path
            if not absolute.exists():
                continue
            recorded = entry.get("mesures") or {}
            fresh = _measure_notebook(absolute)
            degraded.update(_LAST_DEGRADED)
            drift = {}
            for fieldname in _DRIFT_FIELDS:
                old = recorded.get(fieldname)
                new = fresh.get(fieldname)
                if old is None or new is None:
                    continue
                if old != new:
                    drift[fieldname] = {"manifeste": old, "arbre": new}
            if drift:
                findings.append(
                    Finding(
                        "derive",
                        "error",
                        nb_path,
                        "mesures obsolete : "
                        + ", ".join(
                            f"{k} {v['manifeste']} -> {v['arbre']}" for k, v in sorted(drift.items())
                        )
                        + " ; requalifier ce carnet",
                    )
                )
            floor = fresh.get("densite_plancher")
            density = fresh.get("densite")
            if floor is not None and density is not None and density < floor:
                findings.append(
                    Finding(
                        "densite",
                        "warning",
                        nb_path,
                        f"densite {density} sous le plancher {floor} (#13410) : "
                        "defaut d'enrichissement a corriger, pas une requalification",
                    )
                )

    for reason in sorted(degraded):
        findings.append(
            Finding(
                "degrade",
                "warning",
                MANIFEST_RELPATH,
                f"mesure incomplete : {reason}",
            )
        )

    return findings


# --------------------------------------------------------------------------
# Rapports
# --------------------------------------------------------------------------


def _render_report(manifest: dict) -> str:
    lines = []
    for serie in manifest.get("series", []):
        lines.append("=" * 78)
        lines.append(f"serie {serie.get('id')} ({serie.get('path')})")
        lines.append("-" * 78)
        header = f"{'carnet':<46} {'niv':<4} {'rech':<5} {'P':<3} {'O':<3} {'A':<3} {'ex':<4} {'dens':<5}"
        lines.append(header)
        for entry in serie.get("notebooks", []):
            name = entry.get("path", "").rsplit("/", 1)[-1]
            c = entry.get("criteres") or {}
            m = entry.get("mesures") or {}
            lines.append(
                f"{name[:45]:<46} {entry.get('difficulte',''):<4} {entry.get('recherche',''):<5} "
                f"{c.get('prerequis',''):<3} {c.get('outillage',''):<3} {c.get('autonomie',''):<3} "
                f"{m.get('exercices',''):<4} {m.get('densite',''):<5}"
            )
        lines.append("")
    return "\n".join(lines)


def _render_findings(findings: list[Finding]) -> str:
    lines = []
    for f in findings:
        lines.append(f"[{f.severity.upper()}] {f.kind} {f.path} : {f.message}")
    if not lines:
        lines.append("OK : aucune anomalie.")
    return "\n".join(lines)


def refresh_manifest(manifest: dict, root: Path | None = None) -> list[str]:
    """Re-mesure les signaux et reecrit le bloc ``mesures`` du manifeste.

    Seules les **mesures** sont touchees : les valeurs declarees
    (``difficulte``, ``recherche``, ``criteres``) et les justifications ne sont
    jamais regenerees -- elles sont un jugement, pas une mesure. La commande
    rend la liste des carnets dont les mesures ont change.
    """
    root = root or _repo_root()
    changed = []
    for _serie, entry in iter_entries(manifest):
        absolute = root / entry.get("path", "")
        if not absolute.exists():
            continue
        fresh = _measure_notebook(absolute)
        recorded = entry.get("mesures") or {}
        updated = dict(recorded)
        for key, value in fresh.items():
            if value is not None:
                updated[key] = value
        if updated != recorded:
            entry["mesures"] = updated
            changed.append(entry.get("path", ""))
    return changed


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--manifest", help="chemin du manifeste (defaut : docs/curriculum/qualification/manifest.json)")
    parser.add_argument("--report", action="store_true", help="affiche la table de qualification")
    parser.add_argument("--check", action="store_true", help="verifie le manifeste contre l'arbre")
    parser.add_argument("--refresh", action="store_true", help="re-mesure et reecrit le bloc mesures du manifeste")
    parser.add_argument("--fields", action="store_true", help="emet les deux champs par carnet (JSON)")
    parser.add_argument("--json", action="store_true", help="sortie JSON")
    args = parser.parse_args(argv)

    if not (args.report or args.check or args.refresh or args.fields):
        args.check = True

    try:
        manifest = load_manifest(Path(args.manifest) if args.manifest else None)
    except FileNotFoundError:
        print(f"manifeste absent : {manifest_path()}", file=sys.stderr)
        return 2

    if args.refresh:
        target = Path(args.manifest) if args.manifest else manifest_path()
        changed = refresh_manifest(manifest)
        target.write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        print(f"{len(changed)} carnet(s) re-mesure(s) : {target}")
        for path in changed:
            print(f"  - {path}")
        return 0

    if args.fields:
        payload = {
            e.get("path"): {
                "difficulte": e.get("difficulte"),
                "recherche": e.get("recherche"),
            }
            for _s, e in iter_entries(manifest)
        }
        print(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True))
        return 0

    findings: list[Finding] = []
    if args.check:
        findings = check_manifest(manifest)

    if args.json:
        print(
            json.dumps(
                {
                    "manifest": MANIFEST_RELPATH,
                    "findings": [f.as_dict() for f in findings],
                    "errors": sum(1 for f in findings if f.severity == "error"),
                    "warnings": sum(1 for f in findings if f.severity == "warning"),
                },
                ensure_ascii=False,
                indent=2,
            )
        )
        return 1 if any(f.severity == "error" for f in findings) else 0

    if args.report:
        print(_render_report(manifest))
    if args.check:
        print(_render_findings(findings))
        return 1 if any(f.severity == "error" for f in findings) else 0
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
