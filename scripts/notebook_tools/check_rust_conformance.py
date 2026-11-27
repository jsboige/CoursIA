#!/usr/bin/env python3
"""Conformite DIFFERENTIELLE des carnets Rust (Pli 3 de l'Epic Origami #26510).

Ce que cet outil fait
---------------------
Pour un triplet de carnets jumeaux (Python, C#, Rust), il compare les
**sorties numeriques** du carnet Rust a celles de ses jumeaux, a une
**tolerance declaree par cellule**. Il ne compare pas des fichiers, il compare
des **grandeurs** : une grille resolue, un nombre de solutions, un compteur de
noeuds. Chaque grandeur est declaree dans le registre avec, pour chaque cote,
la cellule qui la porte et la regle d'extraction.

Pourquoi un registre, et pas une comparaison « cell by cell » automatique
---------------------------------------------------------------------------
Les trois cotes n'ont **pas** la meme structure : le carnet Rust est un portage
vers la crate `dlx`, le Python est une implementation from-scratch (Knuth
Algorithm X), le C# delega a `DlxLib`. Les cellules ne se correspondent donc
ni par index ni par ordre. Une correspondance automatique serait une
invention : elle comparerait des grandeurs differentes en pretending qu'elles
sont les memes. Ici la correspondance est **ecrite, par un humain, et
attestee** -- et l'outil echoue si une extraction declaree ne donne pas de
valeur.

Le registre vit dans `scripts/notebook_tools/rust_conformance.d/` (un fichier
YAML par triplet, plus `_schema.yaml`).

Les deux controles exiges par le pli
-----------------------------------
- **controle POSITIF** : le pilote `Sudoku/Sudoku-02-DancingLinks-Rust.ipynb`
  est conforme (les grandeurs declarees coincident sur les cotes declares) ;
- **controle NEGATIF** : une sortie alteree doit etre detectee -- un test
  pertube la sortie commitee et exige que l'organe la signale.

Regles fail-CLOSED
------------------
- un cote declare sans extraction lisible -> **finding** (pas un silence) ;
- un cote explicitement `absent:` (avec son motif) -> signale, mais n'echoue
  pas : l'absence est un fait declare, pas une mesure absence ;
- une tolerance declaree s'applique aux grandeurs numeriques ; les grandeurs
  non numeriques se comparent a l'egalite stricte ; la transformation
  `labels` compare un ENSEMBLE d'etiquettes, sans tenir compte de leur
  ordre (l'ordre de retour d'un core n'est pas une garantie d'API).

Usage
-----
    python scripts/notebook_tools/check_rust_conformance.py            # tout le registre
    python scripts/notebook_tools/check_rust_conformance.py --entry sudoku-02-dancinglinks
    python scripts/notebook_tools/check_rust_conformance.py --json

Sortie : `0` si toutes les grandeurs declarees sont conformes, `1` si au moins
une diverge (ou si une extraction declaree echoue), `2` si l'instrument lui-meme
est en panne (registre illisible, notebook absent) **ou si la selection
demarree n'a rien controle** (`--entry` sans correspondance, registre vide) :
un controle qui ne mesure rien ne rend jamais un vert.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

try:
    import yaml
except ImportError:  # pragma: no cover - dependance de l'instrument
    print("YAML manquant : `pip install pyyaml` (l'organe lit un registre YAML)",
          file=sys.stderr)
    raise

SIDE_ORDER = ("python", "csharp", "rust")
DEFAULT_REGISTRY = Path(__file__).resolve().parent / "rust_conformance.d"


# --- lecture des notebooks ---------------------------------------------------

def read_notebook_outputs(path: Path) -> dict[int, str]:
    """Retourne {index de cellule de code: texte des sorties}.

    Les sorties sont cumulees : `stream` (texte), `execute_result` et
    `display_data` (mime `text/plain`). Une cellule sans sortie donne une
    chaine vide -- l'absence de sortie est une donnee, pas une erreur de
    lecture (c'est l'extraction declaree qui decidera).
    """
    nb = json.loads(path.read_text(encoding="utf-8"))
    out: dict[int, str] = {}
    for index, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        chunks: list[str] = []
        for output in cell.get("outputs") or []:
            if "text" in output:
                chunks.append("".join(output["text"]))
            data = output.get("data") or {}
            if "text/plain" in data:
                chunks.append("".join(data["text/plain"]))
        out[index] = "".join(chunks)
    return out


def _transform(region: str, transform: str) -> str | float | int:
    """Applique la transformation declaree a la region capturee."""
    if transform == "digits":
        return re.sub(r"\D", "", region)
    if transform == "float":
        match = re.search(r"-?\d+(?:[.,]\d+)?", region)
        if not match:
            raise ValueError("aucun nombre dans la region capturee")
        return float(match.group(0).replace(",", "."))
    if transform == "int":
        match = re.search(r"-?\d+", region)
        if not match:
            raise ValueError("aucun entier dans la region capturee")
        return int(match.group(0))
    if transform == "text":
        return region.strip()
    if transform == "text_lf":
        # Meme chose que `text`, une fois les fins de ligne ramenees a LF :
        # un carnet C# execute sous Windows stocke ses sorties en CRLF, et le
        # texte est identique au Python une fois cette difference de plateforme
        # neutralisee. Rien d'autre n'est normalise (accents, espaces, casse).
        return region.replace("\r\n", "\n").replace("\r", "\n").strip()
    if transform == "labels":
        # Comparaison d'un ENSEMBLE d'etiquettes, independamment de leur
        # ordre : les jetons sont tries avant la comparaison.
        #
        # Pourquoi : `get_unsat_core` renvoie un sous-ensemble insatisfaisable
        # d'etiquettes, mais l'API ne garantit NI l'ordre de retour NI la
        # minimalite generale. Comparer le core en texte strict comparerait
        # une grandeur qui n'en est pas une (la position d'une etiquette).
        # Compare comme un ENSEMBLE, la mesure porte sur le contenu du core.
        jetons = re.findall(r"[A-Za-z0-9_]+", region)
        if not jetons:
            raise ValueError("aucune etiquette dans la region capturee")
        return " ".join(sorted(jetons))
    raise ValueError(f"transformation inconnue : {transform!r}")


def extract_value(text: str, spec: dict) -> tuple[str | float | int | None, str]:
    """Extrait la valeur declaree dans la sortie d'une cellule.

    Retourne `(valeur, motif)` : la valeur est `None` quand l'extraction
    echoue, et le motif explique pourquoi (fail-CLOSED : l'appelant doit
    pouvoir distinguer « pas de sortie » de « sortie illisible »).
    """
    cell = spec.get("cell")
    if cell is None:
        return None, "aucune cellule declaree"
    if cell not in text:
        # `text` est le dict {index: texte} passe par l'appelant -- cette
        # branche est atteinte par le appelant, pas ici.
        return None, f"cellule {cell} absente"
    body = text[cell]
    if not body.strip():
        return None, f"cellule {cell} sans sortie"
    pattern = spec.get("pattern")
    if not pattern:
        return None, "aucun motif declare"
    match = re.search(pattern, body, re.DOTALL)
    if not match:
        return None, f"motif absent dans la cellule {cell}"
    region = match.group(1) if match.groups() else match.group(0)
    try:
        return _transform(region, spec.get("transform", "text")), ""
    except ValueError as exc:
        return None, str(exc)


# --- registre ----------------------------------------------------------------

def load_registry(registry_dir: Path) -> list[dict]:
    """Lit tous les triplets declares dans le registre (un YAML par triplet)."""
    entries: list[dict] = []
    for path in sorted(registry_dir.glob("*.yaml")):
        if path.name.startswith("_"):
            continue
        data = yaml.safe_load(path.read_text(encoding="utf-8")) or []
        if isinstance(data, dict):
            data = [data]
        for entry in data:
            entry = dict(entry)
            entry["_source"] = path.name
            entries.append(entry)
    return entries


def _values_match(left, right, tolerance: float,
                  case_insensitive: bool = False) -> bool:
    """Compare deux valeurs : numerique a la tolerance, sinon egalite stricte."""
    if isinstance(left, (int, float)) and isinstance(right, (int, float)):
        return abs(float(left) - float(right)) <= tolerance
    if case_insensitive:
        return str(left).strip().lower() == str(right).strip().lower()
    return str(left) == str(right)


# --- controle ----------------------------------------------------------------

def check_measure(entry: dict, measure: dict, outputs: dict[str, dict[int, str]]
                  ) -> dict:
    """Controle une grandeur declaree sur tous ses cotes."""
    tolerance = float(measure.get("tolerance", 0.0))
    case_insensitive = bool(measure.get("case_insensitive"))
    sides = measure.get("sides") or {}
    reference_side = measure.get("reference") or next(
        (s for s in SIDE_ORDER if s in sides), None)
    extracted: dict[str, object] = {}
    absent: dict[str, str] = {}
    failures: list[str] = []

    for side in SIDE_ORDER:
        spec = sides.get(side)
        if spec is None:
            continue
        if spec.get("absent"):
            absent[side] = str(spec["absent"])
            continue
        value, reason = extract_value(outputs.get(side, {}), spec)
        if value is None:
            failures.append(f"{side}: {reason}")
            continue
        extracted[side] = value

    if reference_side is None or reference_side not in extracted:
        failures.append(
            f"cote de reference absent ou illisible : {reference_side!r}")
    else:
        reference = extracted[reference_side]
        for side, value in sorted(extracted.items()):
            if side == reference_side:
                continue
            if not _values_match(reference, value, tolerance, case_insensitive):
                failures.append(
                    f"{side} != {reference_side} : {value!r} vs {reference!r} "
                    f"(tolerance {tolerance})")

    return {
        "id": measure.get("id"),
        "description": measure.get("description", ""),
        "reference": reference_side,
        "tolerance": tolerance,
        "values": {k: (v if isinstance(v, (int, float)) else str(v))
                   for k, v in sorted(extracted.items())},
        "absent": absent,
        "failures": failures,
        "status": "OK" if not failures else "DIVERGENCE",
    }


def check_entry(entry: dict, repo_root: Path) -> dict:
    """Controle un triplet : lecture des trois carnets, puis de ses grandeurs.

    Le cote `rust` est obligatoire (c'est l'objet de l'organe) ; les cotes
    `python` et `csharp` sont facultatifs -- une serie peut n'avoir qu'un
    jumeau Python, et une grandeur peut alors n'etre comparee qu'entre le
    Rust et le Python. Un cote declare dont le FICHIER manque est une
    anomalie ; un cote non declare n'en est pas une.
    """
    paths = {side: entry.get(side) for side in SIDE_ORDER}
    outputs: dict[str, dict[int, str]] = {}
    missing: list[str] = []
    if not paths.get("rust"):
        missing.append("rust: non declare (le cote Rust est obligatoire)")
    for side, rel in paths.items():
        if not rel:
            continue
        path = repo_root / rel
        if not path.exists():
            missing.append(f"{side}: fichier absent ({rel})")
            continue
        outputs[side] = read_notebook_outputs(path)

    measures = [check_measure(entry, measure, outputs)
                for measure in entry.get("measures") or []]
    findings = list(missing)
    findings += [f"mesure {m['id']} : {f}" for m in measures for f in m["failures"]]
    return {
        "name": entry.get("name"),
        "source": entry.get("_source"),
        "missing": missing,
        "measures": measures,
        "status": "OK" if not findings else "DIVERGENCE",
        "findings": findings,
    }


def run(registry_dir: Path, repo_root: Path,
        only: str | None = None) -> tuple[int, dict]:
    """Controle complet du registre. Retourne (rc, rapport).

    **fail-CLOSED sur la selection.** Un `--entry` qui ne correspond a aucun
    triplet n'est PAS une conformite : c'est une demande non satisfaite. Une
    coquille dans le nom d'une entree (ou un renommage) donnerait sinon un
    vert muet -- l'organe aurait « controle » zero triplet et l'afficherait
    conforme. Meme principe pour un registre vide : un controle qui ne mesure
    rien ne peut pas rendre un vert.
    """
    if not registry_dir.is_dir():
        print(f"registre introuvable : {registry_dir}", file=sys.stderr)
        return 2, {"entries": []}
    entries = load_registry(registry_dir)
    if only:
        selection = [e for e in entries
                     if only in (e.get("name") or "") or only in e.get("_source", "")]
        if not selection:
            print(f"entree introuvable : --entry {only!r} ne correspond a aucun "
                  f"triplet du registre ({len(entries)} entree(s) declaree(s))",
                  file=sys.stderr)
            return 2, {"entries": [], "conformes": 0, "divergences": 0,
                       "error": f"entree introuvable : {only}"}
        entries = selection
    if not entries:
        print(f"registre vide : aucune entree declaree dans {registry_dir}",
              file=sys.stderr)
        return 2, {"entries": [], "conformes": 0, "divergences": 0,
                   "error": "registre vide"}
    results = [check_entry(entry, repo_root) for entry in entries]
    n_div = sum(1 for r in results if r["status"] != "OK")
    return (1 if n_div else 0), {"entries": results,
                                 "conformes": len(results) - n_div,
                                 "divergences": n_div}


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description="Conformite differentielle des carnets Rust (Pli 3, #26510)")
    parser.add_argument("--registry", default=str(DEFAULT_REGISTRY),
                        help="repertoire du registre (defaut : rust_conformance.d)")
    parser.add_argument("--repo-root", default=str(Path(__file__).resolve().parents[2]),
                        help="racine du depot (les chemins du registre y sont relatifs)")
    parser.add_argument("--entry", default=None,
                        help="ne controler qu'un triplet (nom ou fichier)")
    parser.add_argument("--json", action="store_true",
                        help="sortie structuree (JSON)")
    args = parser.parse_args(argv)

    rc, report = run(Path(args.registry), Path(args.repo_root), args.entry)

    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
        return rc

    for entry in report["entries"]:
        print(f"== {entry['name']} ({entry['source']})")
        for measure in entry["measures"]:
            values = ", ".join(f"{k}={v}" for k, v in measure["values"].items())
            absent = "".join(
                f" | absent: {k} ({why})" for k, why in measure["absent"].items())
            print(f"   {measure['status']:<10} {measure['id']}: {values}{absent}")
            for failure in measure["failures"]:
                print(f"       -> {failure}")
        for finding in entry["missing"]:
            print(f"   ANOMALIE  {finding}")
    print(f"\n{report['conformes']} conforme(s), {report['divergences']} divergence(s)")
    return rc


if __name__ == "__main__":
    sys.exit(main())
