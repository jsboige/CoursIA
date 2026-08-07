"""Detecteur quant-4-classes — triage des valeurs quantitatives ecrites en dur
dans les cellules markdown des notebooks.

Suite directe de l'EPIC #9434 (mandat « quantitatif tenu par le CI, pas par la
prose ») et de l'outillage Phase 1 #9768 (detecteurs D1+D3+D4+D5 trans-historique
et D5 v3 intra-revision, PRs #9791 + #9793 MERGED). Reutilise
`_extract_prose_numbers` et `_parse_fr_number` de `scan_d5_prose_outputs_alignment`.

## Les 4 classes (cf. issue #9434)

| Classe | Dérive? | Heuristique |
|---|---|---|
| **STRUCTUREL** | Non | Pas d'unite temporelle, pas de pattern `X.Y.Z` version, valeur theorique ou issue d'une formule |
| **MACHINE-DEP** | Oui (chaque re-exec, chaque machine) | Unite `ms`/`s`/`min`/`sec`/`us`/`ns` ou contexte `benchmark`/`perf`/`timing`/`runtime`/`execution` |
| **ENV-DEP** | Oui (chaque bump de version) | Pattern `X.Y.Z` (3 digits separes par `.`) avec contexte `version`/`numpy`/`python`/`pandas`/`library`/`package` |
| **STOCHASTIQUE-NON-SEEDEE** | Oui (chaque run) | Contexte `fitness`/`reward`/`accuracy`/`score`/`mean` sans mention `seed=` ni `random_state=` |

## Pourquoi ce triage plutot qu'une regle dogmatique

Toutes les valeurs quantitatives ne sont pas equivalentes. Une regle qui
interdirait TOUTES les valeurs en prose ferait perdre de la richesse
pedagogique (le speedup `2.78e24x` du App-11-Picross est structurellement
stable ; le retirer = regression pedagogique). Une regle qui ne ferait rien
laisse la derive se reconstituer apres chaque correction (vague #8052 du
2026-08-04 : 4 PRs pour 4 notebooks, meme symptome). Le triage 4-classes
**applique la regle asymetriquement** : structurel = a garder ;
machine-dep / env-dep / stochastique = a deriver ou retirer.

## Cas ambigus

- `Durée estimée : 45 minutes` (effort etudiant, pacing pedagogique) = **TN structurel/pédagogique**, **hors scope drainage** (arbitrage 2026-08-06 ai-01, cf #9434 thread). Le classifier le classe STRUCTUREL grace au contexte `Durée estimée`.
- Posterieurs bayesiens en minutes (Infer-101 moyennes/variances de trajets) = donnees deterministes, **TN**, classes STRUCTUREL grace au contexte `posterior`/`moyenne`/`variance`.

CLI `--check` avec exit codes 0/1/2 distincts (succes / finding / usage).

## Sortie

JSON structuré par notebook avec `quant_classes` (liste de findings par classe)
+ compteurs par classe. Permet le **recensement chiffre par famille** demande
par #9434 critere d'acceptation #1.

Cf. issue #9434 pour le scope exact et la veine drainage per-notebook CLOSE.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable

# Reutilisation du detecteur v3 (PR #9793 MERGED) pour l'extraction de nombres.
from scan_d5_prose_outputs_alignment import (
    _extract_prose_numbers,
    _parse_fr_number,
    iter_notebooks,
    DEFAULT_INCLUDE_GLOBS,
    DEFAULT_EXCLUDE_DIRS,
)


# --------------------------------------------------------------------------- #
#  Configuration des 4 classes
# --------------------------------------------------------------------------- #

# Regex strictes pour les unites temporelles (machine-dep).
_TIME_UNITS = (
    r"\b\d+\s*(?:ms|millisecondes?|microsecondes?|μs|us)\b",
    r"\b\d+\s*(?:s|sec|secondes?)\b",
    r"\b\d+\s*(?:min|minutes?)\b",
    r"\b\d+\s*(?:h|heures?|hours?)\b",
    r"\b\d+\s*(?:ns|nanosecondes?)\b",
)
TIME_UNIT_RE = re.compile("|".join(_TIME_UNITS), re.IGNORECASE)

# Regex strictes pour les versions (env-dep) — pattern semver simplifie.
SEMVER_RE = re.compile(r"\b\d+\.\d+\.\d+(?:[a-zA-Z0-9._+-]*)?\b")

# Mots-cles contextuels pour MACHINE-DEP (au-dela des unites temporelles).
MACHINE_DEP_KEYWORDS = (
    "benchmark", "perf", "performance", "timing", "runtime", "execution time",
    "elapsed", "durée d'exécution", "wall clock", "cpu time", "wall-time",
    "wall_clock",
    "exécute", "execute", "tourne", "run", "runs", "prend", "dure",
    "takes", "took", "spent", "spent time",
)

# Mots-cles contextuels pour ENV-DEP (au-dela du pattern semver).
ENV_DEP_KEYWORDS = (
    "version", "numpy", "python", "pandas", "scipy", "sklearn", "torch",
    "tensorflow", "jax", "matplotlib", "library", "package", "module",
    "dépendance", "depend", "installed", "installée",
)

# Mots-cles contextuels pour STOCHASTIQUE-NON-SEEDEE.
STOCH_KEYWORDS = (
    "fitness", "reward", "accuracy", "score", "loss", "moyenne",
    "mean", "monte-carlo", "monte carlo", "sampling", "tirage",
    "random", "aléatoire", "stochastique",
)

# Mots-cles STRUCTUREL (a garder) — preuve pedagogique.
STRUCT_KEYWORDS = (
    "théorique", "theorique", "théoriquement", "structurel", "structurel",
    "ordre de grandeur", "combinaisons", "combinatorial", "combinatoire",
    "durée estimée", "durée de l'exercice", "effort estimé",
    "pédagogique", "pedagogique", "pacing", "soutenance",
    "posterior", "postérieur", "vraisemblance", "likelihood",
    "moyenne", "variance", "espérance", "esperance", "expected value",
    "formule", "formula", "théorème", "theoreme",
)

# Mots-cles SEED — si présents, le stochastique est seede et donc STRUCTUREL.
SEED_KEYWORDS = ("seed=", "random_state=", "np.random.seed", "torch.manual_seed",
                 "tf.random.set_seed", "rng.seed", "np_seed")


# --------------------------------------------------------------------------- #
#  Dataclasses
# --------------------------------------------------------------------------- #


QUANT_CLASSES = ("STRUCTUREL", "MACHINE-DEP", "ENV-DEP", "STOCHASTIQUE-NON-SEEDEE")


@dataclass
class QuantClassFinding:
    """Un cas de valeur quantitative classifie."""
    notebook: str
    cell_index: int
    cell_kind: str = "markdown"
    value: float = 0.0
    raw_match: str = ""
    quant_class: str = "UNKNOWN"
    context_prefix: str = ""
    context_suffix: str = ""
    rationale: str = ""


@dataclass
class NotebookQuantClasses:
    """Resultat d'analyse d'un notebook."""
    path: str
    total_findings: int = 0
    findings: list[QuantClassFinding] = field(default_factory=list)
    by_class: dict[str, int] = field(default_factory=dict)
    n_markdown_cells: int = 0
    n_code_cells: int = 0
    error: str | None = None


# --------------------------------------------------------------------------- #
#  Extraction du contexte
# --------------------------------------------------------------------------- #


def _extract_context(text: str, match_start: int, match_end: int, window: int = 40) -> tuple[str, str]:
    """Renvoie (prefix, suffix) de longueur `window` autour d'un match.

    Coupe aux frontières de mot (whitespace) pour eviter de couper au milieu
    d'un mot et donner un contexte decibale.
    """
    # prefix : on remonte jusqu'au debut de la ligne ou `window` chars.
    prefix_start = max(text.rfind("\n", 0, match_start) + 1, match_start - window)
    prefix = text[prefix_start:match_start]
    # suffix : jusqu'à la fin de la ligne ou `window` chars.
    suffix_end_nl = text.find("\n", match_end)
    suffix_end = suffix_end_nl if suffix_end_nl != -1 else match_end + window
    suffix_end = min(suffix_end, match_end + window)
    suffix = text[match_end:suffix_end]
    return prefix.lower(), suffix.lower()


def _classify_quant_value(
    raw: str, value: float, prefix: str, suffix: str
) -> tuple[str, str]:
    """Classifie une valeur quantitative selon le contexte. Renvoie (classe, rationale).

    Ordre d'application des regles (la premiere qui matche gagne) :
    1. STRUCTUREL si mot-cle structurel detecte dans prefix+suffix
    2. SEED dans prefix → bascule STOCHASTIQUE → STRUCTUREL
    3. ENV-DEP si pattern semver ou mot-cle env
    4. MACHINE-DEP si unite temporelle ou mot-cle machine-dep
    5. STOCHASTIQUE-NON-SEEDEE si mot-cle stochastique
    6. STRUCTUREL par defaut (classe residuelle surete)

    Le defaut STRUCTUREL evite les faux positifs massifs sur les valeurs
    qui ne sont aucunement concernees (ex. « Le dataset contient 1000 images »).
    """
    full_context = (prefix + " " + suffix).lower()

    # 0. Filtre semver : si le raw match EST un semver, c'est env-dep en soi.
    if SEMVER_RE.fullmatch(raw):
        return ("ENV-DEP", f"semver pattern match: {raw!r}")

    # 1. STRUCTUREL explicite
    for kw in STRUCT_KEYWORDS:
        if kw in full_context:
            return ("STRUCTUREL", f"mot-cle structurel: {kw!r}")

    # 2. SEED → stochastique seede → STRUCTUREL
    for kw in SEED_KEYWORDS:
        if kw in full_context:
            return ("STRUCTUREL", f"stochastique seede via {kw!r}")

    # 3. ENV-DEP (mots-cles env)
    for kw in ENV_DEP_KEYWORDS:
        if kw in full_context:
            return ("ENV-DEP", f"mot-cle env: {kw!r}")

    # 4. MACHINE-DEP (unites temporelles + mots-cles perf)
    if TIME_UNIT_RE.search(raw) or TIME_UNIT_RE.search(prefix + suffix):
        return ("MACHINE-DEP", f"unite temporelle detectee: {raw!r}")
    for kw in MACHINE_DEP_KEYWORDS:
        if kw in full_context:
            return ("MACHINE-DEP", f"mot-cle machine-dep: {kw!r}")

    # 5. STOCHASTIQUE-NON-SEEDEE
    for kw in STOCH_KEYWORDS:
        if kw in full_context:
            return ("STOCHASTIQUE-NON-SEEDEE", f"mot-cle stochastique: {kw!r}")

    # 6. STRUCTUREL par defaut (classe residuelle)
    return ("STRUCTUREL", "defaut (aucun signal machine-dep/env-dep/stochastique)")


# --------------------------------------------------------------------------- #
#  Analyse notebook
# --------------------------------------------------------------------------- #


def analyze_notebook_quant(path: str | os.PathLike) -> NotebookQuantClasses:
    """Analyse les valeurs quantitatives d'un notebook et les classifie."""
    p = Path(path)
    result = NotebookQuantClasses(path=str(path))
    try:
        nb = json.loads(p.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError) as exc:
        result.error = f"{type(exc).__name__}: {exc}"
        return result

    cells = nb.get("cells") or []
    result.n_markdown_cells = sum(1 for c in cells if c.get("cell_type") == "markdown")
    result.n_code_cells = sum(1 for c in cells if c.get("cell_type") == "code")

    findings: list[QuantClassFinding] = []
    by_class: dict[str, int] = {cls: 0 for cls in QUANT_CLASSES}

    for i, c in enumerate(cells):
        if c.get("cell_type") != "markdown":
            continue
        source = c.get("source") or []
        text = "".join(source) if isinstance(source, list) else str(source)
        if not text:
            continue
        # Reutilisation de l'extraction D5 v3 (qui filtre les annees, #issues,
        # PRJ42, semver simplifie stricte, etc.) — mais on doit scanner le
        # texte brut pour les versions, donc on **re-scan** avec nos propres
        # regex par-dessus les nombres deja extraits.
        for m in re.finditer(
            r"(?<![A-Za-z0-9_])-?\d+(?:[.,]\d+)?(?:[eE][-+]?\d+)?(?![A-Za-z0-9_])",
            text,
        ):
            raw = m.group(0)
            v = _parse_fr_number(raw)
            if v is None:
                continue
            # Skip les annees (4 chiffres) et autres bruits basiques.
            if re.fullmatch(r"\d{4}", raw) and 1900 <= v <= 2099:
                continue
            prefix, suffix = _extract_context(text, m.start(), m.end())
            cls, rationale = _classify_quant_value(raw, v, prefix, suffix)
            # Tronque le snippet pour le rapport.
            snippet = text.strip().splitlines()
            snippet_str = next((ln.strip() for ln in snippet if ln.strip()), "")[:120]
            findings.append(QuantClassFinding(
                notebook=str(path),
                cell_index=i,
                value=v,
                raw_match=raw,
                quant_class=cls,
                context_prefix=prefix[-40:],
                context_suffix=suffix[:40],
                rationale=rationale,
            ))
            by_class[cls] += 1

    result.findings = findings
    result.total_findings = len(findings)
    result.by_class = by_class
    return result


# --------------------------------------------------------------------------- #
#  Walk corpus (reutilise iter_notebooks du detecteur v3)
# --------------------------------------------------------------------------- #


def scan_corpus_quant(
    root: str | os.PathLike,
    include_globs: tuple[str, ...] = DEFAULT_INCLUDE_GLOBS,
    exclude_dirs: tuple[str, ...] = DEFAULT_EXCLUDE_DIRS,
) -> list[NotebookQuantClasses]:
    """Scan a corpus root, return list of NotebookQuantClasses."""
    root_path = Path(root)
    results: list[NotebookQuantClasses] = []
    for nb_path in iter_notebooks(root_path, include_globs, exclude_dirs):
        results.append(analyze_notebook_quant(nb_path))
    return results


# --------------------------------------------------------------------------- #
#  Reporting
# --------------------------------------------------------------------------- #


def render_text_report(results: list[NotebookQuantClasses]) -> str:
    """Format results as markdown text avec compteurs par classe."""
    total_findings = sum(r.total_findings for r in results)
    global_by_class: dict[str, int] = {cls: 0 for cls in QUANT_CLASSES}
    n_drainable = 0  # MACHINE-DEP + ENV-DEP + STOCHASTIQUE-NON-SEEDEE
    for r in results:
        for cls, n in r.by_class.items():
            global_by_class[cls] += n
        n_drainable += (
            r.by_class.get("MACHINE-DEP", 0)
            + r.by_class.get("ENV-DEP", 0)
            + r.by_class.get("STOCHASTIQUE-NON-SEEDEE", 0)
        )
    n_pathological = sum(
        1 for r in results if r.by_class.get("MACHINE-DEP", 0)
        + r.by_class.get("ENV-DEP", 0)
        + r.by_class.get("STOCHASTIQUE-NON-SEEDEE", 0) > 0
    )

    lines: list[str] = []
    lines.append(f"Total notebooks analyses : {len(results)}")
    lines.append(f"Notebooks avec >= 1 valeur drainable (MACHINE/ENV/STOCH) : {n_pathological}")
    lines.append(f"Total findings : {total_findings}")
    lines.append("Repartition par classe :")
    for cls in QUANT_CLASSES:
        lines.append(f"  - {cls} : {global_by_class[cls]}")
    lines.append(f"  - TOTAL drainable : {n_drainable}")
    lines.append("")
    lines.append("## Top 10 notebooks avec le plus de valeurs drainables")
    lines.append("")
    lines.append("| Notebook | MACHINE | ENV | STOCH | Total drainable |")
    lines.append("|---|---|---|---|---|")
    top = sorted(
        results,
        key=lambda r: -(r.by_class.get("MACHINE-DEP", 0)
                        + r.by_class.get("ENV-DEP", 0)
                        + r.by_class.get("STOCHASTIQUE-NON-SEEDEE", 0)),
    )
    for r in top[:10]:
        drainable = (
            r.by_class.get("MACHINE-DEP", 0)
            + r.by_class.get("ENV-DEP", 0)
            + r.by_class.get("STOCHASTIQUE-NON-SEEDEE", 0)
        )
        if drainable == 0:
            continue
        lines.append(
            f"| `{os.path.basename(r.path)}` | {r.by_class.get('MACHINE-DEP', 0)} | "
            f"{r.by_class.get('ENV-DEP', 0)} | {r.by_class.get('STOCHASTIQUE-NON-SEEDEE', 0)} | "
            f"{drainable} |"
        )
    return "\n".join(lines) + "\n"


# --------------------------------------------------------------------------- #
#  CLI
# --------------------------------------------------------------------------- #


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--root", default="MyIA.AI.Notebooks",
        help="Racine du corpus a scanner (defaut: MyIA.AI.Notebooks).",
    )
    parser.add_argument(
        "--notebook", help="Cible un notebook precis (sinon full-corpus).",
    )
    parser.add_argument(
        "--json-out", help="Ecrire le rapport JSON a ce chemin.",
    )
    parser.add_argument(
        "--check", action="store_true",
        help="Mode CI : exit 1 si >= 1 valeur MACHINE-DEP/ENV-DEP/STOCHASTIQUE.",
    )
    parser.add_argument(
        "--limit", type=int, default=0,
        help="Limiter le nombre de notebooks analyses (0 = pas de limite).",
    )
    args = parser.parse_args(list(argv) if argv is not None else None)
    root = Path(args.root)
    if not root.exists():
        print(f"ERREUR: racine '{root}' inexistante.", file=sys.stderr)
        return 2
    if args.notebook:
        nb_path = Path(args.notebook)
        if not nb_path.exists():
            print(f"ERREUR: notebook '{nb_path}' inexistant.", file=sys.stderr)
            return 2
        results = [analyze_notebook_quant(nb_path)]
    else:
        results = scan_corpus_quant(root)
        if args.limit > 0:
            results = results[:args.limit]

    if args.json_out:
        Path(args.json_out).write_text(json.dumps([
            {
                "path": r.path,
                "total_findings": r.total_findings,
                "by_class": r.by_class,
                "n_markdown_cells": r.n_markdown_cells,
                "n_code_cells": r.n_code_cells,
                "findings": [
                    {
                        "cell_index": f.cell_index,
                        "value": f.value,
                        "raw_match": f.raw_match,
                        "quant_class": f.quant_class,
                        "context_prefix": f.context_prefix,
                        "context_suffix": f.context_suffix,
                        "rationale": f.rationale,
                    }
                    for f in r.findings
                ],
                "error": r.error,
            }
            for r in results
        ], indent=2, ensure_ascii=False), encoding="utf-8")

    print(render_text_report(results))
    if args.check:
        drainable = sum(
            r.by_class.get("MACHINE-DEP", 0)
            + r.by_class.get("ENV-DEP", 0)
            + r.by_class.get("STOCHASTIQUE-NON-SEEDEE", 0)
            for r in results
        )
        if drainable > 0:
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
