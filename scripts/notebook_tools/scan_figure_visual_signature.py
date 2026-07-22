#!/usr/bin/env python3
"""Auditeur de signature visuelle des figures PNG (consolidation L777-L1 / L778-L1/L2 / L779-L1/L2 / L780-L1/L2/L3 / L781-L1/L2/L3).

Pourquoi cet outil existe
-------------------------
Le rollout MANIFEST-desc-visuelle (c.754-c.781+, EPIC #5780) a accumule 5
cycles de stats RGB PIL sur les figures des MANIFESTs (ML.Net, ML racine,
IIT/ICT-Series, Probas/DecisionTheory/PyMC, Search/Applications,
QuantConnect/Python). Chaque cycle (c.777+) a developpe un script ad-hoc
dans le scratchpad du worker (`pil_stats_<famille>.py`) qui samplait
2000 pixels random seed 42 et sortait mean R/G/B + std R/G/B. Les 5
cycles ont distille 7 tells discriminants :

  - L777-L1 ★★   : stats RGB PIL = signature discriminante des palettes
                    matplotlib (std faible = scatter epars monochrome,
                    std eleve = zones colorees pleines).
  - L778-L1 ★★   : sub-genre MANIFEST-desc-visuelle recurrent OK si
                    famille distincte + vision-QA fresh (rollout c.754+).
  - L778-L2 ★    : heatmap `imshow` detectable via mean RGB < 100
                    (dark-field dominant). Tell discriminant : mean < 100
                    => imshow, pas courbe plot().
  - L779-L1 ★    : heatmap dense YlOrRd/Viridis/Plasma = mean RGB
                    ~200-250 + std B > 50 sur fond clair (distinct du
                    dark-field mean < 100).
  - L779-L2 ★    : courbe bleu dominant = B mean > R mean + 5.
  - L780-L1 ★    : palette achrome = mean R = mean G = mean B EXACT
                    (>=2000 pixels, sans teinte, distinct des palettes
                    categorielles).
  - L780-L2 ★    : niveau 2D procedural dense multi-couleurs = mean
                    R/G/B ~100-180 + std 50+ (ni fond clair >240, ni
                    dark-field <100).
  - L780-L3 ★    : graphe academique sur blanc = mean R/G/B >=249 +
                    std ~20-30 (nuds minoritaires, fond blanc dominant).
  - L781-L1 ★    : bar chart bleu dominant seaborn-darkgrid = mean B >
                    mean G > mean R + std R > 50 (vs courbe simple ou
                    std R < 30).
  - L781-L2 ★    : matplotlib blanc = mean R = G = B ~248 + std
                    uniforme ~31 (style default ou seaborn-whitegrid).
  - L781-L3 ★    : stacked area orange seaborn-darkgrid = R mean > G
                    mean > B mean + std B > 50 (orange #FFA07A tire R
                    vers le haut, contraste avec fond violet fait monter
                    std B).

Ces tells sont maintenant figes et reproducibles : un auditeur peut
ingester un PNG et dire "ce visuel est compatible avec tel type de
rendu matplotlib, palette tell = X". C'est l'objet de ce script -- il
consolide les 7 ad-hoc en un outil de la partition notebook_tools,
CI-ready (`--check` exit code), et utilisable par les futurs agents
qui auditeront les figures (README, slides, gallery, dashboard).

Ce qu'il DETECTE (deterministe)
-------------------------------
Pour un PNG donne (ou un dossier de PNG), le script echantillonne 2000
pixels random seed 42 et sort un rapport structure (JSON ou texte) :

  - mean R/G/B + std R/G/B (les 6 chiffres bruts, source de verite)
  - dimensions W x H
  - liste des tells discriminations detectes (parmi les 9 ci-dessus)
  - score de confiance 0-1 par tell (force de la discrimination)

Ce qu'il NE fait PAS (par design)
---------------------------------
- Pas de vision semantique : on ne "voit" pas l'image, on classifie
  la palette via stats RGB. Les tells sont des heuristiques, pas
  une lecture de la composition structurelle.
- Pas de scrub / correction : comme les autres detecteurs de la
  partition (detect_blank_figures.py, detect_fabricated_outputs.py,
  etc.), on signale, on ne modifie pas. La correction = audit visuel
  humain (MiniMax M3 / ai-01) + Stop&Repair si necessaire.
- Pas de classification "valide/invalide" : on rapporte les tells,
  on laisse l'humain conclure (le label "correctement matplotlib" vs
  "degenere" reste un jugement, pas une machine).

Usage
-----
  # Rapport JSON sur une figure
  python scripts/notebook_tools/scan_figure_visual_signature.py path/to/figure.png

  # Rapport texte structure (lecture humaine)
  python scripts/notebook_tools/scan_figure_visual_signature.py --format text path/to/figure.png

  # Scan recursif d'un dossier de PNG
  python scripts/notebook_tools/scan_figure_visual_signature.py path/to/dir/ --recursive

  # CI check : exit 0 si tous les PNG ont des tells detectes, exit 1
  # sinon (utilise pour auditer les MANIFEST figures avant PR)
  python scripts/notebook_tools/scan_figure_visual_signature.py --check path/to/dir/

Le check CI considere qu'un PNG "analyse avec succes" est un PNG dont
les stats sont sorties (meme si aucun tell ne matche -- toutes les
figures ne sont pas discriminantes par tell). Le check echoue sur
erreur de lecture / fichier non-PNG / dossier vide.

Sortie type
-----------
  {
    "path": "MyIA.AI.Notebooks/Search/Applications/assets/readme/app11-picross-grid.png",
    "dimensions": [567, 590],
    "mean_rgb": [231.87, 231.87, 231.87],
    "std_rgb": [27.86, 27.86, 27.86],
    "tells_detected": [
      {"name": "achrome_palette", "confidence": 1.0, "lesson": "L780-L1"}
    ],
    "n_samples": 2000,
    "seed": 42
  }

Voir aussi
----------
- scripts/notebook_tools/detect_blank_figures.py -- sibling detector
  Prong-A, degenerescence dimension/taille
- scripts/notebook_tools/detect_fabricated_outputs.py -- sibling
  detector Prong-A, fabrication textuelle (Row N placeholder)
- scripts/notebook_tools/scan_md_hierarchy.py -- scanner structurel
  hierarchie markdown (H1-DEEP / HINT-AS-HEADING / MULTI-H1)
- .claude/rules/sota-not-workaround.md -- Prong A "vrai outil SOTA"
  + Prong B "probleme non-trivial"
- docs/reference/notebook-formatting.md -- EPIC #3966 mise en forme
  visuelle des notebooks
- MEMORY.md section "Lecons durables" -- L777-L1 a L781-L3
"""
from __future__ import annotations

import argparse
import json
import os
import random
import statistics
import sys
from typing import Any


# -----------------------------------------------------------------------------
# Tells catalogues (consolidation L777-L1 / L778-L1/L2 / L779-L1/L2 /
# L780-L1/L2/L3 / L781-L1/L2/L3)
# -----------------------------------------------------------------------------

TELLS: list[dict[str, Any]] = [
    {
        "name": "heatmap_imshow_darkfield",
        "lesson": "L778-L2",
        "description": "Heatmap `imshow` dark-field dominant (mean RGB < 100)",
        "predicate": lambda stats: stats["mean_r"] < 100
        and stats["mean_g"] < 100
        and stats["mean_b"] < 100,
    },
    {
        "name": "matplotlib_blanc_whitegrid",
        "lesson": "L781-L2",
        "description": "matplotlib blanc tell (mean R = G = B ~ 248, std uniforme)",
        "predicate": lambda stats: abs(stats["mean_r"] - 248) < 5
        and abs(stats["mean_g"] - 248) < 5
        and abs(stats["mean_b"] - 248) < 5
        and abs(stats["std_r"] - stats["std_g"]) < 8
        and abs(stats["std_g"] - stats["std_b"]) < 8,
    },
    {
        "name": "graphe_academique_blanc",
        "lesson": "L780-L3",
        "description": "Graphe academique sur blanc (mean >= 249, std 20-30)",
        "predicate": lambda stats: stats["mean_r"] >= 249
        and stats["mean_g"] >= 249
        and stats["mean_b"] >= 249
        and 15 <= stats["std_r"] <= 35
        and 15 <= stats["std_g"] <= 35
        and 15 <= stats["std_b"] <= 35,
    },
    {
        "name": "achrome_palette",
        "lesson": "L780-L1",
        "description": "Palette achrome (mean R = G = B EXACT, pas de teinte)",
        "predicate": lambda stats: abs(stats["mean_r"] - stats["mean_g"]) < 0.5
        and abs(stats["mean_g"] - stats["mean_b"]) < 0.5
        and abs(stats["mean_r"] - stats["mean_b"]) < 0.5,
    },
    {
        "name": "bar_chart_bleu_dominant_seaborn",
        "lesson": "L781-L1",
        "description": "Bar chart bleu dominant seaborn-darkgrid (mean B > G > R, std R > 50)",
        "predicate": lambda stats: stats["mean_b"] > stats["mean_g"]
        and stats["mean_g"] > stats["mean_r"]
        and stats["std_r"] > 50,
    },
    {
        "name": "courbe_bleu_dominant",
        "lesson": "L779-L2",
        "description": "Courbe bleu dominant (B mean > R mean + 5)",
        "predicate": lambda stats: stats["mean_b"] > stats["mean_r"] + 5,
    },
    {
        "name": "stacked_area_orange_seaborn",
        "lesson": "L781-L3",
        "description": "Stacked area orange seaborn-darkgrid (R > G > B + std B > 50)",
        "predicate": lambda stats: stats["mean_r"] > stats["mean_g"]
        and stats["mean_g"] > stats["mean_b"]
        and stats["std_b"] > 50,
    },
    {
        "name": "niveau_2d_procedural_dense",
        "lesson": "L780-L2",
        "description": "Niveau 2D procedural dense multi-couleurs (mean 100-180, std 50+)",
        "predicate": lambda stats: 100 <= stats["mean_r"] <= 180
        and 100 <= stats["mean_g"] <= 180
        and 100 <= stats["mean_b"] <= 180
        and stats["std_r"] > 50
        and stats["std_g"] > 50
        and stats["std_b"] > 50,
    },
    {
        "name": "heatmap_dense_ylorrd",
        "lesson": "L779-L1",
        "description": "Heatmap dense YlOrRd/Viridis/Plasma (mean 200-250, std B > 50)",
        "predicate": lambda stats: 200 <= stats["mean_r"] <= 250
        and stats["mean_g"] < stats["mean_r"]
        and stats["std_b"] > 50,
    },
]


# -----------------------------------------------------------------------------
# Sampling + analyse
# -----------------------------------------------------------------------------


def sample_png(path: str, n_samples: int = 2000, seed: int = 42) -> dict[str, Any] | None:
    """Sample N pixels from PNG, return stats dict or None on error."""
    try:
        from PIL import Image  # local import : dep douce, message clair si absent
    except ImportError:
        print(
            "ERREUR : PIL/Pillow requis. `pip install Pillow` puis reessayer.",
            file=sys.stderr,
        )
        return None

    try:
        img = Image.open(path).convert("RGB")
    except Exception as exc:
        print(f"ERREUR lecture {path}: {exc}", file=sys.stderr)
        return None

    w, h = img.size
    if w == 0 or h == 0:
        print(f"ERREUR dimensions nulles : {path}", file=sys.stderr)
        return None

    random.seed(seed)
    pixels = []
    for _ in range(n_samples):
        x = random.randint(0, w - 1)
        y = random.randint(0, h - 1)
        pixels.append(img.getpixel((x, y)))

    rs = [p[0] for p in pixels]
    gs = [p[1] for p in pixels]
    bs = [p[2] for p in pixels]

    return {
        "width": w,
        "height": h,
        "mean_r": statistics.mean(rs),
        "mean_g": statistics.mean(gs),
        "mean_b": statistics.mean(bs),
        "std_r": statistics.stdev(rs) if len(rs) > 1 else 0.0,
        "std_g": statistics.stdev(gs) if len(gs) > 1 else 0.0,
        "std_b": statistics.stdev(bs) if len(bs) > 1 else 0.0,
        "n_samples": n_samples,
        "seed": seed,
    }


def detect_tells(stats: dict[str, Any]) -> list[dict[str, Any]]:
    """Run all tell predicates, return list of matches with confidence."""
    matches = []
    for tell in TELLS:
        try:
            if tell["predicate"](stats):
                # Confidence = a heuristic ; 1.0 if exactly matches the spec,
                # 0.5-0.9 if "near-match". For now we report 1.0 on strict match
                # since the predicates encode the lessons faithfully.
                matches.append(
                    {
                        "name": tell["name"],
                        "lesson": tell["lesson"],
                        "description": tell["description"],
                        "confidence": 1.0,
                    }
                )
        except Exception:
            # predicate failed (e.g. division by zero) -> skip silently
            continue
    return matches


def scan_path(path: str, recursive: bool = False) -> list[str]:
    """Return list of PNG paths to scan (file or dir [+ recursive])."""
    if os.path.isfile(path):
        return [path] if path.lower().endswith(".png") else []
    if os.path.isdir(path):
        pngs: list[str] = []
        if recursive:
            for root, _dirs, files in os.walk(path):
                for fn in files:
                    if fn.lower().endswith(".png"):
                        pngs.append(os.path.join(root, fn))
        else:
            for fn in os.listdir(path):
                if fn.lower().endswith(".png"):
                    pngs.append(os.path.join(path, fn))
        pngs.sort()
        return pngs
    return []


def render_report(path: str, stats: dict[str, Any], tells: list[dict[str, Any]], fmt: str) -> str:
    if fmt == "json":
        return json.dumps(
            {
                "path": path,
                "dimensions": [stats["width"], stats["height"]],
                "mean_rgb": [round(stats["mean_r"], 2), round(stats["mean_g"], 2), round(stats["mean_b"], 2)],
                "std_rgb": [round(stats["std_r"], 2), round(stats["std_g"], 2), round(stats["std_b"], 2)],
                "tells_detected": tells,
                "n_samples": stats["n_samples"],
                "seed": stats["seed"],
            },
            indent=2,
            ensure_ascii=False,
        )
    # text
    lines = [
        f"=== {path} ===",
        f"  dimensions : {stats['width']} x {stats['height']}",
        f"  mean RGB   : ({stats['mean_r']:.2f}, {stats['mean_g']:.2f}, {stats['mean_b']:.2f})",
        f"  std  RGB   : ({stats['std_r']:.2f}, {stats['std_g']:.2f}, {stats['std_b']:.2f})",
        f"  tells      : {len(tells)} detecte(s)",
    ]
    if tells:
        for t in tells:
            lines.append(f"    - {t['name']} ({t['lesson']}) : {t['description']}")
    else:
        lines.append("    (aucun tell catalogue ne matche les stats ; figure legitime atypique)")
    return "\n".join(lines)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Auditeur de signature visuelle des figures PNG (consolidation L777-L1 / "
            "L778-L1/L2 / L779-L1/L2 / L780-L1/L2/L3 / L781-L1/L2/L3)."
        )
    )
    parser.add_argument("path", help="PNG ou dossier de PNG a scanner")
    parser.add_argument("--recursive", action="store_true", help="Scan recursif si path est un dossier")
    parser.add_argument(
        "--format",
        choices=["json", "text"],
        default="json",
        help="Format de sortie (defaut: json, lecture machine ; text = lecture humaine)",
    )
    parser.add_argument(
        "--n-samples",
        type=int,
        default=2000,
        help="Nombre de pixels echantillonnes (defaut: 2000, cf pattern c.777-c.781)",
    )
    parser.add_argument("--seed", type=int, default=42, help="Seed RNG pour reproductibilite (defaut: 42)")
    parser.add_argument(
        "--check",
        action="store_true",
        help="Mode CI : exit 0 si toutes les figures ont ete scannees avec succes, exit 1 sinon",
    )

    args = parser.parse_args(argv)

    paths = scan_path(args.path, recursive=args.recursive)
    if not paths:
        print(f"Aucun PNG trouve a : {args.path}", file=sys.stderr)
        return 1

    failures = 0
    for path in paths:
        stats = sample_png(path, n_samples=args.n_samples, seed=args.seed)
        if stats is None:
            failures += 1
            continue
        tells = detect_tells(stats)
        print(render_report(path, stats, tells, args.format))

    if args.check and failures > 0:
        print(f"\nCI FAIL : {failures}/{len(paths)} figure(s) illisible(s)", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))