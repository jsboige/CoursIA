#!/usr/bin/env python3
"""Mesure la visibilite des lakes Lean dans le corpus de notebooks.

Un lake enrichi n'existe, pour un lecteur, que si un notebook le montre.
Ce script mesure combien de declarations de chaque `*_lean/` sont citees
quelque part dans les `*.ipynb` du depot, et surtout quels modules ne le
sont **pas du tout** (metrique de tete : un module a 0 est un travail
formel invisible ; un ratio de citation eleve n'est pas l'objectif).

Deux bornes sont rendues, parce qu'un nom court et generique (`map`,
`add`) peut coincider par hasard dans un notebook sans rapport :

  cite_large  : tout nom trouve                     (borne haute)
  cite_strict : noms distinctifs (>=10 car. ou '_') (borne basse)

CONTROLE POSITIF : le script verifie dans la meme invocation que des noms
connus-presents sont bien extraits ET bien trouves, et sort en erreur
sinon. Un zero rendu par un instrument casse est indiscernable d'un zero
mesure -- c'est exactement le defaut que ce garde ferme (cf EPIC #11703).

Usage:
    python scripts/lean/scan_lake_notebook_visibility.py [--json OUT] [--lake NAME]
    python scripts/lean/scan_lake_notebook_visibility.py --pr-base <sha> [--pr-head <sha>] [--json OUT]

Mode --pr-base (acceptance 3 de l'EPIC #11703) : liste les declarations
AJOUTEES par le diff base...head sur les lakes `*_lean/` qui ne sont citees
dans AUCUN notebook du checkout, a la borne large (tout nom trouve). Un nom
invisible meme a la borne large est invisible partout : c'est le signal
le moins bruite possible, et le payload du workflow advisory
lean-visibility-advisory.yml.
"""
from __future__ import annotations

import argparse
import collections
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
NB_ROOT = ROOT / "MyIA.AI.Notebooks"

EXCLUDED = (
    ".lake/packages",       # Mathlib vendored
    "_peters",              # lake externe
    "reference_docs",       # fixtures tierces du prover
    "foundry-lib/lib",      # libs vendored
    ".ipynb_checkpoints",
)

_MODIFIERS = r"(?:private|protected|noncomputable|partial|unsafe|scoped|local)"
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:" + _MODIFIERS + r"\s+)*"
    r"(theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*)"
)
TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")

# (nom, lake) connus presents dans les .lean ET cites par un notebook.
POSITIVE_CONTROL = [("mimoObj", "mimo_lean"), ("flipAt", "mimo_lean")]


def _excluded(path: Path) -> bool:
    s = str(path).replace("\\", "/")
    return any(e in s for e in EXCLUDED)


def is_distinctive(name: str) -> bool:
    """Un nom assez specifique pour qu'une occurrence ne soit pas fortuite."""
    return len(name) >= 10 or "_" in name


def collect_declarations() -> dict[str, dict[str, set[str]]]:
    """lake -> module -> {noms de declarations}. Les siblings `_en.lean`
    (convention i18n #4980) sont ignores : meme substance, compte double."""
    lakes: dict[str, dict[str, set[str]]] = collections.defaultdict(
        lambda: collections.defaultdict(set)
    )
    for f in NB_ROOT.rglob("*.lean"):
        if _excluded(f) or f.name.endswith("_en.lean"):
            continue
        parts = str(f.relative_to(NB_ROOT)).replace("\\", "/").split("/")
        lake = next((p for p in parts if p.endswith("_lean")), None)
        if lake is None:
            continue
        for line in f.read_text(encoding="utf-8", errors="replace").splitlines():
            m = DECL_RE.match(line)
            if m:
                lakes[lake][f.name].add(m.group(2))
    return lakes


def collect_notebook_tokens(names: set[str]):
    """Renvoie (tokens vus, lake_candidate -> Counter(notebook -> hits))."""
    seen: set[str] = set()
    per_nb: dict[str, collections.Counter] = collections.defaultdict(collections.Counter)
    count = 0
    for nb in NB_ROOT.rglob("*.ipynb"):
        if _excluded(nb):
            continue
        count += 1
        toks = set(TOKEN_RE.findall(nb.read_text(encoding="utf-8", errors="replace")))
        seen |= toks
        rel = str(nb.relative_to(NB_ROOT)).replace("\\", "/")
        for n in toks & names:
            if is_distinctive(n):
                per_nb[n][rel] += 1
    return seen, per_nb, count


def names_from_unified_diff(diff_text: str) -> dict[str, set[str]]:
    """Declarations AJOUTEES par un diff unifie, par fichier lake.

    Meme filtre que collect_declarations (exclusions canoniques, suffixe
    `_lean`, siblings `_en.lean` ignores) et meme DECL_RE : le signal PR et
    la metrique de tete ne peuvent pas diverger d'extracteur.
    """
    added: dict[str, set[str]] = collections.defaultdict(set)
    path: str | None = None
    for line in diff_text.splitlines():
        if line.startswith("+++ b/"):
            path = line[6:]
            continue
        if line.startswith("+++") or line.startswith("---"):
            continue
        if path is None:
            continue
        if not line.startswith("+"):
            if line.startswith("diff --git"):
                path = None
            continue
        m = DECL_RE.match(line[1:])
        if m:
            added[path].add(m.group(2))
    out: dict[str, set[str]] = {}
    for p, names in added.items():
        if p.endswith("_en.lean") or _excluded(p):
            continue
        parts = p.split("/")
        if not any(seg.endswith("_lean") for seg in parts):
            continue
        out[p] = names
    return out


def run_pr_diff(base: str, head: str) -> str:
    """Diff unifie 3-points base...head limite aux .lean (depuis ROOT)."""
    proc = subprocess.run(
        ["git", "diff", "--unified=0", f"{base}...{head}", "--", "*.lean"],
        cwd=ROOT, capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    if proc.returncode != 0:
        raise RuntimeError(f"git diff {base}...{head} a echoue: {proc.stderr.strip()}")
    return proc.stdout


def main_pr_mode(base: str, head: str, out_path: str | None) -> int:
    diff_text = run_pr_diff(base, head)
    added = names_from_unified_diff(diff_text)
    all_names = set().union(*added.values()) if added else set()
    seen, _, n_notebooks = collect_notebook_tokens(all_names)
    if n_notebooks == 0:
        print("ERREUR: aucun notebook lu -- instrument casse, pas un resultat.", file=sys.stderr)
        return 2

    rows = []
    for p in sorted(added):
        lake = next(seg for seg in p.split("/") if seg.endswith("_lean"))
        for n in sorted(added[p]):
            rows.append({"lake": lake, "file": p, "name": n, "cited": n in seen})
    uncited = [r for r in rows if not r["cited"]]

    print(f"{n_notebooks} notebooks lus ; {len(rows)} declaration(s) ajoutee(s) "
          f"sur les lakes dans base...{head[:10]}")
    if not rows:
        print("Aucune declaration ajoutee sur un lake -- rien a signaler.")
    for r in uncited:
        print(f"  AJOUTEE NON CITEE: {r['name']}  ({r['lake']}/{Path(r['file']).name})")
    if rows:
        print(f"TOTAL ajoutees: {len(rows)}  non citees (borne large): {len(uncited)}")

    if out_path:
        Path(out_path).write_text(
            json.dumps({"added": len(rows), "uncited": len(uncited), "detail": uncited},
                       indent=1, ensure_ascii=False),
            encoding="utf-8",
        )
        print(f"detail -> {out_path}")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--json", dest="out", help="ecrire le detail machine-lisible ici")
    ap.add_argument("--lake", help="restreindre l'affichage a un lake")
    ap.add_argument("--pr-base", dest="pr_base",
                    help="mode PR : declarations ajoutees par le diff base...HEAD non citees")
    ap.add_argument("--pr-head", dest="pr_head", default="HEAD",
                    help="tete du diff en mode PR (defaut: HEAD)")
    args = ap.parse_args()

    if args.pr_base:
        return main_pr_mode(args.pr_base, args.pr_head, args.out)

    lakes = collect_declarations()
    if not lakes:
        print("ERREUR: aucun lake trouve -- instrument casse, pas un resultat.", file=sys.stderr)
        return 2

    owner = {}
    for lake, mods in lakes.items():
        for mod, names in mods.items():
            for n in names:
                owner.setdefault(n, (lake, mod))

    seen, per_nb, n_notebooks = collect_notebook_tokens(set(owner))

    # --- controle positif : un zero doit etre une mesure, jamais une panne ---
    for name, lake in POSITIVE_CONTROL:
        extracted = set().union(*lakes.get(lake, {}).values()) if lake in lakes else set()
        if name not in extracted:
            print(f"CONTROLE POSITIF KO: '{name}' non extrait de {lake} "
                  f"-- l'extracteur a une lacune, le resultat est faux.", file=sys.stderr)
            return 2
        if name not in seen:
            print(f"CONTROLE POSITIF KO: '{name}' absent du corpus notebooks "
                  f"-- le scan de notebooks n'a pas lu ce qu'il croit avoir lu.", file=sys.stderr)
            return 2

    rows, out = [], {}
    for lake in sorted(lakes):
        names = set().union(*lakes[lake].values())
        distinct = {n for n in names if is_distinctive(n)}
        cite_large = sum(1 for n in names if n in seen)
        cite_strict = sum(1 for n in distinct if n in seen)
        dark = [m for m, v in sorted(lakes[lake].items())
                if v and not any(n in seen and is_distinctive(n) for n in v)]
        top = collections.Counter()
        for n in distinct & seen:
            top.update(per_nb.get(n, {}))
        companion = top.most_common(1)
        rows.append((lake, len(names), cite_large, cite_strict, dark, companion))
        out[lake] = {
            "declarations": len(names), "distinctive": len(distinct),
            "cite_large": cite_large, "cite_strict": cite_strict,
            "modules": len(lakes[lake]), "dark_modules": dark,
            "companion_notebook": companion[0][0] if companion else None,
        }

    print(f"{n_notebooks} notebooks lus, {len(lakes)} lakes, {len(owner)} declarations\n")
    print(f"{'lake':24} {'decl':>5} {'large':>6} {'strict':>7} {'noirs':>6}  compagnon principal")
    for lake, tot, cl, cs, dark, comp in sorted(rows, key=lambda r: r[3] / r[1] if r[1] else 1):
        if args.lake and lake != args.lake:
            continue
        c = comp[0][0] if comp else "-- AUCUN --"
        print(f"{lake:24} {tot:5} {cl:6} {cs:7} {len(dark):3}/{out[lake]['modules']:<3} {c}")
        if args.lake:
            for m in dark:
                print(f"    module invisible: {m} ({len(lakes[lake][m])} declarations)")

    T = sum(r[1] for r in rows)
    print(f"\nTOTAL {sum(r[2] for r in rows)}/{T} (borne haute)  "
          f"{sum(r[3] for r in rows)}/{T} (borne basse)  "
          f"modules invisibles: {sum(len(r[4]) for r in rows)}/"
          f"{sum(len(lakes[l]) for l in lakes)}")

    if args.out:
        Path(args.out).write_text(json.dumps(out, indent=1, ensure_ascii=False), encoding="utf-8")
        print(f"\ndetail -> {args.out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
