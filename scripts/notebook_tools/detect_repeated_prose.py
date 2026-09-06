#!/usr/bin/env python3
"""Detecteur de prose repetee intra-notebook (« radotage »).

Incident fondateur (demande user 2026-09-05, fix PR #14794) : dans
Search-09c-CombinatorialDiscrepancy.ipynb, la section 5 portait trois puces
« ponts vers le reste du parcours » (funnel PyMC, double-Q MGS, anti-fantome
ICT) qui paraphrasait les trois lignes correspondantes de la table
« 7. Ponts avec le reste de la serie » -- meme contenu, deux habits, deux
cellules d'ecart. Aucune surface de garde existente n'a vu le doublon : ce
n'etait ni un lien casse, ni une erreur d'execution, ni une desaccentuation --
c'est la MEME IDEE dite deux fois, et l'oeil ne la voit plus a la relecture.

Deux signaux, tous deux INTRA-notebook (jamais cross-fichier) :

  A. Bloc verbatim duplique -- un bloc markdown normalise (espacements
     reduits) d'au moins 120 caracteres qui apparait 2+ fois dans le
     notebook. Attrape le copier-coller reflowe.

  B. Bloc paraphrase -- un bloc d'au moins 200 caracteres dont les mots
     pleins RARES (df <= 4 a travers les cellules markdown du notebook)
     sont majoritairement contenus dans une AUTRE cellule markdown
     (containment >= 0.30, au moins 10 mots rares partages). C'est le
     signal qui attrape le cas fondateur : la paraphrase ne partage aucune
     sequence de 4 mots, mais partage son vocabulaire discriminant
     (funnel, pymc, conspiration, fantome, antidote...). Mesure sur le cas
     fondateur : 26 mots rares partages, containment 0.48 ; temoin negatif
     (paragraphe distinct de la meme section) : 3 mots, 0.09.

Pourquoi la rarete (df intra-notebook) : les mots de sujet ('discrepance',
'solution') reviennent partout dans un notebook pedagogique et ne prouvent
rien ; un mot qui n'apparait que dans DEUX endroits du notebook, dont un
bloc-suspicieux, est une empreinte de duplication. Le seuil df <= 4 garde
les vocabulaires de section (3-4 occurrences legitimes) hors du signal.

Portee et cout : scan texte pur (stdlib), O(blocs x cellules) intersections
d'ensembles de <= ~100 mots -- quelques millisecondes par notebook, quelques
secondes pour le corpus entier (mesure en corpus dans le body de la PR de
cablage). Le cablage CI est un garde advisory per-notebook (registre
TRANCHE7) : il signale sur les notebooks TOUCHES par la PR, jamais un scan
repo-wide bloquant.

Codes de retour : 0 = clean ; 1 = fichier illisible/introuvable ou scan
vacuue (aucune cellule markdown) ; 2 = findings (avec --fail-on-findings).
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import time
import unicodedata
from collections import Counter
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

# Mots outils FR + EN. Liste FERMEE, volontairement courte : un mot outil
# oublie ne crée pas de faux positif (il ne compte pas comme rare
# partage s'il revient partout, donc df > 4 le filtre deja).
STOPWORDS = frozenset("""
le la les de des du un une et en dans pour par sur avec ou ou_ au aux ce cette
ces que qui quoi dont est sont sera etre plus moins ne pas non tout tous toute
toutes comme meme aussi alors donc si car mais or ni son sa ses leur leurs il
ils elle elles on nous vous y a c d j l m n s t qu
the of to and in for with or is are was were be been this that these those it
its as an on at by from we you they he she not but can will would should may
might must into over under between each other more most such no only own same
so than too very
""".split())

WORD_RE = re.compile(r"[A-Za-zÀ-ÖØ-öø-ÿœŒæÆ0-9]{2,}")
STRIP_RE = re.compile(
    r"https?://\S+"          # URLs
    r"|\$[^$]*\$"            # maths inline
    r"|\$\$[^$]*\$\$"        # maths display
    r"|`[^`]*`"              # code spans
)

MIN_VERBATIM_CHARS = 120     # signal A
MIN_PARAPHRASE_CHARS = 200   # signal B
MAX_DF = 4                   # rarete intra-notebook
MIN_SHARED_RARE = 10         # signal B : plancher absolu de mots rares partages
MIN_CONTAINMENT = 0.30       # signal B : |shared| / |rare(block)|


def strip_markup(text: str) -> str:
    return STRIP_RE.sub(" ", text)


def content_words(text: str) -> set[str]:
    words = WORD_RE.findall(strip_markup(text).lower())
    return {w for w in words
            if w not in STOPWORDS and not w.isdigit()}


def markdown_cells(nb: dict) -> list[tuple[int, str]]:
    out = []
    for i, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") == "markdown":
            src = cell.get("source", "")
            if isinstance(src, list):
                src = "".join(src)
            out.append((i, src))
    return out


def blocks(text: str) -> list[str]:
    """Decoupe en blocs sur les lignes vides (paragraphe / liste / table)."""
    return [b.strip() for b in re.split(r"\n\s*\n", text) if b.strip()]


def normalize_verbatim(text: str) -> str:
    return " ".join(text.split())


def detect(nb: dict) -> list[dict]:
    """Renvoie les findings d'un notebook (liste, vide = clean)."""
    cells = markdown_cells(nb)
    findings: list[dict] = []

    # --- Signal A : bloc verbatim duplique --------------------------------
    seen: dict[str, list[tuple[int, int]]] = {}
    for ci, text in cells:
        for bi, block in enumerate(blocks(text)):
            if len(block) < MIN_VERBATIM_CHARS:
                continue
            key = normalize_verbatim(block)
            seen.setdefault(key, []).append((ci, bi))
    for key, locs in seen.items():
        if len(locs) >= 2:
            findings.append({
                "type": "verbatim_block",
                "occurrences": [{"cell": ci, "block": bi} for ci, bi in locs],
                "excerpt": key[:80],
                "chars": len(key),
            })

    # --- Signal B : bloc paraphrase ---------------------------------------
    cell_words = {ci: content_words(text) for ci, text in cells}
    df: Counter[str] = Counter()
    for ws in cell_words.values():
        df.update(ws)

    for ci, text in cells:
        for bi, block in enumerate(blocks(text)):
            if len(block) < MIN_PARAPHRASE_CHARS:
                continue
            rare = {w for w in content_words(block) if df[w] <= MAX_DF}
            if len(rare) < MIN_SHARED_RARE:
                continue
            best = None
            for cj, ws_j in cell_words.items():
                if cj == ci:
                    continue
                shared = rare & ws_j
                if len(shared) < MIN_SHARED_RARE:
                    continue
                containment = len(shared) / len(rare)
                if containment < MIN_CONTAINMENT:
                    continue
                if best is None or containment > best["containment"]:
                    best = {
                        "target_cell": cj,
                        "shared_rare": sorted(shared),
                        "containment": round(containment, 2),
                    }
            if best:
                findings.append({
                    "type": "paraphrased_block",
                    "cell": ci,
                    "block": bi,
                    "chars": len(block),
                    **best,
                })
    findings.sort(key=lambda f: (f.get("cell", -1), f["type"]))
    return findings


def load_notebook(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def scan_one(path: Path, as_json: bool) -> tuple[int, str]:
    try:
        nb = load_notebook(path)
    except (OSError, json.JSONDecodeError) as exc:
        return 1, f"illisible : {exc}"
    if not markdown_cells(nb):
        return 1, "aucune cellule markdown (scan vacuue)"
    findings = detect(nb)
    if as_json:
        out = json.dumps(
            {"file": path.as_posix(), "findings": findings,
             "counts": {"total": len(findings),
                        "verbatim": sum(1 for f in findings
                                        if f["type"] == "verbatim_block"),
                        "paraphrased": sum(1 for f in findings
                                           if f["type"] == "paraphrased_block")}},
            ensure_ascii=False, indent=1)
    else:
        if not findings:
            out = f"{path.as_posix()}: clean"
        else:
            lines = [f"{path.as_posix()}: {len(findings)} finding(s)"]
            for f in findings:
                if f["type"] == "verbatim_block":
                    lines.append(
                        f"  [verbatim] x{len(f['occurrences'])} "
                        + ", ".join(f"cell[{o['cell']}].b{o['block']}"
                                    for o in f["occurrences"])
                        + f" ({f['chars']} c) « {f['excerpt'][:60]}… »")
                else:
                    lines.append(
                        f"  [paraphrase] cell[{f['cell']}].b{f['block']} "
                        f"-> cell[{f['target_cell']}] "
                        f"containment={f['containment']} "
                        f"{len(f['shared_rare'])} mots rares : "
                        f"{' '.join(f['shared_rare'][:8])}")
            out = "\n".join(lines)
    print(out)
    return (2 if findings else 0), out


def scan_all(as_json: bool, fail: bool) -> int:
    t0 = time.perf_counter()
    results = []
    for path in sorted(REPO_ROOT.glob("MyIA.AI.Notebooks/**/*.ipynb")):
        rc, _ = scan_one(path, as_json=False)
        results.append((path, rc))
    elapsed = time.perf_counter() - t0
    flagged = [p for p, rc in results if rc == 2]
    unreadable = [p for p, rc in results if rc == 1]
    print(f"\n[scan-all] {len(results)} notebooks en {elapsed:.1f}s "
          f"({len(flagged)} findings, {len(unreadable)} illisibles/vacuues)")
    for p in flagged:
        print(f"  RADOTE : {p.relative_to(REPO_ROOT).as_posix()}")
    if as_json:
        print(json.dumps({"scanned": len(results), "seconds": round(elapsed, 1),
                          "flagged": len(flagged),
                          "files": [p.relative_to(REPO_ROOT).as_posix()
                                    for p in flagged]},
                         ensure_ascii=False, indent=1))
    return 2 if (fail and flagged) else 0


# --- Self-test : le temoin fondateur DOIT tirer, le fix DOIT etre muet ----
# (lecon #11685 : un detecteur qu'on ne peut pas montrer en train de tirer
# est indistinguishable d'un detecteur debranche).
FIXTURE = Path(__file__).parent / "tests" / "fixtures" / "search09c_ponts_pair.json"


def _nb_from_cells(cells: list[dict]) -> dict:
    return {"cells": cells, "metadata": {}, "nbformat": 4,
            "nbformat_minor": 5}


def self_test() -> int:
    fx = json.loads(FIXTURE.read_text(encoding="utf-8"))
    assert fx["provenance"]["founding_pr"] == 14794, "fixture corrompue"
    failures = []

    # 1. TEMOIN POSITIF — pre-fix Search-09c : signal B DOIT tirer.
    pre = detect(_nb_from_cells(fx["pre_cells"]))
    para = [f for f in pre if f["type"] == "paraphrased_block"]
    if not para:
        failures.append("NEGATIF CRITIQUE : le temoin fondateur (puces "
                        "section 5 vs table section 7) NE TIRE PAS -- "
                        "detecteur debranche ou seuils casses")
    else:
        f0 = para[0]
        if f0["cell"] != 0 or f0["target_cell"] != 1:
            failures.append(f"temoin tire sur les mauvaises cellules : {f0}")
        if len(f0["shared_rare"]) < MIN_SHARED_RARE:
            failures.append(f"temoin sous le plancher : {len(f0['shared_rare'])}")

    # 2. TEMOIN NEGATIF — post-fix (renvoi d'une phrase) : silence attendu.
    post = detect(_nb_from_cells(fx["post_cells"]))
    if [f for f in post if f["type"] == "paraphrased_block"]:
        failures.append("post-fix NON muet : le renvoi d'une phrase vers la "
                        "section 7 declenche encore le signal")

    # 3. Signal A — bloc verbatim duplique (synthetique).
    dup = ("Ce paragraphe pedagogique de cent quarante caracteres explique "
           "en detail pourquoi la recherche a ecart borne echoue sans "
           "heuristique adaptee, avec des exemples concrets et mesures.")
    nb_dup = _nb_from_cells([
        {"cell_type": "markdown", "source": f"# Titre\n\n{dup}\n", "outputs": []},
        {"cell_type": "markdown", "source": f"## Autre\n\n  {dup}  \n", "outputs": []},
    ])
    got_a = [f for f in detect(nb_dup) if f["type"] == "verbatim_block"]
    if not got_a:
        failures.append("signal A muet sur un bloc verbatim duplique")

    # 4. Controle negatif — memes mots de sujet, propos distincts.
    p1 = ("Le funnel de la variance apparait quand des parametres derivent "
          "ensemble ; la geometrie contrainte restaure l'independance et le "
          "sampling redevient efficace sur les modeles hierarchiques profonds.")
    p2 = ("En TP, on observera le funnel sur un modele a huit parametres : "
          "tracer la variance conditionnelle par niveau, puis comparer les "
          "chaines avant et apres reparametrisation non centree du predicteur.")
    nb_ok = _nb_from_cells([
        {"cell_type": "markdown", "source": f"# A\n\n{p1}", "outputs": []},
        {"cell_type": "markdown", "source": f"# B\n\n{p2}", "outputs": []},
    ])
    if detect(nb_ok):
        failures.append("faux positif : deux paragraphes distincts partagent "
                        "un vocabulaire de sujet et declenchent un finding")

    if failures:
        print("SELF-TEST FAILED")
        for f in failures:
            print(f"  - {f}")
        return 1
    print(f"self-test OK : temoin fondateur tire ({len(para[0]['shared_rare'])} "
          f"mots rares, containment {para[0]['containment']}), post-fix muet, "
          f"A/B positifs, negatif silencieux.")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("notebooks", nargs="*",
                        help="notebook(s) .ipynb a scanner")
    parser.add_argument("--json", action="store_true",
                        help="sortie machine (JSON) par notebook")
    parser.add_argument("--fail-on-findings", action="store_true",
                        help="exit 2 si au moins un finding")
    parser.add_argument("--scan-all", action="store_true",
                        help="scanner tout MyIA.AI.Notebooks (sweep + timing)")
    parser.add_argument("--self-test", action="store_true",
                        help="controles positif/negatif sur le temoin "
                             "fondateur (refuse de passer a vide)")
    args = parser.parse_args(argv)

    if args.self_test:
        return self_test()
    if args.scan_all:
        return scan_all(args.json, args.fail_on_findings)

    if not args.notebooks:
        parser.error("fournir un notebook, --scan-all ou --self-test")
    rc_max = 0
    for raw in args.notebooks:
        rc, _ = scan_one(Path(raw), args.json)
        rc_max = max(rc_max, rc)
    return rc_max if args.fail_on_findings else 0


if __name__ == "__main__":
    sys.exit(main())
