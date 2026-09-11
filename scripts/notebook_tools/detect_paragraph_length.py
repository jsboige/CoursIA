#!/usr/bin/env python3
"""Detecteur de paragraphes markdown trop longs (« wall of text »).

Incident fondateur (remarque user 2026-09-10 sur le commit 76d7a5bc, PR
#15405, audit README Probas) : le README de la serie Probas portait un
paragraphe unique de **3336 caracteres / 24 phrases sur une seule ligne
physique** (« Cette serie couvre trois stacks... »), issu du diff
d'audit README de #15405. Illisible, impossible a scanner, et **passe au
CI** : aucun garde n'intercepte un paragraphe markdown trop long.

Calibration 2026-09-10 (rglob des `*.md` du repo, 791 fichiers / 23049
paragraphes) :
  p50=79  p75=274  p90=536  p95=760  p99=1437  max=13409 caracteres

Le seuil 2000 est choisi pour :
  (a) capturer le paragraphe-mur incident (3336 c) avec marge (~1.6x) ;
  (b) signaler seulement les vrais outliers : 42 fichiers / 84 paragraphes
      > 2000 c sur le corpus complet (avant ce garde, la majorite sont
      des sous-sections techniques longues et legitimes -- ils ne sont
      PAS corriges ici, voir issue de suivi).

Signal : tout bloc contigu de lignes non-vides, en dehors de fences de
code (``` ou ~~~), de lignes de tableau markdown (commencant par `|`) et
de titres (`#`, `##`, ...). Listes, blockquotes et paragraphes ordinaires
comptent comme bloc -- un item de liste de 10k caracteres est un mur
aussi.

Codes de retour : 0 = clean ; 1 = fichier illisible/introuvable ou scan
vacuue (aucun bloc eligible) ; 2 = findings (avec --fail-on-findings).

Detection : stdlib uniquement (regex). O(n_lignes) par fichier, ~1 ms
pour 1000 lignes. Voir scripts/notebook_tools/tests/fixtures/
paragraph_wall_md.md pour les cas fondateur.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import time
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

# Seuil unique verrouille par la calibration 2026-09-10 (voir docstring).
# Deliberement NON exposable en CLI -- un seuil arbitraire detruit le
# signal ; cf. pedagogy_density.DENSITY_THRESHOLD pour le precedent.
MAX_PARAGRAPH_LEN = 2000

# Catastrophes qui degradent la lisibilite et qu'on ne veut PAS confondre
# avec un mur de prose : fences code ```/~~~, lignes de tableau markdown,
# titres (# ... ######), commentaires HTML <!-- ... --> (utilises par le
# marqueur CATALOG-STATUS), directives Sphinx/RST (^:[a-z]+:).
FENCE_RE = re.compile(r"^\s*(```|~~~)")
TABLE_ROW_RE = re.compile(r"^\s*\|")
HEADING_RE = re.compile(r"^\s*#{1,6}\s")
HTML_COMMENT_RE = re.compile(r"^\s*<!--")
SPHINX_DIRECTIVE_RE = re.compile(r"^\s*:[a-z]+:")
LIST_ITEM_RE = re.compile(r"^\s*(?:[-*+]|\d+\.)\s")
BLOCKQUOTE_RE = re.compile(r"^\s*>\s?")
ALERT_RE = re.compile(r"^\s*!\[")  # ![NOTE], ![WARNING]


def _is_ignorable_line(line: str) -> bool:
    """Vrai si la ligne appartient a un contexte qu'on exclut du comptage.

    Les fences sont gerees au niveau bloc (on entre/sort d'un etat), pas
    ici. Les titres, lignes de tableau, commentaires HTML et directives
    Sphinx sont ignores parce qu'ils sont de la structure, pas de la
    prose. Listes et blockquotes **comptent** : un item de 10k c est un
    mur (la calibration le confirme -- 4 des top-15 sont des listes).
    """
    return (
        FENCE_RE.match(line) is not None
        or TABLE_ROW_RE.match(line) is not None
        or HEADING_RE.match(line) is not None
        or HTML_COMMENT_RE.match(line) is not None
        or SPHINX_DIRECTIVE_RE.match(line) is not None
        or ALERT_RE.match(line) is not None
    )


def _is_fence_open(line: str) -> bool:
    return FENCE_RE.match(line) is not None


def iter_paragraphs(text: str) -> list[tuple[int, int, str]]:
    """Decoupe en paragraphes eligibles, retourne (start_line, length, body).

    Un paragraphe = une suite de lignes contigues non-vides. On saute les
    blocs de code fences (entre ``` et ```). Les lignes de tableau, titres
    et commentaires HTML sont retirees du calcul de longueur mais ne
    rompent pas un paragraphe legitime -- elles sont ignorees
    (reconstructibles via leur contexte).

    Longueur = len(text) du paragraphe nettoye, sans les nouvelles
    lignes de separation. Premiere ligne rapportee = 0-indexe.
    """
    paragraphs: list[tuple[int, int, str]] = []
    buf: list[str] = []
    buf_start = 0
    in_fence = False
    for i, raw in enumerate(text.splitlines()):
        line = raw.rstrip()
        if in_fence:
            if _is_fence_open(line):
                in_fence = False
            continue
        if _is_fence_open(line):
            if buf:
                paragraphs.append((buf_start, _para_len(buf), "\n".join(buf)))
                buf = []
            in_fence = True
            continue
        if not line.strip():
            if buf:
                paragraphs.append((buf_start, _para_len(buf), "\n".join(buf)))
                buf = []
            continue
        if _is_ignorable_line(line):
            # Ne casse pas le paragraphe : skip la structure, garde la prose
            # autour. Une ligne de tableau au milieu d'un paragraphe
            # narratif est un mur (la calibration en capture).
            if buf:
                buf.append("")
            continue
        if not buf:
            buf_start = i
        buf.append(line)
    if buf:
        paragraphs.append((buf_start, _para_len(buf), "\n".join(buf)))
    return paragraphs


def _para_len(lines: list[str]) -> int:
    """Longueur d'un paragraphe en caracteres (hors separateurs internes).

    Les lignes vides inserees pour skipper la structure comptent quand
    meme (sinon un mur de 9 paragraphes-listes en para unique serait
    invisible). On mesure la longueur totale du bloc, pas seulement la
    prose -- c'est l'experience de lecture qu'on cherche a borner.
    """
    return sum(len(line) for line in lines)


def detect(text: str) -> list[dict]:
    findings: list[dict] = []
    for start_line, length, body in iter_paragraphs(text):
        if length > MAX_PARAGRAPH_LEN:
            findings.append({
                "type": "oversized_paragraph",
                "start_line": start_line,
                "chars": length,
                "excerpt": body.strip().replace("\n", " ")[:80],
            })
    findings.sort(key=lambda f: (-f["chars"], f["start_line"]))
    return findings


def scan_one(path: Path, as_json: bool) -> tuple[int, str]:
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        return 1, f"illisible : {exc}"
    findings = detect(text)
    if as_json:
        out = json.dumps(
            {"file": path.as_posix(), "findings": findings,
             "counts": {"total": len(findings)}},
            ensure_ascii=False, indent=1)
    else:
        if not findings:
            out = f"{path.as_posix()}: clean"
        else:
            lines = [f"{path.as_posix()}: {len(findings)} finding(s)"]
            for f in findings:
                lines.append(
                    f"  [oversized] line {f['start_line']+1} "
                    f"({f['chars']} c > {MAX_PARAGRAPH_LEN}) "
                    f"« {f['excerpt']}… »")
            out = "\n".join(lines)
    print(out)
    return (2 if findings else 0), out


def scan_paths(paths: list[Path], as_json: bool, fail: bool) -> int:
    if not paths:
        return 0
    t0 = time.perf_counter()
    flagged: list[Path] = []
    unreadable: list[Path] = []
    rc_max = 0
    # Mode agrégé (--scan-json) : un seul dict {files: [...]} sur stdout,
    # parseable par le CI sans awk de NDJSON. Sinon : un JSON par fichier
    # (compat legacy, debug local).
    aggregated: list[dict] = []
    for p in paths:
        if as_json:
            try:
                text = p.read_text(encoding="utf-8")
            except (OSError, UnicodeDecodeError) as exc:
                unreadable.append(p)
                aggregated.append({"file": p.as_posix(), "findings": [],
                                   "error": str(exc), "counts": {"total": 0}})
                rc_max = max(rc_max, 1)
                continue
            findings = detect(text)
            if findings:
                flagged.append(p)
                rc_max = max(rc_max, 2)
            aggregated.append({"file": p.as_posix(), "findings": findings,
                               "counts": {"total": len(findings)}})
        else:
            rc, _ = scan_one(p, as_json=False)
            rc_max = max(rc_max, rc)
            if rc == 2:
                flagged.append(p)
            elif rc == 1:
                unreadable.append(p)
    elapsed = time.perf_counter() - t0
    if as_json:
        # Un seul dict : {files, summary:{total_findings, file_count, flagged_count}}
        print(json.dumps(
            {"files": aggregated,
             "summary": {"file_count": len(paths),
                         "flagged_count": len(flagged),
                         "unreadable_count": len(unreadable),
                         "total_findings": sum(f["counts"]["total"]
                                               for f in aggregated),
                         "elapsed_seconds": round(elapsed, 3)}},
            ensure_ascii=False, indent=1))
    else:
        print(f"\n[scan] {len(paths)} fichiers en {elapsed:.2f}s "
              f"({len(flagged)} findings, {len(unreadable)} illisibles)")
    return (2 if (fail and flagged) else 0)


# --- Self-test : le temoin fondateur DOIT tirer, les controles negatifs
# DOIVENT rester muets (lecon #11685 : un detecteur qu'on ne peut pas
# montrer en train de tirer est indistinguishable d'un detecteur
# debranche). Pas de fixture externe : les cas fondateurs tiennent en
# 4 chaines ci-dessous -- la fixture markdown vit dans
# tests/fixtures/paragraph_wall_md.md pour pytest.
FOUNDING_PARAGRAPH = (
    "Cette serie couvre trois stacks complementaires : **Infer.NET** "
    "(Microsoft, C#/.NET Interactive) pour l'inference par **message "
    "passing deterministe** (EP/VMP, plus un echantillonneur de Gibbs "
    "disponible), **PyMC** (Python) pour l'**echantillonnage "
    "stochastique MCMC** (NUTS), et des **applications standalone** "
    "(RSA, identification causale avec DoWhy, percolation de liens sur "
    "tore fini). Elle totalise **69 notebooks** -- **28 en C#/.NET "
    "Interactive**, **38 en Python**, **3 en Lean 4** (voir le marqueur "
    "CATALOG-STATUS ci-dessus pour le decompte autoritatif). Le corpus "
    "bayesien ([`Infer/`](Infer/README.md)) compte **21 notebooks** -- "
    "socle numerote 1-20 (le numero 6 n'existe pas : le debugging vit "
    "en accretion `Infer-2b`), accretion de premier modele "
    "`Infer-1b`, et `Infer-20` *Quotients et fibres* en kernel Python "
    "-- couvrant fondements (distributions, graphes de facteurs), "
    "modeles classiques (reseaux bayesiens, TrueSkill, LDA, HMM), "
    "frontieres (causalite, processus gaussiens, modeles "
    "hierarchiques, filtre de Kalman, detection de rupture, analyse "
    "de survie) et geometrie categorique (quotients, fibres, "
    "recollement). L'arc decision Infer.NET en extrait **8 notebooks "
    "C#** ([`DecisionTheory/DecInfer/`](DecisionTheory/DecInfer/"
    "README.md) : utilite esperee, EVPI, MDPs, bandits, jusqu'au "
    "Thompson Sampling DecInfer-10). Le versant PyMC porte ces "
    "modeles en Python avec l'echantillonnage NUTS : **19 notebooks "
    "corpus** ([`PyMC/`](PyMC/README.md), en parite 1:1 avec "
    "Infer -- fondations, modeles classiques, inference causale, "
    "puis frontieres : sequences, reco, processus gaussien epars, "
    "filtre de Kalman, change-point, survie) et **12 miroirs de "
    "l'arc decision** ([`DecisionTheory/PyMC/`](DecisionTheory/PyMC/"
    "README.md), renumerotes 1-12, dont la **jambe actuarielle** "
    "8-12). L'arc decision est en outre certifie par un lake "
    "compagnon **Lean 4** ([`decision_theory_lean`]"
    "(decision_theory_lean/)) et ses **2 notebooks a kernel Lean** "
    "(DecInfer-02, utilite esperee vNM ; DecInfer-09, indice de "
    "Gittins) : les identites d'escompte y sont demontrees "
    "(`0 sorry`), le theoreme d'optimalite restant enonce -- sa "
    "preuve complete attend une formalisation des MDP absente de "
    "Mathlib. La percolation ([`Applications/Percolation/`](Applications/"
    "Percolation/README.md)) complete ce trio Lean avec "
    "[`Percolation-Lean`](Applications/Percolation/Percolation-Lean.ipynb) "
    "(noyau fini prouve sans `sorry`, compagnon du lake "
    "`percolation_lean`), jumeau de la simulation Python "
    "[`Percolation-Supercritique`](Applications/Percolation/"
    "Percolation-Supercritique.ipynb) (trois regimes mesures). "
    "Enfin, un **pont causal** ([`DecisionTheory/Causal-Bridges/`](DecisionTheory/"
    "Causal-Bridges/README.md), 4 notebooks Python, kernels `python3` "
    "et `coursia-ml-training`) federe les quatre traitements de la "
    "causalite dissemines dans le depot -- Tweety (logique), "
    "Infer.NET, PyMC et l'emergence causale (PyPhi) -- autour de "
    "l'echelle de Pearl et du do-calculus. Sur l'outil de reference "
    "[`dowhy`](https://www.pywhy.org/dowhy/), le pont identifie "
    "l'estimande (backdoor, front-door, variable instrumentale), "
    "l'estime puis le refute ; il monte au troisieme echelon de Pearl "
    "(contrefactuel individuel) et couvre les methodes "
    "quasi-experimentales (DiD, controle synthetique, RDD)."
)


def self_test() -> int:
    failures: list[str] = []

    # 1. TEMOIN POSITIF -- paragraphe-mur fondateur Probas (PR #15405).
    got = detect(FOUNDING_PARAGRAPH + "\n")
    wall = [f for f in got if f["type"] == "oversized_paragraph"]
    if not wall:
        failures.append("NEGATIF CRITIQUE : le paragraphe fondateur "
                        "(3336 c, Probas #15405) NE TIRE PAS -- "
                        "detecteur debranche ou seuil casse")
    elif wall[0]["chars"] < 3000:
        failures.append(f"longueur sous-estimee : {wall[0]['chars']} c")

    # 2. TEMOIN NEGATIF -- post-fix (6 paragraphes aeres, voir PR A) : muet.
    post_fix_text = (
        "Cette serie couvre trois stacks complementaires.\n\n"
        "Le corpus bayesien compte 21 notebooks.\n\n"
        "L'arc decision en extrait 8 notebooks C#.\n\n"
        "Le versant PyMC porte ces modeles.\n\n"
        "La percolation complete ce trio Lean.\n\n"
        "Enfin, un pont causal federe les traitements.\n"
    )
    if detect(post_fix_text):
        failures.append("post-fix NON muet : 6 paragraphes aeres "
                        "declenchent encore un finding")

    # 3. SEUIL FRONTIERE -- un paragraphe pile a 2000 caracteres ne tire
    # pas (>2000 strict), un a 2001 tire.
    edge_ok = "a" * 2000 + "\n"
    if detect(edge_ok):
        failures.append("SEUIL : paragraphe de 2000 c declenche (> au lieu de >)")
    edge_over = "a" * 2001 + "\n"
    if not detect(edge_over):
        failures.append("SEUIL : paragraphe de 2001 c ne declenche pas")

    # 4. IGNORANCE -- fences, titres, lignes de tableau, commentaires HTML.
    fence_text = "# Titre\n\n```python\n# 2500 chars de code dans une fence\nprint('a' * 2500)\n```\n\nParagraphe normal.\n"
    if detect(fence_text):
        failures.append("fence/structure non ignoree")
    catalog_text = "<!--\nCATALOG-STATUS: pedagogical_count: 69\nbreakdown: Infer=21\nmaturity: BETA=68\n-->\n\nParagraphe normal.\n"
    if detect(catalog_text):
        failures.append("commentaire HTML (CATALOG-STATUS) non ignore")
    table_text = "| col1 | col2 |\n|------|------|\n| " + "x" * 3000 + " | y |\n"
    if detect(table_text):
        failures.append("ligne de tableau longue non ignoree")

    # 5. SCAN VACUITE -- fichier avec uniquement des titres/listes vides.
    vacuous = "## Titre\n## Autre\n- item\n"
    if detect(vacuous):
        failures.append("scan non vacu : structure seule signalee comme prose")

    if failures:
        print("SELF-TEST FAILED")
        for f in failures:
            print(f"  - {f}")
        return 1
    print(f"self-test OK : temoin fondateur tire ({wall[0]['chars']} c), "
          f"post-fix muet, seuil exact, fences/structure ignorees.")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("paths", nargs="*",
                        help="fichier(s) .md a scanner (defaut: stdin si -)")
    parser.add_argument("--json", action="store_true",
                        help="sortie machine : un dict agrege {files, "
                             "summary} sur stdout (CI-friendly)")
    parser.add_argument("--fail-on-findings", action="store_true",
                        help="exit 2 si au moins un finding")
    parser.add_argument("--self-test", action="store_true",
                        help="controles positif/negatif sur le temoin "
                             "fondateur (refuse de passer a vide)")
    args = parser.parse_args(argv)

    if args.self_test:
        return self_test()

    if not args.paths:
        parser.error("fournir un chemin .md ou --self-test")
    paths = [Path(p) for p in args.paths]
    rc = scan_paths(paths, args.json, args.fail_on_findings)
    return rc if args.fail_on_findings else 0


if __name__ == "__main__":
    sys.exit(main())