#!/usr/bin/env python3
"""Organe factual-mislabel (#18354 tranche 2, campagne #17073).

Détecte une cellule markdown qui énonce un compte d'entité CONTREDIT par
le stream text committé de la cellule code qu'elle décrit -- canon :
App-5-Timetabling énonce « 3 salles » et « (3 × 20)^8 » alors que le
stream committé imprime « Salles : 4 » et « (4 x 20)^8 = 1.68e+15 ».

Deux facettes, toutes deux des contradictions (un compte DIFFÉRENT du
stream) -- l'absence pure d'un nombre relève de l'organe stale-claim
(tranche 1) :

1. compte d'unité : « N <unit> » en markdown vs « <Unit> : M » dans le
   stream d'une cellule code adjacente (fenêtre +-2), même unité,
   N != M ;
2. formule-tuple : « (N × K)^P » en markdown vs « (M x K)^P » dans le
   stream, N != M.

Sortie : rc=0 propre, rc=1 au moins un finding, rc=2 erreur d'usage.
Advisory par construction (patron #11435) -- jamais bloquant seul.

#20035 : la portee du vocabulaire d'unites a ete etendue pour couvrir
les substantifs de comptage trouves sur les cotes hors-App-5 (carnet,
lemme, modele, ...). Le scope par defaut est `extended` ; un audit
cible peut rejouer en `core` (les 14 unites historiques d'App-5) via
`--units core`. Le test de regression documente en haut reste vert
dans les deux scopes (la garde SUBCOUNT_CONTEXT_RE filtre les
sous-comptes qui produiraient les FP).

MESURE CORPUS (exigence #20035, relevee le 2026-10-21 sur ai-01) --
corpus `MyIA.AI.Notebooks`, 1 553 carnets, organe execute sur les
deux scopes avant et apres la garde compte/valeur :

| scope | avant la garde | apres la garde |
|---|---|---|
| `core` | 15 | 15 (inchange) |
| `extended` | 45 | 38 |

Les 7 findings disparus etaient tous de la classe VALEUR lue comme
COMPTE (moyennes decimales). Sur les 38 restants, la lecture
classe par classe donne ~3 vrais (le canon App-5 : « 3 salles » vs
`Salles : 4`, cellules md 2 et 4, plus la formule-tuple) et ~35
faux positifs classes : separateur de milliers par espace (2),
plages de valeurs (« 1-2 iterations », « 4-6 »), comptes partiels
(Train 382 / Test 164 pour un total de 546), sous-comptes par item
(« 16 slots a 1 seul », « 8 slots a 2 »), et quantites de nature
differente (horizon « 5 jours » vs 6 300 lignes, « 40 epochs
configureses » vs 6 executees).

CONSEQUENCE : le scope `extended` rend un taux de faux positifs de
~92 % sur le corpus. L'organe reste ADVISORY (patron #11435, jamais
bloquant seul), donc ce taux ne bloque rien -- mais il produit du
bruit. L'arbitrage du defaut (`extended` par defaut, ou `core` par
defaut + `extended` en opt-in explicite) est soumis au coordinateur ;
le defaut actuel n'est pas change par ce correctif, qui ferme une
classe de faux positifs et documente la mesure.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import unicodedata
from pathlib import Path

UNITS = (
    "salles?|cours|cre?neaux?|enseignants?|professeurs?|etudiants?|"
    "agents?|variables?|contraintes?|jours?|rooms?|courses?|slots?|teachers?"
)

# #20035 : la liste UNITS est mono-domaine (App-5 / emploi du temps).
# Le cas fondateur documente en #19918 est "15 carnets dans Serre100/"
# vs prose "les huit carnets" : le substantif `carnet` n'est pas dans
# la liste, l'organe est aveugle par construction. La voie "ajouter une
# unite a la fois" ne tient pas -- chaque instance trouve une autre
# (carnet, lemme, fichier, modele, ...). La voie choisie est une liste
# fermee, documentee, et couplee a la garde SUBCOUNT_CONTEXT_RE deja
# en place (chacun, par, au moins, ...) : les faux positifs mesures
# sur App-5 (3 FP tues) restent la base de reference. La liste est
# ajoutee par defaut -- c'est elle qui rend l'organe utile aux cotes
# hors App-5 -- et un drapeau --units=core la desactive pour les usages
# qui veulent la portee historique (la portee du test de regression
# documente en haut du fichier : 0 FP / 30 carnets sur le corpus de
# reference d'avant #20035).
UNITS_EXTENDED = (
    # Carnets / notebooks / pages / sections (Serre100, IIT, ICT, ML,
    # SymbolicAI) : substantifs que le stream peut enumerer directement
    # (print d'un listing ou d'un compteur).
    "carnets?|notebooks?|fichiers?|sections?|pages?|cellules?|"
    "modules?|bibliotheques?|paquets?|"
    # Preuves / theoremes / lemmes (Lean) : le stream d'une campagne
    # `lake envlean` rend `Build OK` (pas de compte) ; le compteur
    # apparait surtout dans les re-executions `print(N_theorems)`.
    "theoremes?|lemmes?|preuves?|corollaires?|propositions?|"
    "definitions?|axiomes?|hypotheses?|"
    # ML / training : modeles, predictions, echantillons.
    "modeles?|predictions?|echantillons?|hyperparametres?|"
    "parametres?|epochs?|iterations?|episodes?|"
    # Quantbooks : strategies, backtests.
    "strategies?|backtests?|"
    # Solveurs / moteurs : problemes, solutions, instances.
    "problemes?|solutions?|instances?|"
    # Tests : cas, scenarios, fixtures.
    "scenarios?|fixtures?|"
    # Genres d'objets code : classes, fonctions, methodes, lignes.
    "classes?|fonctions?|methodes?|lignes?|"
    # Datasets / fichiers de donnees.
    "datasets?|colonnes?|tableaux?|"
    # Pluriels courants en prose pedagogique : parties, etapes, chapitres.
    "parties?|etapes?|chapitres?|paragraphes?"
)

# Le pattern regex depend du scope d'unites (core vs extended). Compile
# une seule fois par appel de scan_notebook ; un cache par process
# suffirait, mais le scan est lui-meme le chemin chaud. Les regex sont
# par-fonction pour que le test puisse mocker les deux sans toucher au
# scope par defaut.
def _build_count_patterns(units: str) -> tuple[re.Pattern, re.Pattern]:
    """Compile les regexes MD/stream compte pour le scope d'unites.

    Le pattern stream utilise `[ \t]*` (et non `\\s*`) entre le nom
    d'unite et le separateur, et entre le separateur et le chiffre :
    `\\s*` absorbe le saut de ligne et lit le premier digit d'une
    liste numerotee comme un compte -- ex. `Etapes:\\n  1. Preparer`
    devient `etapes = 1` (faux positif, Hermes 2026-10-15 sur
    `GenAI/Texte/03_Structured_Outputs.ipynb` cellule md 19).
    `[ \t]*` preserve les separateurs en espace/tabulation sur la
    meme ligne et tue la classe FP sur les listes numerotees.

    Les deux motifs refusent un nombre suivi d'une partie decimale
    (garde `(?!\\d*[.,]\\d)`) : un nombre a virgule ou a point est une VALEUR, pas
    un compte. Sans cette garde, « Recompense moyenne sur 10 episodes:
    465.1 » donnait `episodes = 465` dans le stream, contredit par les « 10
    episodes » de la prose -- faux positif mesure sur
    `RL/RL-02-Wrappers-Sauvegarde-Callbacks-Python.ipynb` cellules md 12 et
    18 (signale par la lane adjointe, cycle c2204).

    LIMITE CONNUE, non couverte par cette garde : le separateur de
    milliers PAR ESPACE (« 10 000 iterations », « 6 912 variables »). Le
    motif MD lit alors le dernier groupe (« 000 iterations »), un
    compte faux -- classe distincte, mesuree a 2 findings sur le corpus
    (GameTheory-13 c16, SocialChoice-04 c16). Elle n'est pas traitee ici :
    la corriger exige de distinguer un groupe de milliers d'un compte,
    ce qui suppose une grammaire de nombre, pas une garde de lookahead.
    La faute la plus grave (une valeur lue comme un compte, donc une
    contradiction FABRIQUEE) est, elle, fermee.
    """
    return (
        re.compile(rf"(?i)\b(\d{{1,5}})(?!\d*[.,]\d)\s*({units})\b"),
        re.compile(rf"(?i)\b({units})[ \t]*[:=][ \t]*(\d{{1,5}})(?!\d*[.,]\d)\b"),
    )


MD_TUPLE_RE = re.compile(r"\(\s*(\d{1,5})\s*(?:[x×]|\\times\s*)\s*(\d{1,5})\s*\)\s*\^")
STREAM_TUPLE_RE = re.compile(r"\(\s*(\d{1,5})\s*x\s*(\d{1,5})\s*\)\s*\^")

# Sous-comptes par entite (« Dupont enseigne 2 cours », « chacun 2 cours »,
# « par jour », bornes « au moins/au plus ») : le total du stream ne les
# contredit pas -- mesure sur App-5 (md c.6 : 3 faux « 2 cours » vs
# stream « Cours : 8 »).
SUBCOUNT_CONTEXT_RE = re.compile(
    r"(?i)(enseign\w*|chacun\w*|par\s+\w+|au\s+(?:moins|plus)|maximum|minimum|"
    r"environ|centaines?|dizaines?)"
)

WINDOW = 3


def _unaccent(s: str) -> str:
    return "".join(
        c for c in unicodedata.normalize("NFD", s) if unicodedata.category(c) != "Mn"
    )


def _output_text(cell: dict) -> str:
    parts: list[str] = []
    for o in cell.get("outputs", []):
        t = o.get("text", "")
        parts.append("".join(t) if isinstance(t, list) else (t if isinstance(t, str) else ""))
        data = o.get("data", {}) if isinstance(o.get("data"), dict) else {}
        for key in ("text/plain", "text/html"):
            v = data.get(key, "")
            parts.append("".join(v) if isinstance(v, list) else (v if isinstance(v, str) else ""))
    return "\n".join(parts)


def _nearby_streams(cells: list[dict], idx: int) -> str:
    lo = max(0, idx - WINDOW)
    hi = min(len(cells), idx + WINDOW + 1)
    parts = [
        _output_text(c)
        for c in cells[lo:hi]
        if c["cell_type"] == "code" and _output_text(c).strip()
    ]
    return "\n".join(parts)


def _singular(unit: str) -> str:
    return unit.rstrip("s").lower()


def scan_notebook(path: Path, *, units_scope: str = "extended") -> list[dict]:
    """Scanne un carnet. ``units_scope`` :
    - ``"core"`` : UNITS seulement (la portee historique, App-5) ;
    - ``"extended"`` (defaut) : UNITS + UNITS_EXTENDED. La liste etendue
      couvre les substantifs de comptage trouves sur les cotes
      hors-App-5 (carnet, lemme, modele, ...). Le scope etendu est
      l'opt-in le plus prudent pour la detection reelle, mais reste
      un argument du scan : un audit cible (ex. App-5 seul) peut
      rejouer en ``"core"`` pour comparer la portee historique.
    """
    try:
        nb = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return [{"file": str(path), "error": f"unreadable notebook: {exc}"}]
    if units_scope == "core":
        units = UNITS
    elif units_scope == "extended":
        units = UNITS + "|" + UNITS_EXTENDED
    else:
        raise ValueError(f"units_scope inconnu: {units_scope!r} (attendu 'core' ou 'extended')")
    md_count_re, stream_count_re = _build_count_patterns(units)
    findings: list[dict] = []
    for idx, cell in enumerate(nb["cells"]):
        if cell["cell_type"] != "markdown":
            continue
        src = _unaccent("".join(cell.get("source", [])))
        stream = _unaccent(_nearby_streams(nb["cells"], idx))
        if not stream.strip():
            continue
        # facette 1 : comptes d'unites contredits
        stream_counts: dict[str, set[int]] = {}
        for m in stream_count_re.finditer(stream):
            stream_counts.setdefault(_singular(m.group(1)), set()).add(int(m.group(2)))
        seen_unit_claims: set[tuple[int, str, str]] = set()
        for m in md_count_re.finditer(src):
            n, unit = int(m.group(1)), _singular(m.group(2))
            key = (idx, unit, str(n))
            if key in seen_unit_claims:
                continue
            after = src[m.end(): m.end() + 12]
            before = src[max(0, m.start() - 15): m.start()]
            ctx_before = src[max(0, m.start() - 60): m.start()]
            if SUBCOUNT_CONTEXT_RE.search(ctx_before) or SUBCOUNT_CONTEXT_RE.search(
                src[m.end(): m.end() + 30]
            ):
                continue
            # composé hypotheque (creneaux-salles) ou rapport (creneaux/jour) :
            # l'unite n'y est PAS la meme grandeur que le total du stream
            if after.lstrip().startswith("-") or re.match(r"\s*/\s*\w", after):
                continue
            # operande droite d'un produit « 5 jours x 4 creneaux » : c'est une
            # decomposition du total, pas un compte total contredit
            if re.search(r"[x×]\s*$", before) or re.search(r"\d\s*[x×]\s*$", before):
                continue
            if unit in stream_counts and n not in stream_counts[unit]:
                seen_unit_claims.add(key)
                findings.append(
                    {
                        "file": str(path),
                        "cell_index": idx,
                        "verdict": "FACTUAL_MISLABEL",
                        "kind": "unit-count",
                        "unit": unit,
                        "claimed": str(n),
                        "stream": sorted(stream_counts[unit]),
                        "context": src[max(0, m.start() - 40): m.end() + 30].strip()[:160],
                    }
                )
        # facette 2 : tuples de formule contredits
        stream_tuples = {(int(m.group(1)), int(m.group(2))) for m in STREAM_TUPLE_RE.finditer(stream)}
        for m in MD_TUPLE_RE.finditer(src):
            t = (int(m.group(1)), int(m.group(2)))
            if stream_tuples and t not in stream_tuples and any(
                t[1] == s[1] and t[0] != s[0] for s in stream_tuples
            ):
                findings.append(
                    {
                        "file": str(path),
                        "cell_index": idx,
                        "verdict": "FACTUAL_MISLABEL",
                        "kind": "tuple-formula",
                        "unit": "tuple",
                        "claimed": f"({t[0]} x {t[1]})^",
                        "stream": [f"({a} x {b})^" for a, b in sorted(stream_tuples)],
                        "context": src[max(0, m.start() - 40): m.end() + 30].strip()[:160],
                    }
                )
    return findings


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--units", choices=("core", "extended"), default="extended",
                    help="#20035 : portee du vocabulaire d'unites. "
                         "`core` = App-5 (defaut historique, 14 unites), "
                         "`extended` (defaut depuis #20035) = + substantifs "
                         "de comptage trouves sur les cotes hors-App-5 "
                         "(carnet, lemme, modele, ...). Le test de "
                         "regression historique (0 FP / 30 carnets) reste "
                         "rejouable via `--units core`.")
    ap.add_argument("notebooks", nargs="+", type=Path)
    args = ap.parse_args(argv)

    findings: list[dict] = []
    for p in args.notebooks:
        findings.extend(scan_notebook(p, units_scope=args.units))

    if args.json:
        print(json.dumps({"anomaly_count": len(findings), "findings": findings}, ensure_ascii=False, indent=1))
    else:
        for f in findings:
            if "error" in f:
                print(f"[ERROR] {f['file']}: {f['error']}")
                continue
            print(
                f"[FACTUAL_MISLABEL] {f['file']} cell={f['cell_index']} "
                f"{f['kind']} unit={f['unit']} claimed={f['claimed']} "
                f"stream={f['stream']} :: {f['context'][:110]}"
            )
        print(f"anomaly_count: {len(findings)}")
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
