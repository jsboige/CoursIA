#!/usr/bin/env python3
"""Detecte les accent-strippings dans les notebooks pedagogiques FR (registre #2876).

Pourquoi cet outil existe
-------------------------
Le registre #2876 (restauration des accents francais) a accumule ~22 PRs manuelles
repetitives sur des notebooks ou un mauvais passage d'encodage avait stripp les
accents (ex. Sudoku-11-Choco-Python #6799 : 169 lignes). Chaque PR etait faite a
la main, avec un script ad-hoc non-committe pour verifier le caractere "accent-only"
du diff. Ce tool formalise la moitie DETECTION de ce travail : il liste les mots
francais dont les accents ont ete perdus, pour guider la restauration manuelle.

Il DETECTE, il ne RESTAURE PAS. La restauration automatique est ambiguë
("a" -> "a" ou "a" ou "a" ? "ou" -> "ou" ou "ou" ?) : po-2025 a explicitement
skippe ces cas ambigus sur #6799. Cet outil laisse l'humain decider.

G.1 finding (c.539 forensic #6799)
----------------------------------
Le scan accent historique de #2876 etait ~96% de faux positifs (memoire
`accent-scan-parameters-tres-fp`, `readme-drift-checker-fp-classes`) car il
matchait des mots valides FR sans accent comme "complete", "ou", "a", "la",
"tres" (dans des noms de parametres Python). Pour eviter cela, le dictionnaire
ci-dessous est CONSERVATEUR : seules les paires ou la forme *stripped* n'est PAS
un mot francais valide sont incluses. "complete" / "ou" / "a" / "la" / "valeur"
sont exclus (mots FR valides sans accent). Le dictionnaire est extensible : ajouter
les paires au fil des rencontres dans les PRs #2876 futures.

Comment ca marche
-----------------
Pour chaque cellule source (markdown OU code), l'outil cherche les occurrences des
formes *stripped* du dictionnaire (insensible a la casse, limitees aux frontieres
de mot). Chaque hit est rapporte avec :
  - index de cellule + type (markdown/code)
  - numero de ligne dans la cellule
  - mot stripped trouve + suggestion accentuee
  - la ligne complete pour contexte

L'outil ne touche pas les cellules : il lit seulement. Aucun risque de regression.

Usage
-----
    python detect_accent_stripping.py NB.ipynb                 # un notebook
    python detect_accent_stripping.py --family Sudoku          # une famille
    python detect_accent_stripping.py                           # tous les notebooks pedagogiques
    python detect_accent_stripping.py NB.ipynb --json          # sortie machine
    python detect_accent_stripping.py NB.ipynb --check         # exit 1 si hits (CI-ready)

Exit codes
----------
    0 -- aucun accent-stripping detecte (ou mode non --check)
    1 -- un ou plusieurs hits detectes (--check seulement)
    2 -- erreur (notebook illisible, famille introuvable)

Voir aussi
----------
- count_exercises.py (meme convention CLI pour un autre audit pedagogique)
- Registre #2876 (backlog accents), EPIC #3801 (SOTA, non lie mais meme famille d'outils)
- Memoires : accent-scan-parameters-tres-fp, readme-drift-checker-fp-classes (FP historiques)
"""
import argparse
import json
import re
import sys
import unicodedata
from pathlib import Path

# --- Dictionnaire cure : forme stripped (sans accent) -> forme accentuee correcte ---
# CONSERVATEUR : la forme stripped ne doit PAS etre un mot francais valide seul,
# sinon on genere des faux positifs massifs (le scan #2876 historique etait ~96% FP).
# Mots expressément EXCLUS car valides sans accent : complete, ou, a, la, valeur,
# niveau, exemple, fonction, variable, modele(wait inclus car non-mot), code, option,
# branche, analyse, finale, suite, mais, donc, car, or, ni, puis, alors, ici, chaque.
# Etendre ce dictionnaire au fil des rencontres dans les PRs #2876 (grain durable).
ACCENT_PAIRS = {
    # accent grave
    "probleme": "problème",
    "caractere": "caractère",
    "caracteres": "caractères",
    "parametre": "paramètre",
    "parametres": "paramètres",
    "tres": "très",
    "apres": "après",
    "systeme": "système",
    "systemes": "systèmes",
    "theme": "thème",
    "themes": "thèmes",
    "modele": "modèle",
    "modeles": "modèles",
    "requete": "requête",
    "requetes": "requêtes",
    "tache": "tâche",
    "taches": "tâches",
    # accent aigu
    "theorie": "théorie",
    "theories": "théories",
    "donnees": "données",
    "methode": "méthode",
    "methodes": "méthodes",
    "categorie": "catégorie",
    "categories": "catégories",
    "precedent": "précédent",
    "precedents": "précédents",
    "precedente": "précédente",
    "precedentes": "précédentes",
    "generalement": "généralement",
    "generaux": "généraux",
    "generale": "générale",
    "generales": "générales",
    "generateurs": "générateurs",
    "generateur": "générateur",
    "numero": "numéro",
    "numeros": "numéros",
    "deja": "déjà",
    "developpement": "développement",
    "developpements": "développements",
    "experience": "expérience",
    "experiences": "expériences",
    "resultat": "résultat",
    "resultats": "résultats",
    "selectionner": "sélectionner",
    "selection": "sélection",
    "preference": "préférence",
    "preferences": "préférences",
    "execution": "exécution",
    "executions": "exécutions",
    "operation": "opération",
    "operations": "opérations",
    "iteration": "itération",
    "iterations": "itérations",
    "recursif": "récursif",
    "recursive": "récursive",
    "booleen": "booléen",
    "booleens": "booléens",
    "scenario": "scénario",
    "scenarios": "scénarios",
    "ecole": "école",
    "ecoles": "écoles",
    "etude": "étude",
    "etudes": "études",
    "equipe": "équipe",
    "equipes": "équipes",
    "degre": "degré",
    "degres": "degrés",
    "different": "différent",
    "differents": "différents",
    "differentes": "différentes",
    "differente": "différente",
    "difference": "différence",
    "differences": "différences",
    "independant": "indépendant",
    "independance": "indépendance",
    "dependance": "dépendance",
    "etape": "étape",
    "etapes": "étapes",
    "creer": "créer",
    "cree": "créé",
    "cres": "créés",
    "evenement": "événement",
    "evenements": "événements",
    "premiere": "première",
    "premieres": "premières",
    "derniere": "dernière",
    "dernieres": "dernières",
    "element": "élément",
    "elements": "éléments",
    "modifiee": "modifiée",
    "modifies": "modifiés",
    "affichee": "affichée",
    "affiches": "affichés",
    "remplacee": "remplacée",
    "remplaces": "remplacés",
    # accent circonflexe
    "fenetre": "fenêtre",
    "fenetres": "fenêtres",
    "chaine": "chaîne",
    "chaines": "chaînes",
    "meme": "même",
    "memes": "mêmes",
    "hotel": "hôtel",
    "hotels": "hôtels",
    "role": "rôle",
    "roles": "rôles",
    "gite": "gîte",
    # --- Extension c.589 (#2876, PR accent-dict-extension) ---
    # Conservative pairs whose stripped form is NEITHER a valid FR word NOR a
    # common EN word (so no FP in bilingual/code context). The -tion/-ence
    # anglicisms (generation/evaluation/implementation/reference/sequence/
    # definition/integration/prediction/regression/representation/...) are
    # deliberately EXCLUDED: their stripped form is a common EN word -> FP risk
    # in EN prose or code identifiers (the silent-corruption class flagged by
    # po-2025 c.591). Verified >=3 notebooks / >=5 hits each across the corpus.
    # strategie (not FR strategie, not EN strategy)
    "strategie": "stratégie",
    "strategies": "stratégies",
    "strategique": "stratégique",
    "strategiques": "stratégiques",
    # controle (not FR controle, not EN control)
    "controle": "contrôle",
    "controles": "contrôles",
    "controler": "contrôler",
    # definir family (not FR, not EN define)
    "definir": "définir",
    "definit": "définit",
    "defini": "défini",
    "definie": "définie",
    "definis": "définis",
    "definies": "définies",
    # mecanisme (not FR, not EN mechanism)
    "mecanisme": "mécanisme",
    "mecanismes": "mécanismes",
    # criteres (not FR criteres, not EN criteria)
    "criteres": "critères",
    # creez/creee/creent (conjugated creer forms missing from existing cree/cres)
    "creez": "créez",
    "creee": "créée",
    "creees": "créées",
    "creent": "créent",
    # operateur (not FR, not EN operator)
    "operateur": "opérateur",
    "operateurs": "opérateurs",
    # theorique (not FR, not EN theoretic)
    "theorique": "théorique",
    "theoriques": "théoriques",
    # caracteristique (not FR, not EN characteristic)
    "caracteristique": "caractéristique",
    "caracteristiques": "caractéristiques",
    # numerique (not FR, not EN numeric)
    "numerique": "numérique",
    "numeriques": "numériques",
    # systematique (not FR, not EN systematic)
    "systematique": "systématique",
    "systematiques": "systématiques",
    # metaheuristique (not FR, not EN)
    "metaheuristique": "métaheuristique",
    "metaheuristiques": "métaheuristiques",
    # genetique (not FR, not EN genetic)
    "genetique": "génétique",
    "genetiques": "génétiques",
    # hierarchie (not FR, not EN hierarchy)
    "hierarchie": "hiérarchie",
    "hierarchies": "hiérarchies",
    "hierarchique": "hiérarchique",
    "hierarchiques": "hiérarchiques",
    # semantique (not FR, not EN semantic)
    "semantique": "sémantique",
    "semantiques": "sémantiques",
    # specifique (not FR, not EN specific)
    "specifique": "spécifique",
    "specifiques": "spécifiques",
    # interet (not FR, not EN interest)
    "interet": "intérêt",
    "interets": "intérêts",
    # precis (not FR precis, not EN precise)
    "precis": "précis",
    "precisement": "précisément",
    # egalement (not FR egalement, not EN)
    "egalement": "également",
    # sequentiel (not FR, not EN sequential)
    "sequentiel": "séquentiel",
    "sequentielle": "séquentielle",
    "sequentielles": "séquentielles",
    "sequentiels": "séquentiels",
    # deterministe (not FR, not EN deterministic)
    "deterministe": "déterministe",
    "deterministes": "déterministes",
    # regle (not FR regle, not EN rule)
    "regle": "règle",
    "regles": "règles",
}


def _build_regex():
    """Construit une regex qui matche n'importe quelle forme stripped (frontieres de mot)."""
    # Trier par longueur decroissante pour que les formes plurielles (caracteres) matchent
    # avant les formes singuliers (caractere) et evitent un match partiel trompeur.
    forms = sorted(ACCENT_PAIRS.keys(), key=len, reverse=True)
    # echapper (rien de special ici, mais par principe) + frontieres de mot + insensible casse
    pattern = r"\b(?:" + "|".join(re.escape(f) for f in forms) + r")\b"
    return re.compile(pattern, re.IGNORECASE)


_STRIP_RE = _build_regex()


def _src_lines(cell):
    """Retourne la liste des lignes de source d'une cellule."""
    s = cell.get("source", [])
    if isinstance(s, str):
        return s.splitlines()
    # nbformat : liste de strings, chacune peut porter son \n final
    out = []
    for chunk in s:
        out.extend(chunk.splitlines())
    return out


def scan_notebook(path):
    """Scanne un notebook, retourne la liste des hits.

    Un hit = dict {cell_idx, cell_type, line_no, stripped, suggestion, line}.
    """
    try:
        with open(path, encoding="utf-8") as f:
            nb = json.load(f)
    except (OSError, json.JSONDecodeError) as exc:
        return {"error": str(exc)}

    hits = []
    for idx, cell in enumerate(nb.get("cells", [])):
        ctype = cell.get("cell_type", "?")
        for line_no, line in enumerate(_src_lines(cell), start=1):
            for m in _STRIP_RE.finditer(line):
                stripped = m.group(0)
                # reagreger la cle canonique (minuscules) pour la suggestion
                key = stripped.lower()
                suggestion = ACCENT_PAIRS.get(key)
                if suggestion is None:
                    # match insensible a la casse sur une forme plurielle/non listee : skip
                    continue
                hits.append({
                    "cell_idx": idx,
                    "cell_type": ctype,
                    "line_no": line_no,
                    "stripped": stripped,
                    "suggestion": suggestion,
                    "line": line.rstrip(),
                })
    return hits


def _iter_notebooks(family_filter=None):
    """Genere les chemins des notebooks pedagogiques (MyIA.AI.Notebooks/**/*.ipynb)."""
    root = Path("MyIA.AI.Notebooks")
    if not root.is_dir():
        return
    for nb in sorted(root.rglob("*.ipynb")):
        # skip checkpoints et archives
        if ".ipynb_checkpoints" in nb.parts or "_archive" in nb.parts:
            continue
        if family_filter is not None:
            # family = sous-dossier de niveau 1 (ex. Sudoku, ML, Probas)
            if len(nb.parts) < 2 or nb.parts[1] != family_filter:
                continue
        yield nb


def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Detecte les accent-strippings dans les notebooks pedagogiques FR (#2876)."
    )
    parser.add_argument("notebook", nargs="?", help="Notebook a scanner (defaut: tous)")
    parser.add_argument("--family", help="Limiter a une famille (ex. Sudoku, ML, Probas)")
    parser.add_argument("--json", action="store_true", help="Sortie JSON (machine-readable)")
    parser.add_argument("--check", action="store_true",
                        help="Exit 1 si au moins un accent-stripping detecte (CI-ready)")
    args = parser.parse_args(argv)

    targets = []
    if args.notebook:
        p = Path(args.notebook)
        if not p.is_file():
            print(f"error: notebook introuvable: {args.notebook}", file=sys.stderr)
            return 2
        targets = [p]
    else:
        targets = list(_iter_notebooks(args.family))
        if not targets:
            where = f"famille {args.family!r}" if args.family else "MyIA.AI.Notebooks/"
            print(f"error: aucun notebook trouve sous {where}", file=sys.stderr)
            return 2

    all_hits = {}
    total = 0
    errors = []
    for nb in targets:
        result = scan_notebook(nb)
        if isinstance(result, dict) and "error" in result:
            errors.append((nb, result["error"]))
            continue
        if result:
            all_hits[str(nb)] = result
            total += len(result)

    if args.json:
        out = {"total_hits": total, "notebooks": all_hits, "errors": errors,
               "dict_size": len(ACCENT_PAIRS)}
        json.dump(out, sys.stdout, ensure_ascii=False, indent=2)
        sys.stdout.write("\n")
    else:
        if errors:
            for nb, exc in errors:
                print(f"warn: illisible {nb}: {exc}", file=sys.stderr)
        if total == 0:
            print(f"OK: 0 accent-stripping detecte "
                  f"(dictionnaire cure de {len(ACCENT_PAIRS)} paires, "
                  f"{len(targets)} notebook(s) scanne(s)).")
        else:
            print(f"FOUND {total} accent-stripping(s) dans {len(all_hits)} notebook(s) "
                  f"(dictionnaire cure de {len(ACCENT_PAIRS)} paires):\n")
            for nb, hits in all_hits.items():
                print(f"=== {nb} ({len(hits)} hits) ===")
                for h in hits:
                    print(f"  cell {h['cell_idx']} [{h['cell_type']}] L{h['line_no']}: "
                          f"{h['stripped']!r} -> {h['suggestion']!r}")
                    print(f"    | {h['line']}")
                print()

    if args.check and total > 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
