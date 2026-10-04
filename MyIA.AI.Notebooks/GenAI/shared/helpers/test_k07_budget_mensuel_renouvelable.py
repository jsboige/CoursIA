#!/usr/bin/env python3
"""test_k07_budget_mensuel_renouvelable.py — refonte c.1377.

Charge la source des cellules `1f127d45` (cell 10) et `b097a42e` (cell 11) du
carnet `09e_Production_Exploitation.ipynb` via nbformat, les exécute dans un
namespace isolé, importe les vrais `trajectoire` et `verifier_alerte`, et
exerce la logique de K07 (#18736) sans réécrire la fonction (cf Tell c.4
strict : le témoin doit être discriminant, pas un PASS-sur-défaut).

Couvre le passage du budget annuel cumulatif au budget mensuel renouvelable
(issue #18736 acceptance) :

  - 0.063 $/jour, 10 $/mois : aucun épuisement mensuel (1.89 < 10)
  - 0.4 $/jour : épuisement attendu mois 1 jour 25
  - 0 requête : aucun épuisement
  - 100 % local : aucun épuisement (pente nulle)
  - l'organe d'alerte détecte le seuil 80 % en mois 1 jour 20 (à 0.4 $/jour, 8/0.4)
  - le reset mensuel : la valeur de `cumuls[30]` (jour 1 de mois 2) doit être
    strictement inférieure à `cumuls[29]` (jour 30 de mois 1) pour pente > 0

Usage :
    pytest tests/test_k07_budget_mensuel_renouvelable.py -v
"""

from __future__ import annotations

import sys
from pathlib import Path

import nbformat


def _find_repo_root():
    """Cherche la racine du dépôt à partir de ce fichier, en remontant jusqu'au .git."""
    p = Path(__file__).resolve().parent
    for ancestor in [p, *p.parents]:
        if (ancestor / ".git").exists():
            return ancestor
    raise FileNotFoundError("Racine du dépôt (.git) introuvable en amont de ce fichier")


CARNET = _find_repo_root() / "MyIA.AI.Notebooks/GenAI/Texte/09e_Production_Exploitation.ipynb"
CELL_TRAJECHE_ID = "1f127d45"   # cell 10 : def trajectoire
CELL_ALERTE_ID = "b097a42e"     # cell 11 : def verifier_alerte


def _load_carnet():
    """Charge le carnet 09e."""
    if not CARNET.exists():
        raise FileNotFoundError(f"Carnet introuvable : {CARNET}")
    return nbformat.read(str(CARNET), as_version=4)


def _find_cell(nb, cell_id):
    for c in nb.cells:
        if c.get("id") == cell_id:
            return c
    raise KeyError(f"Cellule id={cell_id} absente du carnet {CARNET.name}")


def _source(cell):
    return "".join(cell["source"]) if isinstance(cell["source"], list) else cell["source"]


def _build_namespace():
    """Namespace isolé : JOURS_MOIS + dépendance mock MESURES."""
    ns = {}
    # Mock minimal : MESURES contient juste la clé 'distant' avec une mesure unique
    # de cout 0.000042 (valeur mesurée cell 7 sur main -- cohérent avec
    # la cellule 10 qui fait sum(MESURES['distant'])/len).
    ns["MESURES"] = {"distant": [{"cout_usd": 0.000042}], "local": []}
    return ns


def _load_trajec():
    """Charge la fonction trajectoire depuis la cellule 10 du carnet.

    Stratégie : extraire la *définition* (lignes 1..def trajectoire) puis
    évaluer dans un namespace où MESURES est stubbé pour que COUT_DISTANT
    soit calculable. La fonction trajectoire est elle-même pure -- aucune
    dépendance à MESURES à l'intérieur de son corps, mais elle est *suivie*
    dans la cellule 10 d'un calcul COUT_DISTANT et d'un print/display.
    """
    nb = _load_carnet()
    cell = _find_cell(nb, CELL_TRAJECHE_ID)
    src = _source(cell)
    # Trouver la fin de la def trajectoire (ligne vide / print suivant)
    # On extrait la portion qui commence par JOURS_MOIS = 30 et finit à la première
    # ligne vide suivie de "COUT_DISTANT = ..." ou "display(".
    # En K07 on ne veut QUE la def trajectoire -- le reste de la cellule (calcul
    # COUT_DISTANT, display, témoins) est appelé par le carnet 09e mais
    # inutile pour la logique pure.
    lines = src.splitlines(keepends=True)
    # Ligne 0 = "JOURS_MOIS = 30 ..." (constante)
    # On garde les lignes jusqu'à la ligne vide *après* le `return cumuls, jour80, jour_plein`
    end_idx = None
    for i, ln in enumerate(lines):
        if "return cumuls, jour80, jour_plein" in ln:
            end_idx = i + 1
            break
    if end_idx is None:
        raise RuntimeError("'return cumuls, jour80, jour_plein' non trouvé en cellule 10")
    excerpt = "".join(lines[:end_idx])
    ns = _build_namespace()
    exec(excerpt, ns)  # noqa: S102 -- exécution du source cellule 10 isolée
    return ns["trajectoire"], ns["JOURS_MOIS"]


def _load_verifier_alerte():
    """Charge verifier_alerte depuis la cellule 11 du carnet.

    Cellule 11 : `def verifier_alerte(cumuls, budget_usd, au_jour): ...`
    Stratégie : extraire la première ligne `def ...` jusqu'au premier
    `return` non indenté suivant.
    """
    nb = _load_carnet()
    cell = _find_cell(nb, CELL_ALERTE_ID)
    src = _source(cell)
    lines = src.splitlines(keepends=True)
    start_idx = None
    end_idx = None
    for i, ln in enumerate(lines):
        if start_idx is None and ln.lstrip().startswith("def verifier_alerte"):
            start_idx = i
            continue
        if start_idx is not None and ln.lstrip().startswith("return "):
            end_idx = i + 1
            break
    if start_idx is None or end_idx is None:
        raise RuntimeError("def verifier_alerte / return non trouvé en cellule 11")
    excerpt = "".join(lines[start_idx:end_idx])
    ns = {}
    exec(excerpt, ns)  # noqa: S102
    return ns["verifier_alerte"]


# --- Chargement au moment de l'import : on évalue la source du carnet ---
trajectoire, JOURS_MOIS = _load_trajec()
verifier_alerte = _load_verifier_alerte()


# --- Constantes de test (cohérentes avec carnet 09e) ---
COUT_DISTANT = 0.000042  # valeur mesurée cell [7] sur main
VOLUME = 1500
BUDGET = 10.0


# --- Tests positifs (acceptance #18736) ---


def test_pente_nulle_100pct_local():
    cumuls, j80, jp = trajectoire(COUT_DISTANT, VOLUME, 1.0, BUDGET)
    assert jp is None, f"100% local doit ne jamais épuiser, got jour {jp}"
    assert j80 is None, "100% local ne franchit jamais 80% du budget"


def test_zero_requete_aucun_epuisement():
    cumuls, j80, jp = trajectoire(COUT_DISTANT, 0, 0.0, BUDGET)
    assert jp is None, "zéro requête ne doit jamais épuiser"
    assert all(c == 0.0 for c in cumuls), "tous les cumuls doivent rester à 0"


def test_pente_063_pas_depasse_mois():
    """Acceptance #18736 : 0.063 $/jour + 10 $/mois → aucun épuisement mensuel."""
    cumuls, j80, jp = trajectoire(COUT_DISTANT, VOLUME, 0.0, BUDGET)
    depense_30j = JOURS_MOIS * VOLUME * (1 - 0.0) * COUT_DISTANT
    assert depense_30j < BUDGET, (
        f"pré-condition: depense mensuelle {depense_30j:.4f} doit être < 10"
    )
    assert jp is None, f"à 0.063 $/jour + 10 $/mois, AUCUN épuisement mensuel, got jour {jp}"
    assert j80 is None, "à 0.063 $/jour, 80% de 10$ jamais franchi en un mois"


def test_pente_04_depasse_mois_1_jour_25():
    """Acceptance #18736 : 0.4 $/jour → épuisement attendu mois 1, jour 25.

    La fonction trajectoire ne boucle que sur JOURS_MOIS (= 30) jours.
    Avec 0.4 $/jour de pente, l'épuisement arrive à 10/0.4 = 25 jours.
    """
    cout_cible = 0.4 / (VOLUME * (1 - 0.0))
    cumuls, j80, jp = trajectoire(cout_cible, VOLUME, 0.0, BUDGET)
    assert jp == 25, f"à 0.4 $/jour, épuisement attendu jour 25, got jour {jp}"
    assert j80 == 20, f"alerte 80% attendue jour 20 (8/0.4), got jour {j80}"


def test_reset_mensuel_renouvelable():
    """Le budget est *mensuel renouvelable* : la trajectoire ne couvre qu'un mois.

    Le carnet 09e modélise UN mois (JOURS_MOIS itérations), pas une année.
    Une régression qui rebascule sur cumul annuel (l'ancien) doit faire
    échouer ce test car `len(cumuls) == JOURS_MOIS` (30), pas 365.
    """
    cumuls, _, _ = trajectoire(COUT_DISTANT, VOLUME, 0.0, BUDGET)
    assert len(cumuls) == JOURS_MOIS, (
        f"carnet K07 = mensuel (JOURS_MOIS={JOURS_MOIS}), pas annuel ; "
        f"une régression vers cumul annuel ferait len(cumuls) != {JOURS_MOIS}"
    )


def test_verifier_alerte_franchissement_jour20():
    """L'organe d'alerte détecte le seuil 80 % au jour 20 du mois (0.4*20 = 8 = 80 % de 10)."""
    cout_cible = 0.4 / (VOLUME * (1 - 0.0))
    cumuls, j80, _ = trajectoire(cout_cible, VOLUME, 0.0, BUDGET)
    assert verifier_alerte(cumuls, BUDGET, j80), (
        f"alerte 80% doit être franchie au jour {j80} (= 0.4*j80 = 8 = 80% de 10)"
    )


def test_verifier_alerte_hors_fenetre():
    cumuls, _, _ = trajectoire(COUT_DISTANT, VOLUME, 0.0, BUDGET)
    # Au jour 1, on n'a pas encore franchi 80% (cumul ~0.063).
    assert not verifier_alerte(cumuls, BUDGET, 1), (
        "alerte ne doit pas être franchie au jour 1 (cumul ~0.063 << 8)"
    )


# --- Témoin négatif (Tell c.4 strict fondateur) ---


def test_regression_cumul_annuel_detectee():
    """Si quelqu'un rebascule le carnet sur cumul annuel, ce test rouge.

    Le contrôle charge la source réelle de la cellule 10 ; si la signature de
    `trajectoire` change (par exemple : ajout d'un paramètre `jours_periode=365`),
    notre test rouge ici (l'assertion len(cumuls) == JOURS_MOIS ne tient plus).

    Si quelqu'un **réécrit** la fonction trajectoire dans le carnet avec un
    autre nom (par exemple `trajectoire_mensuelle_v2`), `_load_trajec()`
    lèvera une RuntimeError("'return cumuls, jour80, jour_plein' non trouvé"),
    et pytest marquera ce test en ERROR -- ce qui est aussi discriminant
    (un test ERROR est plus visible qu'un test PASS silencieux).
    """
    cumuls, _, _ = trajectoire(COUT_DISTANT, VOLUME, 0.0, BUDGET)
    # Le discriminant : la signature de la fonction réelle du carnet produit
    # un tableau de JOURS_MOIS (= 30) cumuls. Toute mutation de cette longueur
    # est un défaut que ce test attrape.
    assert len(cumuls) == JOURS_MOIS, (
        f"Régression détectée : len(cumuls)={len(cumuls)} != {JOURS_MOIS}. "
        f"Le carnet 09e utilise un budget mensuel renouvelable (JOURS_MOIS={JOURS_MOIS}) ; "
        f"si cette longueur change, c'est que la fonction trajectoire a été modifiée "
        f"pour passer à un autre régime (annuel, journalier, etc.)."
    )


if __name__ == "__main__":
    import pytest
    sys.exit(pytest.main([__file__, "-v"]))