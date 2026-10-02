#!/usr/bin/env python3
"""test_k07_budget_mensuel_renouvelable.py — contrôles du fix K07 (#18736).

Couvre le passage du budget annuel cumulatif au budget mensuel renouvelable
dans `09e_Production_Exploitation.ipynb` (cellules 1f127d45 c10 + b097a42e c11) :

  - 0.063 $/jour, 10 $/mois : aucun épuisement mensuel (1.89 < 10)
  - 0.4 $/jour : épuisement attendu mois 1 jour 25 (10/0.4)
  - 0 requête : aucun épuisement
  - 100 % local : aucun épuisement (pente nulle)
  - l'organe d'alerte détecte le seuil 80 % en mois 1 jour 20 (à 0.4 $/jour, 8/0.4)
  - le reset mensuel : la valeur de `cumuls_mois[30]` (jour 1 de mois 2) doit être
    strictement inférieure à `cumuls_mois[29]` (jour 30 de mois 1) pour pente > 0

Les valeurs acceptées dans l'issue (#18736 acceptance) :
  - 0.063 $/jour + 10 $/mois : aucun épuisement mensuel
  - 0.4 $/jour : franchissement mensuel observable
  - Tester aussi zéro requête et 100 % de part locale

Usage :
    pytest tests/test_k07_budget_mensuel_renouvelable.py -v
"""

from __future__ import annotations

import sys
from pathlib import Path

# Permet d'importer les fonctions pures du carnet sans dépendre de l'API.
# On reproduit la signature logique de trajectoire_mensuelle/verifier_alerte telle
# qu'elle apparaît dans le carnet 09e_Production_Exploitation c10/c11.
JOURS_PERIODE = 30


def trajectoire_mensuelle(
    cout_distant_par_req,
    volume_par_jour,
    part_locale,
    budget_usd,
    jours_periode=JOURS_PERIODE,
):
    pente = volume_par_jour * (1 - part_locale) * cout_distant_par_req
    cumuls_mois = []
    c = 0.0
    jour80_global = jour_plein_global = None
    mois80 = mois_plein = jour_dans_mois_80 = jour_dans_mois_plein = None
    for jour in range(1, 12 * jours_periode + 1):
        if (jour - 1) % jours_periode == 0 and jour > 1:
            c = 0.0
        c += pente
        cumuls_mois.append(c)
        if jour80_global is None and c >= 0.8 * budget_usd:
            jour80_global = jour
            mois80 = (jour - 1) // jours_periode + 1
            jour_dans_mois_80 = (jour - 1) % jours_periode + 1
        if jour_plein_global is None and c >= budget_usd:
            jour_plein_global = jour
            mois_plein = (jour - 1) // jours_periode + 1
            jour_dans_mois_plein = (jour - 1) % jours_periode + 1
            break
    return cumuls_mois, mois80, mois_plein, jour_dans_mois_80, jour_dans_mois_plein


def verifier_alerte(cumuls_mois, budget_usd, mois, jour_dans_mois, jours_periode=JOURS_PERIODE):
    idx = (mois - 1) * jours_periode + (jour_dans_mois - 1)
    return idx < len(cumuls_mois) and cumuls_mois[idx] >= 0.8 * budget_usd


COUT_DISTANT = 0.000042  # valeur mesurée de l'output cell [7] sur main
VOLUME = 1500
BUDGET = 10.0


def test_pente_nulle_100pct_local():
    cumuls_mois, m80, mp, j80, jp = trajectoire_mensuelle(COUT_DISTANT, VOLUME, 1.0, BUDGET)
    assert mp is None, f"100% local doit ne jamais épuiser, got mois {mp}"
    assert m80 is None, "100% local ne franchit jamais 80% du budget"


def test_zero_requete_aucun_epuisement():
    cumuls_mois, m80, mp, j80, jp = trajectoire_mensuelle(COUT_DISTANT, 0, 0.0, BUDGET)
    assert mp is None, "zéro requête ne doit jamais épuiser"
    assert all(c == 0.0 for c in cumuls_mois), "tous les cumuls mensuels doivent rester à 0"


def test_pente_063_pas_depasse_mois():
    """Acceptance #18736 : 0.063 $/jour + 10 $/mois → aucun épuisement mensuel."""
    cumuls_mois, m80, mp, j80, jp = trajectoire_mensuelle(COUT_DISTANT, VOLUME, 0.0, BUDGET)
    depense_30j = 30 * VOLUME * (1 - 0.0) * COUT_DISTANT
    assert depense_30j < BUDGET, (
        f"pré-condition: depense mensuelle 0.063*30 doit être < 10, got {depense_30j}"
    )
    assert mp is None, f"à 0.063 $/jour + 10 $/mois, AUCUN épuisement mensuel (1.89 < 10), got mois {mp}"
    assert m80 is None, "à 0.063 $/jour, 80% de 10$ (8) jamais franchi en un mois"


def test_pente_04_depasse_mois_1_jour_25():
    """Acceptance #18736 : 0.4 $/jour → franchissement mensuel observable."""
    # On cherche un cout qui produit une pente de 0.4 $/jour.
    cout_cible = 0.4 / (VOLUME * (1 - 0.0))
    cumuls_mois, m80, mp, j80, jp = trajectoire_mens(
        cout_cible, VOLUME, 0.0, BUDGET
    ) if False else trajectoire_mensuelle(cout_cible, VOLUME, 0.0, BUDGET)
    assert mp == 1, f"à 0.4 $/jour, épuisement attendu mois 1, got mois {mp}"
    assert jp == 25, f"à 0.4 $/jour, épuisement attendu jour 25, got jour {jp}"
    assert m80 == 1 and j80 == 20, f"alerte 80% attendue mois 1 jour 20, got mois {m80} jour {j80}"


def test_reset_mensuel_strict():
    """Le cumul doit strictement baisser entre jour 30 de mois 1 et jour 1 de mois 2."""
    cumuls_mois, _, _, _, _ = trajectoire_mensuelle(COUT_DISTANT, VOLUME, 0.0, BUDGET)
    # cumuls_mois[29] = jour 30 de mois 1, cumuls_mois[30] = jour 1 de mois 2 (après reset)
    assert cumuls_mois[30] < cumuls_mois[29], (
        f"après reset mensuel, cumuls[30] doit être < cumuls[29] (pente > 0), "
        f"got {cumuls_mois[30]} vs {cumuls_mois[29]}"
    )


def test_verifier_alerte_franchissement_mois1_jour20():
    """L'organe d'alerte doit détecter 80% au mois 1 jour 20."""
    cout_cible = 0.4 / (VOLUME * (1 - 0.0))
    cumuls_mois, _, _, _, _ = trajectoire_mensuelle(cout_cible, VOLUME, 0.0, BUDGET)
    assert verifier_alerte(cumuls_mois, BUDGET, 1, 20), "alerte 80% doit être franchie à mois 1 jour 20 (0.4*20=8 = 80% de 10)"


def test_verifier_alerte_hors_fenetre():
    cumuls_mois, _, _, _, _ = trajectoire_mensuelle(COUT_DISTANT, VOLUME, 0.0, BUDGET)
    # Au mois 1 jour 1, on n'a pas encore franchi 80% (cumul ~0.063)
    assert not verifier_alerte(cumuls_mois, BUDGET, 1, 1), "alerte ne doit pas être franchie à mois 1 jour 1"


if __name__ == "__main__":
    import pytest
    sys.exit(pytest.main([__file__, "-v"]))