"""Organes canoniques de la ligne dowhy -- sensibilite au confondeur cache (DoWhy-4).

Issue #14049 (grain DoWhy-4). DoWhy-1 suppose le graphe, DoWhy-3 le decouvre
(avec sa borne structurelle). Ce module attaque l'hypothese qu'aucun des deux
ne peut trancher : **l'existence d'un confondeur NON OBSERVE**. L'enonce cible
de l'issue : « quelle force devrait avoir un confondeur cache pour annuler cet
effet ? » -- un chiffre, pas une reserve rhetorique.

Trois formalisations SOTA de la meme question, reellement executees (regle F /
SOTA-OK -- ``dowhy`` natif, jamais de reimplementation jouet) :

1. **Robustness value (R2 partiel)** -- Cinelli & Hazlett 2020, via
   ``refute_estimate(..., simulation_method="linear-partial-R2")`` : le R2
   partiel minimal qu'un confondeur cache devrait avoir AVEC le traitement ET
   AVEC l'issue (apres ajustement) pour annuler l'estime. Repondu sur monde
   continu lineaire.
2. **E-value** -- Ding & VanderWeele 2017, via ``simulation_method="e-value"``
   (implemente des R packages EValue/tipr) : sur l'echelle des risques
   relatifs, la force d'association minimale qu'un confondeur cache devrait
   avoir avec le traitement ET l'issue pour expliquer entierement
   l'association. Avec le benchmark McGowan & Greevy : l'E-value OBSERVE de
   chaque covariable mesuree, pour comparer l'hypothetique au reel.
3. **Bornes de Rosenbaum (Gamma)** -- Rosenbaum 2002 : sur paires appariees,
   le facteur de desequilibre cache minimal Gamma* qui rend l'effet non
   significatif. Calcul exact binomial (il n'existe pas de package Python
   etabli pour cette borne -- R ``rbounds`` est la reference ; la borne EST
   une binomiale, le calcul exact est la methode, pas un contournement).

Et le pont concret : ``confondeur_simule`` execute le refuter
``direct-simulation`` de dowhy -- un confondeur U* de force croissante est
injecte, l'estime ajuste est recalcule, la COURBE DE BASCULE montre ou
l'effet croise zero.

Pieges API dowhy 0.14 que ce module encapsule, mesures :

1. ``linear-partial-R2`` exige ``effect_fraction_on_treatment`` et
   ``effect_fraction_on_outcome`` en **LISTES**. Un int devient un array 0-d
   qui s'effondre en scalaire -> ``any()`` sur un float leve TypeError ; un
   ndarray n'est pas dans ``[int, list, float]`` -> l'attribut n'est jamais
   assigne -> AttributeError.
2. ``linear-partial-R2`` exige ``benchmark_common_causes`` explicite : sans
   lui, ``r2tu_w`` reste None et ``compute_bias_adjusted`` crashe sur NoneType.
3. GLM : ``estimate_effect(...).value`` rend un CONTRASTE MARGINAL (ratio de
   risques predits, ~1.04 mesure), pas le RR. Le log-RR du lien log se lit
   sur le COEFFICIENT (position 1 -- dowhy renomme les regressieurs x1, x2).
4. L'E-value de la borne d'IC peut valoir ``None`` quand l'IC contient deja 1
   (l'association est deja « tippee » au seuil).
5. Verifie : l'E-value rendu par dowhy vaut exactement
   ``RR + sqrt(RR * (RR - 1))`` (2.9796 mesure contre la formule).

Resultats enseignes (mesures, 10 seeds, monde par defaut) :

- Monde continu : estime naive ~1.15 (vrai 0.5, oracle ajuste C+U ~0.53),
  robustness value ~0.68 ; le U REEL de ce monde a un R2 partiel de ~0.49
  avec X et ~0.45 avec Y -- en dessous du RV : l'association ne peut pas etre
  annulee par un confondeur de cette force, mais elle est quand meme reduite
  de moitie. La sensibilite ne certifie pas l'estime ; elle chiffre l'attaque.
- Monde binaire : RR naive ~1.8 (vrai 1.49), E-value ~3.0, E-value de l'IC
  ~2.0, E-value OBSERVE du confondeur mesure C ~1.16 -- un cache qui
  annulerait devrait etre bien plus fort que C. Gamma* de Rosenbaum ~1.3 :
  un desequilibre cache modeste suffirait a masquer l'effet apparie.

Fonctions exposees
------------------

- ``generer_donnees_continues(n, seed, cacher_u, coef_u_x, coef_u_y)`` --
  monde A : X continu, Y continu, confondeur observe C + confondeur cache U.
- ``generer_donnees_binaires(n, seed, cacher_u, b_x, b_u_y)`` -- monde B :
  X binaire, Y binaire rare (~7 %), C binaire ; risques multiplicatifs
  (lien log), RR vrai = exp(B_X) ~ 1.49.
- ``estimer_effet_continu(donnees)`` -- dowhy backdoor linear_regression,
  ajustement {C} (U invisible a l'analyste).
- ``robustesse_partielle_r2(model, estimand, estimate, benchmark)`` -- le
  chiffre de Cinelli-Hazlett : robustness_value (annuler) et
  robustness_value_alpha (rendre non significatif).
- ``r2_partiel(donnees, cible, variable, ajustement)`` -- le R2 partiel
  exact d'une variable (statsmodels OLS imbriques) : la verite terrain
  quand la variable est observee.
- ``confondeur_simule(model, estimand, estimate, k_fixe, k_max, pas,
  diagonale)`` -- refute_estimate direct-simulation en boucle : la courbe de
  bascule de l'estime ajuste contre la force du confondeur simule.
- ``kappa_bascule(tableau)`` -- le point de bascule (interpolation au
  franchissement de zero).
- ``estimer_rr_binaire(donnees)`` -- dowhy GLM Poisson lien log, RR lu sur
  le coefficient (piege 3 encapsule).
- ``sensibilite_e_value(model, estimand, estimate, tracer)`` -- l'E-value
  dowhy natif + les benchmarks McGowan-Greevy.
- ``paires_appariees(donnees, seed)`` -- appariement exact 1:1 sur C, rend
  les paires discordantes (1 = traite malade / temoin sain).
- ``bornes_rosenbaum(succes, m, gamma)`` -- bornes exactes de la p-valeur du
  test du signe sous desequilibre cache Gamma.
- ``gamma_critique(succes, m, seuil)`` -- Gamma* : la borne haute croise le
  seuil.
- ``verdict_sensibilite(r2_u_x, r2_u_y, robustesse)`` / ``verdict_e_value`` --
  les verdicts honnetes.

Doctrine de parametrisation (cf. ``dowhy_organs.py``,
``dowhy_discovery_organs.py``) : RandomState LOCAL par fonction, constantes
en module documentees, dataclasses de sortie, imports lourds dans les
fonctions.

References
----------

- Notebook consommateur : ``DoWhy-4-Sensibilite-Confounder-Cache.ipynb``.
- Robustness value : Cinelli & Hazlett, « Making Sense of Sensitivity :
  Extending Omitted-Variable Bias », JRSS-B 82 (2020).
- E-value : VanderWeele & Ding, « Sensitivity Analysis in Observational
  Research: Introducing the E-Value », Annals of Internal Medicine 167
  (2017) ; benchmark McGowan & Greevy Jr., arXiv:2011.07030.
- Bornes : Rosenbaum, « Observational Studies » (2e ed., Springer 2002),
  chap. 4 (le test du signe sur paires discordantes).
- API dowhy 0.14 : ``CausalModel.refute_estimate(method_name=
  "add_unobserved_common_cause", simulation_method=...)``.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

import numpy as np
import pandas as pd

# ---------------------------------------------------------------------------
# Constantes par defaut -- l'unique verite des deux simulateurs
# ---------------------------------------------------------------------------
# Monde A (continu), tous bruits gaussiens independants :
#     U ~ N(0, 1)                          confondeur CACHE
#     C ~ N(0, 1)                          confondeur OBSERVE
#     X = COEF_U_X * U + COEF_C_X * C + N(0, BRUIT_X)
#     Y = TAU_VRAI  * X + COEF_U_Y * U + COEF_C_Y * C + N(0, BRUIT_Y)
# L'analyste ne voit que (X, Y, C) : son ajustement backdoor {C} laisse U
# faire le travail -> l'estime naive (~1.15) est biaisé vers le haut contre
# l'effet vrai TAU_VRAI = 0.5 (oracle ajuste C+U ~ 0.53).
TAU_VRAI: float = 0.5
COEF_U_X: float = 0.7
COEF_C_X: float = 0.5
COEF_U_Y: float = 0.9
COEF_C_Y: float = 0.4
BRUIT_X: float = 0.7
BRUIT_Y: float = 0.7
N_A_DEFAUT: int = 2000

# Monde B (binaire, issue rare ~ 7 %) :
#     U ~ N(0, 1) ; C ~ Bernoulli(P_C)
#     X ~ Bernoulli(sigmoid(LOGIT_U * U + LOGIT_C * C + LOGIT_A))
#     P(Y=1) = clip(exp(A0 + B_X * X + B_U_Y * U + B_C_Y * C), 0, 1)
# Risques multiplicatifs (lien log) : le GLM Poisson lien log de dowhy est
# bien specifie, et le RR vrai vaut exp(B_X) ~ 1.49. U cache fait monter le
# RR naive ajuste-C a ~1.8.
B_X: float = 0.4
B_U_Y: float = 0.5
B_C_Y: float = 0.3
A0: float = -3.2
LOGIT_U: float = 0.9
LOGIT_C: float = 0.5
LOGIT_A: float = -0.3
P_C: float = 0.4
N_B_DEFAUT: int = 3000

SEUIL_ALPHA: float = 0.05
SEED_SIMULATION: int = 20260913  # re-seed du RNG global de dowhy (cf. confondeur_simule)


# ---------------------------------------------------------------------------
# Generateurs -- RandomState LOCALE, reproductible, U optionnellement cache
# ---------------------------------------------------------------------------
def generer_donnees_continues(
    n: int = N_A_DEFAUT,
    seed: int = 42,
    cacher_u: bool = True,
    coef_u_x: float = COEF_U_X,
    coef_u_y: float = COEF_U_Y,
    tau: float = TAU_VRAI,
    bruit_y: float = BRUIT_Y,
) -> pd.DataFrame:
    """Monde A : traitement continu, issue continue, confondeur cache U.

    ``cacher_u=True`` (defaut) rend la vue ANALYSTE (X, Y, C) -- celle que
    voit le praticien qui soupconne un confondeur cache sans le mesurer.
    ``cacher_u=False`` rend la vue ORACLE (avec U), pour la verite terrain
    (R2 partiels reels, estime ajuste C+U). ``coef_u_*``, ``tau`` et
    ``bruit_y`` permettent d'explorer : renforcer U renforce l'association
    OBSERVEE autant que l'attaque (le RV monte avec) ; affaiblir l'effet
    vrai sous bruit eleve fait baisser le RV sous la force de U --
    l'association devient annulable (mesure : exercice 1 du notebook).
    """
    rng = np.random.RandomState(seed)
    u = rng.normal(0, 1, n)
    c = rng.normal(0, 1, n)
    x = coef_u_x * u + COEF_C_X * c + rng.normal(0, BRUIT_X, n)
    y = tau * x + coef_u_y * u + COEF_C_Y * c + rng.normal(0, bruit_y, n)
    donnees = {"X": x, "Y": y, "C": c}
    if not cacher_u:
        donnees["U"] = u
    return pd.DataFrame(donnees)


def generer_donnees_binaires(
    n: int = N_B_DEFAUT,
    seed: int = 42,
    cacher_u: bool = True,
    b_x: float = B_X,
    b_u_y: float = B_U_Y,
) -> pd.DataFrame:
    """Monde B : traitement binaire, issue binaire rare, C binaire.

    Vue analyste (X, Y, C) par defaut, oracle avec U sinon. Les risques sont
    multiplicatifs (lien log) : le RR conditionnel vrai vaut ``exp(b_x)``.
    """
    rng = np.random.RandomState(seed)
    u = rng.normal(0, 1, n)
    c = (rng.uniform(0, 1, n) < P_C).astype(int)
    p_x = 1.0 / (1.0 + np.exp(-(LOGIT_U * u + LOGIT_C * c + LOGIT_A)))
    x = (rng.uniform(0, 1, n) < p_x).astype(int)
    p_y = np.clip(np.exp(A0 + b_x * x + b_u_y * u + B_C_Y * c), 0.0, 1.0)
    y = (rng.uniform(0, 1, n) < p_y).astype(int)
    donnees = {"X": x, "Y": y, "C": c}
    if not cacher_u:
        donnees["U"] = u
    return pd.DataFrame(donnees)


# ---------------------------------------------------------------------------
# Monde A : estime naive + robustesse value (R2 partiel)
# ---------------------------------------------------------------------------
@dataclass
class ResultatEffetContinu:
    """Estime backdoor dowhy du monde A, avec le necessaire pour refuter."""

    model: object
    estimand: object
    estimate: object
    value: float
    se: float
    ic: Tuple[float, float]


def estimer_effet_continu(donnees: pd.DataFrame) -> ResultatEffetContinu:
    """Estime dowhy backdoor (linear_regression) en ajustant {C} seulement.

    C'est l'estime NAIF : U n'est pas dans les donnees de l'analyste. Le
    modele dowhy construit ici est reutilise par tous les refuters de
    sensibilite (robustesse_partielle_r2, confondeur_simule).
    """
    from dowhy import CausalModel

    colonnes = [c for c in donnees.columns if c in ("X", "Y", "C")]
    model = CausalModel(
        data=donnees[colonnes], treatment="X", outcome="Y", common_causes=["C"]
    )
    estimand = model.identify_effect(proceed_when_unidentifiable=True)
    estimate = model.estimate_effect(
        estimand, method_name="backdoor.linear_regression", test_significance=True
    )
    se = float(np.atleast_1d(estimate.get_standard_error())[0])
    return ResultatEffetContinu(
        model=model,
        estimand=estimand,
        estimate=estimate,
        value=float(estimate.value),
        se=se,
        ic=(float(estimate.value - 1.96 * se), float(estimate.value + 1.96 * se)),
    )


@dataclass
class ResultatRobustesse:
    """Le chiffre de Cinelli-Hazlett : la force qui annule l'effet."""

    robustness_value: float
    robustness_value_alpha: float
    r2yt_w: float
    stats: Dict[str, object]
    benchmarking: pd.DataFrame
    analyzer: object


def robustesse_partielle_r2(
    model: object,
    estimand: object,
    estimate: object,
    benchmark: Optional[List[str]] = None,
) -> ResultatRobustesse:
    """Robustness value via ``simulation_method="linear-partial-R2"``.

    ``robustness_value`` : le R2 partiel minimal d'un confondeur cache AVEC
    le traitement ET avec l'issue (apres ajustement de {C}) pour ANNULER
    l'estime (le ramener a zero). ``robustness_value_alpha`` : idem pour le
    rendre statistiquement non significatif.

    Encapsule les pieges 1 et 2 du docstring module : fractions passees en
    LISTES et ``benchmark_common_causes`` explicite (defaut : ["C"]).
    """
    if benchmark is None:
        benchmark = ["C"]
    refut = model.refute_estimate(
        estimand,
        estimate,
        method_name="add_unobserved_common_cause",
        simulation_method="linear-partial-R2",
        significance_level=SEUIL_ALPHA,
        benchmark_common_causes=benchmark,
        effect_fraction_on_treatment=[1.0],
        effect_fraction_on_outcome=[1.0],
        plot_estimate=False,
    )
    return ResultatRobustesse(
        robustness_value=float(refut.stats["robustness_value"]),
        robustness_value_alpha=float(refut.stats["robustness_value_alpha"]),
        r2yt_w=float(refut.stats["r2yt_w"]),
        stats=dict(refut.stats),
        benchmarking=refut.benchmarking_results,
        analyzer=refut,
    )


def r2_partiel(
    donnees: pd.DataFrame,
    cible: str,
    variable: str,
    ajustement: List[str],
) -> float:
    """R2 partiel exact de ``variable`` pour ``cible`` apres ``ajustement``.

    Regression lineaire imbriquee (statsmodels OLS) :
    ``R2_partiel = (R2_plein - R2_reduit) / (1 - R2_reduit)``. C'est la
    verite terrain quand la variable est observee : le R2 partiel REEL du
    confondeur cache U se calcule sur la vue oracle, puis se compare a la
    robustness value.
    """
    import statsmodels.api as sm

    exogenes = [c for c in ajustement if c != variable]
    r_plein = sm.OLS(donnees[cible], sm.add_constant(donnees[exogenes + [variable]])).fit()
    r_reduit = sm.OLS(donnees[cible], sm.add_constant(donnees[exogenes])).fit()
    return float((r_plein.rsquared - r_reduit.rsquared) / (1.0 - r_reduit.rsquared))


def verdict_sensibilite(
    r2_u_x: float,
    r2_u_y: float,
    robustesse: ResultatRobustesse,
) -> Dict[str, object]:
    """Le verdict honnete du monde continu : survive a QUEL confondeur.

    La robustness value de Cinelli & Hazlett est le seuil pour un
    confondeur de force EGALE des deux cotes (meme R2 partiel avec le
    traitement et avec l'issue). La comparaison juste pour un confondeur
    reel de forces (r2_u_x, r2_u_y) : meme en prenant son cote le plus
    fort des deux cotes, annule-t-il ? Si max(r2_u_x, r2_u_y) < RV, aucun
    cache aussi fort que ce confondeur n'annule l'estime. Comparer les R2
    partiels REELS d'un confondeur connu au RV chiffre exactement
    l'attaque, sans certifier l'estime.
    """
    rv = robustesse.robustness_value
    force_max = max(r2_u_x, r2_u_y)
    if force_max < rv:
        message = (
            f"RESULTAT : l'association survit a ce confondeur -- meme a force "
            f"egale des deux cotes au niveau de son cote le plus fort "
            f"({force_max:.2f} < RV {rv:.2f}), le cache n'annule pas l'estime. "
            f"ATTENTION : survivre a l'annulation n'est pas etre juste -- "
            f"l'estime reste biaisé tant que le confondeur n'est pas mesure."
        )
        verdict = "SURVIT_A_CE_CONFOUNDEUR"
    else:
        message = (
            f"RESULTAT : l'association est annulable -- un cache a force egale "
            f"des deux cotes de {force_max:.2f} (>= RV {rv:.2f}) suffit a "
            f"expliquer l'estime. L'effet observe n'est PAS distingue d'un "
            f"biais de cette force : c'est un chiffre, pas une certification."
        )
        verdict = "ANNULABLE_PAR_CE_CONFOUNDEUR"
    return {"verdict": verdict, "robustness_value": rv, "message": message}


# ---------------------------------------------------------------------------
# Monde A : le confondeur simule -- la courbe de bascule
# ---------------------------------------------------------------------------
def confondeur_simule(
    model: object,
    estimand: object,
    estimate: object,
    k_fixe: float = 0.7,
    k_max: float = 1.6,
    pas: float = 0.2,
    diagonale: bool = False,
) -> pd.DataFrame:
    """Refuter par confondeur SIMULE (direct-simulation) en balayant la force.

    Pour chaque valeur k, un confondeur U* gaussien est injecte dans les
    donnees avec un coefficient k sur l'issue (et k_fixe sur le traitement ;
    en mode ``diagonale``, k des deux cotes -- la convention « meme force des
    deux cotes » de l'E-value), puis l'estime backdoor est recalcule avec
    U* dans l'ensemble d'ajustement. Rend un DataFrame [k, kappa_t,
    estime_ajuste] : la courbe de bascule.

    Appels monovalueurs (le mode grille de dowhy ne rend que (min, max) --
    la matrice complete serait dans new_effect_array ; la boucle garde le
    couple (k, estime) explicite).

    REPRODUCTIBILITE : dowhy tire U* du RNG numpy GLOBAL
    (``scipy.stats.norm().rvs`` sans graine) -- sans re-seed, la courbe
    varie d'un process a l'autre. Chaque appel re-seed le RNG global avec
    une graine derivee de l'indice, la courbe est byte-reproductible.
    """
    valeurs = np.round(np.arange(0.0, k_max + pas / 2, pas), 4)
    lignes = []
    for i, k in enumerate(valeurs):
        k_t = float(k) if diagonale else float(k_fixe)
        np.random.seed(SEED_SIMULATION + i)
        refut = model.refute_estimate(
            estimand,
            estimate,
            method_name="add_unobserved_common_cause",
            simulation_method="direct-simulation",
            confounders_effect_on_treatment="linear",
            confounders_effect_on_outcome="linear",
            effect_strength_on_treatment=k_t,
            effect_strength_on_outcome=float(k),
            plotmethod=None,
        )
        lignes.append(
            {
                "k": float(k),
                "kappa_t": k_t,
                "estime_ajuste": float(np.atleast_1d(refut.new_effect)[0]),
            }
        )
    return pd.DataFrame(lignes)


def kappa_bascule(tableau: pd.DataFrame) -> Optional[float]:
    """Le point de bascule : premiere valeur de k ou l'estime croise zero.

    Interpolation lineaire entre le dernier positif et le premier
    non-positif. Rend None si la courbe ne bascule pas dans la plage
    balayee.
    """
    estimes = tableau["estime_ajuste"].to_numpy()
    ks = tableau["k"].to_numpy()
    for i in range(1, len(estimes)):
        if estimes[i - 1] > 0 >= estimes[i]:
            e0, e1 = estimes[i - 1], estimes[i]
            k0, k1 = ks[i - 1], ks[i]
            if e0 == e1:
                return float(k1)
            return float(k0 + (k1 - k0) * e0 / (e0 - e1))
    return None


# ---------------------------------------------------------------------------
# Monde B : RR binaire (GLM Poisson) + E-value natif
# ---------------------------------------------------------------------------
@dataclass
class ResultatRR:
    """RR de Poisson lien log, lu sur le coefficient (piege 3 encapsule)."""

    model: object
    estimand: object
    estimate: object
    log_rr: float
    se_log_rr: float
    rr: float
    rr_inf: float
    rr_sup: float


def estimer_rr_binaire(donnees: pd.DataFrame) -> ResultatRR:
    """Estime le RR via dowhy ``backdoor.generalized_linear_model`` (Poisson).

    PIEGE ENCAPSULE : ``estimate_effect(...).value`` rend un contraste
    marginal sur l'echelle des probabilites predites (~1.04 mesure sur le
    monde par defaut), PAS le risque relatif. Le log-RR du lien log se lit
    sur le coefficient du traitement, en position 1 -- dowhy renomme les
    regressieurs (x1 = traitement, x2.. = confondeurs). L'IC est
    ``coef +- 1.96 * se`` retransforme par exp.
    """
    import statsmodels.api as sm
    from dowhy import CausalModel

    colonnes = [c for c in donnees.columns if c in ("X", "Y", "C")]
    model = CausalModel(
        data=donnees[colonnes], treatment="X", outcome="Y", common_causes=["C"]
    )
    estimand = model.identify_effect(proceed_when_unidentifiable=True)
    estimate = model.estimate_effect(
        estimand,
        method_name="backdoor.generalized_linear_model",
        method_params={"init_params": {"glm_family": sm.families.Poisson()}},
        test_significance=True,
    )
    ajuste = estimate.estimator.model
    log_rr = float(ajuste.params.iloc[1])
    se = float(ajuste.bse.iloc[1])
    return ResultatRR(
        model=model,
        estimand=estimand,
        estimate=estimate,
        log_rr=log_rr,
        se_log_rr=se,
        rr=float(np.exp(log_rr)),
        rr_inf=float(np.exp(log_rr - 1.96 * se)),
        rr_sup=float(np.exp(log_rr + 1.96 * se)),
    )


@dataclass
class ResultatEValue:
    """L'E-value dowhy natif + le benchmark des covariables mesurees."""

    rr_converti: float
    evalue_estime: float
    evalue_ic_limite: Optional[float]
    benchmarking: pd.DataFrame
    analyzer: object
    stats: Dict[str, object]


def sensibilite_e_value(
    model: object,
    estimand: object,
    estimate: object,
    tracer: bool = False,
) -> ResultatEValue:
    """L'E-value de Ding & VanderWeele, calcule par dowhy (des R EValue/tipr).

    ``evalue_estime`` : la force d'association minimale (echelle RR) qu'un
    confondeur cache devrait avoir AVEC le traitement ET avec l'issue,
    conditionnellement aux covariables mesurees, pour expliquer ENTIEREMENT
    l'association estimee. ``evalue_ic_limite`` : idem pour la borne de l'IC
    la plus proche de 1 (None si l'IC contient deja 1 -- piege 4).

    ``benchmarking`` : l'E-value OBSERVE de chaque covariable mesuree
    (McGowan & Greevy : on la retire, on re-estime, on mesure le
    deplacement) -- l'hypothetique compare au reel.
    """
    refut = model.refute_estimate(
        estimand,
        estimate,
        method_name="add_unobserved_common_cause",
        simulation_method="e-value",
        plot_estimate=tracer,
    )
    return ResultatEValue(
        rr_converti=float(refut.stats["converted_estimate"]),
        evalue_estime=float(refut.stats["evalue_estimate"]),
        evalue_ic_limite=(
            None
            if refut.stats.get("evalue_lower_ci") is None
            else float(refut.stats["evalue_lower_ci"])
        ),
        benchmarking=refut.benchmarking_results,
        analyzer=refut,
        stats=dict(refut.stats),
    )


def verdict_e_value(evalue: ResultatEValue) -> Dict[str, object]:
    """Le verdict honnete du monde binaire : robuste par RAPPORT a quoi.

    Un E-value brut (ex. 3.0) ne se lit pas dans l'absolu -- « 3 c'est
    grand ? » n'a pas de reponse universelle. Le benchmark McGowan-Greevy
    donne l'echelle : si le confondeur MESURE le plus fort de l'etude a un
    E-value observe de 1.2, un cache qui annulerait devrait etre ~2.5x plus
    fort que ce confondeur reel. La robustesse est RELATIVE aux forces
    observees dans l'etude -- un RESULTAT, pas une certification.
    """
    observes = evalue.benchmarking["observed_covariate_e_value"].astype(float)
    plus_fort_observe = float(observes.max())
    rapport = evalue.evalue_estime / plus_fort_observe if plus_fort_observe > 0 else float("inf")
    if rapport >= 1.5:
        verdict = "ROBUSTE_RELATIVEMENT_AUX_OBSERVES"
        conclusion = (
            f"un confondeur cache devrait etre {rapport:.1f}x plus fort "
            f"(echelle E-value) que le meilleur confondeur mesure pour "
            f"annuler l'association"
        )
    else:
        verdict = "FRAGILE_RELATIVEMENT_AUX_OBSERVES"
        conclusion = (
            f"un confondeur cache seulement {rapport:.1f}x plus fort que le "
            f"meilleur confondeur mesure suffirait a annuler l'association"
        )
    message = (
        f"RESULTAT : E-value {evalue.evalue_estime:.2f} contre un maximum "
        f"observe de {plus_fort_observe:.2f} -- {conclusion}. La robustesse "
        f"est relative aux forces observees dans CETTE etude, pas une "
        f"certification d'absence de confondeur."
    )
    return {"verdict": verdict, "rapport": float(rapport), "message": message}


# ---------------------------------------------------------------------------
# Monde B : paires appariees et bornes de Rosenbaum (exactes)
# ---------------------------------------------------------------------------
def paires_appariees(donnees: pd.DataFrame, seed: int = 0) -> np.ndarray:
    """Appariement exact 1:1 sur C ; rend les paires DISCORDANTES.

    Chaque paire (un traite, un temoin de la meme strate de C, tirage
    aleatoire reproductible) contribue 1 si le traite est malade et le
    temoin sain, 0 sinon. Les paires concordantes (meme issue) ne
    renseignent pas : le test du signe de Rosenbaum ne vit que sur les
    discordantes.
    """
    rng = np.random.RandomState(seed)
    indicateurs: List[int] = []
    for strate in sorted(donnees["C"].unique()):
        d = donnees[donnees["C"] == strate]
        traites = d[d["X"] == 1].sample(frac=1, random_state=rng)
        temoins = d[d["X"] == 0].sample(frac=1, random_state=rng)
        m = min(len(traites), len(temoins))
        for (_, a), (_, b) in zip(traites.iloc[:m].iterrows(), temoins.iloc[:m].iterrows()):
            if a["Y"] != b["Y"]:
                indicateurs.append(int(a["Y"] == 1 and b["Y"] == 0))
    return np.array(indicateurs, dtype=int)


def bornes_rosenbaum(succes: int, m: int, gamma: float) -> Tuple[float, float]:
    """Bornes exactes de la p-valeur du test du signe sous biais cache Gamma.

    Sous l'hypothese nulle sans biais cache, chaque paire discordante est un
    tirage equitable (p = 1/2) de « le traite est le malade ». Un
    desequilibre cache Gamma borne p dans [1/(1+Gamma), Gamma/(1+Gamma)] ;
    les bornes de la p-valeur sont les queues binomiales exactes a ces deux
    extremums (Rosenbaum 2002, chap. 4). Gamma = 1 rend la p-valeur observee.
    """
    from scipy import stats as sps

    if gamma < 1.0:
        raise ValueError("Gamma >= 1 requis (Gamma = 1 : absence de biais cache)")
    p_basse = float(sps.binom.sf(succes - 1, m, 1.0 / (1.0 + gamma)))
    p_haute = float(sps.binom.sf(succes - 1, m, gamma / (1.0 + gamma)))
    return p_basse, p_haute


def gamma_critique(succes: int, m: int, seuil: float = SEUIL_ALPHA) -> float:
    """Gamma* : le desequilibre cache minimal qui rend l'effet non significatif.

    Plus petit Gamma tel que la borne HAUTE de la p-valeur atteint le seuil
    (dichotomie sur la fonction continue en Gamma). C'est le chiffre de
    Rosenbaum : « a partir d'un desequilibre cache de Gamma*, meme le pire
    des mondes compatibles explique l'association appariée ».
    """
    from scipy.optimize import brentq

    def ecart(g: float) -> float:
        return bornes_rosenbaum(succes, m, g)[1] - seuil

    return float(brentq(ecart, 1.0, 100.0))
