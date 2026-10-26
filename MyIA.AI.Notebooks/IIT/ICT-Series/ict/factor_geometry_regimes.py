"""Campagnes des regimes generatifs (suivi #20071) : resoudre les deux falsifiables.

Les constructions sont livrees depuis #20091 (``NoisedChannel`` dans
``bench_factorise``, ``ConditionalBench``, ``conditional_child_floor``) et le
carnet ICT-36 en a rendu une premiere lecture a 400 pas. Deux falsifiables
sont restes OUVERTS, et ce module porte les corrections de protocole qui
les tranchent :

1. **Bruit du canal -- la lecture doit exister aussi la ou le gate echoue.**
   La premiere passe ne rendait la geometrie qu'aux niveaux ou la perte
   jointe passait sous l'uniforme : or la question du critere est la
   LISIBILITE DU FACTEUR, pas la reussite du modele. La falsifiable
   (« overlap_coef_max retombe dans la bande du temoin au-dela d'un seuil,
   ou n'en sort jamais ») se joue precisement aux niveaux ou le modele
   n'apprend plus rien -- c'est la que la geometrie d'un modele qui n'a rien
   appris doit se confondre avec celle des initialisations non entrainees.
   :func:`sweep_channel_noise` entraîne PAR NIVEAU, rejoue le temoin a
   CHAQUE niveau et rend la lecture a TOUS les niveaux, gate reussi ou
   echoue (tagge).

2. **Structure conditionnelle -- de-saturer le discriminant.**
   L'``additivity_gap`` est un entier vivant au rang pres : sur les bancs
   Mess3 x Mess3, le temoin rendait la meme valeur aux six initialisations
   (bande de largeur NULLE, une bande qui ne discrimine aucun modele -- le
   controle independant mesurait deja -2.000 partout). La correction est
   double : la metrique continue ``overlap_energy`` (ajoutee au rapport par
   ce suivi, bandes de temoin de largeur non nulle) ET un budget plus fort
   (kappa eleve vers sa borne de stochasticite, 1200 pas, trois graines
   modele). :func:`conditional_campaign` mesure le banc conditionnel contre
   le controle INDEPENDANT aux memes marginales, meme enfant, memes seeds.

Les campagnes sont deterministes (seeds explicites), bornees (minutes CPU),
et se persistent en JSON sous ``ict/results/`` (convention des artefacts
committes de la serie) : le carnet ICT-36 lit les
artefacts, il ne rejoue pas la campagne (pattern artefacts-commits du banc
ICT-25).
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Dict, List, Sequence

import numpy as np

from ict import factor_geometry_trained as fgt
from ict.bench_factorise import (
    ConditionalBench,
    ConditionalStateBench,
    FactoredBench,
    Mess3Canonical,
    NoisedChannel,
    RRXOR,
    conditional_child_floor,
)

__all__ = [
    "position_contre_bande",
    "sweep_channel_noise",
    "conditional_campaign",
    "conditional_necessity",
    "conditional_state_campaign",
    "main",
]


def _jsonable(obj):
    """NaN/inf -> None : le JSON strict refuse NaN, l'artefact doit rester portable."""
    if isinstance(obj, dict):
        return {k: _jsonable(v) for k, v in obj.items()}
    if isinstance(obj, (list, tuple)):
        return [_jsonable(v) for v in obj]
    if isinstance(obj, bool):
        return obj
    if isinstance(obj, (np.bool_,)):
        return bool(obj)
    if isinstance(obj, (np.integer, int)):
        return int(obj)
    if isinstance(obj, (np.floating, float)):
        v = float(obj)
        return v if math.isfinite(v) else None
    return obj


def format_ou_na(valeur: object, fmt: str = "{:.3f}") -> str:
    """Formate une valeur d'artefact, ou ``n/a`` si elle n'est pas definie.

    Une metrique non definie d'un artefact JSON vaut ``None`` (``null``) :
    elle se **rapporte**, elle ne s'affiche pas comme un nombre. Les
    lecteurs de carnet (ICT-36) utilisent cette fonction pour qu'un niveau
    degenere s'affiche ``n/a`` au lieu de faire echouer la cellule de
    lecture -- et sans dependre d'un helper defini dans une autre cellule.
    """
    v = _nombre_fini(valeur)
    if not np.isfinite(v):
        return "n/a"
    return fmt.format(v)


def _nombre_fini(valeur: object) -> float:
    """Nombre flottant, ou ``nan`` si la valeur est absente ou non finie.

    Un artefact JSON ne peut pas porter ``NaN`` : il le remplace par
    ``null``. Un lecteur qui relit l'artefact (le carnet ICT-36 lit les
    quatre artefacts) doit donc traiter ``None`` comme une valeur **non
    definie**, pas comme une erreur : ``float(None)`` leve ``TypeError`` et
    ferait tomber la cellule de lecture sur le seul niveau degenere
    (``gamma = 1``, cible constante au bit pres).
    """
    if valeur is None:
        return float("nan")
    try:
        v = float(valeur)
    except (TypeError, ValueError):
        return float("nan")
    return v if np.isfinite(v) else float("nan")


def _bornes_finies(bande: Dict[str, object]) -> tuple:
    """Bornes p05 / p95 d'une bande, rendues finies ou ``nan``."""
    return (_nombre_fini(bande.get("p05")), _nombre_fini(bande.get("p95")))


def bande_degeneree(bande: Dict[str, float]) -> bool:
    """La bande p05-p95 du temoin peut-elle discriminer une position ?

    Une bande de largeur NULLE ne discrimine rien : toute valeur qui n'est
    pas exactement egale a p05 = p95 sort de la bande, et toute valeur egale
    y entre -- la position devient un artefact de l'egalite et non une
    mesure. C'est le cas mesure du 2026-10-26 pour l'``additivity_gap``
    (entier au rang pres) : les six initialisations non entrainées rendent
    toutes 0, donc la bande est [0 ; 0] et le critere 2 de #20071
    (``additivity_gap < 0`` hors bande) ne peut etre tranche QUE par le
    signe, jamais par la comparaison a une bande large.
    """
    p05, p95 = _bornes_finies(bande)
    if not (np.isfinite(p05) and np.isfinite(p95)):
        return True
    return (p95 - p05) <= 1e-12


def position_contre_bande(
    valeur: float, bande: Dict[str, float], *, comparer_bande_degeneree: bool = False
) -> str:
    """Position d'une metrique contre la bande p05-p95 de son temoin du MEME niveau.

    ``n/a`` si la metrique ou la bande est degenerree (cible constante ->
    sonde de rang nul a gamma = 1, bande sans valeur finie, bande de largeur
    NULLE qui ne discrimine rien) : un niveau degenerere se RAPPORTE, il ne
    se supprime pas.

    Le vocabulaire est volontairement inchange (``dans_bande``,
    ``sous_bande``, ``dessus_bande``, ``n/a``) : une bande de largeur nulle
    rend la position **indecidable**, pas « dans la bande » -- dire
    « dans_bande » d'une bande qui ne peut rien dire, c'est exactement le
    piege que le suivi du 15/09 denonce (une mesure dans la bande est
    muette). :func:`bande_degeneree` distingue explicitement le cas quand
    un rapport doit en rendre compte.

    ``comparer_bande_degeneree=True`` compare malgre la bande de largeur
    nulle : c'est le mode du **critere 2**, ou la question posee est le
    SIGNE du gap (« ``additivity_gap < 0`` hors de la bande ») et non sa
    position dans une bande -- une bande [0 ; 0] ne peut etre franchie que
    par le signe, et c'est exactement ce que le critere demande.
    """
    v = _nombre_fini(valeur)
    p05, p95 = _bornes_finies(bande)
    if not (np.isfinite(v) and np.isfinite(p05) and np.isfinite(p95)):
        return "n/a"
    if bande_degeneree(bande) and not comparer_bande_degeneree:
        return "n/a"
    if v < p05:
        return "sous_bande"
    if v > p95:
        return "dessus_bande"
    return "dans_bande"


def verdict_sweep_bande(
    lignes: Sequence[Dict[str, object]], metrique: str
) -> Dict[str, object]:
    """Verdict du CRITERE 1 : la courbe retombe-t-elle dans la bande du temoin ?

    Le falsifiable de #20071 : « une courbe ``overlap_coef_max(niveau)`` qui
    **retombe dans la bande du temoin au-dela d'un seuil**, ou qui **n'en
    sort jamais** ». Le verdict est donc l'un des trois :

    - ``retour_durable`` : il existe un seuil ``gamma*`` tel qu'aucun niveau
      au-dela de ``gamma*`` ne sort PLUS de la bande du temoin -- la structure
      lisible est perdue au-dela du seuil, et le seuil est nomme ;
    - ``jamais_sorti`` : aucun niveau ne sort de la bande (la courbe y reste
      du debut a la fin) ;
    - ``indecidable`` : la courbe sort de la bande par endroits sans jamais
      y revenir durablement -- aucun des deux bouts du falsifiable n'est
      atteint, et le critere reste ouvert.

    Un niveau dont la bande est **degeneree** (largeur nulle) ne compte ni
    comme sortie ni comme retour : il est rendu ``n/a`` par
    :func:`position_contre_bande` et le verdict le dit.
    """
    positions = []
    for l in lignes:
        pos = position_contre_bande(l["rapport"][metrique], l["temoin"][metrique])
        positions.append({"gamma": float(l["gamma"]), "valeur": float(l["rapport"][metrique]),
                          "position": pos})
    dessus = [p for p in positions if p["position"] == "dessus_bande"]
    if not dessus:
        return {"metrique": metrique, "issue": "jamais_sorti", "seuil": None,
                "positions": positions}
    gammas = sorted({p["gamma"] for p in positions})
    for seuil in gammas:
        suite = [p for p in positions if p["gamma"] >= seuil]
        if all(p["position"] in ("dans_bande", "sous_bande") for p in suite):
            return {"metrique": metrique, "issue": "retour_durable", "seuil": float(seuil),
                    "positions": positions}
    return {"metrique": metrique, "issue": "indecidable", "seuil": None, "positions": positions}


def verdicts_critere_1(lignes: Sequence[Dict[str, object]]) -> Dict[str, object]:
    """Verdict du critere 1 sur la metrique NOMMEE par l'issue et sur sa version invariante.

    L'issue nomme ``overlap_coef_max`` ; cette metrique n'est **pas invariante**
    par rotation des bases (cf :func:`ict.factor_geometry_trained.overlap_principal_max`),
    et une courbe qui bouge sous l'effet d'un choix de base ne peut pas
    trancher un critere. Les deux verdicts sont donc rendus, et leur
    eventuel desaccord est visible au lieu d'etre masque par un choix
    silencieux.
    """
    return {
        "overlap_coef_max": verdict_sweep_bande(lignes, "overlap_coef_max"),
        "overlap_principal_max": verdict_sweep_bande(lignes, "overlap_principal_max"),
        "overlap_energy": verdict_sweep_bande(lignes, "overlap_energy"),
    }


def verdict_critere_2(
    resultats: Dict[str, object], appariement: Dict[str, object]
) -> Dict[str, object]:
    """Verdict du CRITERE 2 : ``additivity_gap < 0`` hors de la bande du temoin.

    Le falsifiable de #20071 : « ``additivity_gap < 0`` sur le modele
    entraine **hors** de la bande du temoin, avec les marginales de chaque
    facteur verifiees identiques entre les variantes ».

    Le verdict est donc, par bras :

    - ``satisfait`` : au moins une graine entrainee donne un gap strictement
      negatif ET ce gap sort de la bande du temoin ;
    - ``non_satisfait`` : le gap reste nul (ou positif) : le modele n'encode
      pas la dependance -- soit la dependance n'est pas necessaire (banc a
      variante d'emission), soit le modele l'ignore.

    Les marginales appariees sont une **condition** du critere : si elles ne
    sont pas verifiees, le critere est rendu ``marginales_non_appariees``
    et ne peut etre Satisfait, quelle que soit la geometrie.
    """
    apparie = bool(appariement.get("marginales_exactes", appariement.get("matrices_exact", False)))
    out: Dict[str, object] = {"marginales_appariees": apparie, "bras": {}}
    for nom, ent in resultats.items():
        par_seed = ent["par_seed"] if isinstance(ent, dict) and "par_seed" in ent else {}
        temoin = ent["temoin"] if isinstance(ent, dict) else {}
        gaps = []
        for sd, e in par_seed.items():
            gap = float(e["rapport"]["additivity_gap"])
            pos = (
                position_contre_bande(
                    gap, temoin["additivity_gap"], comparer_bande_degeneree=True
                )
                if "additivity_gap" in temoin
                else "n/a"
            )
            gaps.append({"graine": int(sd), "additivity_gap": gap, "position": pos})
        negatifs = [g for g in gaps if np.isfinite(g["additivity_gap"]) and g["additivity_gap"] < 0]
        hors_bande = [g for g in negatifs if g["position"] in ("sous_bande", "dessus_bande")]
        out["bras"][nom] = {
            "gaps": gaps,
            "gap_negatif": bool(negatifs),
            "hors_bande": bool(hors_bande),
            "satisfait": bool(hors_bande) and apparie,
            "temoin_additivity_gap": temoin.get("additivity_gap"),
        }
    return out


def sweep_channel_noise(
    gammas: Sequence[float] = (0.0, 0.25, 0.5, 0.65, 0.75, 0.9, 1.0),
    *,
    length: int = 100,
    n_train: int = 300,
    n_val: int = 40,
    steps: int = 1200,
    eval_every: int = 100,
    data_seed: int = 1,
    model_seed: int = 0,
    n_init: int = 6,
    device: str | None = None,
) -> List[Dict[str, object]]:
    """Critere 1 : entrainement complet PAR niveau de bruit du canal, temoin rejoue
    a CHAQUE niveau, lecture rendue a TOUS les niveaux (gate reussi OU echoue).

    Le bruit porte sur les emissions des DEUX facteurs (matrice ``E`` du
    Mess3, tenseur d'aretes ``W`` du RRXOR), transitions intactes. La
    lecture rendue au niveau a gate echoue est taggee : la falsifiable du
    critere -- la courbe overlap(gamma) retombe-t-elle dans la bande ? --
    se joue exactement la, ou un modele qui n'a rien appris doit se confondre
    avec le temoin de SON niveau.
    """
    if not fgt.HAS_TORCH:
        raise RuntimeError("sweep_channel_noise exige torch (pip install torch)")
    import torch

    uniforme_joint = float(np.log(3.0) + np.log(2.0))
    n_total = length * (n_train + n_val) + length
    n_tranche = n_train * length
    lignes: List[Dict[str, object]] = []
    for g in gammas:
        bench_g = FactoredBench(NoisedChannel(Mess3Canonical(), g), NoisedChannel(RRXOR(), g))
        ech_g = bench_g.sample(n_total, seed_a=data_seed, seed_b=data_seed)
        xj = np.stack([ech_g["obs_a"], ech_g["obs_b"]], axis=1).astype(np.int64)
        pl_a = fgt.bayes_floor(bench_g.factor_a, ech_g["obs_a"][:n_tranche])
        pl_b = fgt.bayes_floor(bench_g.factor_b, ech_g["obs_b"][:n_tranche])
        xtr = torch.from_numpy(xj[:n_tranche].reshape(n_train, length, 2))
        xva = torch.from_numpy(
            xj[n_tranche : n_tranche + n_val * length].reshape(n_val, length, 2)
        )
        modele_g = fgt.FactoredRNN(seed=model_seed)
        res_g = fgt.train_model(modele_g, xtr, xva, steps=steps, eval_every=eval_every, seed=model_seed, device=device)
        bel_a = bench_g.factor_a.beliefs(ech_g["obs_a"][:n_tranche])
        bel_b = bench_g.factor_b.beliefs(ech_g["obs_b"][:n_tranche])
        rapport = fgt.factor_geometry_report(
            fgt.collect_activations(modele_g, xtr, device=device), bel_a, bel_b
        )
        temoin = fgt.untrained_null(
            lambda sd: fgt.FactoredRNN(seed=sd), xtr, bel_a, bel_b, n_init=n_init,
            device=device,
        )
        lignes.append(
            {
                "gamma": float(g),
                "plancher_a": pl_a,
                "plancher_b": pl_b,
                "plancher_joint": pl_a + pl_b,
                "best_val_nll": float(res_g["best_val_nll"]),
                "best_step": int(res_g["best_step"]),
                "gate": bool(res_g["best_val_nll"] < uniforme_joint),
                "rapport": rapport,
                "temoin": temoin,
            }
        )
    return lignes


def conditional_campaign(
    kappa: float = 0.28,
    child_emission_diag: float = 0.4,
    *,
    length: int = 100,
    n_train: int = 300,
    n_val: int = 40,
    steps: int = 1200,
    eval_every: int = 100,
    data_seed: int = 1,
    model_seeds: Sequence[int] = (0, 1, 7),
    n_init: int = 6,
    device: str | None = None,
) -> Dict[str, object]:
    """Critere 2 : banc conditionnel contre controle independant, memes marginales.

    Corrections de protocole par rapport a la premiere passe (#20091, 400
    pas, kappa = 0.2, une graine) :

    - ``kappa`` pousse vers la borne de stochasticite de l'enfant (enfant a
      emission plus plate : ``emission_diag = 0.4`` -> hors-diagonale 0.30,
      kappa <= 0.30) : la dependance posee par les donnees est plus forte,
      l'appariement des marginales reste EXACT (les rotations s'annulent) ;
    - trois graines modele (le verdict n'est plus celui d'une seule graine) ;
    - le discriminant rendu est ``overlap_energy`` (continu) A COTE du gap
      entier imprime -- c'est la de-saturation mesuree : les bandes du temoin
      en gap entier etaient de largeur nulle sur les deux bancs.

    Le controle independant utilise le MEME enfant (meme ``emission_diag``) :
    tout ecart entre les deux bancs ne peut venir que de la loi jointe.

    **Correction de la troisieme passe (2026-10-26) — les graines des deux
    facteurs sont desormais DISTINCTES.** Les deux passes precedentes
    (#20091, #21652) echantillonnaient les deux facteurs avec la meme graine
    : deux generateurs de meme classe consommant le flux d'uniformes de la
    meme face partagent alors leur trajectoire d'etats caches (mesure :
    etats caches IDENTIQUES et ``I(obs_a ; obs_b) = 0,677 nats`` sur
    ``Mess3 x Mess3``). Le « controle independant » etait donc le banc le
    plus ENTRELACE de la campagne -- son energie de recouvrement (0,348 a
    0,415) sortait meme du haut de sa bande de temoin [0,226 ; 0,409], la
    ou le banc conditionnel restait en dessous de la sienne
    [0,121 ; 0,275] : l'ecart observe etait l'inverse de ce qu'il devait
    etre. L'independance du controle est desormais **mesuree** et publiee
    dans l'artefact (``independance_facteurs``).
    """
    if not fgt.HAS_TORCH:
        raise RuntimeError("conditional_campaign exige torch (pip install torch)")
    import torch

    parent = Mess3Canonical()
    enfant = Mess3Canonical(emission_diag=child_emission_diag)
    bench_cond = ConditionalBench(parent, enfant, kappa=kappa)
    bench_ind = FactoredBench(parent, enfant)
    n_total = length * (n_train + n_val) + length
    n_tranche = n_train * length
    ech_c = bench_cond.sample(n_total, seed_parent=data_seed, seed_child=data_seed + 1)
    ech_i = bench_ind.sample(n_total, seed_a=data_seed, seed_b=data_seed + 1)
    bels_c = bench_cond.beliefs(ech_c["obs_a"], ech_c["obs_b"])
    bels_i = bench_ind.beliefs(ech_i["obs_a"], ech_i["obs_b"])

    # appariement des marginales, verifie sur les MATRICES puis sur l'echantillon
    e_marg = np.asarray(enfant.emission_matrix(), dtype=np.float64)
    apparie_mat = bool(np.allclose(bench_cond.marginal_child(), e_marg, atol=1e-12))
    emp_c = np.bincount(ech_c["obs_b"], minlength=e_marg.shape[1]) / len(ech_c["obs_b"])
    emp_i = np.bincount(ech_i["obs_b"], minlength=e_marg.shape[1]) / len(ech_i["obs_b"])
    apparie_emp = float(np.abs(emp_c - emp_i).max())

    t_e, pi_e = enfant.transition_matrix(), enfant.stationary()
    variants = bench_cond.emission_variants()
    pl_genie = conditional_child_floor(ech_c["obs_b"], ech_c["obs_a"], t_e, variants, pi_e, burn=32)
    pl_aveugle = conditional_child_floor(
        ech_c["obs_b"], ech_c["obs_a"], t_e, (e_marg,) * len(variants), pi_e, burn=32
    )
    pl_parent = fgt.bayes_floor(parent, ech_c["obs_a"][:n_tranche])
    uniforme = float(2.0 * np.log(3.0))

    resultats: Dict[str, object] = {}
    for nom, ech_x, bels in (
        ("conditionnel", ech_c, bels_c),
        ("independant", ech_i, bels_i),
    ):
        xj = np.stack([ech_x["obs_a"], ech_x["obs_b"]], axis=1).astype(np.int64)
        xtr = torch.from_numpy(xj[:n_tranche].reshape(n_train, length, 2))
        xva = torch.from_numpy(
            xj[n_tranche : n_tranche + n_val * length].reshape(n_val, length, 2)
        )
        bel_a = bels["belief_a"][:n_tranche]
        bel_b = bels["belief_b"][:n_tranche]
        par_seed: Dict[int, Dict[str, object]] = {}
        for sd in model_seeds:
            modele_x = fgt.FactoredRNN(n_a=3, n_b=3, seed=sd)
            res_x = fgt.train_model(
                modele_x, xtr, xva, steps=steps, eval_every=eval_every, seed=sd, device=device
            )
            rapport = fgt.factor_geometry_report(
                fgt.collect_activations(modele_x, xtr, device=device), bel_a, bel_b
            )
            par_seed[int(sd)] = {
                "best_val_nll": float(res_x["best_val_nll"]),
                "gate": bool(res_x["best_val_nll"] < uniforme),
                "rapport": rapport,
            }
        temoin = fgt.untrained_null(
            lambda s: fgt.FactoredRNN(n_a=3, n_b=3, seed=s), xtr, bel_a, bel_b,
            n_init=n_init, device=device,
        )
        resultats[nom] = {"par_seed": par_seed, "temoin": temoin}

    return {
        "kappa": float(kappa),
        "child_emission_diag": float(child_emission_diag),
        "steps": int(steps),
        "model_seeds": [int(s) for s in model_seeds],
        "n_init": int(n_init),
        "appariement": {
            "matrices_exact": apparie_mat,
            "ecart_empirique_max": apparie_emp,
        },
        "independance_facteurs": {
            "conditionnel": _information_mutuelle_discrete(
                ech_c["obs_a"], ech_c["obs_b"]
            ),
            "independant": _information_mutuelle_discrete(
                ech_i["obs_a"], ech_i["obs_b"]
            ),
        },
        "planchers": {
            "genie": pl_genie,
            "aveugle": pl_aveugle,
            "prime_conditionnelle": pl_aveugle - pl_genie,
            "parent": pl_parent,
            "uniforme_joint": uniforme,
        },
        "resultats": resultats,
    }


# --------------------------------------------------------------------------
# 3. Regime a etat couple : rendre la structure conditionnelle NECESSAIRE
# --------------------------------------------------------------------------


def _sonde_lineaire_r2(x: np.ndarray, y: np.ndarray, ridge: float = 1e-6) -> float:
    """R2 hors echantillon d'une sonde lineaire (one-hot -> cible), blocs contigus.

    Les blocs sont **contigus** et non aleatoires, comme dans
    :func:`ict.factor_geometry_trained.probe_holdout_r2` : les observations du
    banc sont temporellement correlees, un decoupage aleatoire laisserait
    fuir l'information d'un pas vers son voisin.
    """
    n = len(x)
    if n < 10:
        return float("nan")
    cut = int(0.8 * n)
    xt = np.hstack([x[:cut], np.ones((cut, 1))])
    xv = np.hstack([x[cut:], np.ones((n - cut, 1))])
    a = xt.T @ xt + ridge * np.eye(xt.shape[1])
    w = np.linalg.solve(a, xt.T @ y[:cut])
    p = xv @ w
    ss_res = float(((y[cut:] - p) ** 2).sum())
    ss_tot = float(((y[cut:] - y[cut:].mean(axis=0, keepdims=True)) ** 2).sum())
    return 1.0 - ss_res / ss_tot if ss_tot > 0.0 else float("nan")


def _information_mutuelle_discrete(x: np.ndarray, y: np.ndarray) -> float:
    """I(X ; Y) en nats, estimee par les frequences empiriques (X et Y discrets)."""
    x = np.asarray(x, dtype=np.int64)
    y = np.asarray(y, dtype=np.int64)
    joint = np.zeros((int(x.max()) + 1, int(y.max()) + 1))
    np.add.at(joint, (x, y), 1.0)
    total = joint.sum()
    if total <= 0:
        return float("nan")
    joint /= total
    px = joint.sum(axis=1, keepdims=True)
    py = joint.sum(axis=0, keepdims=True)
    nz = joint > 0
    return float((joint[nz] * np.log(joint[nz] / (px @ py)[nz])).sum())


def _mesures_necessite(
    token: np.ndarray, belief_b: np.ndarray, obs_b: np.ndarray
) -> Dict[str, object]:
    """Mesures de NECESSARITE de la structure conditionnelle pour la cible.

    - ``r2_token_belief_b`` : part de la variance de la **cible** ``belief_b``
      qu'explique le token du parent (sonde lineaire, blocs contigus). C'est
      la mesure de necessite : proche de 0, un modele peut ignorer la
      dependance sans perdre en exactitude sur la cible, et l'entremelement
      n'a aucune raison d'apparaitre ;
    - ``prime_belief`` : I(token ; argmax(belief_b)) en nats, prime
      conditionnelle de la cible elle-meme ;
    - ``prime_observation`` : I(token ; observation de l'enfant) en nats.
    """
    token = np.asarray(token, dtype=np.int64)
    belief_b = np.asarray(belief_b, dtype=np.float64)
    onehot = np.eye(int(token.max()) + 1)[token]
    return {
        "r2_token_belief_b": _sonde_lineaire_r2(onehot, belief_b),
        "variance_belief_b": float(belief_b.var(axis=0).sum()),
        "prime_belief": _information_mutuelle_discrete(
            token, belief_b.argmax(axis=1)
        ),
        "prime_observation": _information_mutuelle_discrete(
            token, np.asarray(obs_b, dtype=np.int64)
        ),
    }


def conditional_necessity(
    *,
    n: int = 20_000,
    data_seed: int = 1,
    shift: int = 1,
    child_emission_diag: float = 0.4,
) -> Dict[str, object]:
    """MESURE CPU : la structure conditionnelle est-elle NECESSAIRE ?

    Compare trois regimes sur les **CIBLES** (aucun apprentissage, donc
    aucun GPU, aucune cle, aucun artefact de campagne) :

    - ``etat_couple`` : l'etat cache de l'enfant est une rotation du token
      (:class:`ict.bench_factorise.ConditionalStateBench`) ;
    - ``emission_variante`` : le banc actuel (:class:`ConditionalBench`,
      ``kappa = 0.28``) ;
    - ``independant`` : le controle, l'enfant suivant sa propre chaine.

    Ce que la mesure tranche : dans le banc a variante d'emission, la
    structure conditionnelle n'est **pas necessaire** (le token n'explique
    qu'une petite part de la variance de la cible) -- donc un ``additivity_gap``
    nul y est la bonne reponse, et aucun budget d'entrainement ne le
    changera. Dans le regime a etat couple, la dependance est **necessaire**
    (le token determine la cible) tout en gardant les marginales appariees.

    L'appariement des marginales est verifie dans les deux sens : en theorie
    (matrices) et sur l'echantillon (frequences).

    **Graine distincte pour les deux facteurs.** Les deux passes precedentes
    (#20091, #21652) échantillonnaient les deux facteurs avec la MEME graine
    (``seed_a = seed_b = data_seed``) : deux generateurs de meme classe
    consommant le flux d'uniformes de la meme face partagent alors leur
    trajectoire d'etats caches -- mesure du 2026-10-26 : etats caches
    IDENTIQUES et ``I(obs_a ; obs_b) = 0,677 nats`` sur ``Mess3 x Mess3``, la
    ou le controle « independant » de la campagne se retrouvait etre le banc
    le plus ENTRELACE de celle-ci (energie de recouvrement 0,348 a 0,415,
    bande de temoin [0,226 ; 0,409]). Les graines sont donc distinctes
    desormais ; l'independance du controle n'est plus supposee, elle est
    **mesuree** ici : ``prime_observation`` du regime ``independant`` vaut
    ``~0`` nats.
    """
    parent = Mess3Canonical()
    enfant = Mess3Canonical(emission_diag=child_emission_diag)
    e = np.asarray(enfant.emission_matrix(), dtype=np.float64)

    bench_etat = ConditionalStateBench(parent, enfant, shift=shift)
    bench_var = ConditionalBench(parent, enfant, kappa=0.28)
    bench_ind = FactoredBench(parent, enfant)

    ech_etat = bench_etat.sample(n, seed_parent=data_seed, seed_child=data_seed + 1)
    ech_var = bench_var.sample(n, seed_parent=data_seed, seed_child=data_seed + 1)
    ech_ind = bench_ind.sample(n, seed_a=data_seed, seed_b=data_seed + 1)
    bel_etat = bench_etat.beliefs(ech_etat["obs_a"], ech_etat["obs_b"])
    bel_var = bench_var.beliefs(ech_var["obs_a"], ech_var["obs_b"])
    bel_ind = bench_ind.beliefs(ech_ind["obs_a"], ech_ind["obs_b"])

    mesures = {
        "etat_couple": _mesures_necessite(
            ech_etat["obs_a"], bel_etat["belief_b"], ech_etat["obs_b"]
        ),
        "emission_variante": _mesures_necessite(
            ech_var["obs_a"], bel_var["belief_b"], ech_var["obs_b"]
        ),
        "independant": _mesures_necessite(
            ech_ind["obs_a"], bel_ind["belief_b"], ech_ind["obs_b"]
        ),
    }

    marg_theo_couple = bench_etat.marginal_child_observations()
    marg_theo_ind = e @ np.asarray(enfant.stationary(), dtype=np.float64)
    emp_couple = np.bincount(ech_etat["obs_b"], minlength=marg_theo_couple.size) / n
    emp_ind = np.bincount(ech_ind["obs_b"], minlength=marg_theo_ind.size) / n
    appariement = {
        "marginales_exactes": bool(
            np.allclose(marg_theo_couple, marg_theo_ind, atol=1e-12)
        ),
        "ecart_theorique_max": float(np.abs(marg_theo_couple - marg_theo_ind).max()),
        "ecart_empirique_max": float(np.abs(emp_couple - emp_ind).max()),
        "marginale_couple": marg_theo_couple.tolist(),
        "marginale_independant": marg_theo_ind.tolist(),
    }
    return {"n": int(n), "data_seed": int(data_seed), "shift": int(shift),
            "mesures": mesures, "appariement": appariement}


def conditional_state_campaign(
    *,
    length: int = 100,
    n_train: int = 300,
    n_val: int = 40,
    steps: int = 1200,
    eval_every: int = 100,
    data_seed: int = 1,
    model_seeds: Sequence[int] = (0, 1, 7),
    n_init: int = 6,
    shift: int = 1,
    child_emission_diag: float = 0.4,
    device: str | None = None,
) -> Dict[str, object]:
    """Critere 2, troisieme passe : regime a etat couple contre le controle
    independant aux MEMES marginales, temoin rejoue a CHAQUE regime.

    Ce que la campagne ajoute aux deux passes precedentes (#20091, #21652) :
    le regime dans lequel la dependance est **necessaire** (voir
    :func:`conditional_necessity`). Sur le banc a variante d'emission, un
    modele qui ignore la dependance est aussi bon -- le ``additivity_gap``
    nul y mesure n'apprend rien sur la representation. Ici, la lecture de
    l'enfant n'a pas d'autre route que la direction du parent, donc un
    modele qui encode la dependance **doit** recouvrir les deux
    sous-espaces : le gap sort de la bande du temoin, et le temoin (non
    entrainne, rejoue a chaque regime) borne la comparaison.

    Le controle independant rejoue le meme protocole sur le banc ou l'enfant
    suit sa propre chaine : memes marginales, meme matrice d'emission, et
    **graines distinctes pour les deux facteurs** (voir la correction de la
    troisieme passe dans :func:`conditional_campaign`) -- tout ecart vient de
    la loi jointe, et l'independance du controle est mesuree puis publiee.
    """
    if not fgt.HAS_TORCH:
        raise RuntimeError("conditional_state_campaign exige torch (pip install torch)")
    import torch

    parent = Mess3Canonical()
    enfant = Mess3Canonical(emission_diag=child_emission_diag)
    e = np.asarray(enfant.emission_matrix(), dtype=np.float64)
    bench_cond = ConditionalStateBench(parent, enfant, shift=shift)
    bench_ind = FactoredBench(parent, enfant)

    n_total = length * (n_train + n_val) + length
    n_tranche = n_train * length
    ech_c = bench_cond.sample(n_total, seed_parent=data_seed, seed_child=data_seed + 1)
    ech_i = bench_ind.sample(n_total, seed_a=data_seed, seed_b=data_seed + 1)
    bels_c = bench_cond.beliefs(ech_c["obs_a"], ech_c["obs_b"])
    bels_i = bench_ind.beliefs(ech_i["obs_a"], ech_i["obs_b"])

    # appariement : marginale d'OBSERVATION de l'enfant, theorique puis empirique
    marg_theo_c = bench_cond.marginal_child_observations()
    marg_theo_i = e @ np.asarray(enfant.stationary(), dtype=np.float64)
    emp_c = np.bincount(ech_c["obs_b"], minlength=marg_theo_c.size) / len(ech_c["obs_b"])
    emp_i = np.bincount(ech_i["obs_b"], minlength=marg_theo_i.size) / len(ech_i["obs_b"])
    appariement = {
        "marginales_exactes": bool(np.allclose(marg_theo_c, marg_theo_i, atol=1e-12)),
        "ecart_theorique_max": float(np.abs(marg_theo_c - marg_theo_i).max()),
        "ecart_empirique_max": float(np.abs(emp_c - emp_i).max()),
    }

    # planchers de l'observation de l'enfant : le genie connait le token (donc
    # l'etat de l'enfant, dont il tire sa loi d'emission), l'aveugle non.
    marg_aveugle = marg_theo_c
    pl_aveugle = float(-np.log(marg_aveugle[ech_c["obs_b"]]).mean())
    etats_c = ech_c["states_b"]
    pl_genie = float(-np.log(e[etats_c, ech_c["obs_b"]]).mean())
    uniforme = float(2.0 * np.log(3.0))

    resultats: Dict[str, object] = {}
    for nom, ech_x, bels in (
        ("conditionnel_etat", ech_c, bels_c),
        ("independant", ech_i, bels_i),
    ):
        xj = np.stack([ech_x["obs_a"], ech_x["obs_b"]], axis=1).astype(np.int64)
        xtr = torch.from_numpy(xj[:n_tranche].reshape(n_train, length, 2))
        xva = torch.from_numpy(
            xj[n_tranche : n_tranche + n_val * length].reshape(n_val, length, 2)
        )
        bel_a = bels["belief_a"][:n_tranche]
        bel_b = bels["belief_b"][:n_tranche]
        par_seed: Dict[int, Dict[str, object]] = {}
        for sd in model_seeds:
            modele_x = fgt.FactoredRNN(n_a=3, n_b=3, seed=sd)
            res_x = fgt.train_model(
                modele_x, xtr, xva, steps=steps, eval_every=eval_every, seed=sd,
                device=device,
            )
            rapport = fgt.factor_geometry_report(
                fgt.collect_activations(modele_x, xtr, device=device), bel_a, bel_b
            )
            par_seed[int(sd)] = {
                "best_val_nll": float(res_x["best_val_nll"]),
                "gate": bool(res_x["best_val_nll"] < uniforme),
                "rapport": rapport,
            }
        temoin = fgt.untrained_null(
            lambda s: fgt.FactoredRNN(n_a=3, n_b=3, seed=s), xtr, bel_a, bel_b,
            n_init=n_init, device=device,
        )
        resultats[nom] = {
            "par_seed": par_seed,
            "temoin": temoin,
            "necessite": _mesures_necessite(
                ech_x["obs_a"][:n_tranche], bel_b, ech_x["obs_b"][:n_tranche]
            ),
        }

    return {
        "shift": int(shift),
        "child_emission_diag": float(child_emission_diag),
        "steps": int(steps),
        "model_seeds": [int(s) for s in model_seeds],
        "n_init": int(n_init),
        "appariement": appariement,
        "independance_facteurs": {
            "conditionnel_etat": _information_mutuelle_discrete(
                ech_c["obs_a"], ech_c["obs_b"]
            ),
            "independant": _information_mutuelle_discrete(
                ech_i["obs_a"], ech_i["obs_b"]
            ),
        },
        "planchers": {
            "genie": pl_genie,
            "aveugle": pl_aveugle,
            "prime_conditionnelle_observation": pl_aveugle - pl_genie,
            "uniforme_joint": uniforme,
        },
        "resultats": resultats,
    }


def _print_sweep(lignes: List[Dict[str, object]]) -> None:
    print("gamma  plancher   val     gate    r2a (bande)          r2b (bande)          ovl (bande)          energie (bande)")
    for l in lignes:
        r, t = l["rapport"], l["temoin"]
        def _b(m):  # bande p05-p95 d'une metrique du temoin
            b = t[m]
            return f"{b['p05']:.3f}-{b['p95']:.3f}" if b.get("n") else "degeneree"
        gate = "PASS  " if l["gate"] else "ECHEC "
        def _v(m):
            v = r[m]
            return f"{v:.3f}" if np.isfinite(v) else "nan"
        print(f"{l['gamma']:.2f}  {l['plancher_joint']:.5f}  {l['best_val_nll']:.4f}  {gate}  "
              f"{_v('probe_r2_a')} [{_b('probe_r2_a')}]  {_v('probe_r2_b')} [{_b('probe_r2_b')}]  "
              f"{_v('overlap_coef_max')} [{_b('overlap_coef_max')}]  {_v('overlap_energy')} [{_b('overlap_energy')}]")
        for m in ("probe_r2_a", "probe_r2_b", "overlap_coef_max", "overlap_energy"):
            pos = position_contre_bande(r[m], t[m])
            if pos != "n/a":
                print(f"       {m}: {pos}")


def main(argv: Sequence[str] | None = None) -> int:
    p = argparse.ArgumentParser(
        description="Campagnes des regimes generatifs #20071 (critere 1 : bruit du canal ; critere 2 : conditionnel)."
    )
    p.add_argument("--out-dir", default=None, help="dossier des artefacts (defaut : ict/results/)")
    p.add_argument("--steps", type=int, default=1200)
    p.add_argument("--quick", action="store_true", help="passe fumee mini (tests CI)")
    p.add_argument(
        "--device",
        default=None,
        help="device torch des entraînements (ex. cuda). Sans option : CPU.",
    )
    p.add_argument(
        "--regimes",
        nargs="+",
        default=["1", "2", "2b"],
        choices=["1", "2", "2b"],
        help="regimes a executer (1 : bruit du canal ; 2 : conditionnel emission ; 2b : conditionnel etat couple)",
    )
    args = p.parse_args(argv)

    out = Path(args.out_dir) if args.out_dir else Path(__file__).resolve().parent / "results"
    out.mkdir(parents=True, exist_ok=True)
    commun = {"steps": args.steps, "length": 100, "n_train": 300, "n_val": 40, "n_init": 6}
    gammas: Sequence[float] = (0.0, 0.25, 0.5, 0.65, 0.75, 0.9, 1.0)
    if args.quick:
        commun.update({"steps": 20, "length": 20, "n_train": 8, "n_val": 4, "n_init": 5})
        gammas = (0.0, 1.0)

    if "1" in args.regimes:
        print("[regime 1] sweep bruit du canal -- entraînement PAR niveau, temoin PAR niveau")
        lignes = sweep_channel_noise(gammas=gammas, steps=commun["steps"], length=commun["length"],
                                     n_train=commun["n_train"], n_val=commun["n_val"],
                                     n_init=commun["n_init"], device=args.device)
        _print_sweep(lignes)
        verdicts = verdicts_critere_1(lignes)
        for nom, v in verdicts.items():
            print(f"[regime 1] verdict sur {nom} : {v['issue']}"
                  + (f" (seuil gamma = {v['seuil']})" if v["seuil"] is not None else ""))
        art1 = out / "ict36_regime1_sweep_bruit_canal.json"
        art1.write_text(
            json.dumps(_jsonable({"protocole": commun, "niveaux": lignes,
                                  "verdicts": verdicts}), indent=1, ensure_ascii=False),
            encoding="utf-8",
        )
        print(f"[regime 1] artefact -> {art1}")

    if "2" in args.regimes:
        print("[regime 2] conditionnel vs independant -- memes marginales, kappa fort, 3 graines")
        camp = conditional_campaign(steps=commun["steps"], length=commun["length"],
                                    n_train=commun["n_train"], n_val=commun["n_val"],
                                    n_init=commun["n_init"], device=args.device)
        pl = camp["planchers"]
        print(f"appariement matrices exact : {camp['appariement']['matrices_exact']}  "
              f"ecart empirique max : {camp['appariement']['ecart_empirique_max']:.4f}")
        print(f"planchers enfant : genie {pl['genie']:.4f} / aveugle {pl['aveugle']:.4f}  "
              f"prime {pl['prime_conditionnelle']:+.4f} nats")
        for nom, ent in camp["resultats"].items():
            t_gap, t_enr = ent["temoin"]["additivity_gap"], ent["temoin"]["overlap_energy"]
            print(f"{nom:12s} temoin gap [{t_gap['p05']:+.3f},{t_gap['p95']:+.3f}]  "
                  f"energie [{t_enr['p05']:.3f},{t_enr['p95']:.3f}]")
            for sd, e in ent["par_seed"].items():
                r = e["rapport"]
                print(f"  seed {sd}: val={e['best_val_nll']:.4f} gate={'PASS' if e['gate'] else 'ECHEC'}  "
                      f"gap={r['additivity_gap']:+.3f} [{position_contre_bande(r['additivity_gap'], t_gap)}]  "
                      f"energie={r['overlap_energy']:.3f} [{position_contre_bande(r['overlap_energy'], t_enr)}]  "
                      f"ovl={r['overlap_coef_max']:.3f}  r2=({r['probe_r2_a']:.3f},{r['probe_r2_b']:.3f})")
        art2 = out / "ict36_regime2_conditionnel.json"
        camp["verdict_critere_2"] = verdict_critere_2(camp["resultats"], camp["appariement"])
        for nom, v in camp["verdict_critere_2"]["bras"].items():
            print(f"[regime 2] critere 2 sur {nom} : "
                  f"{'SATISFAIT' if v['satisfait'] else 'non satisfait'}  "
                  f"(gap negatif : {v['gap_negatif']}, hors bande : {v['hors_bande']})")
        art2.write_text(json.dumps(_jsonable(camp), indent=1, ensure_ascii=False), encoding="utf-8")
        print(f"[regime 2] artefact -> {art2}")

    if "2b" in args.regimes:
        print("[regime 2b] NECESSITE (CPU) : la dependance est-elle requise par la cible ?")
        nec = conditional_necessity(n=2000 if args.quick else 20000)
        for nom, m in nec["mesures"].items():
            print(f"  {nom:18s} R2(token -> belief_b) = {m['r2_token_belief_b']:+.4f}  "
                  f"prime cible = {m['prime_belief']:+.4f} nats  "
                  f"prime observation = {m['prime_observation']:+.4f} nats")
        print(f"  appariement marginales : exact = {nec['appariement']['marginales_exactes']}  "
              f"ecart empirique max = {nec['appariement']['ecart_empirique_max']:.4f}")
        art_nec = out / "ict36_regime2b_necessite.json"
        art_nec.write_text(
            json.dumps(_jsonable(nec), indent=1, ensure_ascii=False), encoding="utf-8"
        )
        print(f"[regime 2b] mesure CPU -> {art_nec}")

        print("[regime 2b] conditionnel a etat couple vs independant -- entrainement")
        camp_b = conditional_state_campaign(steps=commun["steps"], length=commun["length"],
                                            n_train=commun["n_train"], n_val=commun["n_val"],
                                            n_init=commun["n_init"], device=args.device)
        pl_b = camp_b["planchers"]
        print(f"appariement marginales exact : {camp_b['appariement']['marginales_exactes']}  "
              f"ecart empirique max : {camp_b['appariement']['ecart_empirique_max']:.4f}")
        print(f"planchers observation : genie {pl_b['genie']:.4f} / aveugle {pl_b['aveugle']:.4f}  "
              f"prime {pl_b['prime_conditionnelle_observation']:+.4f} nats")
        for nom, ent in camp_b["resultats"].items():
            t_gap, t_enr = ent["temoin"]["additivity_gap"], ent["temoin"]["overlap_energy"]
            print(f"{nom:18s} temoin gap [{t_gap['p05']:+.3f},{t_gap['p95']:+.3f}]  "
                  f"energie [{t_enr['p05']:.3f},{t_enr['p95']:.3f}]  "
                  f"R2(token->belief_b) = {ent['necessite']['r2_token_belief_b']:+.4f}")
            for sd, e in ent["par_seed"].items():
                r = e["rapport"]
                print(f"  seed {sd}: val={e['best_val_nll']:.4f} gate={'PASS' if e['gate'] else 'ECHEC'}  "
                      f"gap={r['additivity_gap']:+.3f} [{position_contre_bande(r['additivity_gap'], t_gap)}]  "
                      f"energie={r['overlap_energy']:.3f} [{position_contre_bande(r['overlap_energy'], t_enr)}]  "
                      f"ovl={r['overlap_coef_max']:.3f}  r2=({r['probe_r2_a']:.3f},{r['probe_r2_b']:.3f})")
        art2b = out / "ict36_regime2b_conditionnel_etat.json"
        camp_b["verdict_critere_2"] = verdict_critere_2(
            camp_b["resultats"], camp_b["appariement"]
        )
        for nom, v in camp_b["verdict_critere_2"]["bras"].items():
            print(f"[regime 2b] critere 2 sur {nom} : "
                  f"{'SATISFAIT' if v['satisfait'] else 'non satisfait'}  "
                  f"(gap negatif : {v['gap_negatif']}, hors bande : {v['hors_bande']})")
        art2b.write_text(json.dumps(_jsonable(camp_b), indent=1, ensure_ascii=False), encoding="utf-8")
        print(f"[regime 2b] artefact -> {art2b}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
