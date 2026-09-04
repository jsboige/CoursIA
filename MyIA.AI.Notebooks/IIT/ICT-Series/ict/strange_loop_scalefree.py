"""Case 8c (#8182, iceberg L4) : une metrique de re-adaptation SANS ECHELLE.

La case 8b (``strange_loop_irreducible``, PR #14180) a rendu
``INCONCLUSIF_INSTRUMENT``. Sa manipulation avait REUSSI -- le canal
*self* etait devenu irreductible (``residual_share`` median 0.35 contre
0.0000 sur la politique deterministe de la case 8) -- et c'est cette
reussite qui a casse la mesure : rendre le canal self irreductible fait
diverger les asymptotes pre-shift des bras d'un facteur 2.86, or le
seuil de rattrapage vaut ``1.2 x sa PROPRE asymptote``. Le bras le moins
precis recoit donc un seuil 2.86x plus lache et se pose au plancher de
l'echelle (5/5 graines) pendant que le self-modele n'y touche jamais
(0/5). ``rho_beta`` et ``kappa`` cessent alors de comparer des vitesses :
ils comparent des largeurs de seuil.

**Une seule chose change ici : la metrique.** Dynamique, politiques,
modeles, shift, graines et seuils de decision sont importes tels quels
des cases 8 et 8b -- litteralement ``from .strange_loop_selfmodel import
...`` et ``from .strange_loop_irreducible import ...``, jamais reecrits
"a l'identique".

La metrique de remplacement est le **temps de relaxation** : on soustrait
l'asymptote au lieu de la prendre pour seuil, et on rapporte la
decroissance a son propre pic de perturbation.

    s(t)      = moyenne glissante de l'erreur, fenetre ``win``
    excess(t) = s(t) - pre
    peak      = max excess sur la fenetre de perturbation, en t_peak
    T         = min { t >= t_peak : excess(t) < gamma . peak }
    relaxation = T - t_peak

Sous ``errs -> c . errs`` (c > 0) : ``pre -> c.pre``, donc
``excess -> c.excess``, donc ``peak -> c.peak``, donc la comparaison
``excess(t) < gamma . peak`` est inchangee TERME A TERME et l'``argmax``
ne bouge pas. ``t_peak``, ``T`` et ``relaxation`` sont donc *exactement*
invariants -- propriete demontrable, pas un reglage.

Pre-enregistrement scelle AVANT ce fichier :
``docs/ict/strange-loop-scalefree-pre-enregistrement.md`` (commit
``a0dc764023``, anterieur -- ordre git verifiable, comme ``55d4aad9ef``
precede le jouet de la case 8 et ``85dbca6364`` celui de la case 8b).

  P1 seconde  instrument  : T(c.errs) == T(errs) exactement, ET
                            l'ANCIENNE metrique change sur >= 1 bras
  P2 seconde  travail     : rho_beta_sf = T_surr / T_loop >= 3 (>= 4/5)
  P3 seconde  specificite : kappa_sf = T_noise / T_surr median [0.5, 2]
  Porte       non-degen.  : aucun bras au plancher ni au plafond sur une
                            majorite de graines, et peak > 0 partout

Grade C documentaire : on corrige un INSTRUMENT sur un substrat
scalaire. Une metrique sans echelle ne rend pas la mesure "vraie" --
elle retire une confusion identifiee, et rien de plus.

References
----------
Douglas Hofstadter, *Godel, Escher, Bach*, Basic Books 1979, ISBN
978-0465026562 ; *I Am a Strange Loop*, Basic Books 2007, ISBN
978-0465003010.
"""

from __future__ import annotations

import numpy as np

from .strange_loop_irreducible import AutonomousPolicy, NoiseChannelSurrogate
from .strange_loop_selfmodel import (
    CompositeSurrogate,
    LoopPolicy,
    LoopSystem,
    SelfLoopModel,
)

# --- Constantes scellees au pre-enregistrement -------------------------
GAMMA = 0.5          # demi-vie : choix canonique, aucune autre essayee
WIN = 50             # fenetre de lissage, celle de l'ancienne metrique
PEAK_WINDOW = 400    # fenetre ou le pic de perturbation est cherche
CATCHUP_FACTOR = 1.2  # ancienne metrique, reprise telle quelle
SCALES = (0.1, 10.0)  # facteurs du controle d'invariance P1 seconde


def collect_trace(model, pol, *, shift_kind: str = "beta",
                  n_steps: int = 4000, shift_step: int = 2000,
                  seed: int = 0) -> np.ndarray:
    """Boucle de simulation des cases 8 / 8b, rendant la trace BRUTE.

    C'est mot pour mot la boucle de ``adaptation_horizon`` (case 8) et
    ``adaptation_horizon_irr`` (case 8b) -- y compris le ``new_step()``
    notifie aux modeles portant un canal exogene, qui est un no-op pour
    tous les modeles de la case 8 (aucun ne definit ce hook). La seule
    difference est le RETOUR : la trace au lieu d'un verdict, pour que
    les deux metriques s'appliquent aux MEMES nombres.

    Cette fidelite n'est pas supposee : ``test_trace_fidele_a_la_case8``
    et son jumeau 8b verifient que l'ancienne metrique recalculee sur
    cette trace rend exactement l'horizon publie par les modules
    d'origine.
    """
    sys_ = LoopSystem(shift_step=shift_step, shift_kind=shift_kind, seed=seed)
    step_hook = getattr(model, "new_step", None)
    errs: list[float] = []
    x = sys_.x
    for _ in range(n_steps):
        if step_hook is not None:
            step_hook()
        a = pol.act(x)
        x_next = sys_.step(a)
        model.update(x, a, x_next)
        errs.append(abs(model.predict(x, a) - x_next))
        x = x_next
    return np.asarray(errs, dtype=float)


def horizon_from_errs(errs: np.ndarray, *, shift_step: int = 2000,
                      warmup: int = 1500,
                      catchup_factor: float = CATCHUP_FACTOR) -> int:
    """L'ANCIENNE metrique, recalculee sur une trace fournie.

    Reprise a l'identique de ``adaptation_horizon`` : elle n'est pas ici
    pour mesurer quoi que ce soit, mais pour servir de TEMOIN au
    controle d'invariance (P1 seconde). Sans elle, "la nouvelle metrique
    est invariante" serait indiscernable de "toute metrique l'est".
    """
    pre = float(np.median(errs[warmup:shift_step]))
    n_steps = len(errs)
    tail = n_steps - shift_step
    horizon = tail
    for t in range(shift_step + WIN, n_steps):
        if float(np.mean(errs[t - WIN:t])) < catchup_factor * pre:
            horizon = t - shift_step
            break
    return int(horizon)


def relaxation(errs: np.ndarray, *, shift_step: int = 2000,
               warmup: int = 1500, win: int = WIN, gamma: float = GAMMA,
               peak_window: int = PEAK_WINDOW) -> dict:
    """Temps de relaxation SANS ECHELLE, et ses deux gardes.

    ``relaxation_time`` est le nombre de pas, APRES le pic de
    perturbation, pour que l'exces d'erreur sur l'asymptote retombe sous
    ``gamma`` fois ce pic. La recherche demarre au pic et non au shift :
    un point anterieur au pic peut etre sous le seuil sans qu'aucune
    relaxation n'ait eu lieu.

    Deux quantites, toutes deux invariantes sous ``err -> c.err`` :

    * ``relaxation_time`` -- COMBIEN DE TEMPS le bras absorbe le choc ;
    * ``disruption`` = ``peak / pre`` -- DE COMBIEN il en a ete sorti.

    L'ancienne metrique les confondait : un bras structurellement moins
    precis a un ``pre`` plus haut *et* un ``peak`` plus haut, si bien
    que les deux axes le neutralisent la ou l'ancien seuil, lui, le
    recompensait.
    """
    pre = float(np.median(errs[warmup:shift_step]))
    n_steps = len(errs)
    tail = n_steps - shift_step
    # POST-HOC (non pre-enregistre) : asymptote APRES le shift. Sert a
    # distinguer "rattrape vite" de "jamais derange" -- une distinction
    # que l'ancienne metrique ne peut pas exprimer, faute d'un signe.
    post = float(np.median(errs[shift_step + peak_window:]))
    post_ratio = float(post / pre) if pre > 0 else float("inf")

    # s(t) = moyenne glissante sur [shift + t - win, shift + t]
    ts = np.arange(win, tail + 1)
    s = np.array([errs[shift_step + t - win:shift_step + t].mean()
                  for t in ts], dtype=float)
    excess = s - pre

    in_window = ts <= peak_window
    i_peak = int(np.argmax(excess[in_window]))
    peak = float(excess[i_peak])
    t_peak = int(ts[i_peak])

    if peak <= 0.0:
        # Le shift n'a pas sorti ce bras de son regime : il n'y a rien a
        # relaxer, et un temps de relaxation n'aurait aucun sens.
        return {"pre_median_err": pre, "peak_excess": peak,
                "t_peak": t_peak, "T": tail, "relaxation_time": tail,
                "disruption": 0.0, "perturbed": False,
                "post_median_err": post, "post_shift_ratio": post_ratio,
                "at_floor": False, "at_ceiling": True}

    T = tail
    for t, e in zip(ts[i_peak:], excess[i_peak:]):
        if e < gamma * peak:
            T = int(t)
            break
    relax = T - t_peak
    return {
        "pre_median_err": pre,
        "peak_excess": peak,
        "t_peak": t_peak,
        "T": int(T),
        "relaxation_time": int(relax),
        # peak / pre : sans echelle, comme le temps lui-meme.
        "disruption": float(peak / pre) if pre > 0 else float("inf"),
        "perturbed": True,
        "post_median_err": post,
        "post_shift_ratio": post_ratio,
        # Plancher : la decroissance tient dans une fenetre de lissage,
        # donc elle n'est pas RESOLUE -- meme lecture que le `at_floor`
        # de la case 8b, sur une echelle differente.
        "at_floor": bool(relax <= win),
        "at_ceiling": bool(T >= tail),
    }


def scale_invariance(errs: np.ndarray, scales=SCALES) -> dict:
    """Controle d'instrument P1 seconde, a DEUX faces.

    Positif : le temps de relaxation doit etre *exactement* egal sur
    ``errs`` et sur ``c . errs``. Negatif : l'ANCIENNE metrique doit,
    elle, bouger sur au moins une echelle -- sinon le test ne
    distinguerait pas une metrique sans echelle d'une metrique sans
    pouvoir de resolution, et une constante le passerait.
    """
    base_rel = relaxation(errs)["relaxation_time"]
    base_old = horizon_from_errs(errs)
    rel_stable, old_moved = True, False
    for c in scales:
        scaled = errs * c
        if relaxation(scaled)["relaxation_time"] != base_rel:
            rel_stable = False
        if horizon_from_errs(scaled) != base_old:
            old_moved = True
    return {
        "relaxation_invariant": bool(rel_stable),
        "old_metric_moved": bool(old_moved),
        "relaxation_time": int(base_rel),
        "old_horizon": int(base_old),
    }


def baseline_offset_control(errs: np.ndarray, offsets=(0.0, 1.0, 3.0), *,
                            shift_step: int = 2000,
                            warmup: int = 1500) -> dict:
    """CONTROLE POST-HOC -- ecrit APRES avoir vu echouer P1 seconde.

    P1 seconde predisait que l'ancienne metrique BOUGERAIT sous
    ``errs -> c . errs``. Elle ne bouge pas, et la demonstration tient
    en une ligne : son test est ``mean(errs[t-win:t]) < 1.2 . pre``, et
    sous ``errs -> c . errs`` les DEUX membres sont multiplies par
    ``c`` -- donc le premier ``t`` qui le franchit est le meme. La face
    negative de P1 seconde etait INSATISFAISABLE PAR CONSTRUCTION. Ce
    n'est pas l'instrument qui a echoue : c'est ma specification du
    controle. Le pre-enregistrement le dit lui-meme -- "si elle echoue,
    l'implementation trahit la definition" -- et c'est cette phrase-la
    qui etait fausse.

    Le vrai discriminant n'est pas multiplicatif mais ADDITIF. Sous
    ``errs -> errs + k . pre`` : l'exces ``s(t) - pre`` est INCHANGE
    (le decalage se soustrait), donc le temps de relaxation ne bouge
    pas ; mais la bande de l'ancienne metrique, ``1.2 . pre``,
    s'ELARGIT de ``1.2 . k . pre``, donc l'ancien horizon RETRECIT sans
    qu'aucune re-adaptation n'ait change. C'est la normalisation par la
    LIGNE DE BASE, et non par la PERTURBATION, qui est le defaut -- ce
    que la case 8b avait correctement nomme mais mal caracterise.

    Cette fonction ne peut produire AUCUN verdict positif : elle ne
    rend que deux series de nombres, et aucun seuil de decision de
    cette case ne la lit. Elle retire une lecture ; elle n'en fabrique
    aucune.
    """
    pre = float(np.median(errs[warmup:shift_step]))
    old, rel, peaks = [], [], []
    for k in offsets:
        shifted = errs + k * pre
        old.append(horizon_from_errs(shifted, shift_step=shift_step,
                                     warmup=warmup))
        r = relaxation(shifted, shift_step=shift_step, warmup=warmup)
        rel.append(r["relaxation_time"])
        peaks.append(r["peak_excess"])
    return {
        "offsets": [float(k) for k in offsets],
        "old_horizon": [int(v) for v in old],
        "relaxation_time": [int(v) for v in rel],
        "peak_excess": [float(v) for v in peaks],
        # Le SENS de la dissociation, pas un verdict : l'ancienne bouge,
        # la nouvelle non.
        "old_metric_moved": bool(len(set(old)) > 1),
        "relaxation_stable": bool(len(set(rel)) == 1),
    }


def _arm(model, pol, *, seed: int, shift_kind: str = "beta") -> dict:
    """Une trace, les DEUX metriques dessus, et les deux controles.

    ``scale`` est le controle PRE-ENREGISTRE (P1 seconde, multiplicatif) ;
    ``offset`` est le controle POST-HOC (additif) ecrit apres l'avoir vu
    echouer. Les deux sont conserves : effacer le premier reviendrait a
    reecrire une prediction scellee.
    """
    errs = collect_trace(model, pol, shift_kind=shift_kind, seed=seed)
    out = relaxation(errs)
    out["old_horizon"] = horizon_from_errs(errs)
    out["scale"] = scale_invariance(errs)
    out["offset"] = baseline_offset_control(errs)
    return out


def run_case8c(n_seeds: int = 5, n_feat: int = 8,
               motive_std: float = 0.6) -> dict:
    """Protocole pre-enregistre case 8c sur ``n_seeds`` graines.

    Les CINQ bras sont mesures par graine, avec la MEME metrique et le
    MEME ``gamma`` : les trois de la case 8b (politique autonome) et les
    deux de la case 8 (politique deterministe). C'est le garde-fou
    contre le sur-ajustement -- la metrique ne peut pas etre accordee a
    une case sans que cela se voie sur l'autre, et la case 8, dont le
    verdict ``FALSIFIED`` est deja publie (PR #12942), sert de temoin
    fixe.
    """
    rows = []
    for s in range(n_seeds):
        def auto_pol() -> AutonomousPolicy:
            return AutonomousPolicy(n_feat=n_feat, seed=s + 1000,
                                    motive_std=motive_std)

        def det_pol() -> LoopPolicy:
            return LoopPolicy(n_feat=n_feat, seed=s + 1000)

        # --- case 8b : le canal self est irreductible ---
        b_loop = _arm(SelfLoopModel(n_feat=n_feat, seed=s), auto_pol(), seed=s)
        b_surr = _arm(CompositeSurrogate(n_feat=n_feat, seed=s), auto_pol(),
                      seed=s)
        b_noise = _arm(NoiseChannelSurrogate(n_feat=n_feat, seed=s),
                       auto_pol(), seed=s)

        # --- case 8 : le canal self est deductible de l'etat ---
        a_loop = _arm(SelfLoopModel(n_feat=n_feat, seed=s), det_pol(), seed=s)
        a_surr = _arm(CompositeSurrogate(n_feat=n_feat, seed=s), det_pol(),
                      seed=s)

        rows.append({
            "seed": s,
            "c8b_loop": b_loop, "c8b_surrogate": b_surr, "c8b_noise": b_noise,
            "c8_loop": a_loop, "c8_surrogate": a_surr,
            "rho_beta_sf": b_surr["relaxation_time"]
            / max(b_loop["relaxation_time"], 1),
            "kappa_sf": b_noise["relaxation_time"]
            / max(b_surr["relaxation_time"], 1),
            "rho_beta_sf_case8": a_surr["relaxation_time"]
            / max(a_loop["relaxation_time"], 1),
        })

    arms_8b = ("c8b_loop", "c8b_surrogate", "c8b_noise")
    arms_all = arms_8b + ("c8_loop", "c8_surrogate")

    def med(key: str) -> float:
        return float(np.median([r[key] for r in rows]))

    rho = [r["rho_beta_sf"] for r in rows]
    invariant_all = all(r[a]["scale"]["relaxation_invariant"]
                        for r in rows for a in arms_all)
    old_moved_any = any(r[a]["scale"]["old_metric_moved"]
                        for r in rows for a in arms_all)
    floors = {a: sum(r[a]["at_floor"] for r in rows) for a in arms_all}
    ceils = {a: sum(r[a]["at_ceiling"] for r in rows) for a in arms_all}
    perturbed_all = all(r[a]["perturbed"] for r in rows for a in arms_all)
    half = n_seeds // 2 + 1
    degenerate = (not perturbed_all
                  or any(v >= half for v in floors.values())
                  or any(v >= half for v in ceils.values()))

    # --- POST-HOC, hors verdict : le controle ADDITIF corrige, et le
    # signe de la perturbation. Aucun seuil de decision ne les lit ; ils
    # ne peuvent donc rien confirmer, seulement expliquer.
    n_arms = len(rows) * len(arms_all)
    off_moved = sum(r[a]["offset"]["old_metric_moved"]
                    for r in rows for a in arms_all)
    off_stable = sum(r[a]["offset"]["relaxation_stable"]
                     for r in rows for a in arms_all)
    unperturbed = {a: sum(not r[a]["perturbed"] for r in rows)
                   for a in arms_all}
    post_ratio = {a: float(np.median([r[a]["post_shift_ratio"] for r in rows]))
                  for a in arms_all}

    # P1 seconde est un CONTROLE : il ne decouvre rien, il atteste que
    # l'implementation realise bien la definition. S'il tombe, aucune
    # autre ligne de ce resume n'est lisible.
    instrument_valid = bool(invariant_all and old_moved_any)

    if not instrument_valid:
        verdict = "INSTRUMENT_INVALIDE"
    elif degenerate:
        verdict = "INCONCLUSIF_INSTRUMENT"
    elif sum(x >= 3.0 for x in rho) >= 4:
        verdict = "CONFIRMED"
    else:
        verdict = "FALSIFIED"

    return {
        "rows": rows,
        "summary": {
            "n_seeds": n_seeds,
            # --- P1 seconde : controle d'instrument, deux faces ---
            "relaxation_invariant_all": bool(invariant_all),
            "old_metric_moved_any": bool(old_moved_any),
            "instrument_valid": instrument_valid,
            # --- P2 seconde / P3 seconde ---
            "rho_beta_sf_median": med("rho_beta_sf"),
            "rho_beta_sf_ge3_count": int(sum(x >= 3.0 for x in rho)),
            "kappa_sf_median": med("kappa_sf"),
            # --- temoin fixe : la case 8, verdict deja publie ---
            "rho_beta_sf_case8_median": med("rho_beta_sf_case8"),
            # --- porte de non-degenerescence ---
            "floor_counts": floors,
            "ceiling_counts": ceils,
            "all_perturbed": bool(perturbed_all),
            "instrument_degenerate": bool(degenerate),
            # --- POST-HOC (non pre-enregistre, hors verdict) ---
            # Le controle ADDITIF que P1 seconde aurait du specifier :
            # l'ancienne metrique bouge, la nouvelle non.
            "posthoc_offset_old_moved": "%d/%d" % (off_moved, n_arms),
            "posthoc_offset_relaxation_stable": "%d/%d" % (off_stable, n_arms),
            # Le SIGNE de la perturbation : un ratio < 1 dit que le shift
            # a RENDU LE BRAS MEILLEUR -- il n'y a rien a rattraper.
            "posthoc_unperturbed_counts": unperturbed,
            "posthoc_post_shift_ratio_median": post_ratio,
            # --- les deux axes, par bras (medianes) ---
            "relaxation_median": {
                a: float(np.median([r[a]["relaxation_time"] for r in rows]))
                for a in arms_all},
            "disruption_median": {
                a: float(np.median([r[a]["disruption"] for r in rows]))
                for a in arms_all},
            "old_horizon_median": {
                a: float(np.median([r[a]["old_horizon"] for r in rows]))
                for a in arms_all},
            "verdict": verdict,
        },
    }


if __name__ == "__main__":  # pragma: no cover
    import json

    print(json.dumps(run_case8c()["summary"], indent=2, sort_keys=True))
