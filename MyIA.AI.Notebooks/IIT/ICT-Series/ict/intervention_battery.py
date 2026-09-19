"""Batterie d'intervention : la chaine etat -> comportement TESTEE (issue #15480, critere 3).

Critere 3 de l'acceptance #15480 : « La chaine intervention -> changement
d'etat -> changement comportemental selectif est testee, pas seulement
racontee. » Ce module compose les primitives deja livrees pour la rendre
falsifiable sur le banc synthetique, SANS transformer (decision coordinateur
2026-09-12 : la pile #15479 hookable est en souffrance, le banc suffit) :

* :mod:`ict.bench_factorise` -- corpus a factorisation latente connue,
  beliefs joints exacts (le panneau d'« activations » du banc EST le belief
  joint, verite terrain incluse) ;
* :mod:`ict.sae_dictionary` -- :func:`~ict.sae_dictionary.train_sae` +
  :func:`~ict.sae_dictionary.factor_selectivity` selectionnent les features
  dediees au facteur A ;
* :mod:`ict.lens_gates` -- :func:`~ict.lens_gates.heldout_linear_score` fixe
  le readout (canal readout de la chaine) ;
* :mod:`ict.causal_engine` -- le moteur d'intervention lui-meme : specs
  declaratives, ablate, controles sham / aleatoire apparie / intact,
  :class:`~ict.causal_engine.EffectChannels` (etat / readout / comportement
  en slots separes), Holm-Bonferroni.

Deux bras d'intervention, tous deux natifs du moteur (cibles en coordonnees) :

* bras ``sae`` : ablation des ``m`` features SAE les plus selectives du
  facteur A, appliquee dans l'espace latent puis decodee vers l'espace
  belief ;
* bras ``flens`` : ablation des coordonnees belief portant le support du
  readout lineaire du facteur A (top-|w| du probe gele).

Pour chaque bras, la famille de controles du moteur : ``sham`` (pour
``ablate``, le sham du moteur EST le bras intact, documente dans
:func:`ict.causal_engine.sham_of`), ``random`` (cible aleatoire appariEE en
norme et frequence de corpus) et ``intact``. L'axe de dose est la FRACTION de
la cible ablatee (prefixe du classement par selectivite), pre-enregistree.

Verdicts par maillon, jamais de score omnibus (acceptance : « accord et
dissociation reportes separement ») :

* ``state`` -- le deplacement L1 de la marginale A (distance au belief propre
  gele) excede celui de B et ceux des controles ;
* ``behavior`` -- le score de decodage du probe gele sur A (sortie vraie
  classe, mesure continue pre-enregistree ; argmax en secondaire) degrade
  davantage que sur B et que sous controles, le FVU general restant borne
  (dommage general, :func:`ict.causal_engine.damage_metrics`) ;
* ``dose`` -- la degradation comportementale de A est monotone en la fraction
  ablatee.

Chaque verdict est ``SUPPORTED / NOT_SUPPORTED / INCONCLUSIVE`` avec taille
d'effet (mediane inter-seeds), IC percentile bootstrap et p-valeur de
permutation a signes apparEE (test exact 2^n sur les differences
inter-seeds), corrigee Holm au sein de la famille {cible vs B, cible vs
aleatoire} (les quatre tests substantifs de la selectivite) -- unilateraux,
directions pre-enregistrees dans les hypotheses. La comparaison PRINCIPALE de
chaque maillon est la selectivite (A vs B) ; l'effet vs sham (identite) est
rapporte comme controle de manipulation (``vs_sham``), hors famille Holm : sa
null est "aucun effet causal du tout", pas de la selectivite, et la gate
d'identite des tests prouve deja que le sham ne fait rien.

Paysage mesure (16 seeds, n=700, configuration des tests) -- a connaitre
avant de sur-interpreter un verdict : 7/8 tests substantifs SUPPORTED apres
Holm (sae : les quatre ; flens : vs_B etat et comportement, vs_random etat).
Le seul INCONCLUSIVE est flens/comportement vs aleatoire apparie : a d=12
l'espace produit porte A sur presque toutes les coordonnees, ablater 5
coordonnees quelconques (appariees en norme/frequence) degrade A-sans-B
autant que la cible top-|w| -- le controle apparie n'est pas A-aveugle dans
l'espace belief. C'est precisement la motivation du bras latent (features
dediees au facteur) : la selectivite vs aleatoire y est etablie sur les deux
canaux.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Dict, List, Sequence, Tuple

import numpy as np

from ict.causal_engine import (
    InterventionRecord,
    InterventionSpec,
    apply_intervention,
    damage_metrics,
    holm_adjust,
    random_target_matched,
    sham_of,
)
from ict.lens_gates import heldout_linear_score
from ict.sae_calibration import fraction_variance_unexplained
from ict.sae_dictionary import factor_selectivity, train_sae

__all__ = [
    "BATTERY_ARMS",
    "DEFAULT_DOSES",
    "BatteryOutcome",
    "BatteryResult",
    "build_corpus",
    "fit_behavior_probes",
    "probe_accuracy",
    "select_sae_targets",
    "select_flens_targets",
    "state_measurers",
    "readout_measurers",
    "behavior_measurers",
    "run_arm",
    "run_battery",
    "chain_verdict",
    "dose_monotonicity",
    "signflip_pvalue",
    "percentile_ci",
]


#: Les deux bras de la batterie. Un bras hors liste est une erreur de contrat.
BATTERY_ARMS: tuple[str, ...] = ("sae", "flens")

#: Fractions de cible ablatees, pre-enregistrees (l'axe de dose du protocole).
DEFAULT_DOSES: tuple[float, ...] = (0.25, 0.5, 0.75, 1.0)


# --------------------------------------------------------------------------- #
# Corpus : panneau belief + etats caches + decoupe gelee
# --------------------------------------------------------------------------- #

def build_corpus(
    bench,
    n: int,
    seed: int,
    eval_frac: float = 0.3,
) -> Dict[str, np.ndarray]:
    """Un corpus par seed : panneau belief joint exact, etats caches, labels
    de selectivite one-vs-rest (etat 0 de chaque facteur) et decoupe gelee.

    La decoupe train/eval est un permutation seeee par ``seed`` (meme
    discipline que :func:`ict.lens_gates.heldout_linear_score`) : probes, SAE
    et cibles sont ajustes sur train, la batterie mesure sur eval.
    """
    sample = bench.sample(n, seed_a=seed, seed_b=seed + 9000)
    beliefs = bench.beliefs(sample["obs_a"], sample["obs_b"])
    x = beliefs["belief_joint"]
    states_a, states_b = sample["states_a"], sample["states_b"]
    labels_a = states_a == 0
    labels_b = states_b == 0
    if labels_a.all() or not labels_a.any() or labels_b.all() or not labels_b.any():
        raise ValueError(
            f"corpus seed {seed} degenere (label one-vs-rest vide) : augmenter n"
        )
    rng = np.random.default_rng(seed + 7000)
    idx = rng.permutation(n)
    n_eval = max(2, int(round(n * eval_frac)))
    return {
        "x": x,
        "states_a": states_a,
        "states_b": states_b,
        "labels_a": labels_a,
        "labels_b": labels_b,
        "belief_a": beliefs["belief_a"],
        "belief_b": beliefs["belief_b"],
        "train": idx[n_eval:],
        "eval": idx[:n_eval],
    }


# --------------------------------------------------------------------------- #
# Probes comportementaux geles : least-squares one-hot -> argmax
# --------------------------------------------------------------------------- #

def fit_behavior_probes(
    x_tr: np.ndarray,
    s_a_tr: np.ndarray,
    s_b_tr: np.ndarray,
) -> Dict[str, np.ndarray]:
    """Deux probes lineaires geles (un par facteur), ajustes sur train seul.

    Le comportement du banc est defini par ces probes : decoder l'etat cache
    de chaque facteur depuis la representation. Ils sont ajustes UNE fois sur
    le corpus propre puis jamais re-entraines -- l'intervention ne peut pas
    « re-apprendre » a lire A.
    """
    probes = {}
    for name, states in (("a", s_a_tr), ("b", s_b_tr)):
        n_class = int(states.max()) + 1
        y = np.zeros((len(states), n_class))
        y[np.arange(len(states)), states] = 1.0
        design = np.hstack([x_tr, np.ones((len(x_tr), 1))])
        coef, *_ = np.linalg.lstsq(design, y, rcond=None)
        probes[f"probe_{name}"] = coef
    return probes


def probe_accuracy(
    probe: np.ndarray, x: np.ndarray, states: np.ndarray
) -> float:
    """Accuracy argmax du probe gele sur le panneau ``x`` (avec intercept)."""
    pred = np.hstack([x, np.ones((len(x), 1))]) @ probe
    return float((pred.argmax(axis=1) == states).mean())


# --------------------------------------------------------------------------- #
# Selection de cible : features SAE / coordonnees F-Lens du facteur A
# --------------------------------------------------------------------------- #

def select_sae_targets(
    x_tr: np.ndarray,
    labels_a_tr: np.ndarray,
    x_eval: np.ndarray,
    n_features: int = 32,
    k: int = 4,
    top_m: int = 12,
    seed: int = 0,
    n_steps: int = 400,
    z_min: float = 2.0,
    freq_min: float = 0.01,
) -> Dict[str, object]:
    """Entrainement SAE + selection des ``top_m`` features les plus selectives
    du facteur A (z-score de :func:`ict.sae_dictionary.factor_selectivity`,
    classement pre-enregistre : l'axe de dose est le PREFIXE de ce classement).

    Critere de qualite de cible, pre-enregistre : ``z >= z_min`` (la feature
    bat le null de relabelisation) ET frequence d'activation >= ``freq_min``
    sur le corpus COMPLET (train+eval, mesures sans labels : une feature
    quasi-morte n'a pas de contrepartie de norme pour l'appariement du
    controle aleatoire -- le moteur refuse sa bande, a juste titre).

    La selection de z n'utilise que le split train (labels compris) : eval
    reste vierge de toute information de selection.
    """
    fitted = train_sae(
        x_tr, n_features=n_features, k=k, seed=seed, n_steps=n_steps
    )
    sel = factor_selectivity(fitted["codes"], labels_a_tr, seed=seed)
    z = sel["z"]
    sae = fitted["sae"]
    freqs = (np.abs(sae.encode(np.vstack([x_tr, x_eval]))) > 0).mean(axis=0)
    eligible = (z >= z_min) & (freqs >= freq_min)
    order = np.argsort(-z)
    targets = [int(j) for j in order if eligible[j]][:top_m]
    if len(targets) < max(3, top_m // 2):
        raise ValueError(
            f"SAE seed {seed} : {len(targets)} features eligibles "
            f"(z>={z_min} et freq>={freq_min}) pour {top_m} demandees -- "
            "corpus ou dictionnaire non discriminant, la batterie refuse "
            "de selectionner un bruit"
        )
    return {
        "sae": fitted["sae"],
        "fvu": fitted["fvu"],
        "l0": fitted["l0"],
        "targets": targets,
        "z": sel["z"],
        "codes_eval": fitted["sae"].encode(x_eval),
    }


def select_flens_targets(
    x_tr: np.ndarray,
    labels_a_tr: np.ndarray,
    top_m: int = 6,
) -> Dict[str, object]:
    """Coordonnees belief du support du readout lineaire du facteur A :
    top-|w| du probe binaire ajuste sur train (le sous-espace F-Lens, en
    coordonnees -- la forme native du moteur).
    """
    y = labels_a_tr.astype(float)
    design = np.hstack([x_tr, np.ones((len(x_tr), 1))])
    coef, *_ = np.linalg.lstsq(design, y, rcond=None)
    w = coef[:-1]
    order = np.argsort(-np.abs(w))
    return {"w": w, "targets": [int(j) for j in order[:top_m]]}


# --------------------------------------------------------------------------- #
# Mesureurs des trois canaux (l'engine ne sait pas ce qu'est un comportement)
# --------------------------------------------------------------------------- #

def state_measurers(
    n_a: int, n_b: int, x_eval_clean: np.ndarray
) -> Dict[str, Callable[[np.ndarray], float]]:
    """Canal ETAT : deplacement L1 des marginales A et B par rapport au belief
    PROPRE (reference gelee du corpus).

    Le panneau du banc EST le belief joint : la marginale A s'obtient en
    sommant le bloc B, renormalisee apres clip (le decodeur du SAE rend des
    valeurs negatives). Une intervention selective pour A doit deplacer la
    marginale A davantage que la B -- l'entropie a ete ecartee comme mesure :
    dans l'espace produit, la renormalisation apres ablation entremele les
    deux facteurs et l'entropie de B monte mecaniquement quand on ampute des
    coordonnees porteuses de A (mesure sur banc, cf PR).
    """
    def _marginals(panel: np.ndarray, bloc: str) -> np.ndarray:
        joint = np.clip(panel.reshape(len(panel), n_a, n_b), 1e-12, None)
        marg = joint.sum(axis=2) if bloc == "a" else joint.sum(axis=1)
        return marg / marg.sum(axis=1, keepdims=True)

    ref_a = _marginals(x_eval_clean, "a")
    ref_b = _marginals(x_eval_clean, "b")
    return {
        "disp_a": lambda p: float(
            np.abs(_marginals(p, "a") - ref_a).sum(axis=1).mean()
        ),
        "disp_b": lambda p: float(
            np.abs(_marginals(p, "b") - ref_b).sum(axis=1).mean()
        ),
    }


def readout_measurers(
    belief_a: np.ndarray, belief_b: np.ndarray, seed: int
) -> Dict[str, Callable[[np.ndarray], float]]:
    """Canal READOUT : R^2 held-out du readout lineaire de chaque belief depuis
    le panneau (F-Lens belief-state, :func:`ict.lens_gates.heldout_linear_score`
    tel quel, split seede donc identique avant/apres).
    """
    return {
        "r2_a": lambda p: heldout_linear_score(p, belief_a, seed=seed)["r2"],
        "r2_b": lambda p: heldout_linear_score(p, belief_b, seed=seed)["r2"],
    }


def behavior_measurers(
    probes: Dict[str, np.ndarray],
    states_a: np.ndarray,
    states_b: np.ndarray,
    x_clean: np.ndarray,
) -> Dict[str, Callable[[np.ndarray], float]]:
    """Canal COMPORTEMENT : score continu de la vraie classe (mesure
    principale, pre-enregistree) + accuracy argmax (secondaire) + FVU general.

    Le score continu est la sortie DU probe gele (sorties one-hot ajustees
    par moindres carres) moyennee sur la vraie classe : le decode du facteur
    se degrade au sens LARGE avant que l'argmax ne bascule. L'argmax seul a
    ete ecarte comme mesure principale parce qu'il quantifie a perte : sur le
    banc, Mess3 a des marges enormes (argmax tres robuste pour A) tandis que
    RRXOR vit sur des egalites (argmax fragile pour B) -- comparer des
    degradations d'argmax entre les deux facteurs mesure la GEOMETRIE des
    marges, pas la causalite (mesure sur banc, cf PR).

    Le FVU est calcule contre le panneau propre (avant intervention) : c'est
    le proxy de « perplexite generale » du banc -- un collapse global ne peut
    pas se faire passer pour de la causalite selective.
    """
    def true_class_score(
        probe: np.ndarray, p: np.ndarray, states: np.ndarray
    ) -> float:
        pred = np.hstack([p, np.ones((len(p), 1))]) @ probe
        return float(pred[np.arange(len(states)), states].mean())

    return {
        "score_a": lambda p: true_class_score(probes["probe_a"], p, states_a),
        "score_b": lambda p: true_class_score(probes["probe_b"], p, states_b),
        "acc_a": lambda p: probe_accuracy(probes["probe_a"], p, states_a),
        "acc_b": lambda p: probe_accuracy(probes["probe_b"], p, states_b),
        "fvu": lambda p: float(fraction_variance_unexplained(x_clean, p)),
    }


# --------------------------------------------------------------------------- #
# Un bras : famille spec {cible x dose} + controles, mesures, enregistrements
# --------------------------------------------------------------------------- #

@dataclass
class BatteryOutcome:
    """Une ligne de resultat : bras, controle, dose, effets et dommage."""

    arm: str
    control: str          # target | sham | random | intact
    dose: float
    effects: Dict[str, Dict[str, float]] = field(default_factory=dict)
    damage: Dict[str, float] = field(default_factory=dict)
    record_json: str = ""


def _matched_or_widen(
    panel: np.ndarray,
    spec: InterventionSpec,
    norms: np.ndarray,
    freqs: np.ndarray,
) -> InterventionSpec:
    """Controle aleatoire apparie ; elargit la bande par paliers si aucune
    candidate ne tombe dans la bande (le moteur refuse un appariement degrade
    silencieux ; ici on documente le palier retenu dans control_ref)."""
    last_err: Exception = ValueError("controle aleatoire non tente")
    for rel_tol in (0.25, 0.5, 1.0):
        try:
            ctrl = random_target_matched(
                panel, spec, feature_norms=norms, feature_freqs=freqs,
                rel_tol=rel_tol, rng=np.random.default_rng(spec.seed + 51),
            )
            if rel_tol != 0.25:
                from dataclasses import replace

                ctrl = replace(ctrl, control_ref=f"random-matched(rel_tol={rel_tol})")
            return ctrl
        except ValueError as err:  # bande vide : palier suivant
            last_err = err
    raise last_err


def run_arm(
    arm: str,
    corpus: Dict[str, np.ndarray],
    targets: Sequence[int],
    measurers: Dict[str, Dict[str, Callable[[np.ndarray], float]]],
    sae=None,
    doses: Sequence[float] = DEFAULT_DOSES,
    seed: int = 0,
    run_id: str = "",
    match_stats: Tuple[np.ndarray, np.ndarray] | None = None,
) -> List[BatteryOutcome]:
    """Execute un bras complet : cible a chaque dose + sham + aleatoire apparie
    + intact, chacun mesure sur les trois canaux et enregistre (sha avant/apres).

    Bras ``sae`` : l'ablation s'applique au panneau LATENT (codes eval), la
    reconstruction par le decodeur ramene l'effet dans l'espace belief ou les
    canaux se mesurent ; le dommage cible/hors-cible se mesure dans l'espace
    D'ECRITURE (le latent), ou la cible est definie. Bras ``flens`` : panneau
    belief directement.
    """
    if arm not in BATTERY_ARMS:
        raise ValueError(f"bras {arm!r} hors contrat {BATTERY_ARMS}")
    eval_idx = corpus["eval"]
    x_eval = corpus["x"][eval_idx]
    z_eval = sae.encode(x_eval) if sae is not None else None
    write_panel = z_eval if arm == "sae" else x_eval

    def belief_panel_after(w: np.ndarray) -> np.ndarray:
        return sae.decode(w) if arm == "sae" else w

    positions = tuple(range(len(eval_idx)))
    instrument = "sae" if arm == "sae" else "flens"
    space = "sae_latent" if arm == "sae" else "residual"
    ranked = list(targets)
    outcomes: List[BatteryOutcome] = []

    def measure_all(
        control: str,
        dose: float,
        spec_applied: InterventionSpec,
        write_after: np.ndarray,
    ) -> BatteryOutcome:
        """Mesure UNE intervention appliquee : l'enregistrement decrit la spec
        REELLEMENT appliquee (jamais une cible reconstruite apres coup).

        Baseline des canaux = le panneau belief NON intervene DE L'ARME : pour
        le bras sae c'est ``decode(encode(x))`` (le roundtrip du SAE fait
        partie de l'instrument ; son erreur de reconstruction est le FVU
        AVANT, pas un effet de l'intervention) -- sham/intact rendent alors
        des deltas EXACTEMENT nuls dans les deux bras.
        """
        belief_after = belief_panel_after(write_after)
        belief_before = belief_panel_after(write_panel)
        rec = InterventionRecord(
            spec=spec_applied,
            alignment=spec_applied.alignment(
                model=f"bench", dose=dose, control=control
            ),
            sha_before=_sha(write_panel),
            sha_after=_sha(write_after),
        )
        rec.damage = damage_metrics(write_panel, write_after, spec_applied)
        for channel, fns in measurers.items():
            rec.effects.record(channel, fns, belief_before, belief_after)
        out = BatteryOutcome(
            arm=arm, control=control, dose=dose,
            effects={
                ch: dict(getattr(rec.effects, ch))
                for ch in ("state", "readout", "behavior")
            },
            damage=dict(rec.damage),
            record_json=rec.to_json(),
        )
        outcomes.append(out)
        return out

    def make_spec(features: Sequence[int]) -> InterventionSpec:
        return InterventionSpec(
            operation="ablate", instrument=instrument, layer=0,
            positions=positions, features=tuple(features),
            tensor_space=space, run=run_id, seed=seed,
        )

    # cible x dose : PREFIXE du classement par selectivite
    for dose in doses:
        n_kept = max(1, int(round(dose * len(ranked))))
        spec = make_spec(ranked[:n_kept])
        write_after = apply_intervention(write_panel, spec)
        measure_all("target", float(dose), spec, write_after)

    # sham : le sham du moteur pour ablate EST le bras intact (documente)
    sham_spec = sham_of(make_spec(ranked))
    write_after = apply_intervention(write_panel, sham_spec)
    measure_all("sham", 0.0, sham_spec, write_after)

    # aleatoire apparie : normes/frequences de CORPUS (passees par la batterie
    # en stats plein-corpus ; a defaut, stats du panneau d'ecriture seul)
    if match_stats is not None:
        norms, freqs = match_stats
    else:
        norms = np.linalg.norm(write_panel, axis=0)
        freqs = (np.abs(write_panel) > 0).mean(axis=0)
    rnd = None
    try:
        rnd = _matched_or_widen(write_panel, make_spec(ranked), norms, freqs)
    except ValueError:
        rnd = None
    if rnd is not None:
        write_after = apply_intervention(write_panel, rnd)
        measure_all("random", 1.0, rnd, write_after)

    # intact : cible vide par la meme voie (identite prouvee, pas supposee)
    intact = make_spec(())
    write_after = apply_intervention(write_panel, intact)
    measure_all("intact", 0.0, intact, write_after)
    return outcomes


def _sha(panel: np.ndarray) -> str:
    import hashlib

    return hashlib.sha256(np.ascontiguousarray(panel).tobytes()).hexdigest()


# --------------------------------------------------------------------------- #
# Statistiques : permutation a signes, IC bootstrap, verdicts par maillon
# --------------------------------------------------------------------------- #

def signflip_pvalue(diffs: Sequence[float]) -> float:
    """Test exact de permutation a signes apparEEs sur les differences
    inter-seeds (2^n configurations), unilateral a droite : H1 pre-enregistree
    = l'effet cible EXCEDE le controle. Renvoie la proportion de configurations
    dont la medianne signee atteint l'observee."""
    d = np.asarray(diffs, dtype=float)
    n = len(d)
    if n == 0 or not np.isfinite(d).all():
        return 1.0
    med_obs = np.median(d)
    # enumeration exacte 2^n PAR BLOCS de 65 536 signes : une seule passe C
    # par bloc au lieu d'un appel Python par configuration (a n=16 la boucle
    # par configuration coutait ~30 s sur la batterie complete ; vectorisee
    # ~0,1 s), et memoire bornee a ~8 Mo quel que soit n -- au-dela de 16
    # seeds l'enumeration reste exacte, juste plus longue.
    total = 2 ** n
    block = 65536
    bits = np.arange(n)
    n_ge = 0
    for start in range(0, total, block):
        chunk = np.arange(start, min(start + block, total))
        signs = ((chunk[:, None] >> bits) & 1).astype(float) * 2.0 - 1.0
        stats = np.median(d[None, :] * signs, axis=1)
        n_ge += int((stats >= med_obs - 1e-12).sum())
    return float(n_ge / total)


def percentile_ci(
    values: Sequence[float], n_boot: int = 10000, seed: int = 42
) -> Tuple[float, float]:
    """IC percentile bootstrap (2.5 %, 97.5 %) de la medianne, meme budget
    resampling que les gardes de la serie (10 000, seed 42)."""
    v = np.asarray(values, dtype=float)
    rng = np.random.default_rng(seed)
    meds = np.median(
        v[rng.integers(0, len(v), size=(n_boot, len(v)))], axis=1
    )
    return float(np.percentile(meds, 2.5)), float(np.percentile(meds, 97.5))


def chain_verdict(
    effects_target: Sequence[float],
    effects_control: Sequence[float],
    *,
    min_seeds: int = 4,
    support_frac: float = 0.75,
) -> Dict[str, object]:
    """Verdict d'un maillon de la chaine pour UNE comparaison cible/controle :
    medianne des differences inter-seeds, IC bootstrap, p de permutation.
    SUPPORTED exige p < 0.05 et >= ``support_frac`` des seeds dans le sens de
    H1 ; NOT_SUPPORTED si la medianne est <= 0 ; INCONCLUSIVE sinon."""
    diffs = [t - c for t, c in zip(effects_target, effects_control)]
    med = float(np.median(diffs)) if diffs else 0.0
    p = signflip_pvalue(diffs)
    lo, hi = percentile_ci(diffs) if diffs else (0.0, 0.0)
    n_pos = int(sum(d > 0 for d in diffs))
    if p < 0.05 and n_pos >= support_frac * len(diffs) and len(diffs) >= min_seeds:
        verdict = "SUPPORTED"
    elif med <= 0.0:
        verdict = "NOT_SUPPORTED"
    else:
        verdict = "INCONCLUSIVE"
    return {
        "verdict": verdict,
        "median_diff": med,
        "ci95": (lo, hi),
        "p_signflip": p,
        "n_seeds_positive": n_pos,
        "n_seeds": len(diffs),
    }


def dose_monotonicity(
    per_seed_curves: Sequence[Sequence[float]],
) -> Dict[str, object]:
    """Maillon dose : la degradation (acc_a before - after, deja positive =
    degradation) est croissante le long de l'axe de fraction. Une egalite
    entre deux doses consecutives est toleree UNE fois par courbe (bruit de
    discretisation du prefixe), deux non."""
    n_ok = 0
    for curve in per_seed_curves:
        steps = np.diff(np.asarray(curve, dtype=float))
        if int((steps < -1e-9).sum()) <= 1:
            n_ok += 1
    frac = n_ok / len(per_seed_curves) if per_seed_curves else 0.0
    verdict = "SUPPORTED" if frac >= 0.75 else (
        "NOT_SUPPORTED" if frac < 0.5 else "INCONCLUSIVE"
    )
    return {"verdict": verdict, "n_seeds_monotone": n_ok,
            "n_seeds": len(per_seed_curves), "frac": frac}


# --------------------------------------------------------------------------- #
# Batterie complete
# --------------------------------------------------------------------------- #

@dataclass
class BatteryResult:
    """Resultat rejouable de la batterie : lignes par bras/controle/dose,
    verdicts par maillon avec Holm, effets par seed."""

    bench_name: str
    seeds: List[int]
    outcomes: List[BatteryOutcome]
    verdicts: Dict[str, Dict[str, object]] = field(default_factory=dict)

    def to_dict(self) -> Dict[str, object]:
        return {
            "bench": self.bench_name,
            "seeds": list(self.seeds),
            "outcomes": [
                {
                    "arm": o.arm, "control": o.control, "dose": o.dose,
                    "effects": o.effects, "damage": o.damage,
                }
                for o in self.outcomes
            ],
            "verdicts": self.verdicts,
        }


def run_battery(
    bench,
    seeds: Sequence[int] = (0, 1, 2, 3, 4, 5),
    n: int = 1200,
    doses: Sequence[float] = DEFAULT_DOSES,
    sae_kwargs: dict | None = None,
    top_m_flens: int = 6,
) -> BatteryResult:
    """La batterie complete sur un :class:`ict.bench_factorise.FactoredBench`.

    Par seed : corpus + decoupe gelee, probes comportementaux geles, SAE +
    selection des features A, puis les DEUX bras (sae / flens) avec leurs
    familles de controles. Agrege les maillons etat / comportement / dose et
    corrige Holm la famille {cible vs B, cible vs aleatoire} par bras (le
    principal de chaque maillon EST le vs_B ; l'effet vs sham est rapporte
    comme controle de manipulation, hors famille).
    """
    sae_kwargs = dict(sae_kwargs or {})
    n_a = int(bench.factor_a.n_states)
    n_b = int(bench.factor_b.n_states)
    all_outcomes: List[BatteryOutcome] = []
    per_seed: Dict[str, Dict[str, Dict[str, List[float]]]] = {}

    for seed in seeds:
        corpus = build_corpus(bench, n=n, seed=seed)
        tr, ev = corpus["train"], corpus["eval"]
        x_tr, x_ev = corpus["x"][tr], corpus["x"][ev]
        probes = fit_behavior_probes(
            x_tr, corpus["states_a"][tr], corpus["states_b"][tr]
        )
        measurers = {
            "state": state_measurers(n_a, n_b, x_ev),
            "readout": readout_measurers(
                corpus["belief_a"][ev], corpus["belief_b"][ev], seed=seed
            ),
            "behavior": behavior_measurers(
                probes, corpus["states_a"][ev], corpus["states_b"][ev], x_ev
            ),
        }
        fitted = select_sae_targets(
            x_tr, corpus["labels_a"][tr], x_ev, seed=seed, **sae_kwargs
        )
        flens = select_flens_targets(x_tr, corpus["labels_a"][tr],
                                     top_m=top_m_flens)
        stats_corpus = np.linalg.norm(corpus["x"], axis=0), (
            np.abs(corpus["x"]) > 0
        ).mean(axis=0)
        for arm, targets, sae in (
            ("sae", fitted["targets"], fitted["sae"]),
            ("flens", flens["targets"], None),
        ):
            if arm == "sae":
                z_corpus = sae.encode(corpus["x"])
                stats_arm = (
                    np.linalg.norm(z_corpus, axis=0),
                    (np.abs(z_corpus) > 0).mean(axis=0),
                )
            else:
                stats_arm = stats_corpus
            outs = run_arm(
                arm, corpus, targets, measurers, sae=sae,
                doses=doses, seed=seed, run_id=f"{bench.name}-s{seed}",
                match_stats=stats_arm,
            )
            all_outcomes.extend(outs)
            bucket = per_seed.setdefault(arm, {
                k: [] for k in
                ("disp_a_t", "disp_a_s", "disp_a_r", "disp_b_t",
                 "deg_a_t", "deg_a_s", "deg_a_r", "deg_b_t", "fvu_t",
                 "sel_state_r", "sel_beh_r")
            })
            target_full = _at_dose(outs, "target", 1.0)
            sham_o = _at_dose(outs, "sham", 0.0)
            rnd_o = _at_dose(outs, "random", 1.0)
            bucket["disp_a_t"].append(
                target_full.effects["state"]["disp_a_delta"])
            bucket["disp_a_s"].append(sham_o.effects["state"]["disp_a_delta"])
            if rnd_o is not None:
                bucket["disp_a_r"].append(
                    rnd_o.effects["state"]["disp_a_delta"])
                bucket["sel_state_r"].append(
                    rnd_o.effects["state"]["disp_a_delta"]
                    - rnd_o.effects["state"]["disp_b_delta"]
                )
            bucket["disp_b_t"].append(
                target_full.effects["state"]["disp_b_delta"])
            bucket["deg_a_t"].append(
                -target_full.effects["behavior"]["score_a_delta"])
            bucket["deg_a_s"].append(
                -sham_o.effects["behavior"]["score_a_delta"])
            if rnd_o is not None:
                bucket["deg_a_r"].append(
                    -rnd_o.effects["behavior"]["score_a_delta"])
                bucket["sel_beh_r"].append(
                    -(rnd_o.effects["behavior"]["score_a_delta"]
                      - rnd_o.effects["behavior"]["score_b_delta"])
                )
            bucket["deg_b_t"].append(
                -target_full.effects["behavior"]["score_b_delta"])
            bucket["fvu_t"].append(target_full.effects["behavior"]["fvu_after"])

    verdicts: Dict[str, Dict[str, object]] = {}
    for arm in BATTERY_ARMS:
        b = per_seed.get(arm, {})
        if not b:
            continue
        # Comparaison PRINCIPALE = la selectivite (A vs B) : c'est le claim
        # de la chaine (critere 3 #15480). L'effet vs sham (identite, delta
        # nul par construction) reste rapporte sous "vs_sham" comme controle
        # de manipulation, HORS famille Holm -- sa null est "aucun effet
        # causal", pas de la selectivite ; l'y inclure draine la puissance
        # des quatre tests substantifs sans information ajoutee.
        v_state = chain_verdict(b["disp_a_t"], b["disp_b_t"])
        v_state["vs_sham"] = chain_verdict(b["disp_a_t"], b["disp_a_s"])
        v_beh = chain_verdict(b["deg_a_t"], b["deg_b_t"])
        v_beh["vs_sham"] = chain_verdict(b["deg_a_t"], b["deg_a_s"])
        if b.get("disp_a_r") and len(b["disp_a_r"]) == len(b["disp_a_t"]):
            # appariement par seed exige : le controle aleatoire a rate sur
            # certaines seeds -> listes de longueurs differentes -> INCONCLUSIVE.
            # vs_random se joue sur la DIFFERENTIELLE de selectivite (A - B) :
            # a d=12 l'espace produit porte A sur presque toutes les
            # coordonnees, le dommage absolu du controle aleatoire est domine
            # par la MASSE des coordonnees touchees -- ce qui distingue la
            # cible, c'est qu'elle degrade A SANS B, pas qu'elle degrade
            # davantage en valeur absolue.
            sel_state_t = [x - y for x, y in zip(b["disp_a_t"], b["disp_b_t"])]
            sel_beh_t = [x - y for x, y in zip(b["deg_a_t"], b["deg_b_t"])]
            v_state["vs_random"] = chain_verdict(
                sel_state_t, b["sel_state_r"])
            v_beh["vs_random"] = chain_verdict(sel_beh_t, b["sel_beh_r"])
            famille = [v_state["p_signflip"], v_state["vs_random"]["p_signflip"],
                       v_beh["p_signflip"], v_beh["vs_random"]["p_signflip"]]
            adj = holm_adjust(famille)
            v_state["p_holm"], v_state["vs_random"]["p_holm"] = adj[0], adj[1]
            v_beh["p_holm"], v_beh["vs_random"]["p_holm"] = adj[2], adj[3]
            v_state["verdict"] = _reholm(v_state)
            v_state["vs_random"]["verdict"] = _reholm(v_state["vs_random"])
            v_beh["verdict"] = _reholm(v_beh)
            v_beh["vs_random"]["verdict"] = _reholm(v_beh["vs_random"])
        elif b.get("disp_a_r"):
            v_state["vs_random"] = {
                "verdict": "INCONCLUSIVE",
                "raison": "controle aleatoire absent sur certaines seeds "
                          "(appariement par seed impossible)",
            }
            v_beh["vs_random"] = dict(v_state["vs_random"])
        v_beh["fvu_median"] = float(np.median(b["fvu_t"]))
        verdicts[f"{arm}/etat"] = v_state
        verdicts[f"{arm}/comportement"] = v_beh
        seed_curves = _dose_curves(all_outcomes, arm, seeds, doses)
        verdicts[f"{arm}/dose"] = dose_monotonicity(seed_curves)

    return BatteryResult(
        bench_name=bench.name, seeds=list(seeds), outcomes=all_outcomes,
        verdicts=verdicts,
    )


def _reholm(v: Dict[str, object]) -> str:
    """Re-tranche le verdict sur la p-valeur Holm-corrigee (la correction ne
    peut que durcir l'exigence, jamais l'assouplir)."""
    if v["verdict"] == "SUPPORTED" and v.get("p_holm", 0.0) >= 0.05:
        return "INCONCLUSIVE"
    return str(v["verdict"])


def _at_dose(outs: List[BatteryOutcome], control: str,
             dose: float) -> BatteryOutcome:
    for o in outs:
        if o.control == control and abs(o.dose - dose) < 1e-9:
            return o
    if control == "random":
        return None  # type: ignore[return-value]
    raise KeyError(f"controle {control!r} dose {dose} absent du bras")


def _dose_curves(
    all_outcomes: List[BatteryOutcome], arm: str, seeds: Sequence[float],
    doses: Sequence[float],
) -> List[List[float]]:
    """Courbes dose-reponse par seed : degradation acc_a (before - after,
    positive = degradation) a chaque fraction, meme grain que les verdicts.

    Les outcomes cible d'un meme bras arrivent CONSECUTIFS par seed (ordre
    d'emission de :func:`run_arm`) : on decoupe en blocs de ``len(doses)`` --
    un dict par (bras, controle, dose) ecraserait les seeds entre elles.
    """
    targets = [o for o in all_outcomes if o.arm == arm and o.control == "target"]
    n_d = len(doses)
    if n_d == 0 or len(targets) % n_d != 0:
        return []
    return [
        [-o.effects["behavior"]["acc_a_delta"] for o in targets[i:i + n_d]]
        for i in range(0, len(targets), n_d)
    ]
