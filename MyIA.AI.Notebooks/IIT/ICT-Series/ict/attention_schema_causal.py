"""Case 5bis — interrogation CAUSALE de l'état attentionnel sur traces gelées (#15798, #8182).

Le verdict INCONCLUSIF de la case 5 (#15547) porte sur le **readout seul** :
à ce substrat (SAE Qwen-Scope layer 12/24 de Qwen3.5-2B-Base), le broadcast
workspace est quasi-uniforme et ne distingue pas une cible attentionnelle
d'une cible d'objet. C'est une limite de l'axe readout, pas une preuve
d'absence du schéma dans l'**état** interne. Ce module ajoute l'axe manquant
avec le moteur d'interventions causales #15479 (``ict.causal_engine``) :
séparer **état / readout / comportement** (EPIC #15475), contrôles
obligatoires compris (sham, cible aléatoire appariée, dose-réponse).

Matériel : les traces gelées de la case 5, RÉUTILISÉES sans ré-extraction
(``traces/case5_s*.npz`` + ``traces/case5calib_s*.npz``), et la calibration
gelée de la case 5 (``ict/results/attention_schema_results.json``,
``sigma_attn``/``epsilon_attn``) dont ce protocole continue la forme.

Protocole case 5bis (scellé AVANT le run — anti-HARKing, cf case 5)
-------------------------------------------------------------------

**Fenêtre d'intervention = suffixe, aligné à la divergence.** Les bras d'un
triplet partagent le contexte amont à l'identique ; seule la clause cible
diffère (pré-enregistrement case 5 : « contre-factuels exacts, mêmes
contextes, seule la cible d'attention diffère »). La fenêtre de A et du
donneur B = les ``k`` DERNIÈRES positions de chaque prompt, ``k = min`` des
longueurs de clause, la clause partant du premier token divergent (trouvé en
comparant les tokens gauche-à-droite). Choix motivé : l'état qui porte la
cible est la fin du prompt (le workspace au moment où la génération
commencerait), pas une « ignition » — la case 5 montre que le quantile
d'ignition dégénère sur T≈40 (une position, souvent le token 0).

**Cible = l'état EMPIRIQUE du donneur à sa fenêtre.** Les features ciblées
sont l'union des top-k actifs du donneur SUR SA fenêtre (mesure préalable
sur seed 0 : patcher la signature agrégée top-64 écrit des zéros sur des
zéros — les features signature ne sont pas forcément actives à la fenêtre ;
le correctif est de porter l'état réel, pas son résumé).

**Opération = patch du moteur, dose par pré-interpolation du donneur.**
Toutes les écritures passent par ``causal_engine.apply_intervention``
(opération ``patch`` = écriture absolue de valeurs empiriques). La dose
``lambda`` interpole le DONNEUR — ``donor_lambda = (1-lambda)·x_A +
lambda·donor`` — jamais la sémantique de l'opération : ``lambda = 1`` est le
patch pur, ``lambda = 0`` est le sham (donneur = soi, écriture par la MÊME
voie de code, résultat identité — ``sham_of`` du moteur).

**Métrique de bascule (canal readout-de-l'état).**
``composition(fenêtre, signature)`` = fraction des positions de la fenêtre
dont l'argmax SAE ∈ signature (top-64 par activation moyenne du bras,
convention case 5). La bascule principale :
``flip(lambda) = composition(fenêtre patchée, sig_donneur) -
composition(fenêtre intacte, sig_donneur)``. HONNÊTE : sur traces gelées,
les positions AVAL ne se recalculent pas (il n'y a pas de génération dans la
trace) — cette métrique mesure la composition READOUT-ELIGIBLE de l'état
(ce que le workspace PORTE), pas sa propagation aval. La propagation
comportementale exige des forward-pass GPU avec état réinjecté : hors scope
de ce module, documentée comme telle dans le verdict par axe.

**Null adversarial, exécuté AVANT les bras principaux** (anti-HARKing,
même ordre que case 5) : le même patch ``lambda = 1`` entre les deux objets
NEUTRES de calibration (Tour Eiffel → Mont Blanc, ``calib_obj1 →
calib_obj2``) sur les traces de calibration. La dispersion des bascules
neutres sur 5 graines fixe ``sigma_null`` ; ``epsilon_flip = 0.5 × sigma_null
× composition(intact, sig_neutre)_médian`` — la forme exacte de la case 5
(``ε = 0.5 × σ × échelle-médiane``), appliquée à la métrique de bascule.

**Contrôles par intervention** (#15479) : sham (``lambda = 0``, identité par
la même voie), cible aléatoire APPARIÉE en norme et fréquence
(``random_target_matched``, normes/fréquences POOLÉES sur les 5 graines ×
(main + calib) — une seule graine n'offre pas assez de candidates, mesure
préalable), bras intact (cible vide). Comparaisons {cible vs aléatoire,
cible vs sham} corrigées Holm-Bonferroni.

**Verdict PAR AXE (scellé)** :

- **état** — « l'état attentionnel est inscriptible de façon
  SPÉCIFIQUE AU CONTENU » : CONFIRMED si bascule médiane (``lambda=1``) ≥
  ``epsilon_flip`` sur ≥ 4/5 graines ET bascule du contrôle aléatoire
  apparié < ``epsilon_flip`` (Holm) ET dose-réponse monotone (bascule
  croissante sur ≥ 3 paliers de lambda sur 4). INCONCLUSIF si la bascule
  dépasse ε mais le contrôle aléatoire aussi (rupture GÉNÉRIQUE, pas
  spécifique au contenu). FALSIFIED si la bascule ne dépasse pas ε (l'état
  n'est pas inscriptible de façon mesurable).
- **readout** — mêmes nombres, étiquette honnête « readout-de-l'état sur
  panneaux gelés » : la composition du fenêtrage après patch. La
  PROPAGATION readout (consommateurs aval recalculés) est GPU-gated et
  suit ce module.
- **comportement** — NON-MESURABLE sur traces gelées (aucune position aval
  ne se recalcule). Le verdict rendu est ``NOT_MEASURABLE_FROZEN``, jamais
  imputé : c'est la limite instrinsèque du matériel, pas un résultat.

Grade C documentaire : ce jouet interroge si l'ÉTAT workspace est
causalement inscriptible vers la représentation d'une autre cible
attentionnelle, avec les contrôles du moteur. Aucune phénoménologie n'est
mesurée (cf avertissements grade C de la matrice, case 5).

References
----------
#15798 (case 5bis), #15479/#15609 (moteur causal), #15547 (case 5 et sa
calibration gelée), EPIC #8182 (dissociations), #15475 (séparation
état/readout/comportement). Pré-enregistrement case 5 :
``docs/ict/dissociations-matrix.md`` l. 297-369.
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from pathlib import Path

import numpy as np

from . import causal_engine as ce
from .attention_schema import SEEDS
from .sae_traces import densify, load_traces, mean_activation_by_set

__all__ = [
    "DIVERGENCE_POLICY",
    "DOSES",
    "K_FEATURES",
    "ARM_PAIRS",
    "find_divergence",
    "suffix_window",
    "donor_features",
    "composition",
    "patch_window",
    "flip_curve",
    "neutral_null",
    "calibrate_null",
    "run_main_arms",
    "axis_verdicts",
    "run_analysis",
]

#: Politique de divergence : premier index où les tokens diffèrent. Deux
#: prompts d'un triplet partagent le contexte amont ; si un token du contexte
#: tokenisait différemment selon la clause qui suit (BPE non local), la
#: divergence remonterait trop tôt -- le run le MESURE et le consigne au lieu
#: de le supposer.
DIVERGENCE_POLICY = "first-differing-token"

#: Doses scellées : interpolation du donneur. lambda=0 = sham (identité par
#: la même voie), lambda=1 = patch pur. 4 paliers + sham.
DOSES: tuple[float, ...] = (0.25, 0.5, 0.75, 1.0)

#: Convention case 5 : signature = top-64 par activation moyenne du bras.
K_FEATURES = 64

#: Paires de bras interrogées : l'état du bras A reçoit l'état du donneur B.
#: Les deux contre-factuels de la case 5 : autre-attention (même complexité
#: agentique, cible attentionnelle différente) et objet (non attentionnel).
ARM_PAIRS: tuple[tuple[str, str], ...] = (
    ("attn_self", "attn_other"),
    ("attn_self", "obj_chaise"),
)


# --------------------------------------------------------------------------- #
# Fenêtre : divergence + suffixe
# --------------------------------------------------------------------------- #
def find_divergence(tokens_a: list[str], tokens_b: list[str]) -> int:
    """Premier index où deux prompts divergent (tokens comparés gauche-droite).

    Rend ``min(len_a, len_b)`` si aucun token ne diffère sur le préfixe
    commun (un prompt préfixe de l'autre : la divergence est la fin du
    court). Jamais négatif, jamais au-delà du prompt le plus court.
    """
    n = min(len(tokens_a), len(tokens_b))
    for i in range(n):
        if tokens_a[i] != tokens_b[i]:
            return i
    return n


def suffix_window(tokens_a: list[str], tokens_b: list[str]) -> tuple[range, range, int]:
    """Fenêtres de patch (suffixes de longueur égale k, alignés à la fin).

    Rend (positions_a, positions_b, k) où ``positions_x`` couvre les k
    DERNIÈRES positions de chaque prompt et ``k = min`` des longueurs de
    clause (longueur moins divergence). Le suffixe porte la clause cible :
    c'est l'état qui précéderait immédiatement la génération.
    """
    div = find_divergence(tokens_a, tokens_b)
    k = min(len(tokens_a) - div, len(tokens_b) - div)
    if k <= 0:
        raise ValueError(
            f"fenêtre vide : div={div}, T=({len(tokens_a)}, {len(tokens_b)})"
        )
    return range(len(tokens_a) - k, len(tokens_a)), range(len(tokens_b) - k, len(tokens_b)), k


# --------------------------------------------------------------------------- #
# État empirique du donneur + métrique de composition
# --------------------------------------------------------------------------- #
def donor_features(donor_dense: np.ndarray, positions: range) -> tuple[int, ...]:
    """Features actives du donneur SUR SA fenêtre (l'état réel, pas le résumé).

    Union des features non nulles du panneau dense du donneur restreint à sa
    fenêtre. Avec des traces top-k, c'est l'union des top-k actifs par
    position -- mesuré avant d'écrire le module : patcher la signature
    agrégée écrit des zéros sur des zéros.
    """
    sub = donor_dense[positions, :]
    active = np.unique(np.nonzero(sub)[1])
    return tuple(int(f) for f in active)


def composition(window_dense: np.ndarray, signature: np.ndarray) -> float:
    """Fraction des positions de la fenêtre dont l'argmax ∈ signature.

    Convention case 5 : la signature d'un bras = top-``K_FEATURES`` par
    activation moyenne. NaN jamais fabriqué : fenêtre vide -> ValueError.
    """
    if window_dense.size == 0:
        raise ValueError("fenêtre vide : composition non définie")
    argmax = np.argmax(window_dense, axis=1)
    sig = set(int(f) for f in signature)
    return float(np.mean([int(a) in sig for a in argmax]))


def patch_window(dense_a: np.ndarray, dense_b: np.ndarray,
                 pos_a: range, pos_b: range, feats: tuple[int, ...],
                 lam: float, *, spec_kwargs: dict | None = None) -> np.ndarray:
    """Patch dose-``lam`` de la fenêtre de A par l'état empirique de B.

    Le donneur est pré-interpolé — ``donor_lam = (1-lam)·x_A + lam·donor`` —
    puis écrit par ``causal_engine.apply_intervention`` (opération ``patch``,
    écriture absolue, la MÊME voie de code à toute dose). ``lam = 0`` est le
    sham du moteur (donneur = soi, identité par la même voie).
    """
    if not 0.0 <= lam <= 1.0:
        raise ValueError(f"lam ∈ [0, 1] exigé, reçu {lam}")
    if not feats:
        raise ValueError("cible vide : utiliser le bras intact du moteur")
    slice_a = dense_a[np.ix_(list(pos_a), list(feats))]
    slice_b = dense_b[np.ix_(list(pos_b), list(feats))]
    donor_lam = ((1.0 - lam) * slice_a + lam * slice_b).astype(dense_a.dtype)
    spec = ce.InterventionSpec(
        operation="patch",
        instrument="sae",
        layer=spec_kwargs.get("layer", 12) if spec_kwargs else 12,
        positions=tuple(int(p) for p in pos_a),
        features=feats,
        dose=float(lam),
        donor=tuple(tuple(float(v) for v in row) for row in donor_lam),
        tensor_space="sae_latent",
        run=spec_kwargs.get("run", "") if spec_kwargs else "",
        paired_run=spec_kwargs.get("paired_run", "") if spec_kwargs else "",
        seed=spec_kwargs.get("seed", 0) if spec_kwargs else 0,
    )
    return ce.apply_intervention(dense_a, spec)


def flip_curve(dense_a: np.ndarray, dense_b: np.ndarray,
               pos_a: range, pos_b: range, sig_donor: np.ndarray,
               doses: tuple[float, ...] = DOSES) -> dict[float, float]:
    """Bascule de composition vers la signature du donneur, par dose.

    ``flip(lam) = composition(fenêtre patchée(lam), sig_donneur) -
    composition(fenêtre intacte, sig_donneur)``. La cible (features) est
    l'état empirique du donneur à SA fenêtre — calculée ICI, une seule
    fois, partagée par toutes les doses.
    """
    feats = donor_features(dense_b, pos_b)
    base = composition(dense_a[pos_a, :], sig_donor)
    curve: dict[float, float] = {}
    for lam in (0.0, *doses):
        patched = patch_window(dense_a, dense_b, pos_a, pos_b, feats, lam)
        curve[lam] = composition(patched[pos_a, :], sig_donor) - base
    return curve


# --------------------------------------------------------------------------- #
# Null adversarial (objets neutres) — AVANT les bras principaux
# --------------------------------------------------------------------------- #
def neutral_null(calib_traces_by_seed: dict[int, dict],
                 *, k_features: int = K_FEATURES) -> dict:
    """Null : patch lambda=1 entre les deux objets NEUTRES de calibration.

    Même machinerie (fenêtre suffixe, état empirique du donneur, patch
    moteur) appliquée à calib_obj1 <- calib_obj2 sur les traces de
    calibration. Rend sigma_null (std ddof=1 des bascules neutres par
    graine) et l'échelle (composition intacte médiane vers la signature
    neutre du donneur), puis epsilon_flip = 0.5 × sigma × échelle -- la
    forme de la case 5 appliquée à la métrique de bascule. Ne lit QUE les
    traces de calibration (anti-HARKing structurel).
    """
    means_by_seed = {s: mean_activation_by_set(t) for s, t in calib_traces_by_seed.items()}
    sig_donor = {
        s: np.argsort(means_by_seed[s]["calib_obj2"])[::-1][:k_features]
        for s in calib_traces_by_seed
    }
    flips: list[float] = []
    scales: list[float] = []
    for seed, traces in sorted(calib_traces_by_seed.items()):
        d_s = _densify_entry(traces, "calib_obj1", 0)
        d_b = _densify_entry(traces, "calib_obj2", 0)
        pos_a, pos_b, _k = suffix_window(
            [str(t) for t in d_s["tokens"]], [str(t) for t in d_b["tokens"]])
        curve = flip_curve(d_s["dense"], d_b["dense"], pos_a, pos_b, sig_donor[seed],
                           doses=(1.0,))
        flips.append(curve[1.0])
        scales.append(composition(d_s["dense"][pos_a, :], sig_donor[seed]))
    if len(flips) < 3:
        raise ValueError(f"null invalide : {len(flips)} graines exploitables (<3)")
    sigma_null = float(np.std(flips, ddof=1))
    scale = float(np.median(scales))
    return {
        "policy": "patch lam=1 calib_obj1<-calib_obj2, fenêtre suffixe, état empirique",
        "flip_by_seed": {str(s): f for s, f in zip(sorted(calib_traces_by_seed), flips)},
        "scale_intact_median": scale,
        "sigma_null": sigma_null,
        "epsilon_flip": 0.5 * sigma_null * scale if scale > 0 else 0.0,
        "formula": "epsilon_flip = 0.5 × sigma_null × composition(intact, sig_neutre)_médian",
        "n_graines": len(flips),
    }


def calibrate_null(calib_paths: dict[int, str | Path], out_path: str | Path) -> dict:
    """Phase 1 du CLI : gèle le null AVANT les bras principaux (fichier exigé)."""
    null = neutral_null({s: load_traces(p) for s, p in calib_paths.items()})
    Path(out_path).write_text(json.dumps(null, ensure_ascii=False, indent=1),
                              encoding="utf-8", newline="\n")
    return null


# --------------------------------------------------------------------------- #
# Bras principaux + contrôles
# --------------------------------------------------------------------------- #
def _densify_entry(traces: dict, set_name: str, idx: int) -> dict:
    """Panneau dense + tokens d'une entrée (set, idx) d'une trace chargée."""
    entry = traces["prompts"][(set_name, idx)]
    d = int(traces["meta"]["d_sae"])
    dense = densify(entry["ids"], entry["vals"], np.arange(d)).astype(np.float32)
    return {"dense": dense, "tokens": [str(t) for t in entry["tokens"]]}


def _pooled_norms_freqs(*trace_dicts: dict[int, dict]) -> tuple[np.ndarray, np.ndarray]:
    """Normes L2 et fréquences d'activation poolées sur TOUS les panneaux.

    Mesure préalable (seed 0 seule) : une graine (~360 positions sur d=32768)
    n'offre AUCUNE candidate appariée à ±25 % pour certaines features. Le
    pooling des 5 graines × (main + calib) est le minimum vital du contrôle.
    Reçoit les dicts SÉPARÉMENT (pas de {**main, **calib}) : les clés de
    graine collisionnent et la fusion ferait silencieusement disparaître les
    panneaux principaux du pool.
    """
    panels = []
    for traces_by_seed in trace_dicts:
      for traces in traces_by_seed.values():
        d = int(traces["meta"]["d_sae"])
        for entry in traces["prompts"].values():
            panels.append(densify(
                entry["ids"], entry["vals"], np.arange(d)).astype(np.float32))
    stacked = np.concatenate(panels, axis=0)
    norms = np.linalg.norm(stacked, axis=0)
    freqs = np.count_nonzero(stacked, axis=0) / stacked.shape[0]
    return norms, freqs


@dataclass
class PairResult:
    """Une paire (bras, donneur) × une graine : bascules + contrôles."""

    arm: str
    donor: str
    seed: int
    context: int
    divergence: int
    window_k: int
    n_target_features: int
    flip_by_dose: dict[float, float]
    flip_random_control: float
    damage: dict[str, float]
    shas: dict[str, str] = field(default_factory=dict)


def run_main_arms(main_traces_by_seed: dict[int, dict],
                  calib_traces_by_seed: dict[int, dict],
                  *, k_features: int = K_FEATURES,
                  rel_tol: float = 0.5) -> list[PairResult]:
    """Patch des bras principaux avec contrôles, sur toutes les graines.

    Pour chaque graine, chaque paire (A, donneur B) d'``ARM_PAIRS``, chaque
    contexte : fenêtre suffixe, état empirique du donneur, courbe de dose,
    contrôle aléatoire apparié (normes poolées main+calib) à lam=1, métriques
    de dommage du moteur. Aucune agrégation ici — les verdicts par axe
    agrègent (:func:`axis_verdicts`). ``rel_tol = 0.5`` : mesuré sur le run
    réel, ±25 % ne laisse AUCUNE candidate pour les features de forte norme
    même avec les normes poolées sur 5 graines (30/30 contrôles
    indisponibles) ; le moteur exige un appariement explicite, jamais
    silencieusement dégradé.
    """
    norms, freqs = _pooled_norms_freqs(main_traces_by_seed, calib_traces_by_seed)
    results: list[PairResult] = []
    for seed, traces in sorted(main_traces_by_seed.items()):
        means = mean_activation_by_set(traces)
        sigs = {arm: np.argsort(means[arm])[::-1][:k_features] for _, arm in ARM_PAIRS}
        sigs["attn_self"] = np.argsort(means["attn_self"])[::-1][:k_features]
        for arm, donor in ARM_PAIRS:
            for ctx in range(3):
                d_a = _densify_entry(traces, arm, ctx)
                d_b = _densify_entry(traces, donor, ctx)
                div = find_divergence(d_a["tokens"], d_b["tokens"])
                pos_a, pos_b, k = suffix_window(d_a["tokens"], d_b["tokens"])
                feats = donor_features(d_b["dense"], pos_b)
                if not feats:
                    continue
                curve = flip_curve(d_a["dense"], d_b["dense"], pos_a, pos_b,
                                   sigs[donor])
                # Contrôle aléatoire apparié : MÊME opération (patch lam=1,
                # mêmes positions), features remplacées par des candidates
                # appariées en norme/fréquence poolées ; donneur = valeurs du
                # panneau B sur ces features (majoritairement nulles -- c'est
                # le point du contrôle : rupture générique vs contenu).
                base_spec = ce.InterventionSpec(
                    operation="patch", instrument="sae", layer=12,
                    positions=tuple(int(p) for p in pos_a), features=feats,
                    dose=1.0,
                    donor=tuple(tuple(float(v) for v in row) for row in
                                d_b["dense"][np.ix_(list(pos_b), list(feats))]),
                    tensor_space="sae_latent", run=f"case5_s{seed}:{arm}__{ctx}",
                    paired_run=f"case5_s{seed}:{donor}__{ctx}", seed=seed)
                rng = np.random.default_rng(seed)
                try:
                    rand_spec = ce.random_target_matched(
                        d_a["dense"], base_spec, feature_norms=norms,
                        feature_freqs=freqs, rel_tol=rel_tol, rng=rng)
                except ValueError:
                    # Candidature impossible : le contrôle est ENREGISTRÉ
                    # manquant, jamais dégradé silencieusement (le verdict
                    # en tiendra compte -- voir axis_verdicts).
                    results.append(PairResult(
                        arm=arm, donor=donor, seed=seed, context=ctx,
                        divergence=div, window_k=k, n_target_features=len(feats),
                        flip_by_dose=curve, flip_random_control=float("nan"),
                        damage={"random_control": "UNAVAILABLE"}))
                    continue
                patched_rand = ce.apply_intervention(d_a["dense"], rand_spec)
                base_comp = composition(d_a["dense"][pos_a, :], sigs[donor])
                flip_rand = (composition(patched_rand[pos_a, :], sigs[donor])
                             - base_comp)
                patched_full = patch_window(d_a["dense"], d_b["dense"], pos_a,
                                            pos_b, feats, 1.0)
                dmg = ce.damage_metrics(d_a["dense"], patched_full, base_spec)
                results.append(PairResult(
                    arm=arm, donor=donor, seed=seed, context=ctx,
                    divergence=div, window_k=k, n_target_features=len(feats),
                    flip_by_dose=curve, flip_random_control=float(flip_rand),
                    damage={k2: float(v) for k2, v in dmg.items()},
                    shas={"before": ce.artifact_sha256(d_a["dense"]),
                          "after": ce.artifact_sha256(patched_full)}))
    return results


# --------------------------------------------------------------------------- #
# Verdicts par axe (état / readout / comportement)
# --------------------------------------------------------------------------- #
def axis_verdicts(results: list[PairResult], null: dict) -> dict:
    """Agrège les paires en verdicts PAR AXE, selon la table scellée.

    état : bascule médiane (lam=1) >= epsilon_flip sur >= 4/5 graines ET
    contrôle aléatoire < epsilon_flip ET dose-réponse monotone (>= 3 paliers
    croissants sur 4) -> CONFIRMED ; bascule >= eps mais contrôle >= eps
    aussi -> INCONCLUSIF (rupture générique) ; bascule < eps -> FALSIFIED.
    readout : mêmes nombres, étiquette « readout-de-l'état » (propagation
    GPU-gated). comportement : NOT_MEASURABLE_FROZEN, jamais imputé.
    """
    eps = float(null["epsilon_flip"])
    axes: dict[str, dict] = {}
    for arm, donor in ARM_PAIRS:
        pair = [r for r in results if r.arm == arm and r.donor == donor]
        if not pair:
            continue
        # Bascule par graine = médiane sur les 3 contextes (lam=1).
        by_seed: dict[int, list[float]] = {}
        rand_by_seed: dict[int, list[float]] = {}
        mono_by_seed: dict[int, bool] = {}
        for r in pair:
            by_seed.setdefault(r.seed, []).append(r.flip_by_dose.get(1.0, float("nan")))
            rand_by_seed.setdefault(r.seed, []).append(r.flip_random_control)
            doses = sorted(d for d in r.flip_by_dose if d > 0)
            vals = [r.flip_by_dose[d] for d in doses]
            mono_by_seed[r.seed] = mono_by_seed.get(
                r.seed, True) and sum(
                    b >= a - 1e-9 for a, b in zip(vals, vals[1:])) >= len(vals) - 2
        seed_flips = {s: float(np.median(v)) for s, v in sorted(by_seed.items())}
        seed_rands = {s: float(np.nanmedian(v)) for s, v in sorted(rand_by_seed.items())}
        n_above = sum(1 for f in seed_flips.values() if f >= eps)
        _rands = [r for r in seed_rands.values() if not np.isnan(r)]
        rand_med = float(np.median(_rands)) if _rands else float("nan")
        rand_missing = any(np.isnan(v) for vs in rand_by_seed.values() for v in vs)
        n_mono = sum(1 for m in mono_by_seed.values() if m)
        key = f"{arm}<-{donor}"
        if n_above < 4:
            state_v = "FALSIFIED"
        elif rand_missing or rand_med >= eps:
            state_v = "INCONCLUSIF"
        elif n_mono < 4:
            state_v = "INCONCLUSIF"
        else:
            state_v = "CONFIRMED"
        axes[key] = {
            "etat": state_v,
            "readout": state_v,   # mêmes nombres ; propagation = GPU-gated
            "comportement": "NOT_MEASURABLE_FROZEN",
            "detail": {
                "epsilon_flip": eps,
                "flip_median_by_seed": {str(s): f for s, f in seed_flips.items()},
                "n_seeds_above_eps": n_above,
                "random_control_median": rand_med,
                "random_control_missing": rand_missing,
                "n_seeds_monotone_dose": n_mono,
            },
        }
    return axes


def _posthoc_diagnostics(main_traces_by_seed: dict[int, dict],
                         *, k_features: int = K_FEATURES) -> list[dict]:
    """Diagnostic POST-HOC, étiqueté NON scellé (jamais dans le verdict).

    Explique le verdict scellé, ne le remplace pas : (1) accord argmax par
    position entre fenêtre patchée (lam=1) et fenêtre ALIGNÉE du donneur --
    lit directement « l'état porte-t-il la fenêtre du donneur » SANS
    l'étalon signature-de-bras (top-64 par moyenne de bras) dont le run
    scellé montre qu'il résume mal l'état local de fenêtre ; (2) même accord
    pour la fenêtre intacte (base de référence).
    """
    out: list[dict] = []
    for seed, traces in sorted(main_traces_by_seed.items()):
        for arm, donor in ARM_PAIRS:
            for ctx in range(3):
                d_a = _densify_entry(traces, arm, ctx)
                d_b = _densify_entry(traces, donor, ctx)
                pos_a, pos_b, _k = suffix_window(d_a["tokens"], d_b["tokens"])
                feats = donor_features(d_b["dense"], pos_b)
                if not feats:
                    continue
                patched = patch_window(d_a["dense"], d_b["dense"], pos_a, pos_b,
                                       feats, 1.0)
                am_donor = np.argmax(d_b["dense"][pos_b, :], axis=1)
                agree_patch = float(np.mean(
                    np.argmax(patched[pos_a, :], axis=1) == am_donor))
                agree_intact = float(np.mean(
                    np.argmax(d_a["dense"][pos_a, :], axis=1) == am_donor))
                out.append({
                    "arm": arm, "donor": donor, "seed": seed, "context": ctx,
                    "argmax_agreement_with_donor_window": {
                        "patched_lam1": agree_patch, "intact_baseline": agree_intact,
                    },
                })
    return out


def supplementary_arms(main_traces_by_seed: dict[int, dict],
                         *, k_features: int = K_FEATURES) -> dict:
    """Bras SUPPLÉMENTAIRES non scellés (conformité opérations #15798).

    L'issue demande « interchange + clamp minimum ». Le run scellé utilise
    ``patch`` (écriture absolue empirique, ⊇ l'écriture du clamp) sur la
    direction A <- B ; ces bras complètent, SANS entrer dans le verdict
    scellé : (1) **interchange bilatéral décomposé** -- la direction inverse
    B <- A (les panneaux de T différents interdisent l'échange de panneaux
    entiers ; l'échange des tranches fenêtre des deux côtés = le patch
    appliqué dans les deux sens, sémantique exacte de ``interchange_panels``
    sur la cible) ; (2) **clamp paramétrique** -- écriture absolue
    ``dose x direction`` où direction = MOYENNE des valeurs de fenêtre du
    donneur (le clamp du Gate 24 : perd la spécificité de position),
    doses symétriques ±{0.5, 1.0} (``symmetric_doses`` du moteur).
    """
    reverse: list[dict] = []
    clamps: list[dict] = []
    for seed, traces in sorted(main_traces_by_seed.items()):
        means = mean_activation_by_set(traces)
        for arm, donor in ARM_PAIRS:
            for ctx in range(3):
                d_a = _densify_entry(traces, arm, ctx)
                d_b = _densify_entry(traces, donor, ctx)
                pos_a, pos_b, _k = suffix_window(d_a["tokens"], d_b["tokens"])
                feats = donor_features(d_b["dense"], pos_b)
                feats_rev = donor_features(d_a["dense"], pos_a)
                if feats and feats_rev:
                    sig_arm = np.argsort(means[arm])[::-1][:k_features]
                    curve_rev = flip_curve(d_b["dense"], d_a["dense"], pos_b,
                                           pos_a, sig_arm)
                    reverse.append({
                        "direction": f"{donor}<-{arm}", "seed": seed,
                        "context": ctx,
                        "flip_by_dose": {str(k2): v for k2, v in curve_rev.items()},
                    })
                if feats:
                    direction = d_b["dense"][np.ix_(list(pos_b), list(feats))].mean(axis=0)
                    base = composition(d_a["dense"][pos_a, :],
                                       np.argsort(means[donor])[::-1][:k_features])
                    row: dict = {"seed": seed, "context": ctx,
                                 "n_features": len(feats), "flip_by_dose": {}}
                    for dose in ce.symmetric_doses(1.0, 2):
                        spec = ce.InterventionSpec(
                            operation="clamp", instrument="sae", layer=12,
                            positions=tuple(int(p) for p in pos_a), features=feats,
                            dose=float(dose),
                            direction=tuple(float(v) for v in direction),
                            tensor_space="sae_latent",
                            run=f"case5_s{seed}:{arm}__{ctx}",
                            seed=seed)
                        clamped = ce.apply_intervention(d_a["dense"], spec)
                        row["flip_by_dose"][f"{dose:+.1f}"] = composition(
                            clamped[pos_a, :],
                            np.argsort(means[donor])[::-1][:k_features]) - base
                    clamps.append(row)
    return {"interchange_reverse_direction": reverse, "clamp_parametric": clamps}


def run_analysis(null: dict, main_traces_by_seed: dict[int, dict],
                 calib_traces_by_seed: dict[int, dict]) -> dict:
    """Assemble le scoreboard case 5bis sérialisable (ict/results/)."""
    results = run_main_arms(main_traces_by_seed, calib_traces_by_seed)
    axes = axis_verdicts(results, null)
    posthoc = _posthoc_diagnostics(main_traces_by_seed)
    supplementary = supplementary_arms(main_traces_by_seed)
    return {
        "case": "case5bis_attention_schema_causal",
        "question": ("l'état workspace attentionnel est-il inscriptible de façon "
                     "SPÉCIFIQUE AU CONTENU (moteur #15479, traces gelées case 5) ?"),
        "protocol": {
            "window": "suffixe aligné à la divergence (clause cible)",
            "target": "état empirique du donneur à sa fenêtre (union des top-k actifs)",
            "operation": "patch moteur, dose par pré-interpolation du donneur",
            "doses": list(DOSES),
            "controls": ["sham (lam=0, identité même voie)",
                         "cible aléatoire appariée norme+fréquence poolées 5 graines",
                         "bras intact"],
            "continuity_case5": ("epsilon_flip = 0.5 × sigma_null × scale, forme "
                                 "exacte de ε_attn case 5 (calibration gelée "
                                 "attention_schema_results.json)"),
        },
        "null": null,
        "pairs": [
            {
                "arm": r.arm, "donor": r.donor, "seed": r.seed, "context": r.context,
                "divergence": r.divergence, "window_k": r.window_k,
                "n_target_features": r.n_target_features,
                "flip_by_dose": {str(k2): v for k2, v in r.flip_by_dose.items()},
                "flip_random_control": (None if np.isnan(r.flip_random_control)
                                        else r.flip_random_control),
                "damage": r.damage, "shas": r.shas,
            }
            for r in results
        ],
        "axes": axes,
        "diagnostic_posthoc_non_scelle": posthoc,
        "bras_supplementaires_non_scelles": supplementary,
        "limits": [
            "traces gelées : aucune position aval ne se recalcule -- la métrique "
            "mesure la composition READOUT-ELIGIBLE de l'état, pas sa propagation",
            "comportement verbal : forward-pass GPU avec état réinjecté = suivi "
            "hors scope, jamais imputé",
        ],
    }


def _cli(argv: list[str] | None = None) -> None:
    """Runner CLI : ``calibrate`` DOIT précéder ``run`` (fichier exigé).

    Même garde anti-HARKing que la case 5 : le null neutre est gelé dans un
    JSON AVANT que les bras principaux ne soient touchés ; ``run`` refuse de
    tourner sans ce fichier.
    """
    import argparse

    from .sae_traces import load_traces as lt

    ap = argparse.ArgumentParser(description="Case 5bis (#15798) — causal AST")
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("calibrate", help="phase 1 : null neutre gelé avant les bras")
    c.add_argument("--calib", nargs=5, required=True, help=".npz calib des 5 graines")
    c.add_argument("--out", required=True)
    r = sub.add_parser("run", help="phase 2 : bras principaux + verdicts par axe")
    r.add_argument("--main", nargs=5, required=True, help=".npz case5 des 5 graines")
    r.add_argument("--calib", nargs=5, required=True)
    r.add_argument("--null", required=True, help="JSON produit par 'calibrate'")
    r.add_argument("--out", required=True, help="JSON résultat (ict/results/)")
    args = ap.parse_args(argv)

    seeds = SEEDS
    if args.cmd == "calibrate":
        null = calibrate_null(dict(zip(seeds, args.calib)), args.out)
        print(f"[calibrate] sigma_null={null['sigma_null']:.6f} "
              f"eps_flip={null['epsilon_flip']:.6f} -> {args.out}")
        return
    null = json.loads(Path(args.null).read_text(encoding="utf-8"))
    result = run_analysis(null, {s: lt(p) for s, p in zip(seeds, args.main)},
                           {s: lt(p) for s, p in zip(seeds, args.calib)})
    Path(args.out).write_text(json.dumps(result, ensure_ascii=False, indent=1),
                              encoding="utf-8", newline="\n")
    for key, axe in result["axes"].items():
        print(f"[run] {key}: etat={axe['etat']} readout={axe['readout']} "
              f"comportement={axe['comportement']}")
    print(f"[run] -> {args.out}")


if __name__ == "__main__":
    _cli()
