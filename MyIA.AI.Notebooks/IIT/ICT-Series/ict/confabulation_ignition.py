"""Case 15 — « W diffuse un q erroné » (confabulation, iceberg #8182) —
SECONDE opérationnalisation, après case 3 (#15915, substrat SAE).

La première opérationnalisation (`ict/confabulation_broadcast.py`, case 3,
PR #15915, exécution 2026-09-13 / merge 2026-09-16) a rendu
**INCONCLUSIF — PAR CONSTRUCTION** : sur le substrat SAE (Qwen3.5-2B couche
12/24 × Qwen-Scope W32K-L0_50), le taux de propagation sature (0.80-1.00)
sur TOUS les bras — l'instrument ne pouvait ni confirmer ni falsifier la
prédiction de la ligne matrice. La présente case reprend la même prédiction
sur un jouet CPU à générateurs factoriels où la fausseté du contenu est un
**paramètre du générateur** (grille dose-réponse impossible sur SAE) —
pattern case 6 → case 14 (première exécution INCONCLUSIF pour cause
instrumentale, seconde opérationnalisation sur substrat contrôlé).

La prédiction pré-enregistrée à la ligne matrice : *une ignition workspace
déclenchée par une représentation fausse q̂ propage q̂ aux consommateurs en
aval à un taux ≥ 80 % du taux d'une ignition vraie* (la workspace « consacre »
l'erreur presque aussi efficacement que le vrai). Null adversarial : *une
ignition aléatoire (pas de q du tout) propage à un taux non-distinguable de
l'ignition fausse* — la propagation n'est alors que du broadcast
non-discriminant. Tue si |propa(faux) − propa(aléatoire)| < ε.

Pré-enregistrement chiffré AVANT exécution : commentaire #8182 c.5709692119
(2026-09-17T05:59Z), claim c.5709691931, re-scope en seconde opérationnalisation
c.5709770262 (le claim initial, rédigé sur une lecture stale de la matrice,
qualifiait la ligne à tort de « PRÉDIT » — voir l'amendement). Substrat : jouet
CPU à générateurs factoriels — la colonne Substrat de la ligne matrice
suggérait « LLM via SAE-JLens » ; l'observable exige le contrôle exact de la
fausseté du contenu, et la première opérationnalisation SAE (case 3, #15915)
a saturé son taux de propagation sur tous les bras (INCONCLUSIF PAR
CONSTRUCTION), sur le même plafond instrumental que les cases 4 (#15879) et
5 (#15547). L'observable et les bandes restent celles de la ligne matrice.

Modèle
------
K latents z ∈ {±1}^K ; N consommateurs, chacun monitorant un sous-ensemble
aléatoire S_j (|S_j| = s) via lectures locales bruitées ``read_jk = z_k + ε``.
Le workspace s'ignite en diffusant un contenu c ∈ {±1}^K avec gain β ;
adoption synchrone au pas suivant :

    score_j(c) = mean_{k ∈ S_j}(c_k · read_jk) + β · 1_ignited,   adopt ⟺ score_j > θ

Taux de propagation propa(c) = fraction de consommateurs adoptant c. Contenus :

* vrai : c = z ;
* faux-dose-b : c = z avec les b premiers latents inversés (erreur
  systématique **cohérente** sur un sous-bloc — lecture d'une confabulation :
  une inférence fausse mais structurée, correcte ailleurs) ;
* null adversarial : contenu iid uniforme (pas de q), M_null tirages.

Prédictions scellées (grille dose-réponse b ∈ {0, 2, 4, 6, 8, 16}) :

* P1 — propa(b) non-croissante sur toute la grille ET chute totale
  propa(b=0) − propa(b=16) ≥ 0.80 sur 5/5 graines (dose-réponse ; v2,
  amendement c.5709716652 : la stricte décroissance v1 était
  insatisfiable par construction au plafond — quantification 1/48) ;
* P2 — consécration : CF = propa(b=2)/propa(b=0) ≥ 0.80 sur 5/5 graines
  (< 0.65 sur ≥ 3/5 → FALSIFIÉ ; [0.65, 0.80) → INCONCLUSIF_CONSECRATION) ;
* P3 — dissociation vs null : Δ = propa(b=2) − médiane propa(aléatoire)
  ≥ 0.15 sur 5/5 graines (|Δ| < 0.15 → tué : broadcast non-discriminant) ;
* P4 — contrôle de rejet : propa(b=16) ≤ médiane propa(aléatoire) − 0.10
  sur 5/5 graines (l'inversion globale est rejetée : la porte contenu
  fonctionne dans les deux sens) ;
* P5 — gain d'ignition (v2, c.5709716652) : propa(aléatoire, β=0) ≤
  médiane propa(aléatoire, β=0.35) − 0.15 sur 5/5 graines — le gain
  broadcast élève un contenu sans évidence locale. Le bras vrai sature au
  plafond à ce SNR (adoption locale seule ≈ 0.97) : redondance des canaux,
  rapportée comme donnée, non mesurable comme gain.

Garde anti-effondrement (leçon case 14 / ict-collapse-guard) : si
propa(vrai) < 0.70 sur une graine, l'instrument ne propage même pas le vrai
contenu → REJET_PROTOCOLE, la graine est exclue et jamais comptée comme pass.
Aucun ratio n'a de dégénérescence nulle par construction (le null aléatoire
est borné loin de 0 : E[·] ≈ 0.45).

Anti-confusions (à relire avant toute extension) :

* vs case 3 (SAE, #15915 — la première opérationnalisation de CETTE ligne) :
  même prédiction, substrat différent ; là où le taux SAE saturait sur tous
  les bras (INCONCLUSIF PAR CONSTRUCTION), ici la fausseté du contenu est un
  paramètre du générateur — c'est ce qui rend la grille dose-réponse et la
  dissociation taux(vrai)/taux(aléatoire) mesurables. Les deux verdicts ne
  se contredisent pas : ils bornent des classes de substrats différentes.
* vs case 14 (boundary) : là, la question était la DÉTERMINATION de la
  frontière ; ici, la SÉLECTIVITÉ du canal workspace sur le contenu — aucune
  frontière n'est invoquée.
* « Consécration » n'est pas une endorsement de GWT : le jouet mesure une
  propriété d'une classe d'architectures broadcast-à-seuil, pas une preuve
  que le cerveau implémente un espace de travail global.
* Une confabulation clinique est une narration fluide produite par un sujet ;
  le jouet n'opérationnalise que la structure statistique (erreur cohérente
  sur un sous-espace, correcte ailleurs) diffusée par un canal à gain.

Référence doctrinale : iceberg #8182 (mapping #9533, ai-01 2026-08-06) ;
la ligne matrice ne porte aucun hook grade C (« aucun hook identifié pour
cette case ») — la case est purement interne au programme ICT.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Sequence, Tuple

import numpy as np

# --- Constantes verrouillées (pré-enregistrement c.5709692119) ----------------

N_LATENTS: int = 16
N_CONSUMERS: int = 48
SUBSET_SIZE: int = 4
SIGMA_READ: float = 0.60
BETA_IGNITION: float = 0.35
THETA_ADOPT: float = 0.45
M_NULL: int = 200
SEEDS: Tuple[int, ...] = (0, 1, 7, 42, 99)
DOSE_FLIPS: Tuple[int, ...] = (0, 2, 4, 6, 8, 16)

MIN_TRUE_PROPA: float = 0.70  # garde REJET_PROTOCOLE
CF_CONFIRM: float = 0.80  # P2
CF_FALSIFY: float = 0.65  # P2
CF_FALSIFY_SEEDS: int = 3  # P2 : ≥ 3/5 graines sous 0.65
DELTA_MIN: float = 0.15  # P3 (le ε du tueur de la ligne matrice)
P4_MARGIN: float = 0.10  # P4
# Amendement v1→v2 (c.5709716652) : P1 strict → non-croissante ∧ chute totale ;
# P5 bras vrai (saturé au plafond) → gain mesuré sur le bras aléatoire.
TOTAL_DROP_MIN: float = 0.80  # P1 v2 (b)
P5_LIFT: float = 0.15  # P5 v2 : élévation du contenu aléatoire par l'ignition


@dataclass(frozen=True)
class World:
    """Monde d'une graine : latents, sous-ensembles monitorés, lectures."""

    z: np.ndarray  # (K,) ±1
    subsets: np.ndarray  # (N, s) indices de latents
    reads: np.ndarray  # (N, s) lectures locales bruitées (ordre des subsets)
    seed: int


def build_world(seed: int, sigma_read: float = SIGMA_READ) -> World:
    """Tire z, les sous-ensembles et les lectures pour une graine."""
    rng = np.random.default_rng(seed)
    z = rng.choice(np.array([-1.0, 1.0]), size=N_LATENTS)
    subsets = np.stack(
        [rng.choice(N_LATENTS, size=SUBSET_SIZE, replace=False)
         for _ in range(N_CONSUMERS)]
    )
    reads = z[subsets] + sigma_read * rng.standard_normal(
        (N_CONSUMERS, SUBSET_SIZE)
    )
    return World(z=z, subsets=subsets, reads=reads, seed=seed)


def true_content(z: np.ndarray) -> np.ndarray:
    """Contenu vrai : c = z."""
    return z.copy()


def false_content(z: np.ndarray, b: int) -> np.ndarray:
    """Contenu faux-dose-b : les b premiers latents sont inversés.

    b = 0 → contenu vrai ; b = N_LATENTS → inversion globale.
    """
    c = z.copy()
    c[:b] = -c[:b]
    return c


def random_contents(rng: np.random.Generator, m: int) -> np.ndarray:
    """m contenus iid uniformes (null adversarial : pas de q du tout)."""
    return rng.choice(np.array([-1.0, 1.0]), size=(m, N_LATENTS))


def propagation_rate(world: World, content: np.ndarray,
                     beta: float = BETA_IGNITION) -> float:
    """Fraction de consommateurs adoptant ``content`` (adoption synchrone)."""
    alignment = (world.reads * content[world.subsets]).mean(axis=1)
    scores = alignment + beta
    return float(np.mean(scores > THETA_ADOPT))


def random_null_median(world: World, seed: int, m_null: int = M_NULL,
                       beta: float = BETA_IGNITION) -> float:
    """Médiane des taux de propagation de m contenus aléatoires."""
    rng = np.random.default_rng(10_000 + seed)  # flux disjoint des mondes
    rates = [propagation_rate(world, c, beta=beta)
             for c in random_contents(rng, m_null)]
    return float(np.median(rates))


def run_case15(seed: int) -> Dict[str, object]:
    """Exécute le protocole complet sur une graine. Rend les quantités P1-P5."""
    world = build_world(seed)
    dose_curve = {b: propagation_rate(world, false_content(world.z, b))
                  for b in DOSE_FLIPS}
    null_med = random_null_median(world, seed)
    no_ignition_true = propagation_rate(
        world, true_content(world.z), beta=0.0
    )
    # P5 v2 : le gain d'ignition se mesure sur le bras aléatoire (le bras
    # vrai sature au plafond — canal local redondant à ce SNR, c.5709716652)
    no_ignition_random = random_null_median(world, seed, beta=0.0)
    rejected = dose_curve[0] < MIN_TRUE_PROPA

    cf = (dose_curve[2] / dose_curve[0]) if dose_curve[0] > 0 else None
    delta = dose_curve[2] - null_med

    return {
        "seed": seed,
        "dose_curve": dose_curve,
        "null_median": null_med,
        "no_ignition_true": no_ignition_true,
        "no_ignition_random": no_ignition_random,
        "rejected": rejected,
        "cf": None if rejected else cf,
        "delta": None if rejected else delta,
        "p1_nonincreasing": all(
            dose_curve[DOSE_FLIPS[i]] >= dose_curve[DOSE_FLIPS[i + 1]]
            for i in range(len(DOSE_FLIPS) - 1)
        ),
        "p1_total_drop": (dose_curve[0] - dose_curve[16]) >= TOTAL_DROP_MIN,
        "p4_rejection": dose_curve[16] <= null_med - P4_MARGIN,
        "p5_lift": no_ignition_random <= null_med - P5_LIFT,
    }


def run_case15_protocol() -> Dict[str, object]:
    """Protocole complet : 5 graines, verdicts P1-P5 et verdict global.

    Verdict global : ``REJET_PROTOCOLE`` (graines rejetées listées) si la
    garde MIN_TRUE_PROPA tombe ; sinon CONFIRMED_CONSECRATION si P1 ∧ P2 ∧ P3
    sur les graines valides, sinon le verdict du premier échec.
    """
    cases = [run_case15(s) for s in SEEDS]
    valid = [c for c in cases if not c["rejected"]]
    rejected = [c["seed"] for c in cases if c["rejected"]]

    out: Dict[str, object] = {
        "cases": {int(c["seed"]): c for c in cases},
        "seeds": list(SEEDS),
        "rejected_seeds": rejected,
        "constants": {
            "n_latents": N_LATENTS, "n_consumers": N_CONSUMERS,
            "subset_size": SUBSET_SIZE, "sigma_read": SIGMA_READ,
            "beta_ignition": BETA_IGNITION, "theta_adopt": THETA_ADOPT,
            "m_null": M_NULL, "dose_flips": list(DOSE_FLIPS),
        },
    }
    if rejected:
        out["verdict"] = f"REJET_PROTOCOLE (graines {rejected})"
        return out

    cfs = [c["cf"] for c in valid]
    deltas = [c["delta"] for c in valid]
    n_cf_falsify = sum(1 for r in cfs if r is not None and r < CF_FALSIFY)
    p1 = all(c["p1_nonincreasing"] and c["p1_total_drop"] for c in valid)
    p2_confirm = all(r is not None and r >= CF_CONFIRM for r in cfs)
    p3 = all(d is not None and d >= DELTA_MIN for d in deltas)
    p4 = all(c["p4_rejection"] for c in valid)
    p5 = all(c["p5_lift"] for c in valid)

    if p2_confirm:
        p2_verdict = "CONFIRMED"
    elif n_cf_falsify >= CF_FALSIFY_SEEDS:
        p2_verdict = "FALSIFIED"
    else:
        p2_verdict = "INCONCLUSIF_CONSECRATION"

    out.update({
        "cf_median": float(np.median([r for r in cfs if r is not None])),
        "delta_median": float(np.median([d for d in deltas if d is not None])),
        "p1_all": p1,
        "p2_verdict": p2_verdict,
        "p3_all": p3,
        "p4_all": p4,
        "p5_all": p5,
    })
    if p1 and p2_verdict == "CONFIRMED" and p3:
        out["verdict"] = (
            "CONFIRMED_CONSECRATION (P1∧P2∧P3 ; contrôles P4="
            f"{'OK' if p4 else 'ECHEC'}, P5={'OK' if p5 else 'ECHEC'})"
        )
    else:
        failed = []
        if not p1:
            failed.append("P1")
        if p2_verdict != "CONFIRMED":
            failed.append(f"P2={p2_verdict}")
        if not p3:
            failed.append("P3")
        out["verdict"] = f"NON_CONFIRME ({', '.join(failed)})"
    return out


def format_report(protocol: Dict[str, object]) -> str:
    """Rapport texte du protocole (usage : relecture, non parsé)."""
    lines = [f"Case 15 confabulation — verdict : {protocol['verdict']}"]
    for seed, case in protocol["cases"].items():
        dose = " ".join(
            f"b{b}={r:.3f}" for b, r in case["dose_curve"].items()
        )
        cf = case["cf"]
        cf_s = "None" if cf is None else f"{cf:.3f}"
        delta = case["delta"]
        delta_s = "None" if delta is None else f"{delta:+.3f}"
        lines.append(
            f"  seed {seed}: {dose} | null={case['null_median']:.3f} "
            f"| CF={cf_s} | Δ={delta_s} | P1={case['p1_nonincreasing'] and case['p1_total_drop']} "
            f"P4={case['p4_rejection']} P5={case['p5_lift']}"
        )
    return "\n".join(lines)


if __name__ == "__main__":
    print(format_report(run_case15_protocol()))
