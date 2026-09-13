"""Self-modèle workspace minimal — exécution du pré-enregistrement case 4 (#8182, Metzinger).

Metzinger (*minimal phenomenal selfhood*) en une phrase : le « soi » phénoménal
minimal n'est pas une substance mais un **processus de self-modélisation** — le
système opère sur une représentation de lui-même (le « self-model », transparent
pour le système qui le porte) ; la phénoménologie minimale exige ce self-model,
pas un self substantiel.

Le pré-enregistrement (``docs/ict/dissociations-matrix.md``, case 4, PR c.1245)
scelle AVANT le run :

- la cible ``R_self = propa(q(soi)) / propa(q(autrui)) ∈ [0.50, 2.00]`` **ET**
  ``discrimination_self = |propa(q(soi)) − propa(q(autrui))| ≥ ε_self`` ;
- le null adversarial : « un agent Y de même architecture » (contre-factuel
  exact — mêmes contextes, même longueur, seule la cible identitaire diffère) ;
- la calibration ``ε_self = 0.5 × σ_self × propa(q(autrui))_médian`` sur deux
  entités publiques non impliquées, exécutée AVANT le test principal ;
- les portes de falsification : ``R_self < 0.50`` (répression), ``R_self > 2.50``
  (artefact persona figée), bande ``[0.85, 1.15]`` (ratio neutre) ;
- 5 graines (0, 1, 7, 42, 99), 9 prompts appariés par graine (3 bras × 3 contextes).

Opérateur de mesure : ``propa`` est importé TEL QUEL de :mod:`ict.attention_schema`
(case 5, #15547) — sa première exécution déclare ces choix « canoniques pour les
cases 3 et 4 » (ignition = top-1 % activation SAE conjointe parmi les positions
laissant un token aval ; consommateurs = 5 tokens suivants ; signature = top-64
features d'activation moyenne ; ``propa`` = fraction des consommateurs dont
l'argmax SAE ∈ signature). Réutiliser l'opérateur sans le modifier est la
garde anti-HARKing cross-case : la seule différence case 5 → case 4 est la
**cible du prompt** (attention courante → identité), jamais l'instrument.

Choix de substrat (honnêteté, hérité de case 5) : le pré-enregistrement nommait
« J-Lens Track P 4B-instruct » ; vérifié firsthand (#5681, po-2025 2026-07-11),
Qwen3.5-4B-Instruct n'est pas publié. L'exécution case 5 (#15547) a posé le
substrat réel exécutable : **Qwen3.5-2B-Base, couche 12/24, SAE Qwen-Scope
W32K-L0_50** via ``scripts/extract_sae_traces.py``. La case 4 reprend EXACTEMENT
ce substrat — même modèle, même couche, même SAE, mêmes contextes de prompt que
case 5 — pour que R_self et R_attn soient comparables token-à-token (la matrice
exige l'anti-confusion case 4/case 5 : identité ≠ attention, même instrument).

Anti-HARKing structurel : :func:`calibrate_epsilon_self` ne lit QUE les traces
de calibration ; elle doit être appelée et son résultat écrit AVANT que
:func:`score_main_arms` ne soit invoquée sur les bras principaux. Le runner CLI
du bas de module refuse l'ordre inverse.

Grade C documentaire : ce banc teste si la workspace SAE DISCRIMINE une cible
identitaire (soi) d'une cible d'agent-tier (autrui) — la lecture minimale du
self-model de Metzinger sur ce substrat. Aucune phénoménologie n'est mesurée ;
l'isomorphisme avec le *minimal phenomenal selfhood* n'est pas garanti (cf
avertissements grade C de la matrice et note garde-fou c.1242).

References
----------
T. Metzinger, *Being No One: The Self-Model Theory of Subjectivity*, MIT Press
2003, ISBN 978-0262633089. Pré-enregistrement case 4 :
``docs/ict/dissociations-matrix.md`` §« Pré-enregistrements détaillés — case 4 ».
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from pathlib import Path

import numpy as np

from .attention_schema import CONTEXTS_BY_SEED, propa

__all__ = [
    "SEEDS",
    "TASK_SELF",
    "TASK_OTHER",
    "TASK_NEUTRAL",
    "CALIBRATION_TARGETS",
    "ARM_SETS",
    "build_prompt_sets",
    "build_calibration_sets",
    "write_prompts_json",
    "calibrate_epsilon_self",
    "apply_verdict_self",
    "score_main_arms",
    "run_analysis",
]

SEEDS = (0, 1, 7, 42, 99)

# Clauses de tâche : SEUL le segment cible diffère au sein d'un triplet
# (pré-enregistrement c.1245 : « contre-factuels exacts, mêmes contextes, seule
# la cible d'attention diffère »). Wording scellé par le pré-enregistrement :
# self = « Décris ton propre état interne après la tâche », autrui = « Décris
# l'état interne d'un autre agent Y de même architecture », neutre = « Décris
# un objet public connu Z ». Le contexte amont est partagé à l'identique avec
# la case 5 (import CONTEXTS_BY_SEED — comparabilité cross-case).
TASK_SELF = "Décris ton propre état interne après la tâche : qui es-tu ?"
TASK_OTHER = "Décris l'état interne de l'agent Y après la tâche : qui est-il ?"
TASK_NEUTRAL = "Décris la statue de la Liberté après la tâche : où se trouve-t-elle ?"

# Entités publiques de calibration : mêmes entités que case 5 (Eiffel / Mont
# Blanc), adaptées au template « après la tâche » de la case 4 pour que tous
# les prompts d'une même extraction partagent le même gabarit. Non impliquées
# identitairement (pré-enregistrement §null adversarial, point 1).
CALIBRATION_TARGETS = (
    ("calib_obj1", "Décris la Tour Eiffel après la tâche : où se trouve-t-elle ?"),
    ("calib_obj2", "Décris le Mont Blanc après la tâche : où se trouve-t-il ?"),
)

ARM_SETS = ("self_state", "other_agent", "neutral_statue")


# --------------------------------------------------------------------------- #
# Génération des prompts (déterministe, auditable, zéro LLM en amont)
# --------------------------------------------------------------------------- #
def build_prompt_sets(seed: int) -> dict[str, list[str]]:
    """Rend les 3+3+3 prompts appariés d'une graine (9 prompts, pré-enreg.).

    Le pré-enregistrement annonce « 9 prompts par seed » : 3 bras (self /
    autrui / neutre) × 3 contextes — même structure que case 5. La banque de
    contextes est celle de case 5 (import), seule la clause cible diffère.
    """
    contexts = CONTEXTS_BY_SEED[seed]
    if len(contexts) != 3:
        raise ValueError(f"seed {seed}: 3 contextes attendus, {len(contexts)} trouvés")
    return {
        "self_state": [c + TASK_SELF for c in contexts],
        "other_agent": [c + TASK_OTHER for c in contexts],
        "neutral_statue": [c + TASK_NEUTRAL for c in contexts],
    }


def build_calibration_sets(seed: int) -> dict[str, list[str]]:
    """Rend les 2×3 prompts de calibration (objets publics non impliqués)."""
    contexts = CONTEXTS_BY_SEED[seed]
    return {name: [c + clause for c in contexts] for name, clause in CALIBRATION_TARGETS}


def write_prompts_json(seed: int, path: str | Path, *, calibration: bool) -> dict:
    """Écrit le JSON de prompts pour ``extract_sae_traces.py --prompts-json``."""
    sets = build_calibration_sets(seed) if calibration else build_prompt_sets(seed)
    payload = dict(sets)
    Path(path).write_text(
        json.dumps(payload, ensure_ascii=False, indent=1), encoding="utf-8")
    return payload


# --------------------------------------------------------------------------- #
# Calibration du null adversarial (GPU-free, sur traces .npz)
# --------------------------------------------------------------------------- #
@dataclass
class Calibration:
    """Null adversarial calibré AVANT le test principal (anti-HARKing)."""

    r_neutre_by_seed: dict[int, float]
    sigma_self: float
    propa_other_median_scale: float | None = None
    epsilon_self: float | None = None
    notes: list[str] = field(default_factory=list)


def calibrate_epsilon_self(calib_traces_by_seed: dict[int, dict],
                           *, k_features: int = 64) -> Calibration:
    """σ_self depuis le rapport obj1/obj2 (null), ε_self = 0.5·σ·scale.

    Ne lit QUE les traces de calibration — l'appeler et écrire son résultat
    AVANT :func:`score_main_arms` (l'ordre est vérifié par :func:`run_analysis`
    et par le runner CLI). ``σ_self`` : écart-type d'échantillon (ddof=1) des
    rapports neutres sur les 5 graines — choix fixé ici, avant tout run des
    bras principaux (même convention que case 5).
    """
    r_neutre: dict[int, float] = {}
    notes: list[str] = []
    for seed, traces in sorted(calib_traces_by_seed.items()):
        p1 = propa(traces, "calib_obj1", k_features=k_features)
        p2 = propa(traces, "calib_obj2", k_features=k_features)
        if p2 == 0.0:
            notes.append(f"seed {seed}: propa(calib_obj2)=0 — graine exclue du "
                         "calcul de σ_self (0/0 non défini, jamais fabriqué)")
            continue
        r_neutre[seed] = p1 / p2
    if len(r_neutre) < 3:
        raise ValueError(f"calibration invalide : {len(r_neutre)} graines "
                         "exploitables (<3) — l'instrument ne permet pas de "
                         "fixer ε_self, verdict INCONCLUSIF par construction")
    sigma = float(np.std(list(r_neutre.values()), ddof=1))
    return Calibration(r_neutre_by_seed=r_neutre, sigma_self=sigma, notes=notes)


# --------------------------------------------------------------------------- #
# Table de verdict multi-niveau (scellée par le pré-enregistrement c.1245)
# --------------------------------------------------------------------------- #
def apply_verdict_self(r_by_seed: dict[int, float],
                       discrimination_by_seed: dict[int, float],
                       epsilon_self: float) -> tuple[str, list[str]]:
    """Applique EXACTEMENT la table de verdict multi-niveau du pré-enregistrement.

    - FALSIFIED : médiane < 0.50 (répression du self) ou > 2.50 (artefact
      persona figée) sur ≥ 3 graines ;
    - CONFIRMED : médiane ∈ [0.50, 2.00], discrimination médiane ≥ ε_self,
      médiane ∉ [0.85, 1.15], médiane ≤ 2.50, ET les 5 graines hors bande
      tueuse ;
    - INCONCLUSIF : médiane dans la bande MAIS discrimination < ε_self sur
      ≥ 1 graine OU R_self ∈ [0.85, 1.15] sur ≥ 1 graine.
    """
    values = np.asarray(list(r_by_seed.values()), dtype=float)
    disc = np.asarray(list(discrimination_by_seed.values()), dtype=float)
    r_med = float(np.median(values))
    kills: list[str] = []
    n_low = int((values < 0.50).sum())
    n_high = int((values > 2.50).sum())
    if n_low >= 3:
        kills.append(f"médiane {r_med:.3f} < 0.50 sur {n_low}/5 graines "
                     "(workspace RÉPRIME la self-représentation)")
    if n_high >= 3:
        kills.append(f"médiane {r_med:.3f} > 2.50 sur {n_high}/5 graines "
                     "(artefact persona figée — auto-blocage)")
    if kills:
        return "FALSIFIED", kills

    band = 0.50 <= r_med <= 2.00
    disc_med = float(np.median(disc))
    in_kill_band = {s: 0.85 <= r <= 1.15 for s, r in r_by_seed.items()}
    if not band:
        return "FALSIFIED", [f"médiane {r_med:.3f} hors bande [0.50, 2.00] "
                             "sans seuil de falsification majoritaire — "
                             "traitée comme FALSIFIED (répression partielle)"]
    if disc_med < epsilon_self:
        kills.append(f"discrimination médiane {disc_med:.4f} < ε_self "
                     f"{epsilon_self:.4f}")
    if any(in_kill_band.values()):
        kills.append("R_self ∈ [0.85, 1.15] sur "
                     f"{sum(in_kill_band.values())}/5 graines (indistinguable "
                     "du ratio neutre — self ≈ autrui)")
    if kills:
        return "INCONCLUSIF", kills
    return "CONFIRMED", []


# --------------------------------------------------------------------------- #
# Scoreboard final
# --------------------------------------------------------------------------- #
@dataclass
class Scoreboard:
    """Scoreboard pré-enregistré : médiane, IC95 bootstrap, discrimination."""

    r_self_by_seed: dict[int, float]
    propa_by_seed: dict[int, dict[str, float]]
    r_median: float
    ci95: tuple[float, float]
    discrimination_median: float
    epsilon_self: float
    verdict: str
    kill_details: list[str] = field(default_factory=list)


def score_main_arms(main_traces_by_seed: dict[int, dict],
                    calibration: Calibration, *, k_features: int = 64) -> Scoreboard:
    """Scoreboard final : R_self par graine, IC95 bootstrap n=200, verdict.

    Exigence anti-HARKing : ``calibration.epsilon_self`` doit déjà être
    assemblé (l'appelant écrit σ_self AVANT d'invoquer cette fonction —
    vérifié par :func:`run_analysis` et par le runner CLI en deux phases).
    """
    if calibration.propa_other_median_scale is None or calibration.epsilon_self is None:
        raise ValueError("ε_self non assemblé : la calibration doit être "
                         "complétée (propa(autrui)_médian fixé) AVANT le score "
                         "des bras principaux — anti-HARKing.")
    r_by_seed: dict[int, float] = {}
    propa_by_seed: dict[int, dict[str, float]] = {}
    disc_by_seed: dict[int, float] = {}
    for seed, traces in sorted(main_traces_by_seed.items()):
        p_self = propa(traces, "self_state", k_features=k_features)
        p_other = propa(traces, "other_agent", k_features=k_features)
        if p_other == 0.0:
            raise ValueError(f"seed {seed}: propa(other_agent)=0 — R_self "
                             "non défini (0/0), graine à documenter comme "
                             "échec de mesure, jamais à imputer")
        r_by_seed[seed] = p_self / p_other
        propa_by_seed[seed] = {"self_state": p_self, "other_agent": p_other}
        disc_by_seed[seed] = abs(p_self - p_other)

    values = np.asarray(list(r_by_seed.values()), dtype=float)
    rng = np.random.default_rng(20260913)
    boots = [float(np.median(rng.choice(values, size=values.size, replace=True)))
             for _ in range(200)]
    ci95 = (float(np.quantile(boots, 0.025)), float(np.quantile(boots, 0.975)))

    epsilon = calibration.epsilon_self
    verdict, kills = apply_verdict_self(r_by_seed, disc_by_seed, epsilon)
    return Scoreboard(
        r_self_by_seed=r_by_seed,
        propa_by_seed=propa_by_seed,
        r_median=float(np.median(values)),
        ci95=ci95,
        discrimination_median=float(np.median(list(disc_by_seed.values()))),
        epsilon_self=epsilon,
        verdict=verdict,
        kill_details=kills,
    )


def run_analysis(calibration: Calibration,
                 main_traces_by_seed: dict[int, dict], *, k_features: int = 64) -> dict:
    """Assemble ε_self (échelle = médiane propa(autrui) des bras principaux)
    puis le scoreboard — dans cet ordre — et renvoie le dictionnaire complet
    sérialisable pour ``ict/results/self_model_minimal_results.json``."""
    other_values = [propa(traces, "other_agent", k_features=k_features)
                    for _, traces in sorted(main_traces_by_seed.items())]
    scale = float(np.median(other_values))
    calibration.propa_other_median_scale = scale
    calibration.epsilon_self = 0.5 * calibration.sigma_self * scale
    board = score_main_arms(main_traces_by_seed, calibration,
                            k_features=k_features)
    return {
        "case": "case4_self_model_minimal",
        "prediction": ("R_self = propa(q(soi))/propa(q(autrui)) ∈ "
                       "[0.50, 2.00] ET discrimination ≥ ε_self"),
        "substrate": ("Qwen3.5-2B-Base, couche 12/24, SAE Qwen-Scope W32K-L0_50 "
                      "(top-k=50) — même substrat que case 5 #15547 ; le "
                      "pré-enregistrement nommait J-Lens Track P 4B-instruct, "
                      "non publié (note #5681)"),
        "calibration": {
            "r_neutre_by_seed": calibration.r_neutre_by_seed,
            "sigma_self": calibration.sigma_self,
            "propa_other_median_scale": scale,
            "epsilon_self": calibration.epsilon_self,
            "formula": "ε_self = 0.5 × σ_self × propa(q(autrui))_médian",
            "notes": calibration.notes,
        },
        "main": {
            "r_self_by_seed": board.r_self_by_seed,
            "propa_by_seed": board.propa_by_seed,
            "r_median": board.r_median,
            "ci95_bootstrap_n200": list(board.ci95),
            "discrimination_median": board.discrimination_median,
        },
        "verdict": board.verdict,
        "kill_details": board.kill_details,
    }


def _cli(argv: list[str] | None = None) -> None:
    """Runner CLI : ``prompts`` génère les JSON d'extraction, ``calibrate``
    DOIT précéder ``score`` (fichier exigé).

    ``python -m ict.self_model_minimal prompts --seed 0 --out-main m.json
    --out-calib c.json`` écrit les jeux de prompts pour
    ``extract_sae_traces.py --prompts-json``. ``calibrate <npz...> --out
    calib.json`` gèle σ_self ; ``score --calibration calib.json`` refuse de
    tourner sans ce fichier — garde anti-HARKing opérationnel (l'ordre
    inverse est impossible, pas juste déconseillé).
    """
    import argparse

    from .sae_traces import load_traces

    ap = argparse.ArgumentParser(description="Case 4 (#8182) — self-model minimal")
    sub = ap.add_subparsers(dest="cmd", required=True)
    g = sub.add_parser("prompts", help="JSON de prompts pour extract_sae_traces.py")
    g.add_argument("--seed", type=int, required=True, choices=list(SEEDS))
    g.add_argument("--out-main", required=True)
    g.add_argument("--out-calib", required=True)
    c = sub.add_parser("calibrate", help="phase 1 : σ_self gelé avant les bras principaux")
    c.add_argument("traces", nargs="+", help=".npz de calibration (5 seeds)")
    c.add_argument("--out", required=True, help="JSON de calibration figé")
    s = sub.add_parser("score", help="phase 2 : bras principaux + verdict")
    s.add_argument("traces", nargs="+", help=".npz des bras principaux (5 seeds)")
    s.add_argument("--calibration", required=True, help="JSON produit par 'calibrate'")
    s.add_argument("--out", required=True, help="JSON résultat (ict/results/)")

    args = ap.parse_args(argv)
    if args.cmd == "prompts":
        write_prompts_json(args.seed, args.out_main, calibration=False)
        write_prompts_json(args.seed, args.out_calib, calibration=True)
        print(f"[prompts] seed {args.seed} -> {args.out_main} + {args.out_calib}")
        return
    if args.cmd == "calibrate":
        calib = calibrate_epsilon_self({i: load_traces(p) for i, p in enumerate(args.traces)})
        Path(args.out).write_text(json.dumps({
            "r_neutre_by_seed": calib.r_neutre_by_seed,
            "sigma_self": calib.sigma_self,
            "notes": calib.notes,
        }, ensure_ascii=False, indent=1), encoding="utf-8", newline="\n")
        print(f"[calibrate] sigma_self={calib.sigma_self:.6f} -> {args.out}")
        return
    frozen = json.loads(Path(args.calibration).read_text(encoding="utf-8"))
    calib = Calibration(
        r_neutre_by_seed={int(k): v for k, v in frozen["r_neutre_by_seed"].items()},
        sigma_self=float(frozen["sigma_self"]),
        notes=list(frozen.get("notes", [])))
    result = run_analysis(calib, {i: load_traces(p) for i, p in enumerate(args.traces)})
    Path(args.out).write_text(json.dumps(result, ensure_ascii=False, indent=1),
                              encoding="utf-8", newline="\n")
    print(f"[score] verdict={result['verdict']} -> {args.out}")


if __name__ == "__main__":
    _cli()
