"""Diffusion workspace d'un q erroné — exécution du pré-enregistrement case 3 (#8182).

La confabulation en une phrase : le système tient une représentation FAUSSE
d'une cible POURTANT connue et la diffuse en aval avec la même efficacité que
le vrai — l'erreur n'est pas un raté du broadcast, elle EST broadcastée : la
workspace « consacre » l'erreur (row 204 de la matrice de dissociations).

Le pré-enregistrement (``docs/ict/dissociations-matrix.md`` §« Case 3 — W
diffuse un q erroné (confabulation) — pré-enregistrement chiffré », scellé
avant run) fixe AVANT le test :

- la cible ``R_confab = propa(q̂_faux) / propa(q̂_vrai) ∈ [0.80, 1.00]`` ;
- le null adversarial RÉSIDUEL : ``ε_stable = 0.5 × (propa(q̂_vrai) −
  propa(aléatoire))`` — l'écart faux vs aléatoire doit valoir au moins la
  moitié de l'écart vrai vs aléatoire (« l'écart maximal que la propagation
  peut porter ») pour parler de consécration SPÉCIFIQUE de l'erreur — sinon
  la « consécration » n'est que du broadcast non-discriminant ;
- l'ordre anti-HARKing : la calibration (bras vrai + aléatoire) est mesurée
  et GELÉE dans un JSON AVANT que le bras faux ne soit scoré. Le dénominateur
  de R_confab ET ε_stable sont donc tous deux gelés avant la mesure
  principale — plus strict que cases 4/5, où seule l'échelle était gelée ;
- 5 graines (0, 1, 7, 42, 99), 3 prompts par bras sur la banque de contextes
  partagée (import ``CONTEXTS_BY_SEED`` — comparabilité cross-case).

Choix de substrat (honnêteté, hérité de case 5) : le pré-enregistrement
nommait « SAETrajectoires strate 5 (Qwen2.5-3B) » ; l'exécution case 5
(#15547) a posé le substrat réel exécutable et déclaré ses choix canoniques
« pour les cases 3 et 4 » : **Qwen3.5-2B-Base, couche 12/24, SAE Qwen-Scope
W32K-L0_50** via ``scripts/extract_sae_traces.py``. La case 3 reprend
EXACTEMENT ce substrat pour que R_confab soit comparable à R_attn (case 5) et
R_self (case 4). L'opérateur ``propa`` est importé TEL QUEL de
:mod:`ict.attention_schema` — la seule différence case 5 → case 3 est la
cible du prompt, jamais l'instrument.

Opérationnalisation des bras (panel verrouillé avant test, matrice l.565) :
chaque prompt = un contexte amont de la banque partagée + une clause cible.
La clause vrai et la clause faux portent la MÊME cible connue (la carafe
d'eau) et ne diffèrent que par le mot de la propriété (claire/bleue) —
contre-factuel exact au niveau de la propriété, « la cible est connue, mais
q̂ ≠ cible ». La clause aléatoire porte un stimulus sans rapport à aucun
objet de la tâche (le tramway), « pas de représentation d'aucun objet de la
tâche » (matrice l.546).

Grade C : la matrice n'identifie AUCUN hook grade C pour cette case (« aucun
hook identifié dans #9533 ») ; le banc teste si la workspace SAE consacre un
q̂ faux aussi efficacement qu'un q̂ vrai. Aucune phénoménologie clinique de
la confabulation n'est mesurée ni revendiquée.

Référence pré-enregistrement :
``docs/ict/dissociations-matrix.md`` §« Case 3 — W diffuse un q erroné »
(l.539-585), scellé avant cette exécution (statut-cible c.1242).
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from pathlib import Path

import numpy as np

from .attention_schema import CONTEXTS_BY_SEED, propa

__all__ = [
    "SEEDS",
    "TASK_VRAI",
    "TASK_FAUX",
    "TASK_ALEA",
    "ARM_CALIB",
    "ARM_MAIN",
    "build_calibration_sets",
    "build_prompt_sets",
    "write_prompts_json",
    "calibrate_epsilon_stable",
    "apply_verdict_confab",
    "score_main_arms",
    "run_analysis",
]

SEEDS = (0, 1, 7, 42, 99)

# Clauses de tâche : la cible (la carafe d'eau) est identique et connue dans
# les bras vrai et faux — SEUL le mot de la propriété diffère (claire/bleue),
# « la cible est connue, mais q̂ ≠ cible » (matrice l.544). La clause
# aléatoire est un stimulus sans rapport à aucun objet de la tâche (l.546).
# Les contextes amont sont la banque de case 5 (import), partagée à
# l'identique par les trois bras.
TASK_VRAI = ("Décris la carafe d'eau posée sur la table : "
             "l'eau qu'elle contient est claire, n'est-ce pas ?")
TASK_FAUX = ("Décris la carafe d'eau posée sur la table : "
             "l'eau qu'elle contient est bleue, n'est-ce pas ?")
TASK_ALEA = "Décris le passage du tramway dans la rue : quel bruit fait-il ?"

ARM_CALIB = ("target_vrai", "control_alea")
ARM_MAIN = ("confab_faux",)


# --------------------------------------------------------------------------- #
# Génération des prompts (déterministe, auditable, zéro LLM en amont)
# --------------------------------------------------------------------------- #
def build_prompt_sets(seed: int) -> dict[str, list[str]]:
    """Rend les 3 prompts du bras principal (faux) d'une graine.

    Le pré-enregistrement annonce « 3 prompts à représentation erronée
    (faux) » : le bras principal est le bras faux SEUL — les bras vrai et
    aléatoire appartiennent à la calibration, gelée avant le score (c'est la
    structure anti-HARKing propre à la case 3 : dénominateur et ε_stable
    sont tous deux gelés avant la mesure principale).
    """
    contexts = CONTEXTS_BY_SEED[seed]
    if len(contexts) != 3:
        raise ValueError(f"seed {seed}: 3 contextes attendus, {len(contexts)} trouvés")
    return {"confab_faux": [c + TASK_FAUX for c in contexts]}


def build_calibration_sets(seed: int) -> dict[str, list[str]]:
    """Rend les 3+3 prompts de calibration (vrai + aléatoire, null résiduel)."""
    contexts = CONTEXTS_BY_SEED[seed]
    if len(contexts) != 3:
        raise ValueError(f"seed {seed}: 3 contextes attendus, {len(contexts)} trouvés")
    return {
        "target_vrai": [c + TASK_VRAI for c in contexts],
        "control_alea": [c + TASK_ALEA for c in contexts],
    }


def write_prompts_json(seed: int, path: str | Path, *, calibration: bool) -> dict:
    """Écrit le JSON de prompts pour ``extract_sae_traces.py --prompts-json``."""
    sets = build_calibration_sets(seed) if calibration else build_prompt_sets(seed)
    payload = dict(sets)
    Path(path).write_text(
        json.dumps(payload, ensure_ascii=False, indent=1), encoding="utf-8")
    return payload


# --------------------------------------------------------------------------- #
# Calibration résiduelle du null adversarial (GPU-free, sur traces .npz)
# --------------------------------------------------------------------------- #
@dataclass
class Calibration:
    """Null adversarial calibré AVANT le test principal (anti-HARKing).

    ``gap_by_seed`` ne contient que les graines exploitables (gap > 0) ; une
    graine à gap ≤ 0 est dégénérée — l'instrument n'y porte aucun écart vrai
    vs aléatoire, elle ne peut pas témoigner d'une consécration et compte
    comme non-passante au critère 5/5 (jamais imputée).
    """

    propa_vrai_by_seed: dict[int, float]
    propa_alea_by_seed: dict[int, float]
    gap_by_seed: dict[int, float] = field(default_factory=dict)
    epsilon_stable_by_seed: dict[int, float] = field(default_factory=dict)
    epsilon_stable_median: float | None = None
    notes: list[str] = field(default_factory=list)


def calibrate_epsilon_stable(calib_traces_by_seed: dict[int, dict],
                             *, k_features: int = 64) -> Calibration:
    """ε_stable = 0.5 × (propa(vrai) − propa(aléatoire)), par graine puis médian.

    Ne lit QUE les traces de calibration — l'appeler et écrire son résultat
    AVANT :func:`score_main_arms` (l'ordre est vérifié par :func:`run_analysis`
    et par le runner CLI en deux phases). La formule est RESIDUELLE, scellée
    par le pré-enregistrement : l'écart faux vs aléatoire devra valoir au
    moins la moitié de l'écart vrai vs aléatoire mesuré ici.
    """
    calib = Calibration(propa_vrai_by_seed={}, propa_alea_by_seed={})
    for seed, traces in sorted(calib_traces_by_seed.items()):
        p_v = propa(traces, "target_vrai", k_features=k_features)
        p_a = propa(traces, "control_alea", k_features=k_features)
        calib.propa_vrai_by_seed[seed] = p_v
        calib.propa_alea_by_seed[seed] = p_a
        gap = p_v - p_a
        if gap <= 0.0:
            calib.notes.append(
                f"graine {seed}: gap propa(vrai)−propa(aléatoire) = {gap:.4f} ≤ 0 — "
                "calibration dégénérée : la graine ne peut pas témoigner d'une "
                "consécration (comptée non-passante au critère 5/5, jamais imputée)")
            continue
        calib.gap_by_seed[seed] = gap
        calib.epsilon_stable_by_seed[seed] = 0.5 * gap
    if len(calib.gap_by_seed) < 3:
        raise ValueError(f"calibration invalide : {len(calib.gap_by_seed)} graines "
                         "exploitables (<3) — l'instrument ne permet pas de fixer "
                         "ε_stable, verdict INCONCLUSIF par construction")
    calib.epsilon_stable_median = float(np.median(list(calib.epsilon_stable_by_seed.values())))
    return calib


# --------------------------------------------------------------------------- #
# Table de verdict multi-niveau (scellée par le pré-enregistrement)
# --------------------------------------------------------------------------- #
def apply_verdict_confab(r_by_seed: dict[int, float],
                         passes_by_seed: dict[int, bool]) -> tuple[str, list[str]]:
    """Applique EXACTEMENT la table de verdict multi-niveau du pré-enregistrement.

    - **Rejet** : médiane(R_confab) < 0.80 → FALSIFIED (la workspace DISTINGUE
      le faux du vrai et pénalise l'erreur) ;
    - **Agrégé** : médiane ∈ [0.80, 1.00] ET discrimination ≥ ε_stable sur
      5/5 graines → CONFIRMED (la workspace CONSACRE l'erreur) ;
    - **Partiel** : médiane ∈ [0.80, 1.00] MAIS ≥ 1 graine sous ε_stable →
      INCONCLUSIF (null adversarial partiel : broadcast non-discriminant) ;
    - médiane > 1.00 : hors table scellée → INCONCLUSIF, signalé comme tel
      (la section Lectures du pré-enregistrement y lirait une consécration a
      fortiori — R ≥ 0.80 — mais la table agrégée exige médiane ∈ [0.80,
      1.00] ; aucun verdict n'est inventé, la bande de prudence ± 0.05 de la
      matrice est rappelée).
    """
    values = np.asarray(list(r_by_seed.values()), dtype=float)
    r_med = float(np.median(values))
    kills: list[str] = []
    if r_med < 0.80:
        if r_med >= 0.75:
            kills.append(f"médiane {r_med:.3f} dans la bande de prudence "
                         "[0.75, 0.80) (tolérance ± 0.05, matrice) — Rejet "
                         "annoncé, pas un échec franc")
        return "FALSIFIED", kills
    if r_med > 1.00:
        prudence = " (bande de prudence (1.00, 1.05])" if r_med <= 1.05 else ""
        kills.append(
            f"médiane {r_med:.3f} > 1.00 : hors table de verdict scellée — la "
            "section Lectures y lirait une consécration a fortiori (R ≥ 0.80), "
            f"la table agrégée exige médiane ∈ [0.80, 1.00]{prudence} ; rapporté "
            "sans inventer de verdict")
        return "INCONCLUSIF", kills
    n_fail = sum(1 for p in passes_by_seed.values() if not p)
    if n_fail:
        failed = sorted(s for s, p in passes_by_seed.items() if not p)
        kills.append(
            f"discrimination < ε_stable sur {n_fail}/{len(passes_by_seed)} graines "
            f"(graines {failed}) — la « consécration » n'est pas de la consécration : "
            "broadcast non-discriminant, null adversarial partiel")
        return "INCONCLUSIF", kills
    return "CONFIRMED", []


# --------------------------------------------------------------------------- #
# Scoreboard final
# --------------------------------------------------------------------------- #
@dataclass
class Scoreboard:
    """Scoreboard pré-enregistré : médiane, IC95 bootstrap, discrimination 5/5."""

    r_confab_by_seed: dict[int, float]
    propa_faux_by_seed: dict[int, float]
    discrimination_by_seed: dict[int, float]
    passes_by_seed: dict[int, bool]
    r_median: float
    ci95: tuple[float, float]
    epsilon_stable_median: float
    verdict: str
    kill_details: list[str] = field(default_factory=list)


def score_main_arms(main_traces_by_seed: dict[int, dict],
                    calibration: Calibration, *, k_features: int = 64) -> Scoreboard:
    """Scoreboard final : R_confab par graine, IC95 bootstrap n=200, verdict.

    Exigence anti-HARKing : ``calibration.epsilon_stable_median`` doit être
    gelé (le fichier de calibration produit par la phase 1 doit exister et
    être chargé) AVANT le score du bras faux — le CLI refuse l'ordre inverse.
    Le dénominateur ``propa(q̂_vrai)`` vient des traces de calibration gelées,
    pas d'une re-mesure au moment du score.
    """
    if calibration.epsilon_stable_median is None or not calibration.epsilon_stable_by_seed:
        raise ValueError("ε_stable non gelé : la calibration résiduelle doit être "
                         "complétée (propa(vrai), propa(aléatoire) et ε_stable "
                         "écrits dans le JSON de calibration) AVANT le score du "
                         "bras faux — anti-HARKing.")
    r_by_seed: dict[int, float] = {}
    propa_faux: dict[int, float] = {}
    disc_by_seed: dict[int, float] = {}
    passes: dict[int, bool] = {}
    for seed, traces in sorted(main_traces_by_seed.items()):
        if seed not in calibration.propa_vrai_by_seed:
            raise ValueError(f"graine {seed} absente de la calibration gelée — "
                             "les traces de calibration et du bras faux doivent "
                             "couvrir les mêmes graines")
        p_v = calibration.propa_vrai_by_seed[seed]
        p_a = calibration.propa_alea_by_seed[seed]
        if p_v <= 0.0:
            raise ValueError(f"graine {seed}: propa(q̂_vrai)={p_v} ≤ 0 — R_confab "
                             "non défini, graine à documenter comme échec de "
                             "mesure, jamais à imputer")
        p_f = propa(traces, "confab_faux", k_features=k_features)
        r_by_seed[seed] = p_f / p_v
        propa_faux[seed] = p_f
        disc_by_seed[seed] = p_f - p_a
        eps = calibration.epsilon_stable_by_seed.get(seed)
        passes[seed] = eps is not None and disc_by_seed[seed] >= eps
    if len(r_by_seed) < 3:
        raise ValueError(f"score invalide : {len(r_by_seed)} graines exploitables "
                         "(<3) — verdict INCONCLUSIF par construction")

    values = np.asarray(list(r_by_seed.values()), dtype=float)
    rng = np.random.default_rng(20260913)
    boots = [float(np.median(rng.choice(values, size=values.size, replace=True)))
             for _ in range(200)]
    ci95 = (float(np.quantile(boots, 0.025)), float(np.quantile(boots, 0.975)))

    verdict, kills = apply_verdict_confab(r_by_seed, passes)
    return Scoreboard(
        r_confab_by_seed=r_by_seed,
        propa_faux_by_seed=propa_faux,
        discrimination_by_seed=disc_by_seed,
        passes_by_seed=passes,
        r_median=float(np.median(values)),
        ci95=ci95,
        epsilon_stable_median=calibration.epsilon_stable_median,
        verdict=verdict,
        kill_details=kills,
    )


def run_analysis(calibration: Calibration,
                 main_traces_by_seed: dict[int, dict], *, k_features: int = 64) -> dict:
    """Score le bras faux contre la calibration GELÉE et rend le dictionnaire
    complet sérialisable pour ``ict/results/confabulation_broadcast_results.json``."""
    board = score_main_arms(main_traces_by_seed, calibration, k_features=k_features)
    return {
        "case": "case3_confabulation_broadcast",
        "prediction": ("R_confab = propa(q̂_faux)/propa(q̂_vrai) ∈ [0.80, 1.00] ET "
                       "propa(q̂_faux) − propa(aléatoire) ≥ ε_stable (5/5 graines)"),
        "substrate": ("Qwen3.5-2B-Base, couche 12/24, SAE Qwen-Scope W32K-L0_50 "
                      "(top-k=50) — même substrat que case 5 #15547 et case 4 "
                      "#15879 ; le pré-enregistrement nommait SAETrajectoires "
                      "strate 5 (Qwen2.5-3B), case 5 a posé le substrat réel "
                      "exécutable et déclaré l'instrument canonique pour les "
                      "cases 3 et 4"),
        "calibration": {
            "propa_vrai_by_seed": calibration.propa_vrai_by_seed,
            "propa_alea_by_seed": calibration.propa_alea_by_seed,
            "gap_by_seed": calibration.gap_by_seed,
            "epsilon_stable_by_seed": calibration.epsilon_stable_by_seed,
            "epsilon_stable_median": calibration.epsilon_stable_median,
            "formula": "ε_stable = 0.5 × (propa(q̂_vrai) − propa(aléatoire)) — "
                       "calibration RÉSIDUELLE gelée AVANT le bras faux",
            "notes": calibration.notes,
        },
        "main": {
            "r_confab_by_seed": board.r_confab_by_seed,
            "propa_faux_by_seed": board.propa_faux_by_seed,
            "discrimination_by_seed": board.discrimination_by_seed,
            "passes_by_seed": board.passes_by_seed,
            "r_median": board.r_median,
            "ci95_bootstrap_n200": list(board.ci95),
        },
        "verdict": board.verdict,
        "kill_details": board.kill_details,
    }


def _cli(argv: list[str] | None = None) -> None:
    """Runner CLI : ``prompts`` génère les JSON d'extraction, ``calibrate``
    DOIT précéder ``score`` (fichier exigé).

    ``python -m ict.confabulation_broadcast prompts --seed 0 --out-calib c.json
    --out-main m.json`` écrit les jeux de prompts pour
    ``extract_sae_traces.py --prompts-json`` (calibration = vrai + aléatoire,
    6 prompts ; main = faux, 3 prompts). ``calibrate <npz...> --out
    calib.json`` gèle propa(vrai), propa(aléatoire) et ε_stable ;
    ``score --calibration calib.json`` refuse de tourner sans ce fichier —
    garde anti-HARKing opérationnelle (l'ordre inverse est impossible, pas
    juste déconseillé). Les clés de graine des JSON sont les ORDINAUX des
    fichiers passés (même convention que cases 4/5) : passer les 5 .npz dans
    l'ordre des graines 0, 1, 7, 42, 99.
    """
    import argparse

    from .sae_traces import load_traces

    ap = argparse.ArgumentParser(description="Case 3 (#8182) — confabulation broadcast")
    sub = ap.add_subparsers(dest="cmd", required=True)
    g = sub.add_parser("prompts", help="JSON de prompts pour extract_sae_traces.py")
    g.add_argument("--seed", type=int, required=True, choices=list(SEEDS))
    g.add_argument("--out-calib", required=True,
                   help="JSON calibration (vrai + aléatoire, 6 prompts)")
    g.add_argument("--out-main", required=True,
                   help="JSON bras principal (faux, 3 prompts)")
    c = sub.add_parser("calibrate", help="phase 1 : ε_stable gelé avant le bras faux")
    c.add_argument("traces", nargs="+", help=".npz de calibration (5 graines, en ordre)")
    c.add_argument("--out", required=True, help="JSON de calibration figé")
    s = sub.add_parser("score", help="phase 2 : bras faux + verdict")
    s.add_argument("traces", nargs="+", help=".npz du bras faux (5 graines, en ordre)")
    s.add_argument("--calibration", required=True, help="JSON produit par 'calibrate'")
    s.add_argument("--out", required=True, help="JSON résultat (ict/results/)")

    args = ap.parse_args(argv)
    if args.cmd == "prompts":
        write_prompts_json(args.seed, args.out_calib, calibration=True)
        write_prompts_json(args.seed, args.out_main, calibration=False)
        print(f"[prompts] seed {args.seed} -> {args.out_calib} + {args.out_main}")
        return
    if args.cmd == "calibrate":
        calib = calibrate_epsilon_stable(
            {i: load_traces(p) for i, p in enumerate(args.traces)})
        Path(args.out).write_text(json.dumps({
            "propa_vrai_by_seed": calib.propa_vrai_by_seed,
            "propa_alea_by_seed": calib.propa_alea_by_seed,
            "gap_by_seed": calib.gap_by_seed,
            "epsilon_stable_by_seed": calib.epsilon_stable_by_seed,
            "epsilon_stable_median": calib.epsilon_stable_median,
            "notes": calib.notes,
        }, ensure_ascii=False, indent=1), encoding="utf-8", newline="\n")
        print(f"[calibrate] epsilon_stable_median={calib.epsilon_stable_median:.6f} "
              f"-> {args.out}")
        return
    frozen = json.loads(Path(args.calibration).read_text(encoding="utf-8"))
    calib = Calibration(
        propa_vrai_by_seed={int(k): v for k, v in frozen["propa_vrai_by_seed"].items()},
        propa_alea_by_seed={int(k): v for k, v in frozen["propa_alea_by_seed"].items()},
        gap_by_seed={int(k): v for k, v in frozen["gap_by_seed"].items()},
        epsilon_stable_by_seed={int(k): v
                                for k, v in frozen["epsilon_stable_by_seed"].items()},
        epsilon_stable_median=(float(frozen["epsilon_stable_median"])
                               if frozen["epsilon_stable_median"] is not None else None),
        notes=list(frozen.get("notes", [])))
    result = run_analysis(calib, {i: load_traces(p) for i, p in enumerate(args.traces)})
    Path(args.out).write_text(json.dumps(result, ensure_ascii=False, indent=1),
                              encoding="utf-8", newline="\n")
    print(f"[score] verdict={result['verdict']} -> {args.out}")


if __name__ == "__main__":
    _cli()
