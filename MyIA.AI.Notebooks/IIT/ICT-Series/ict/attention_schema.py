"""Schéma attentionnel du workspace — exécution du pré-enregistrement case 5 (#8182, Graziano AST).

Graziano (Attention Schema Theory) en une phrase : la conscience d'accès
s'appuie sur un modèle interne SIMPLIFIÉ que le système construit de son
propre état attentionnel — un « schéma » de l'attention, comme le schéma
corporel est un modèle abstrait du corps, pas une copie fidèle.

Le pré-enregistrement (``docs/ict/dissociations-matrix.md``, case 5,
PR c.435) scelle AVANT le run :

- la cible ``R_attn = propa(q̂(attention)) / propa(q̂(objet)) ∈ [0.50, 2.00]``
  ET ``discrimination_attn = |propa(q̂(attention)) − propa(q̂(objet))| ≥ ε_attn`` ;
- le null adversarial « décris une chaise » (objet tiers sans mention
  agentique) ;
- la calibration ``ε_attn = 0.5 × σ_attn × propa(q̂(objet))_médian`` sur deux
  entités publiques non impliquées, exécutée AVANT le test principal ;
- les trois portes de falsification : ``R_attn < 0.50`` (répression),
  ``R_attn > 2.50`` (artefact de blocage), bande passante mais
  discrimination sous ``ε_attn`` (INCONCLUSIF) ;
- 5 graines (0, 1, 7, 42, 99), 9 prompts appariés par graine.

Ce module est l'exécutant GPU-free : la mesure ``propa`` consomme les traces
SAE produites par ``scripts/extract_sae_traces.py`` (pipeline #5101, SAE
officiel Qwen-Scope top-k), exactement comme les cases 3 et 4 le prévoient.

Opérationnalisation de ``propa`` (première exécution de ce protocole, ces
choix deviennent canoniques pour les cases 3 et 4) :

- **ignition** ``W_t`` : positions dont l'activation SAE CONJOINTE (somme des
  valeurs du top-k) est dans le top-1 % des positions CANDIDATES du prompt ;
  sont candidates les positions laissant au moins un token aval (``0 .. T-6``)
  — une ignition sans consommateur mesurable n'est pas une propagation ;
- **consommateurs** : les 5 tokens suivant chaque position d'ignition ;
- **signature** ``top-k_features(q̂(A))`` : les 64 features d'activation
  moyenne maximale du bras A (``mean_activation_by_set`` → top-64) ;
- ``propa(A) = fraction des consommateurs c avec argmax(SAE(c)) ∈ signature``.

Anti-HARKing structurel : :func:`calibrate_epsilon` ne lit QUE les traces de
calibration ; elle doit être appelée et son résultat écrit AVANT que
:func:`score_main_arms` ne soit invoquée sur les bras principaux. Le runner
CLI du bas de module refuse l'ordre inverse.

Grade C documentaire : ce jouet teste si la workspace SAE DISCRIMINE une
cible attentionnelle d'une cible d'objet — la lecture minimale d'AST sur ce
substrat. Aucune phénoménologie n'est mesurée ; l'isomorphisme avec le
schéma attentionnel neurobiologique de Graziano n'est pas garanti (cf
avertissements grade C de la matrice).

References
----------
M.S.A. Graziano, *Consciousness and the Social Brain*, Oxford University
Press 2013, ISBN 978-0199928644. Pré-enregistrement case 5 :
``docs/ict/dissociations-matrix.md`` (l. 297-369).
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from pathlib import Path

import numpy as np

from .sae_traces import load_traces, mean_activation_by_set

__all__ = [
    "SEEDS",
    "TASK_SELF",
    "TASK_OTHER",
    "TASK_OBJECT",
    "CONTEXTS_BY_SEED",
    "CALIBRATION_TARGETS",
    "build_prompt_sets",
    "build_calibration_sets",
    "write_prompts_json",
    "propa",
    "calibrate_epsilon",
    "score_main_arms",
    "apply_verdict",
    "run_analysis",
]

SEEDS = (0, 1, 7, 42, 99)

# Clauses de tâche : SEUL le segment cible diffère au sein d'un triplet
# (pré-enregistrement : « contre-factuels exacts, mêmes contextes, seule la
# cible d'attention diffère »). Le contexte amont est partagé à l'identique.
TASK_SELF = "Décris ton attention maintenant : sur quoi porte-t-elle ?"
TASK_OTHER = "Décris l'attention de l'agent Y maintenant : sur quoi porte-t-elle ?"
TASK_OBJECT = "Décris la chaise en bois maintenant : sur quoi est-elle posée ?"

# Entités publiques de calibration : connues, non impliquées identitairement
# ni attentionnellement (pré-enregistrement §null adversarial, point 1).
CALIBRATION_TARGETS = (
    ("calib_obj1", "Décris la Tour Eiffel maintenant : où se trouve-t-elle ?"),
    ("calib_obj2", "Décris le Mont Blanc maintenant : où se trouve-t-il ?"),
)

CONTEXTS_BY_SEED: dict[int, tuple[str, ...]] = {
    0: (
        "La salle de réunion est calme ce matin. Le carnet est ouvert sur la table, à côté d'une tasse encore chaude. ",
        "L'atelier sent la sciure fraîche. Les outils sont rangés sur le panneau mural, chacun à sa place. ",
        "Le bureau donne sur la cour intérieure. Une pile de feuilles attend près de la lampe allumée. ",
    ),
    1: (
        "La bibliothèque du rez-de-chaussée est silencieuse. Les rayons montent jusqu'au plafond, éclairés par des néons pâles. ",
        "Le laboratoire vient d'être nettoyé. Les éprouvettes sèchent sur l'égouttoir, étiquetées au marqueur. ",
        "La véranda baigne dans la lumière de fin d'après-midi. Les plantes en pot ont été arrosées le matin même. ",
    ),
    7: (
        "Le quai est désert à cette heure. Les voiliers amarrés tanguent doucement contre leurs amarres. ",
        "La cuisine du restaurant est vide entre deux services. Les casseroles de cuivre brillent au-dessus du plan de travail. ",
        "Le dortoir du refuge est tranquille. Les sacs de couchage sont roulés au pied des lits superposés. ",
    ),
    42: (
        "La salle de classe est vide après la sonnerie. Les tables restent alignées, les tableaux effacés à moitié. ",
        "Le garage sent l'huile et le béton froid. Le pont élévateur est descendu au niveau du sol. ",
        "La serre est humide et tiède. Les gouttes condensées ruissellent le long des vitres. ",
    ),
    99: (
        "Le studio d'enregistrement est insonorisé. Le micro pend au-dessus de la table de mixage. ",
        "La gare de banlieue est presque vide. Les affiches jaunies bordent le quai numéro deux. ",
        "L'observatoire domine la colline. Le dôme est fermé, les instruments au repos. ",
    ),
}

ARM_SETS = ("attn_self", "attn_other", "obj_chaise")


# --------------------------------------------------------------------------- #
# Génération des prompts (déterministe, auditable, zéro LLM en amont)
# --------------------------------------------------------------------------- #
def build_prompt_sets(seed: int) -> dict[str, list[str]]:
    """Rend les 3+3+3 prompts appariés d'une graine (9 prompts, pré-enreg.)."""
    contexts = CONTEXTS_BY_SEED[seed]
    if len(contexts) != 3:
        raise ValueError(f"seed {seed}: 3 contextes attendus, {len(contexts)} trouvés")
    return {
        "attn_self": [c + TASK_SELF for c in contexts],
        "attn_other": [c + TASK_OTHER for c in contexts],
        "obj_chaise": [c + TASK_OBJECT for c in contexts],
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
# Mesure propa (GPU-free, sur traces .npz du pipeline #5101)
# --------------------------------------------------------------------------- #
def propa(traces: dict, set_name: str, *, k_features: int = 64,
          consumer_width: int = 5, ignition_quantile: float = 0.99) -> float:
    """Taux de propagation workspace du bras ``set_name`` (formule c.435).

    ``propa = (1/|panel|) Σ_c 𝟙[argmax(SAE(c)) ∈ top-64_features(bras)]`` où
    les consommateurs ``c`` sont les ``consumer_width`` tokens suivant chaque
    position d'ignition (top ``ignition_quantile`` de l'activation SAE
    conjointe, parmi les positions laissant un token aval).

    Lève ``ValueError`` si le bras est absent de la trace ou si le panel
    consommateur est vide (mesure non définie — jamais fabriquée).
    """
    means = mean_activation_by_set(traces)
    if set_name not in means:
        raise ValueError(f"bras '{set_name}' absent de la trace "
                         f"(jeux présents : {sorted(means)})")
    signature = np.argsort(means[set_name])[::-1][:k_features]
    signature_set = set(int(f) for f in signature)

    hits, total = 0, 0
    for (name, _i), entry in sorted(traces["prompts"].items()):
        if name != set_name:
            continue
        ids, vals = entry["ids"], entry["vals"]
        T = ids.shape[0]
        if T <= consumer_width + 1:
            raise ValueError(f"{set_name}: trace trop courte ({T} tokens)")
        # Candidats d'ignition : toute position avec au moins 1 token aval.
        candidates = np.arange(0, T - 1)
        joint = vals.sum(axis=1)[candidates]
        threshold = np.quantile(joint, ignition_quantile)
        ignitions = candidates[joint >= threshold]
        if ignitions.size == 0:            # impossible par construction (>= q99)
            raise ValueError(f"{name}: aucune ignition — quantile dégénéré")
        consumers = set()
        for t in ignitions:
            consumers.update(range(int(t) + 1, min(int(t) + 1 + consumer_width, T)))
        for c in consumers:
            total += 1
            if int(ids[c, 0]) in signature_set:   # ids[:, 0] = argmax (topk trié)
                hits += 1
    if total == 0:
        raise ValueError(f"{set_name}: panel consommateur vide — "
                         "l'ignition doit précéder au moins un token")
    return hits / total


@dataclass
class Calibration:
    """Null adversarial calibré AVANT le test principal (anti-HARKing)."""

    r_neutre_by_seed: dict[int, float]
    sigma_attn: float
    propa_obj_median_scale: float | None = None
    epsilon_attn: float | None = None
    notes: list[str] = field(default_factory=list)


def calibrate_epsilon(calib_traces_by_seed: dict[int, dict],
                      *, k_features: int = 64) -> Calibration:
    """σ_attn depuis le rapport obj1/obj2 (null), ε_attn = 0.5·σ·scale.

    Ne lit QUE les traces de calibration — l'appeler et écrire son résultat
    AVANT :func:`score_main_arms` (l'ordre est vérifié par :func:`run_analysis`).
    ``σ_attn`` : écart-type d'échantillon (ddof=1) des rapports neutres sur
    les 5 graines — choix fixé ici, avant tout run des bras principaux.
    """
    r_neutre: dict[int, float] = {}
    notes: list[str] = []
    for seed, traces in sorted(calib_traces_by_seed.items()):
        p1 = propa(traces, "calib_obj1", k_features=k_features)
        p2 = propa(traces, "calib_obj2", k_features=k_features)
        if p2 == 0.0:
            notes.append(f"seed {seed}: propa(calib_obj2)=0 — graine exclue du "
                         "calcul de σ_attn (0/0 non défini, jamais fabriqué)")
            continue
        r_neutre[seed] = p1 / p2
    if len(r_neutre) < 3:
        raise ValueError(f"calibration invalide : {len(r_neutre)} graines "
                         "exploitables (<3) — l'instrument ne permet pas de "
                         "fixer ε_attn, verdict INCONCLUSIF par construction")
    sigma = float(np.std(list(r_neutre.values()), ddof=1))
    return Calibration(r_neutre_by_seed=r_neutre, sigma_attn=sigma, notes=notes)


@dataclass
class Scoreboard:
    """Scoreboard pré-enregistré : médiane, IC95 bootstrap, discrimination."""

    r_attn_by_seed: dict[int, float]
    propa_by_seed: dict[int, dict[str, float]]
    r_median: float
    ci95: tuple[float, float]
    discrimination_median: float
    epsilon_attn: float
    verdict: str
    kill_details: list[str] = field(default_factory=list)


def apply_verdict(r_by_seed: dict[int, float], discrimination_by_seed: dict[int, float],
                  epsilon_attn: float) -> tuple[str, list[str]]:
    """Applique EXACTEMENT la table de verdict multi-niveau du pré-enregistrement.

    - FALSIFIED : médiane < 0.50 (répression) ou > 2.50 (artefact) sur ≥ 3 graines ;
    - CONFIRMED : médiane ∈ [0.50, 2.00], discrimination médiane ≥ ε_attn,
      médiane ∉ [0.85, 1.15], médiane ≤ 2.50, ET les 5 graines hors bande tueuse ;
    - INCONCLUSIF : médiane dans la bande MAIS discrimination < ε sur ≥ 1 graine
      OU R_attn ∈ [0.85, 1.15] sur ≥ 1 graine.
    """
    values = np.asarray(list(r_by_seed.values()), dtype=float)
    disc = np.asarray(list(discrimination_by_seed.values()), dtype=float)
    r_med = float(np.median(values))
    kills: list[str] = []
    n_low = int((values < 0.50).sum())
    n_high = int((values > 2.50).sum())
    if n_low >= 3:
        kills.append(f"médiane {r_med:.3f} < 0.50 sur {n_low}/5 graines "
                     "(workspace RÉPRIME la représentation attentionnelle)")
    if n_high >= 3:
        kills.append(f"médiane {r_med:.3f} > 2.50 sur {n_high}/5 graines "
                     "(artefact de blocage, persona figée)")
    if kills:
        return "FALSIFIED", kills

    band = 0.50 <= r_med <= 2.00
    disc_med = float(np.median(disc))
    in_kill_band = {s: 0.85 <= r <= 1.15 for s, r in r_by_seed.items()}
    if not band:
        return "FALSIFIED", [f"médiane {r_med:.3f} hors bande [0.50, 2.00] "
                             "sans seuil de falsification majoritaire — "
                             "traitée comme FALSIFIED (répression partielle)"]
    if disc_med < epsilon_attn:
        kills.append(f"discrimination médiane {disc_med:.4f} < ε_attn "
                     f"{epsilon_attn:.4f}")
    if any(in_kill_band.values()):
        kills.append("R_attn ∈ [0.85, 1.15] sur "
                     f"{sum(in_kill_band.values())}/5 graines (indistinguable "
                     "du ratio neutre)")
    if kills:
        return "INCONCLUSIF", kills
    return "CONFIRMED", []


def score_main_arms(main_traces_by_seed: dict[int, dict],
                    calibration: Calibration, *, k_features: int = 64) -> Scoreboard:
    """Scoreboard final : R_attn par graine, IC95 bootstrap n=200, verdict.

    Exigence anti-HARKing : ``calibration.epsilon_attn`` doit déjà être
    assemblé (l'appelant écrit σ_attn AVANT d'invoquer cette fonction —
    vérifié par :func:`run_analysis` via l'ordre des appels, et par le
    runner CLI qui sépare les deux phases en fichiers).
    """
    if calibration.propa_obj_median_scale is None or calibration.epsilon_attn is None:
        raise ValueError("ε_attn non assemblé : la calibration doit être "
                         "complétée (propa(objet)_médian fixé) AVANT le score "
                         "des bras principaux — anti-HARKing.")
    r_by_seed: dict[int, float] = {}
    propa_by_seed: dict[int, dict[str, float]] = {}
    disc_by_seed: dict[int, float] = {}
    for seed, traces in sorted(main_traces_by_seed.items()):
        p_self = propa(traces, "attn_self", k_features=k_features)
        p_obj = propa(traces, "obj_chaise", k_features=k_features)
        if p_obj == 0.0:
            raise ValueError(f"seed {seed}: propa(obj_chaise)=0 — R_attn "
                             "non défini (0/0), graine à documenter comme "
                             "échec de mesure, jamais à imputer")
        r_by_seed[seed] = p_self / p_obj
        propa_by_seed[seed] = {"attn_self": p_self, "obj_chaise": p_obj}
        disc_by_seed[seed] = abs(p_self - p_obj)

    values = np.asarray(list(r_by_seed.values()), dtype=float)
    rng = np.random.default_rng(20260911)
    boots = [float(np.median(rng.choice(values, size=values.size, replace=True)))
             for _ in range(200)]
    ci95 = (float(np.quantile(boots, 0.025)), float(np.quantile(boots, 0.975)))

    epsilon = calibration.epsilon_attn
    verdict, kills = apply_verdict(r_by_seed, disc_by_seed, epsilon)
    return Scoreboard(
        r_attn_by_seed=r_by_seed,
        propa_by_seed=propa_by_seed,
        r_median=float(np.median(values)),
        ci95=ci95,
        discrimination_median=float(np.median(list(disc_by_seed.values()))),
        epsilon_attn=epsilon,
        verdict=verdict,
        kill_details=kills,
    )


def run_analysis(calibration: Calibration,
                 main_traces_by_seed: dict[int, dict], *, k_features: int = 64) -> dict:
    """Assemble ε_attn (échelle = médiane propa(objet) des bras principaux)
    puis le scoreboard — dans cet ordre, et renvoie le dictionnaire complet
    sérialisable pour ``ict/results/attention_schema_results.json``."""
    obj_values = [propa(traces, "obj_chaise", k_features=k_features)
                  for _, traces in sorted(main_traces_by_seed.items())]
    scale = float(np.median(obj_values))
    calibration.propa_obj_median_scale = scale
    calibration.epsilon_attn = 0.5 * calibration.sigma_attn * scale
    board = score_main_arms(main_traces_by_seed, calibration,
                            k_features=k_features)
    return {
        "case": "case5_attention_schema",
        "prediction": ("R_attn = propa(q̂(attention))/propa(q̂(objet)) ∈ "
                       "[0.50, 2.00] ET discrimination ≥ ε_attn"),
        "calibration": {
            "r_neutre_by_seed": calibration.r_neutre_by_seed,
            "sigma_attn": calibration.sigma_attn,
            "propa_obj_median_scale": scale,
            "epsilon_attn": calibration.epsilon_attn,
            "formula": "ε_attn = 0.5 × σ_attn × propa(q̂(objet))_médian",
            "notes": calibration.notes,
        },
        "main": {
            "r_attn_by_seed": board.r_attn_by_seed,
            "propa_by_seed": board.propa_by_seed,
            "r_median": board.r_median,
            "ci95_bootstrap_n200": list(board.ci95),
            "discrimination_median": board.discrimination_median,
        },
        "verdict": board.verdict,
        "kill_details": board.kill_details,
    }


def _cli(argv: list[str] | None = None) -> None:
    """Runner CLI : ``calibrate`` DOIT précéder ``score`` (fichier exigé).

    ``python -m ict.attention_schema calibrate <npz...> --out calib.json``
    gèle σ_attn ; ``score --calibration calib.json`` refuse de tourner sans
    ce fichier — c'est le garde anti-HARKing opérationnel (l'ordre inverse
    est impossible, pas juste déconseillé).
    """
    import argparse

    from .sae_traces import load_traces

    ap = argparse.ArgumentParser(description="Case 5 (#8182) — schéma attentionnel")
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("calibrate", help="phase 1 : σ_attn gelé avant les bras principaux")
    c.add_argument("traces", nargs="+", help=".npz de calibration (5 seeds)")
    c.add_argument("--out", required=True, help="JSON de calibration figé")
    s = sub.add_parser("score", help="phase 2 : bras principaux + verdict")
    s.add_argument("traces", nargs="+", help=".npz des bras principaux (5 seeds)")
    s.add_argument("--calibration", required=True, help="JSON produit par 'calibrate'")
    s.add_argument("--out", required=True, help="JSON résultat (ict/results/)")

    args = ap.parse_args(argv)
    if args.cmd == "calibrate":
        calib = calibrate_epsilon({i: load_traces(p) for i, p in enumerate(args.traces)})
        Path(args.out).write_text(json.dumps({
            "r_neutre_by_seed": calib.r_neutre_by_seed,
            "sigma_attn": calib.sigma_attn,
            "notes": calib.notes,
        }, ensure_ascii=False, indent=1), encoding="utf-8")
        print(f"[calibrate] sigma_attn={calib.sigma_attn:.6f} -> {args.out}")
        return
    frozen = json.loads(Path(args.calibration).read_text(encoding="utf-8"))
    calib = Calibration(
        r_neutre_by_seed={int(k): v for k, v in frozen["r_neutre_by_seed"].items()},
        sigma_attn=float(frozen["sigma_attn"]),
        notes=list(frozen.get("notes", [])))
    result = run_analysis(calib, {i: load_traces(p) for i, p in enumerate(args.traces)})
    Path(args.out).write_text(json.dumps(result, ensure_ascii=False, indent=1),
                              encoding="utf-8")
    print(f"[score] verdict={result['verdict']} -> {args.out}")


if __name__ == "__main__":
    _cli()
