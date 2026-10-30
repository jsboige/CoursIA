"""Case 5ter (#8182) — versant CONTROLE de l'Attention Schema Theory (Graziano 2017).

Les cases 5 (PR #15547, readout ``R_attn`` sur SAE/LLM, INCONCLUSIF) et 5bis
(#15798, interventions causales etat/readout/comportement) servent l'AST
depuis le livre de 2013. Ce qu'aucune ne couvre — verifie par grep nul sur
Conant / good regulator / van den Boogaard dans ``ict/`` et ``docs/ict/`` —
c'est le versant **controle** du papier 2017 (Front. Robot. AI 4:60, CC-BY,
archive au gisement, empreinte 58a1a461e5d6fc5a) :

1. **Conant-Ashby applique a l'attention** : un controleur d'attention muni
   d'un modele interne (schema) controle mieux — plus stable, meilleure
   correction d'erreur, meilleure adaptation aux perturbations (citations
   1-3 du pre-enregistrement ; precedent computationnel van den Boogaard
   2017, attention avec/sans modele interne).
2. **Dissociation rapport/controle** : le rapport lit le modele, pas l'etat
   — une distorsion du schema passe dans le rapport alors que le controle
   reste preserve aux distorsions sous-cliniques (« the machine is captive
   to its own information », citations 4-6).

Anti-HARKing — le pre-enregistrement est scelle AVANT ce module
----------------------------------------------------------------
``docs/ict/attention-schema-control-pre-enregistrement.md`` (commit
``fb74ec445``) fixe terrain, bras, perturbations, metriques, bandes P1a..P5,
graines d'etude (0, 1, 7, 42, 99) et pilote disjoint (graine 1000) **avant**
toute ligne de ce fichier. Ce module est l'EXECUTANT, pas le designer : les
constantes ci-dessous reprennent le document verbatim. Quatre micro-choix
operationnels que le document ne fixe pas numeriquement sont NOMMES ici
(grade C), verifiables au pilote, et une unique revision v2 du document
(commit separe nommant les valeurs v1) reste ouverte avant l'etude :

* **a1** — saillance vraie des distracteurs : U[0.2, 0.8] par item (cible
  1.0), tiree une fois par graine. Rend la competition non triviale sous un
  bruit d'observation sigma_s = 0.3.
* **a2** — initialisation des bras : l'annonce initiale de la cible charge
  l'EMA reactive et l'etat du schema avec la saillance vraie (foyer initial
  = position de la cible a t=0, vitesse estimee nulle, confiance 1.0).
* **a3** — bras distordu : l'etat interne ``pos_s`` est maintenu par
  l'updater comme au bras schema ; le STOCKAGE ajoute ``d`` et l'allocation
  lit le stockage. ``erreur_rapport`` mesure |stocke - pos_s| : sous cette
  lecture P3a est quasi structurel (le pilot le dira) et la charge
  dynamique de P3 porte sur P3b (controle preserve).
* **a4** — la quantification (grille 0,01) frappe le STOCKAGE (position
  allouee/rapportee), pas l'arithmetique de l'updater. Quantifier l'etat
  creerait une bande morte de 0,005/alpha = 0,05 = w/2 : toute erreur sous
  w/2 serait indefiniment arrondie a zero par la correction alpha.innovation,
  annulant le mandat scelle « corrigé par la prédiction 1-pas » — et rendant
  la distorsion d = w/4 invisible a la correction (confondant P3b avec un
  artefact de grille). Mesure au flux lisse (test mecanique) : erreur_pred
  gele a 0,03 vs 0,01 sous la lecture etat-bloque ; converge sous la lecture
  sortie-bloquee.

Metriques et verdicts suivent le document ; le verdict est borne et publie
tel quel (SUPPORTED / PARTIAL / REFUTED / NON_CONCLUSIF_INSTRUMENT), les
contre-regimes (i)-(iii) sont explicites d'avance. CPU, stdlib + numpy,
deterministe : le terrain est tire une fois par graine puis gele, les bras
le rejouent a l'identique (RNG par bras ``seed + offset``).
"""
from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass, field
from pathlib import Path

import numpy as np

# --- Constantes scellees (pre-enregistrement §3) ---------------------------

N_ITEMS = 12
STEPS = 720
FOCUS_WIDTH = 0.10        # w : champ attentionnel
CAPTURE_GAIN = 2.0        # gain biased competition sur l'item capte
OU_THETA = 0.05           # processus OU discret sur la vitesse
SIGMA_V = 0.002           # bruit de vitesse
SIGMA_POS = 0.002         # bruit de position
SIGMA_SAL = 0.3           # bruit d'observation de la saillance (echelle relative)
EMA_REACTIVE = 0.3        # EMA courte du bras reactif
EMA_SCHEMA = 0.1          # EMA lente du schema (position, vitesse, confiance)
GRID = 0.01               # quantification de la position du schema

SALIENCE_TARGET = 1.0
SALIENCE_DISTRACTORS = (0.2, 0.8)   # choix a1 (voir docstring)

JUMP_TIMES = (150, 390, 630)        # teleportation de la cible, +/- JUMP_SIZE
JUMP_SIZE = 0.15
GAIN_DROP_TIMES = (210, 450, 690)   # efficacite du gain a 40% pendant 60 pas
GAIN_DROP_EFF = 0.4
GAIN_DROP_LEN = 60
DISTRACTOR_TIMES = (90, 330, 570)   # un distracteur a saillance x4 pendant 60 pas
DISTRACTOR_FACTOR = 4.0
DISTRACTOR_LEN = 60

CALM_BEFORE = 10          # fenetre calmue : exclut [pert - 10, pert + 80]
CALM_AFTER = 80
CORRECTION_THRESHOLD = 0.15
CORRECTION_HOLD = 5
CORRECTION_CENSOR = 80

STUDY_SEEDS = (0, 1, 7, 42, 99)
PILOT_SEED = 1000         # disjoint, hors etude, jamais compte dans un verdict

ARM_OFFSETS = {           # RNG par bras : default_rng(seed + offset)
    "reactive": 0,
    "schema": 1,
    "schema_shuffled": 2,
    "schema_distorted": 3,
}
DISTORTED_DS = (FOCUS_WIDTH / 4.0, FOCUS_WIDTH / 2.0)


# --- Terrain gele -----------------------------------------------------------

@dataclass
class Terrain:
    """Terrain tire une fois par graine, rejoue a l'identique par tous les bras."""
    seed: int
    positions: np.ndarray          # [STEPS, N_ITEMS] sur [0, 1)
    velocities: np.ndarray         # [STEPS, N_ITEMS]
    salience_true: np.ndarray      # [N_ITEMS]
    salience_obs: np.ndarray       # [STEPS, N_ITEMS] = vraie + N(0, sigma_s)
    target_idx: int
    jumps: dict                    # {t: +1/-1} signe de teleportation de la cible
    distractor_events: dict        # {t0: item} distracteur dope pendant 60 pas

    @property
    def perturbation_times(self) -> tuple:
        return tuple(JUMP_TIMES) + tuple(GAIN_DROP_TIMES) + tuple(DISTRACTOR_TIMES)


def circ_wrap(x: np.ndarray | float) -> np.ndarray | float:
    return x - np.floor(x)


def circ_delta(a, b):
    """Différence a - b repliée sur [-0.5, 0.5) — distance circulaire signée."""
    d = (a - b) % 1.0
    return np.where(d > 0.5, d - 1.0, d)


def build_terrain(seed: int) -> Terrain:
    rng = np.random.default_rng(seed)
    target_idx = int(rng.integers(N_ITEMS))
    salience_true = rng.uniform(*SALIENCE_DISTRACTORS, size=N_ITEMS)
    salience_true[target_idx] = SALIENCE_TARGET
    positions = np.zeros((STEPS, N_ITEMS))
    velocities = np.zeros((STEPS, N_ITEMS))
    v_stat = SIGMA_V / math.sqrt(2.0 * OU_THETA - OU_THETA ** 2)   # std stationnaire
    positions[0] = rng.uniform(0.0, 1.0, size=N_ITEMS)
    velocities[0] = rng.normal(0.0, v_stat, size=N_ITEMS)
    jumps = {t: int(rng.choice((-1, 1))) for t in JUMP_TIMES}
    distractors = [i for i in range(N_ITEMS) if i != target_idx]
    distractor_events = {t: int(rng.choice(distractors)) for t in DISTRACTOR_TIMES}
    for t in range(1, STEPS):
        velocities[t] = (1.0 - OU_THETA) * velocities[t - 1] + rng.normal(0.0, SIGMA_V, N_ITEMS)
        positions[t] = circ_wrap(positions[t - 1] + velocities[t] + rng.normal(0.0, SIGMA_POS, N_ITEMS))
        if t in jumps:
            positions[t, target_idx] = circ_wrap(positions[t, target_idx] + jumps[t] * JUMP_SIZE)
    salience_obs = salience_true[None, :] + rng.normal(0.0, SIGMA_SAL, size=(STEPS, N_ITEMS))
    return Terrain(seed=seed, positions=positions, velocities=velocities,
                   salience_true=salience_true, salience_obs=salience_obs,
                   target_idx=target_idx, jumps=jumps, distractor_events=distractor_events)


def gain_efficiency(t: int) -> float:
    if any(t0 <= t < t0 + GAIN_DROP_LEN for t0 in GAIN_DROP_TIMES):
        return CAPTURE_GAIN * GAIN_DROP_EFF
    return CAPTURE_GAIN


def effective_salience(terrain: Terrain, t: int, focus: float | None) -> np.ndarray:
    """Saillance effective : observation + dopage distracteur + gain au foyer."""
    s = terrain.salience_obs[t].copy()
    for t0, item in terrain.distractor_events.items():
        if t0 <= t < t0 + DISTRACTOR_LEN:
            s[item] *= DISTRACTOR_FACTOR
    if focus is not None:
        captured = np.abs(circ_delta(terrain.positions[t], focus)) < FOCUS_WIDTH
        s[captured] *= gain_efficiency(t)
    return s


# --- Bras -------------------------------------------------------------------

@dataclass
class ArmResult:
    arm: str
    focus: np.ndarray              # [STEPS]
    error: np.ndarray              # e_t = |circ_delta(focus, position cible)|
    metrics: dict = field(default_factory=dict)


def run_reactive(terrain: Terrain) -> ArmResult:
    """Attention sans modele interne : argmax d'une EMA courte de la saillance."""
    ema = terrain.salience_true.copy()          # annonce initiale (choix a2)
    focus = np.zeros(STEPS)
    for t in range(STEPS):
        focus[t] = terrain.positions[t, int(np.argmax(ema))]   # allouer...
        s_eff = effective_salience(terrain, t, focus[t])
        ema = ema + EMA_REACTIVE * (s_eff - ema)               # ...puis apprendre
    error = np.abs(circ_delta(focus, terrain.positions[:, terrain.target_idx]))
    return ArmResult(arm="reactive", focus=focus, error=error)


def run_schema(terrain: Terrain, seed: int, distorted_d: float = 0.0,
               shuffled: bool = False) -> ArmResult:
    """Controleur a schema appauvri (quantifie, confiance, vitesse, prediction 1-pas).

    ``distorted_d > 0`` : l'encodage stocke ``pos_s + d`` et l'allocation lit le
    stockage (choix a3). ``shuffled`` : l'updater est alimente par une saillance
    permutee entre items (null).
    """
    arm = ("schema_shuffled" if shuffled
           else "schema_distorted" if distorted_d > 0 else "schema")
    rng = np.random.default_rng(seed + ARM_OFFSETS[arm])
    pos_s = terrain.positions[0, terrain.target_idx]      # annonce initiale (choix a2)
    vel_s = 0.0
    conf = 1.0
    focus = np.zeros(STEPS)
    stored_series = np.zeros(STEPS)
    pos_series = np.zeros(STEPS)
    obs_series = np.zeros(STEPS)
    pred_series = np.zeros(STEPS)
    conf_series = np.zeros(STEPS)
    prev = None
    prev_obs = None
    for t in range(STEPS):
        # 1. allouer : le stockage seul est quantifie (choix a4) ; l'updater
        # garde pos_s en pleine precision
        stored = circ_wrap(round((pos_s + distorted_d) / GRID) * GRID)
        focus[t] = stored
        prev = stored
        stored_series[t] = stored
        pos_series[t] = pos_s          # etat qui a genere le stockage alloue
        # 2. observer via la saillance (gain au foyer alloue)
        s_eff = effective_salience(terrain, t, prev)
        if shuffled:
            perm = rng.permutation(N_ITEMS)
            obs_pos = terrain.positions[t, perm[int(np.argmax(s_eff))]]
        else:
            obs_pos = terrain.positions[t, int(np.argmax(s_eff))]
        obs_series[t] = obs_pos
        pred_series[t] = pred = circ_wrap(pos_s + vel_s)
        innovation = circ_delta(obs_pos, pred)
        # 3. apprendre : vitesse = EMA alpha des accroissements OBSERVES (le
        # document scelle "EMA alpha = 0,1" ; coupler la vitesse au delta de
        # pos_new donnerait un gain effectif alpha^2 et une vitesse qui
        # n'apprendrait pas), position corrigee par la prediction 1-pas
        if t > 0:
            vel_s = vel_s + EMA_SCHEMA * (circ_delta(obs_pos, prev_obs) - vel_s)
        prev_obs = obs_pos
        conf = float(np.clip(conf + 0.1 * ((1.0 - min(abs(float(innovation)) / FOCUS_WIDTH, 1.0)) - conf), 0.0, 1.0))
        conf_series[t] = conf
        pos_s = circ_wrap(pred + EMA_SCHEMA * innovation)
    error = np.abs(circ_delta(focus, terrain.positions[:, terrain.target_idx]))
    res = ArmResult(arm=arm, focus=focus, error=error)
    # erreur de prediction 1-pas du schema : pred_t (etat de t-1) contre o_t,
    # puis baselines persistance / EMA-vitesse sur la meme serie d'observations
    pred_err = np.abs(circ_delta(pred_series, obs_series))
    persist_err = np.abs(circ_delta(obs_series[:-1], obs_series[1:]))
    vema = 0.0
    ema_vel_pred = np.zeros(STEPS - 1)
    for t in range(1, STEPS):
        ema_vel_pred[t - 1] = abs(float(circ_delta(obs_series[t - 1] + vema, obs_series[t])))
        vema = vema + EMA_SCHEMA * (float(circ_delta(obs_series[t], obs_series[t - 1])) - vema)
    res.metrics.update({
        "erreur_pred": float(pred_err.mean()),
        "baseline_persistance": float(persist_err.mean()),
        "baseline_ema_vitesse": float(ema_vel_pred.mean()),
        "erreur_rapport": float(np.abs(circ_delta(stored_series, pos_series)).mean()),
        "confiance_moyenne": float(conf_series.mean()),
    })
    return res


# --- Metriques (pre-enregistrement §3) --------------------------------------

def calm_mask() -> np.ndarray:
    m = np.ones(STEPS, dtype=bool)
    for t0 in tuple(JUMP_TIMES) + tuple(GAIN_DROP_TIMES) + tuple(DISTRACTOR_TIMES):
        lo, hi = max(0, t0 - CALM_BEFORE), min(STEPS, t0 + CALM_AFTER + 1)
        m[lo:hi] = False
    return m


def correction_steps(error: np.ndarray, t0: int) -> int:
    """Pas pour e < seuil pendant 5 consecutifs depuis t0, censure a 80."""
    for k in range(CORRECTION_CENSOR + 1):
        j = t0 + k
        if j + CORRECTION_HOLD > STEPS:
            break
        if np.all(error[j:j + CORRECTION_HOLD] < CORRECTION_THRESHOLD):
            return k
    return CORRECTION_CENSOR


def arm_metrics(res: ArmResult) -> dict:
    m = calm_mask()
    corr = [correction_steps(res.error, t0)
            for t0 in tuple(JUMP_TIMES) + tuple(GAIN_DROP_TIMES) + tuple(DISTRACTOR_TIMES)]
    ratios = []
    for times in (JUMP_TIMES, GAIN_DROP_TIMES, DISTRACTOR_TIMES):
        first = correction_steps(res.error, times[0])
        third = correction_steps(res.error, times[2])
        ratios.append(1.0 if first == 0 else third / first)
    out = {
        "stabilite": float(res.error[m].std()),
        "correction": float(np.mean(corr)),
        "correction_par_perturbation": corr,
        "adaptation": float(np.exp(np.mean(np.log(np.maximum(np.array(ratios), 1e-12))))),
    }
    out.update(res.metrics)
    return out


def run_seed(seed: int) -> dict:
    terrain = build_terrain(seed)
    arms = {"reactive": run_reactive(terrain)}
    arms["schema"] = run_schema(terrain, seed)
    arms["schema_shuffled"] = run_schema(terrain, seed, shuffled=True)
    for d in DISTORTED_DS:
        arms[f"schema_distorted_d{d:.3f}"] = run_schema(terrain, seed, distorted_d=d)
    return {"seed": seed, "arms": {k: arm_metrics(v) for k, v in arms.items()}}


# --- Predictions scellees (§4) et verdict -----------------------------------

def _band(per_seed: dict, predicate) -> int:
    return sum(1 for r in per_seed if predicate(r))


def evaluate_predictions(per_seed: list) -> dict:
    p = {}

    def g(r, arm, key):
        return r["arms"][arm][key]

    p["P1a"] = _band(per_seed, lambda r: g(r, "schema", "stabilite") <= 0.8 * g(r, "reactive", "stabilite")) >= 4
    p["P1b"] = _band(per_seed, lambda r: g(r, "schema", "correction") <= 0.75 * g(r, "reactive", "correction")) >= 4
    p["P1c"] = _band(per_seed, lambda r: g(r, "schema", "adaptation") <= 0.9 * g(r, "reactive", "adaptation")) >= 3
    p["P2"] = _band(per_seed, lambda r: g(r, "schema", "erreur_pred") <= 0.9 * min(
        g(r, "schema", "baseline_persistance"), g(r, "schema", "baseline_ema_vitesse"))) >= 4

    def p3a(r):
        ok = True
        for d in DISTORTED_DS:
            if not r["arms"][f"schema_distorted_d{d:.3f}"]["erreur_rapport"] >= 0.8 * d:
                ok = False
        return ok

    p["P3a"] = _band(per_seed, p3a) >= 4

    def p3b(r):
        d = FOCUS_WIDTH / 4.0
        dis = r["arms"][f"schema_distorted_d{d:.3f}"]
        return (dis["stabilite"] - g(r, "schema", "stabilite") <= 0.02
                and dis["correction"] - g(r, "schema", "correction") <= 12.0)

    p["P3b"] = _band(per_seed, p3b) >= 4
    p["P4"] = _band(per_seed, lambda r: (
        g(r, "schema_shuffled", "stabilite") >= 0.95 * g(r, "reactive", "stabilite")
        and g(r, "schema_shuffled", "correction") >= 0.95 * g(r, "reactive", "correction"))) >= 4
    p["P5"] = _band(per_seed, lambda r: (
        g(r, "reactive", "stabilite") <= 0.03 and g(r, "reactive", "correction") <= 10.0)) >= 4
    return p


def verdict(pred: dict) -> str:
    if pred["P5"]:
        return "NON_CONCLUSIF_INSTRUMENT"
    if all(pred[k] for k in ("P1a", "P1b", "P1c", "P2", "P3a", "P3b", "P4")):
        return "SUPPORTED"
    if (pred["P1a"] and pred["P1b"] and pred["P4"]
            and (pred["P2"] or (pred["P3a"] and pred["P3b"]))):
        return "PARTIAL"
    return "REFUTED"


# --- CLI --------------------------------------------------------------------

def _cli(argv=None) -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("pilot", help="pilote disjoint (graine 1000, hors verdict)")
    r.add_argument("--out", required=True)
    r = sub.add_parser("study", help="etude held-out (graines 0/1/7/42/99) + verdict")
    r.add_argument("--out", required=True)
    args = ap.parse_args(argv)

    if args.cmd == "pilot":
        result = run_seed(PILOT_SEED)
        react = result["arms"]["reactive"]
        # P5 est une bande 4/5 : sur le pilote (1 graine) on rend les
        # CONDITIONS par graine, jamais la bande
        p5_cond = {"stabilite_le_0.03": react["stabilite"] <= 0.03,
                   "correction_le_10": react["correction"] <= 10.0}
        payload = {"phase": "pilot", "seed": PILOT_SEED, "seed_result": result,
                   "note": "pilote disjoint, jamais compte dans un verdict",
                   "P5_conditions_reactif": p5_cond}
    else:
        per_seed = [run_seed(s) for s in STUDY_SEEDS]
        pred = evaluate_predictions(per_seed)
        payload = {"phase": "study", "seeds": list(STUDY_SEEDS), "per_seed": per_seed,
                   "predictions": pred, "verdict": verdict(pred),
                   "sealed": {"doc": "docs/ict/attention-schema-control-pre-enregistrement.md",
                              "commit": "fb74ec445", "sealed_at": "2026-10-30"}}
    Path(args.out).write_text(json.dumps(payload, ensure_ascii=False, indent=1), encoding="utf-8")
    if args.cmd == "pilot":
        arms = payload["seed_result"]["arms"]
        print(f"[pilot] reactive stabilite={arms['reactive']['stabilite']:.4f} "
              f"correction={arms['reactive']['correction']:.1f} | "
              f"schema stabilite={arms['schema']['stabilite']:.4f} "
              f"correction={arms['schema']['correction']:.1f} | "
              f"P5(reactif)={payload['P5_conditions_reactif']}")
    else:
        print(f"[study] verdict={payload['verdict']} predictions={payload['predictions']}")
    print(f"-> {args.out}")


if __name__ == "__main__":
    _cli()
