"""Realisation de pertinence -- engagement, traitement adverse et re-commitment.

Operationalisation bornee et declaree des passages de Jaeger, Riedl, Djedovic,
Vervaeke & Walsh (2024), Front. Psychol. 15:1362658 (CC-BY) :

- « opponent processing [...] the continual establishment of trade-offs and
  synergies between competing and complementary [...] behaviors and dynamics » ;
- « constantly play different approaches and strategies against each other in a
  process that iteratively evaluates progress toward a problem solution [...]
  dynamically switching back and forth [...] if the necessity arises » ;
- la pertinence comme probleme d'ENGAGEMENT (allocation de ressources a des
  buts concurrents), le traitement adverse etant une META-HEURISTIQUE.

Les predictions, bandes, bras, graines et le verdict sont fixes AVANT le code
dans docs/ict/vervaeke-insight-pre-enregistrement.md. La these de
non-formalisabilite de l'article n'est pas testee ici.
"""

from __future__ import annotations

import json
import math
from dataclasses import dataclass, field
from pathlib import Path

import numpy as np

N_CUES = 24
K_COMMIT = 6
N_STEPS = 240
SHIFTS = (80, 160)
REPLACED_AT_SHIFT = 5  # sur K_COMMIT : une seule indice ancien survit
DECAY = 0.9
NOISE = 0.2
THETA = 0.15
GRIP_WINDOW = 40
SWITCH_FOCUS = 15
STUDY_SEEDS = (0, 1, 7, 42, 99)
PILOT_SEED = 1000


# --------------------------------------------------------------------------
# Terrain
# --------------------------------------------------------------------------
def _draw_relevant(rng: np.random.Generator, n: int = N_CUES, k: int = K_COMMIT,
                   keep: np.ndarray | None = None,
                   n_keep: int = 1) -> np.ndarray:
    """Tire exactement k indices ; conserve n_keep elements de `keep`."""
    mask = np.zeros(n, dtype=bool)
    kept = np.empty(0, dtype=int)
    if keep is not None and n_keep > 0:
        kept = np.flatnonzero(keep)[:n_keep]
        mask[kept] = True
    pool = np.array([c for c in range(n) if not mask[c]])
    picks = rng.choice(pool, size=k - len(kept), replace=False)
    mask[picks] = True
    return mask


def terrain(seed: int, stationary: bool = False, n: int = N_CUES,
            k: int = K_COMMIT, n_steps: int = N_STEPS,
            shifts=SHIFTS) -> np.ndarray:
    """Tableau (n_steps, n) booleen : indices pertinents a chaque pas.

    Hors `stationary`, la pertinence bascule aux instants `shifts` : le nouvel
    ensemble conserve exactement un indice de l'ancien.
    """
    rng = np.random.default_rng(seed)
    state = _draw_relevant(rng, n, k)
    grid = np.zeros((n_steps, n), dtype=bool)
    change_at = set() if stationary else set(shifts)
    for t in range(n_steps):
        if t in change_at:
            state = _draw_relevant(rng, n, k, keep=state, n_keep=k - REPLACED_AT_SHIFT)
        grid[t] = state
    return grid


# --------------------------------------------------------------------------
# Estimation locale (l'agent ne voit que le signal bruite de ses engagements)
# --------------------------------------------------------------------------
@dataclass
class ValueTable:
    """Estimation par indice du succes attendu, oubli exponentiel."""

    n: int = N_CUES
    value: np.ndarray = field(default_factory=lambda: np.full(N_CUES, 0.5))
    weight: np.ndarray = field(default_factory=lambda: np.zeros(N_CUES))

    def observe(self, cues, successes) -> None:
        self.value *= DECAY
        self.weight *= DECAY
        for c, s in zip(cues, successes):
            self.value[c] += (1.0 - DECAY) * (1.0 if s else 0.0)
            self.weight[c] += (1.0 - DECAY)
        # renormalise vers un a priori neutre quand l'information est ancienne
        self.value = np.clip(self.value + (1.0 - DECAY) * 0.5 * (self.weight < 1e-9), 0.0, 1.0)

    def est(self, c: int) -> float:
        w = self.weight[c]
        if w <= 1e-9:
            return 0.5
        return float(self.value[c] / w)

    def margins(self, chosen: np.ndarray) -> tuple[float, int, int]:
        """Meilleur gain local : (marge, indice a sortir, indice a entrer)."""
        unchosen = [c for c in range(self.n) if c not in set(chosen.tolist())]
        if not unchosen:
            return 0.0, -1, -1
        out_c = min(chosen.tolist(), key=self.est)
        in_c = max(unchosen, key=self.est)
        return self.est(in_c) - self.est(out_c), out_c, in_c

    def dispersion(self) -> float:
        vals = [self.est(c) for c in range(self.n)]
        return float(np.std(vals))


# --------------------------------------------------------------------------
# Agent
# --------------------------------------------------------------------------
@dataclass
class Agent:
    seed: int
    arm: str  # opponent | static | sham_rate | stationary
    rng: np.random.Generator = field(init=False)
    table: ValueTable = field(default_factory=ValueTable)
    chosen: np.ndarray = field(init=False)
    credit_exploit: float = 0.5
    credit_explore: float = 0.5
    # deux evenements distincts, mesures separement : un RE-COMMITMENT est un
    # changement de STRATEGIE (exploit <-> explore), pas un changement d'ensemble.
    switches: list = field(default_factory=list)
    set_changes: list = field(default_factory=list)
    explore_steps: int = 0
    last_advice: str | None = None
    _sham_explore_p: float = 0.0
    _last_observed: float = 0.5

    def __post_init__(self) -> None:
        self.rng = np.random.default_rng(self.seed + 17)
        self.chosen = self.rng.choice(N_CUES, size=K_COMMIT, replace=False)

    # -- decisions ---------------------------------------------------------
    def _exploit_step(self) -> np.ndarray:
        margin, out_c, in_c = self.table.margins(self.chosen)
        if out_c >= 0 and in_c >= 0 and margin > 0.0:
            new = self.chosen.copy()
            new[list(new).index(out_c)] = in_c
            return new
        return self.chosen.copy()

    def _explore_step(self) -> np.ndarray:
        return self.rng.choice(N_CUES, size=K_COMMIT, replace=False)

    def _should_advice(self, arm: str, t: int) -> str:
        if arm == "static":
            return "exploit" if self.rng.random() < 0.8 else "explore"
        if arm == "sham_rate":
            # meme BUDGET d'exploration que le bras adverse, instants tires au hasard
            return "explore" if self.rng.random() < self._sham_explore_p else "exploit"
        # opponent : chaque heuristique porte le score REALISE pendant son usage
        # (source, l.270 : scenarios « played against each other while monitoring
        # the streams of discrepancies they generate ») ; l'inutilisee regresse
        # vers le neutre. L'incumbent cede quand le challenger le depasse de THETA.
        incumbent = "exploit" if self.credit_exploit >= self.credit_explore else "explore"
        challenger = "explore" if incumbent == "exploit" else "exploit"
        if self._score(challenger) > self._score(incumbent) + THETA:
            return challenger
        return incumbent

    def _score(self, which: str) -> float:
        return self.credit_exploit if which == "exploit" else self.credit_explore

    def step(self, t: int, relevant: np.ndarray):
        advice = self._should_advice(self.arm, t)
        if advice == "explore":
            self.explore_steps += 1
        if self.last_advice is not None and advice != self.last_advice:
            self.switches.append(t)
        self.last_advice = advice
        previous = self.chosen
        proposal = self._explore_step() if advice == "explore" else self._exploit_step()
        self.chosen = proposal
        if not np.array_equal(previous, proposal):
            self.set_changes.append(t)
        # signal bruite, uniquement sur les indices engages
        truth = relevant[self.chosen].astype(float)
        successes = (self.rng.random(K_COMMIT) > NOISE) * truth
        self.table.observe(self.chosen.tolist(), successes.tolist())
        observed = float(np.mean(successes))
        # scores REALISES par heuristique, mis a jour pendant son usage ;
        # l'inutilisee regresse lentement vers le neutre (0.5).
        alpha = 0.2
        if advice == "exploit":
            self.credit_exploit = (1 - alpha) * self.credit_exploit + alpha * observed
            self.credit_explore += (0.5 - self.credit_explore) * 0.02
        else:
            self.credit_explore = (1 - alpha) * self.credit_explore + alpha * observed
            self.credit_exploit += (0.5 - self.credit_exploit) * 0.02
        self._last_observed = observed
        return observed, bool(np.array_equal(previous, proposal))


# --------------------------------------------------------------------------
# Execution
# --------------------------------------------------------------------------
def run(seed: int, arm: str, stationary: bool = False) -> dict:
    grid = terrain(seed, stationary=stationary)
    agent = Agent(seed=seed, arm="opponent" if arm == "stationary" else arm)
    true_grip = np.zeros(N_STEPS)
    rewards = np.zeros(N_STEPS)
    for t in range(N_STEPS):
        observed, _ = agent.step(t, grid[t])
        true_grip[t] = float(np.mean(grid[t][agent.chosen]))
        rewards[t] = observed
    switches = list(agent.switches)
    return {
        "seed": seed,
        "arm": arm,
        "stationary": stationary,
        "grip": float(np.mean(true_grip[-GRIP_WINDOW:])),
        "grip_series": true_grip.tolist(),
        "switches": switches,
        "switch_count": len(switches),
        "set_changes": len(agent.set_changes),
        "explore_steps": agent.explore_steps,
        "impasse": impasse_profile(true_grip, switches),
    }


def impasse_profile(grip_series: np.ndarray, switches: list) -> dict:
    """Longueur de la suite sans amelioration avant chaque bascule + gains."""
    best = grip_series[0]
    last_gain = 0
    flat = 0
    profile = []
    for t in range(1, len(grip_series)):
        if grip_series[t] > best + 1e-12:
            best = grip_series[t]
            last_gain = t
            flat = 0
        else:
            flat += 1
        if t in switches:
            before = grip_series[max(0, t - 10):t]
            after = grip_series[t:t + 10]
            gain = float(np.mean(after) - np.mean(before)) if len(before) and len(after) else 0.0
            profile.append({"t": t, "flat": flat, "gain": gain})
            flat = 0
    return profile


def concentration(res: dict) -> float:
    """Part des bascules dans les SWITCH_FOCUS pas suivant un shift / part du temps."""
    shifts = [] if res["stationary"] else list(SHIFTS)
    if not shifts or not res["switches"]:
        return 0.0
    in_window = sum(1 for s in res["switches"]
                    if any(0 <= s - sh < SWITCH_FOCUS for sh in shifts))
    time_share = len({t for t in range(N_STEPS)
                      if any(0 <= t - sh < SWITCH_FOCUS for sh in shifts)}) / N_STEPS
    return float((in_window / len(res["switches"])) / time_share) if time_share else 0.0


def switch_rate_after_shifts(res: dict) -> dict:
    after = [s for s in res["switches"]
             if any(0 <= s - sh < SWITCH_FOCUS for sh in SHIFTS)]
    outside = [s for s in res["switches"]
               if not any(0 <= s - sh < SWITCH_FOCUS for sh in SHIFTS)]
    n_after = len({t for t in range(N_STEPS) if any(0 <= t - sh < SWITCH_FOCUS for sh in SHIFTS)})
    n_out = N_STEPS - n_after
    return {"after": len(after) / max(1, n_after), "outside": len(outside) / max(1, n_out)}


# --------------------------------------------------------------------------
# Evaluation et verdict
# --------------------------------------------------------------------------
def evaluate(seeds=STUDY_SEEDS) -> dict:
    per_seed = {}
    for seed in seeds:
        arms = {a: run(seed, a) for a in ("opponent", "static")}
        arms["sham_rate"] = run_matched_sham(seed)
        arms["stationary"] = {
            "opponent": run(seed, "opponent", stationary=True),
            "static": run(seed, "static", stationary=True),
        }
        per_seed[str(seed)] = {
            "grip": {k: (v["grip"] if isinstance(v, dict) and "grip" in v else None)
                     for k, v in arms.items() if k != "stationary"},
            "grip_stationary": {k: v["grip"] for k, v in arms["stationary"].items()},
            "explore_share_stationary": arms["stationary"]["opponent"]["explore_steps"] / N_STEPS,
            "explore_share_static": 0.2,
            "concentration": concentration(arms["opponent"]),
            "rate_ratio": (lambda r: r["after"] / max(1e-9, r["outside"]))(
                switch_rate_after_shifts(arms["opponent"])),
            "impasse_ok": impasse_share(arms["opponent"]),
            "switch_count": arms["opponent"]["switch_count"],
        }
    return {"per_seed": per_seed, "predictions": verdict(per_seed)}


def run_matched_sham(seed: int) -> dict:
    """Sham apparie en BUDGET : meme part de pas d'exploration que l'adverse,
    instants tires au hasard (aucune evaluation)."""
    ref = run(seed, "opponent")
    grid = terrain(seed)
    agent = Agent(seed=seed, arm="sham_rate")
    agent._sham_explore_p = ref["explore_steps"] / N_STEPS
    true_grip = np.zeros(N_STEPS)
    for t in range(N_STEPS):
        agent.step(t, grid[t])
        true_grip[t] = float(np.mean(grid[t][agent.chosen]))
    return {"seed": seed, "arm": "sham_rate", "stationary": False,
            "grip": float(np.mean(true_grip[-GRIP_WINDOW:])),
            "grip_series": true_grip.tolist(), "switches": list(agent.switches),
            "switch_count": len(agent.switches),
            "set_changes": len(agent.set_changes),
            "explore_steps": agent.explore_steps,
            "impasse": impasse_profile(true_grip, list(agent.switches))}


def impasse_share(res: dict) -> float:
    useful = [p for p in res["impasse"] if p["gain"] >= 0.02]
    if not useful:
        return 0.0
    return sum(1 for p in useful if p["flat"] >= 3) / len(useful)


def verdict(per_seed: dict) -> dict:
    seeds = list(per_seed)
    p1 = all(per_seed[s]["grip"]["opponent"] - per_seed[s]["grip"]["static"] >= 0.05 for s in seeds)
    p2 = all(per_seed[s]["grip"]["opponent"] - per_seed[s]["grip"]["sham_rate"] >= 0.03 for s in seeds)
    conc = float(np.median([per_seed[s]["concentration"] for s in seeds]))
    ratio = float(np.median([per_seed[s]["rate_ratio"] for s in seeds]))
    p3 = conc >= 2.0 and ratio >= 2.0
    p4 = float(np.median([per_seed[s]["impasse_ok"] for s in seeds])) >= 0.60
    # P5 v2 (pre-enregistrement §5) : l'adverse reduit son exploration sous la
    # moitie de celle du melange fixe (0,20) en terrain stationnaire.
    p5 = all(per_seed[s]["explore_share_stationary"] <= 0.10 for s in seeds)
    if p1 and p2 and p3 and p4 and p5:
        v = "SUPPORTED"
    elif p1 and p2 and sum((p3, p4, p5)) >= 2:
        v = "PARTIAL"
    else:
        v = "REFUTED"
    return {"P1": p1, "P2": p2, "P3": p3, "P4": p4, "P5": p5,
            "concentration_median": conc, "rate_ratio_median": ratio,
            "verdict": v}


def main(seeds=STUDY_SEEDS, out: str | None = None) -> dict:
    result = evaluate(seeds)
    payload = json.dumps(result, indent=2, sort_keys=True, ensure_ascii=False)
    if out is None:
        out = str(Path(__file__).parent / "results" / "vervaeke_insight_results.json")
    Path(out).parent.mkdir(parents=True, exist_ok=True)
    Path(out).write_text(payload + "\n", encoding="utf-8")
    print(payload)
    return result


if __name__ == "__main__":
    main()
