"""Module J1 #7291 (strate 6) : banc S1 « adoption polyconvictionnelle ».

Opérationnalise le pré-enregistrement J1 (issue #7291, c.6007595872) : substrat S1
de la spec capstone « L'altérité est-elle un budget ? ». La mesure clause 1
(diversité des points de consigne, ICT-9) y est manipulée EXOGÈNEMENT par le
nombre k de conventions défendues dans la population, et le budget d'état
B(r, tau) (ICT-18b, ``ict.reversibility_budget.state_space_budget``) y est
mesuré sur l'état agrégé — la corrélation A <-> B y est TESTÉE, pas illustrée
(clause 2), et la signature temporelle du contre-régime y est mesurable
(clause 3 : monoculture robuste à court terme, queue lourde au-delà).

Modèle (extension d'``ict.collective_adoption.AdoptionGame``, noyau Roth-Erev
repris tel quel — aucune réimplémentation) :

- ``n_states = 4`` ; alphabet de conventions FIXE de ``n_conventions = 8``
  bijections (C1 = identité, C2..C8 par ordre lexicographique des
  permutations), identique pour tous les bras.
- Population de ``n_agents = 48`` : ``n_pinned = 32`` agents épinglés
  (``instigator_strength``, n'apprennent pas) répartis à parts égales entre
  les k conventions actives du bras (k in {1, 2, 4, 8}), plus 16 flotteurs
  naïfs (Roth-Erev, Q uniforme). Le budget total de rencontres est identique
  pour tous les bras (mêmes tours, même appariement uniforme sur toute la
  population — les rencontres inter-groupes sont la vie du banc).
- État agrégé ``x(t)`` in [0, 1]^8 : fraction des agents dont la convention
  dominante égale C_j (les agents dont la politique ne correspond à aucune
  bijection de l'alphabet ne comptent dans aucune composante — pendant le
  transitoire la somme peut être < 1).
- Perturbation (réalisation d'un état x' dans la boule L2 de rayon r autour
  de l'ancre) : réassignation gloutonne des conventions depuis
  l'affectation d'ancre (déplacement minimal d'agents), Q re-synthétisés au
  motif fort/faible de l'instrument, épinglés inclus (« la secousse
  réassigne les causes ; la structure d'engagement demeure : les épinglés
  n'apprennent pas »). Granularité 1/48.
- Dynamique : chaque pas de ``step_fn`` avance la VRAIE configuration d'une
  fenêtre de ``window`` tours (aucune re-synthèse intermédiaire) ;
  l'adaptateur ``make_step_fn`` présente ça à ``state_space_budget``
  (synthèse au premier appel seulement).

Le pré-enregistrement fixe : T_train=4000 (anneal_to=0.1), window=50, tau=15,
consigne_radius=0.10, grille de rayons {0.05, 0.10, 0.15, 0.25, 0.35, 0.50},
20 seeds/bras (seeds 0..19), n_samples=40.

numpy CPU. Réutilise ``ict.collective_adoption.AdoptionGame`` et
``ict.reversibility_budget`` (organes existants, zéro duplication).
"""

from __future__ import annotations

import json
from itertools import permutations
from typing import Callable, Dict, List, Optional, Sequence, Tuple

import numpy as np

from ict.collective_adoption import AdoptionGame
from ict.reversibility_budget import state_space_budget


def convention_alphabet(n_states: int = 4, n_conventions: int = 8) -> np.ndarray:
    """Alphabet FIXE de ``n_conventions`` bijections sur ``n_states`` états.

    C1 = identité ; les suivantes sont les bijections distinctes de l'identité
    dans l'ordre lexicographique des permutations (déterministe, reproductible
    sans seed). Retour : tableau ``(n_conventions, 2, n_states)`` où
    ``[c, 0, s]`` = signal de la convention c pour l'état s et ``[c, 1, m]``
    = action pour le signal m (bijection : même permutation aux deux rôles).
    """
    perms = sorted(permutations(range(n_states)))
    ident = tuple(range(n_states))
    ordered = [ident] + [p for p in perms if p != ident]
    if len(ordered) < n_conventions:
        raise ValueError(
            f"alphabet : {n_conventions} conventions exigent n_states! >= "
            f"{n_conventions} (reçu n_states={n_states}, soit {len(ordered)} bijections)"
        )
    alphabet = np.empty((n_conventions, 2, n_states), dtype=int)
    for c, perm in enumerate(ordered[:n_conventions]):
        alphabet[c, 0, :] = perm  # signal_par_etat
        alphabet[c, 1, :] = perm  # action_par_signal
    return alphabet


class PolyAdoptionGame(AdoptionGame):
    """Banc S1 : population épinglée sur k conventions + flotteurs Roth-Erev.

    Hérite du noyau d'``AdoptionGame`` (appariement aléatoire, softmax,
    renforcement, épinglage par masque ``is_instigator``). Les différences :

    - les agents épinglés sont répartis en k GROUPES, chacun sur une
      convention distincte de l'alphabet fixe (bras k = 1 : monoculture) ;
    - l'état agrégé est le vecteur d'adoption sur l'alphabet entier
      (dimension 8, fixe inter-bras) ;
    - ``synthesize`` réalise un état perturbé x' (réassignation gloutonne
      minimale depuis l'affectation d'ancre, épinglés inclus) ;
    - ``advance_windows`` avance la VRAIE configuration (pas de re-synthèse).
    """

    def __init__(
        self,
        k_conventions: int,
        *,
        n_agents: int = 48,
        n_pinned: int = 32,
        n_conventions: int = 8,
        instigator_strength: float = 10.0,
        temperature: float = 0.5,
        initial_q: float = 1.0,
        rng: Optional[np.random.Generator] = None,
    ) -> None:
        if n_agents < 2:
            raise ValueError(f"n_agents >= 2 requis (reçu {n_agents}).")
        if n_pinned >= n_agents:
            raise ValueError("il faut des flotteurs : n_pinned < n_agents.")
        if k_conventions < 1 or k_conventions > n_conventions:
            raise ValueError(
                f"k_conventions in [1, {n_conventions}] requis (reçu {k_conventions})."
            )
        if n_pinned % k_conventions != 0:
            raise ValueError(
                f"n_pinned={n_pinned} doit être divisible par k={k_conventions} "
                "(répartition égale des défenseurs)."
            )
        super().__init__(
            n_agents=n_agents,
            n_states=4,
            instigator_fraction=n_pinned / n_agents,
            instigator_strength=instigator_strength,
            temperature=temperature,
            initial_q=initial_q,
            pin_instigators=True,
            rng=rng if rng is not None else np.random.default_rng(),
        )
        self.k_conventions = int(k_conventions)
        self.n_pinned = int(n_pinned)
        self.n_floaters = n_agents - n_pinned
        self.alphabet = convention_alphabet(n_states=4, n_conventions=n_conventions)
        self.n_conventions = int(n_conventions)
        # Convention dominante courante de chaque agent (-1 = aucune).
        self.agent_convention = np.full(n_agents, -1, dtype=int)
        self._synthesize_groups()

    # ------------------------------------------------------------------ #
    # Constitution du banc                                                #
    # ------------------------------------------------------------------ #

    def _pin_agent_to(self, agent: int, convention: int) -> None:
        """Épingler l'agent ``agent`` sur la convention ``convention`` de l'alphabet."""
        strong = self.instigator_strength
        weak = self.initial_q / max(strong, 1.0)
        self.Q_s[agent, :, :] = weak
        self.Q_r[agent, :, :] = weak
        for s in range(self.n_states):
            self.Q_s[agent, s, self.alphabet[convention, 0, s]] = strong
        for m in range(self.n_signals):
            self.Q_r[agent, m, self.alphabet[convention, 1, m]] = strong

    def _synthesize_groups(self) -> None:
        """Répartir les épinglés en k groupes égaux sur les conventions actives.

        Groupe g = agents [g*n_pinned/k, (g+1)*n_pinned/k) — affectation
        déterministe par blocs consécutifs, reproductible sans tirage.
        Les flotteurs (indices [n_pinned, n_agents)) restent naïfs.
        """
        per_group = self.n_pinned // self.k_conventions
        self.is_instigator[:] = False
        self.is_instigator[: self.n_pinned] = True
        self.n_instigators = self.n_pinned
        self.n_naive = self.n_floaters
        for g in range(self.k_conventions):
            for a in range(g * per_group, (g + 1) * per_group):
                self._pin_agent_to(a, g)
        for a in range(self.n_pinned, self.n_agents):
            self.Q_s[a, :, :] = self.initial_q
            self.Q_r[a, :, :] = self.initial_q
        self.joint_state_signal = np.zeros(
            (self.n_agents, self.n_states, self.n_signals), dtype=float
        )
        self.success_history = []
        self._recompute_dominants()

    # ------------------------------------------------------------------ #
    # Mesures d'état                                                      #
    # ------------------------------------------------------------------ #

    def dominant_convention(self, agent: int) -> int:
        """Convention de l'alphabet correspondant à la politique dominante (-1 si aucune)."""
        sig = [int(np.argmax(self.Q_s[agent, s])) for s in range(self.n_states)]
        act = [int(np.argmax(self.Q_r[agent, m])) for m in range(self.n_signals)]
        for c in range(self.n_conventions):
            if sig == list(self.alphabet[c, 0]) and act == list(self.alphabet[c, 1]):
                return c
        return -1

    def _recompute_dominants(self) -> None:
        for a in range(self.n_agents):
            self.agent_convention[a] = self.dominant_convention(a)

    def adoption_vector(self) -> np.ndarray:
        """État agrégé x in [0,1]^8 : fraction d'agents par convention dominante."""
        counts = np.zeros(self.n_conventions)
        for c in self.agent_convention:
            if c >= 0:
                counts[c] += 1.0
        return counts / self.n_agents

    # ------------------------------------------------------------------ #
    # Dynamique                                                           #
    # ------------------------------------------------------------------ #

    def advance_windows(self, n_windows: int, window: int = 50) -> List[np.ndarray]:
        """Avancer la VRAIE configuration de ``n_windows`` fenêtres de ``window`` tours.

        Retourne la trajectoire des vecteurs d'adoption (un point par fenêtre).
        """
        trajectory: List[np.ndarray] = []
        for _ in range(n_windows):
            for _ in range(window):
                self.play_round(reinforce=True)
            self._recompute_dominants()
            trajectory.append(self.adoption_vector())
        return trajectory

    # ------------------------------------------------------------------ #
    # Perturbation : réalisation d'un état x'                             #
    # ------------------------------------------------------------------ #

    def synthesize(self, x_target: np.ndarray, *, anchor_assign: np.ndarray) -> None:
        """Réaliser l'état ``x_target`` par réassignation gloutonne minimale.

        Part de l'affectation d'ancre ``anchor_assign`` (convention par agent)
        et déplace le moins d'agents possible pour atteindre les effectifs
        cibles ``round(x_target * n_agents)`` : les excédents comblent les
        déficits, par ordre de conventions croissant ; les agents sans
        convention (-1) servent de réservoir final pour les déficits
        résiduels (la secousse conscrit les désorganisés). Les Q sont
        re-synthétisés au motif fort/faible pour tous les agents réassignés
        (épinglés comme flotteurs — la secousse réassigne les causes) ; les
        règles d'apprentissage restent celles du banc (les épinglés
        n'apprennent pas).

        Déterministe (aucun tirage) : x' identique -> configuration identique.
        """
        x_target = np.asarray(x_target, dtype=float).ravel()
        if x_target.size != self.n_conventions:
            raise ValueError(f"x_target de dimension {self.n_conventions} requis.")
        counts_target = np.round(x_target * self.n_agents).astype(int)
        assign = np.asarray(anchor_assign, dtype=int).copy()
        counts_now = np.zeros(self.n_conventions, dtype=int)
        for c in assign:
            if c >= 0:
                counts_now[c] += 1
        for c_def in range(self.n_conventions):
            need = int(counts_target[c_def] - counts_now[c_def])
            if need <= 0:
                continue
            for c_sur in range(self.n_conventions):
                if need <= 0:
                    break
                surplus = int(counts_now[c_sur] - counts_target[c_sur])
                if surplus <= 0:
                    continue
                take = min(need, surplus)
                moved = 0
                for a in range(self.n_agents):
                    if moved >= take:
                        break
                    if assign[a] == c_sur:
                        assign[a] = c_def
                        moved += 1
                counts_now[c_sur] -= take
                counts_now[c_def] += take
                need -= take
            if need > 0:
                # Réservoir : agents sans convention (-1), ordre d'indice.
                for a in range(self.n_agents):
                    if need <= 0:
                        break
                    if assign[a] < 0:
                        assign[a] = c_def
                        need -= 1
                counts_now[c_def] = int(np.sum(assign == c_def))
        for a in range(self.n_agents):
            c = assign[a]
            if c >= 0:
                self._pin_agent_to(a, int(c))
            else:
                self.Q_s[a, :, :] = self.initial_q
                self.Q_r[a, :, :] = self.initial_q
        self._recompute_dominants()

    # ------------------------------------------------------------------ #
    # Adaptateur vers l'organe budget (ICT-18b)                           #
    # ------------------------------------------------------------------ #

    def make_step_fn(self, anchor_assign: np.ndarray, window: int = 50) -> Callable[[np.ndarray], np.ndarray]:
        """Adaptateur ``step_fn`` pour ``state_space_budget`` / ``budget_curve``.

        L'organe itère ``x = step_fn(x)`` SUR PLUSIEURS ÉCHANTILLONS avec la
        MÊME fonction : l'adaptateur doit donc reconnaître un NOUVEAU point
        initial. Contrat : si l'argument entrant diffère de la dernière sortie
        (au-delà de 1e-9), c'est un nouveau point perturbé — jeu enfant neuf,
        synthèse depuis lui ; sinon c'est le rebouclage de l'organe (l'argument
        EST la sortie précédente) — on avance la VRAIE configuration d'une
        fenêtre de ``window`` tours, sans re-synthèse intermédiaire. Le bruit
        de chaque enfant dérive du rng du banc (déterministe, ordre d'appel
        fixe).

        Cas limite documenté : un point initial exactement égal à la sortie
        précédente (mesure nulle) poursuivrait le jeu en cours.
        """
        holder: Dict[str, "PolyAdoptionGame"] = {}
        last_out: Dict[str, Optional[np.ndarray]] = {"v": None}

        def step_fn(x: np.ndarray) -> np.ndarray:
            xa = np.asarray(x, dtype=float).ravel()
            if last_out["v"] is None or not np.allclose(xa, last_out["v"], atol=1e-9):
                child = PolyAdoptionGame(
                    self.k_conventions,
                    n_agents=self.n_agents,
                    n_pinned=self.n_pinned,
                    n_conventions=self.n_conventions,
                    instigator_strength=self.instigator_strength,
                    temperature=self.temperature,
                    initial_q=self.initial_q,
                    rng=np.random.default_rng(int(self.rng.integers(0, 2**63 - 1))),
                )
                child.synthesize(xa, anchor_assign=anchor_assign)
                holder["game"] = child
            game = holder["game"]
            for _ in range(window):
                game.play_round(reinforce=True)
            game._recompute_dominants()
            out = game.adoption_vector()
            last_out["v"] = out
            return out

        return step_fn


def anchor_state(
    game: PolyAdoptionGame,
    n_rounds: int = 4000,
    anneal_to: float = 0.1,
) -> Tuple[np.ndarray, np.ndarray]:
    """Entraîner le banc et retourner ``(anchor_vector, anchor_assign)``.

    L'ancre est l'état agrégé après ``n_rounds`` tours (recuit de température
    vers ``anneal_to``) ; l'affectation d'ancre sert de point de départ aux
    réassignations de perturbation.
    """
    game.train(n_rounds, anneal_to=anneal_to)
    game._recompute_dominants()
    return game.adoption_vector(), game.agent_convention.copy()


def effective_alterity(anchor: np.ndarray, mass_threshold: float = 0.05) -> Dict[str, float]:
    """Mesures clause 1 sur l'ancre : A(Sigma) = exp(H) (primaire) + bassins (secondaire)."""
    p = np.asarray(anchor, dtype=float)
    p = p[p > 0]
    p = p / p.sum()
    h = -float(np.sum(p * np.log(p)))
    return {
        "A_expH": float(np.exp(h)),
        "basins": int(np.sum(np.asarray(anchor) >= mass_threshold)),
    }


# --------------------------------------------------------------------------- #
#  Gate P0 (pre-reg J1) : reproduction des instruments AVANT toute mesure      #
# --------------------------------------------------------------------------- #
#
#  P0.a = suites de tests des instruments vertes au SHA de tete (pytest, hors
#         de cette fonction) : test_reversibility_budget, test_argumentation,
#         tests/test_collective_adoption.
#  P0.b = reproduction seedee de la cellule [5] d'ICT-18b (rng=0) : valeurs
#         exactes 1.0 / 0.0 / 0.0 / 1.5 -> tolerance 1e-6.
#  P0.c = reproduction seedee de la cellule [5] d'ICT-28 (seed=0) :
#         critical_threshold_test(24, 3, n_seeds=3) -> tolerance 5e-4
#         (granularite d'impression %.3f du temoin committé ; la reproduction
#         exacte est typiquement plus proche que la tolerance).


def p0_gate() -> Dict[str, object]:
    """Exécuter les jambes P0.b/P0.c et retourner le verdict par jambe (booléens)."""
    import json as _json
    from pathlib import Path as _Path

    from ict import collective_adoption as ca
    from ict import reversibility_budget as rb

    here = _Path(__file__).resolve().parent
    verdict: Dict[str, object] = {}

    # --- P0.b : ICT-18b cellule [5], rng=0 -------------------------------- #
    nb18 = _json.loads(
        (here.parent / "ICT-18b-ReversibilityBudget-Python.ipynb").read_text(encoding="utf-8")
    )
    rng = np.random.default_rng(0)
    b_stable = rb.state_space_budget(
        step_fn=lambda x: 0.5 * x,
        anchor=np.array([0.0]),
        radius=1.0,
        tau=8,
        n_samples=200,
        rng=rng,
        consigne_radius=0.1,
    )
    b_lost = rb.state_space_budget(
        step_fn=lambda x: x + 1.0,
        anchor=np.array([0.0]),
        radius=0.5,
        tau=5,
        n_samples=200,
        rng=rng,
        consigne_radius=0.2,
    )
    p_sym = np.array([[0.5, 0.5], [0.5, 0.5]])
    pi_sym = np.array([0.5, 0.5])
    p_cycle = np.array([[0.0, 1.0, 0.0], [0.0, 0.0, 1.0], [1.0, 0.0, 0.0]])
    pi_cycle = np.full(3, 1.0 / 3.0)
    w_sym = rb.work_budget(p_sym, pi_sym)
    w_cycle = rb.work_budget(p_cycle, pi_cycle)
    committed18 = (1.0, 0.0, 0.0, 1.5)  # sorties committes de la cellule [5]
    verdict["P0.b"] = {
        "recomputed": [float(b_stable), float(b_lost), float(w_sym), float(w_cycle)],
        "committed": list(committed18),
        "ok": bool(
            abs(b_stable - 1.0) <= 1e-6
            and abs(b_lost - 0.0) <= 1e-6
            and abs(w_sym - 0.0) <= 1e-6
            and abs(w_cycle - 1.5) <= 1e-6
        ),
        "cellule": "ICT-18b [5]",
        "notebook_cells": len(nb18["cells"]),
    }

    # --- P0.c : ICT-28 cellule [5], seed=0 -------------------------------- #
    v = ca.critical_threshold_test(n_agents=24, n_states=3, n_seeds=3, seed=0)
    committed28 = {
        "adoption_at_low_rho": 0.000,
        "adoption_at_high_rho": 1.000,
        "max_jump": 0.472,
        "rho_c": 0.425,
    }
    ok_c = all(abs(float(v[key]) - ref) <= 5e-4 for key, ref in committed28.items())
    verdict["P0.c"] = {
        "recomputed": {key: float(v[key]) for key in committed28},
        "committed": committed28,
        "ok": bool(ok_c),
        "cellule": "ICT-28 [5]",
    }
    verdict["P0.ok"] = bool(verdict["P0.b"]["ok"] and verdict["P0.c"]["ok"])
    return verdict


# --------------------------------------------------------------------------- #
#  Sweep J1 : courbes de budget par bras x seed, JSONL reprenable              #
# --------------------------------------------------------------------------- #

RADII = (0.05, 0.10, 0.15, 0.25, 0.35, 0.50)


def s1_seed_curve(
    k: int,
    seed: int,
    *,
    radii: Sequence[float] = RADII,
    n_rounds: int = 4000,
    anneal_to: float = 0.1,
    window: int = 50,
    tau: int = 15,
    n_samples: int = 40,
    consigne_radius: float = 0.10,
) -> Dict[str, object]:
    """Un (bras k, seed) : ancre, mesures clause 1, courbe B(r) complete.

    Retourne un enregistrement JSON-serialisable (une ligne du JSONL du sweep).
    """
    game = PolyAdoptionGame(k, rng=np.random.default_rng(seed))
    anchor, assign = anchor_state(game, n_rounds=n_rounds, anneal_to=anneal_to)
    alter = effective_alterity(anchor)
    curve = []
    for r in radii:
        # Un adaptateur neuf par rayon (le jeu enfant derive son bruit du rng
        # du banc, avance a chaque make_step_fn -> deterministe, ordre fixe).
        step = game.make_step_fn(assign, window=window)
        b = state_space_budget(
            step,
            anchor,
            radius=float(r),
            tau=tau,
            n_samples=n_samples,
            rng=np.random.default_rng(10_000 + seed),
            consigne_radius=consigne_radius,
            bounds=(0.0, 1.0),
        )
        curve.append(float(b))
    return {
        "k": int(k),
        "seed": int(seed),
        "anchor": [float(a) for a in anchor],
        "A_expH": alter["A_expH"],
        "basins": int(alter["basins"]),
        "radii": [float(r) for r in radii],
        "B": curve,
        "params": {
            "n_rounds": n_rounds,
            "window": window,
            "tau": tau,
            "n_samples": n_samples,
            "consigne_radius": consigne_radius,
        },
    }


def run_sweep(
    out_path: str,
    *,
    arms: Sequence[int] = (1, 2, 4, 8),
    seeds: Sequence[int] = tuple(range(20)),
    radii: Sequence[float] = RADII,
) -> Dict[str, object]:
    """Sweep J1 reprenable : une ligne JSONL par (bras, seed), skip des deja-faits.

    Verifie le gate P0 AVANT la premiere ecriture (pre-reg : aucune mesure
    neuve tant que P0 n'est pas vert ; si le fichier existe deja non vide,
    P0 est repute passe par la session precedente).
    """
    from pathlib import Path as _Path

    out = _Path(out_path)
    done: set = set()
    if out.exists() and out.stat().st_size > 0:
        for line in out.read_text(encoding="utf-8").splitlines():
            if line.strip():
                rec = json.loads(line)
                done.add((rec["k"], rec["seed"]))
    else:
        gate = p0_gate()
        if not gate["P0.ok"]:
            return {"error": "P0 gate FAILED", "gate": gate}
        out.parent.mkdir(parents=True, exist_ok=True)

    n_new = 0
    with out.open("a", encoding="utf-8") as fh:
        for k in arms:
            for seed in seeds:
                if (k, seed) in done:
                    continue
                rec = s1_seed_curve(k, seed, radii=radii)
                fh.write(json.dumps(rec, ensure_ascii=False) + "\n")
                fh.flush()
                n_new += 1
    return {"written": n_new, "total_lines": len(done) + n_new, "out": str(out)}

