"""Jouet memoire etendue Otto/Inga pour la distillation Clark & Chalmers (case 9, #8182 iceberg L4).

Clark & Chalmers 1998 (extended mind) en une phrase : si une ressource
externe fonctionne, dans une tache, comme un processus que -- etait-il
dans la tete -- nous reconnaitrions sans hesitation comme cognitif,
alors cette ressource EST (pour le temps de la tache) partie du
processus cognitif ; Otto (Alzheimer + carnet) et Inga (memoire
biologique) sont functionnellement equivalents DES LORS que les
conditions de glue tiennent -- accessibilite constante, endossement
quasi automatique, consultation facile.

Ce module rend la parite et sa limite FALSIFIABLES sur CPU, dans
l'espace 4-objets d'ICT (la question de frontiere : le systeme couple
agent+store est-il UN systeme ou DEUX ; adjacent persona ICT-23/25) :

- ``FactWorld`` : n faits a derive Ornstein-Uhlenbeck (retour doux vers
  0, la memoire a de la valeur : les valeurs passent information au
  futur sans marche pure).
- ``ExtendedAgent`` (Otto) : cache interne k cles (LRU + epinglage
  adaptatif des cles en echec de consultation) + store externe (toutes
  les cles observees) dont la LECTURE est gatee par ``p_read``
  (accessibilite) et bruitee par ``sigma_e`` (endorsement). L'ECRITURE
  au store est libre ; c'est la consultation qui coute.
- ``CompositeAgent`` (Inga) : memoire monolithique des n cles, rappel
  bruite ``sigma_i``, AUCUNE separation interne/externe. Bras temoin
  apparie : au shift, son bruit de rappel est cale pour egaler le
  budget d'erreur TOTAL d'Otto post-shift (paire par seed) -- la
  question est alors si sa degradation est UNIFORME (pas de
  localisation) ou non.
- ``run_case9`` : 3 phases -- baseline 600 (glue OK : p_read=1),
  disruption 300 (p_read -> 0.1 ; Inga matched), recovery 300.

Double dissociation -- le coeur du pre-enregistrement (case 9,
dissociations-matrix.md, commit AVANT le jouet) :

  P1 (parite de performance) : R_p = err_Otto/err_Inga a baseline dans
  [0.80, 1.20] (mediane 5 seeds) -- le canal externe plus bruite ne
  casse pas la parite tant que l'erreur est dominee par la derive.

  P2 (frontiere dynamiquement reelle) : sous degradation de
  l'accessibilite, la degradation d'erreur d'Otto se LOCALISE sur les
  requetes consult-store : rho_split_Otto >= 3 (>= 4/5 seeds) ET
  rho_split_Inga < 2 sous degradation appariee en budget total.

  P3 (saturation de l'adaptation) : l'epinglage adaptatif sature --
  l'erreur consult tardive ne descend plus (w3/w1 dans [0.7, 1.6]) :
  l'erreur residuelle est structurelle (capacite k), pas adaptative.

Nulls adversariaux :
  (a) rho_split_Otto < 2 : le cache absorbe, la frontiere
      interne/externe n'est PAS dynamiquement reelle -- parite
      complete jusqu'aux dynamiques (lecture forte C&C) ;
  (b) R_p hors bande : le canal coute en performance meme sous glue ;
  (c) instabilite inter-seeds du pattern.

Grade C documentaire : ce jouet teste la CLASSE de mecanisme (un store
externe couple sous conditions de glue presente parite de performance
ET signature de perturbation localisee), pas la these philosophique
sur les croyances d'Otto -- aucune phenomenologie n'est mesuree.

References
----------
Andy Clark, David Chalmers, "The Extended Mind", Analysis 58(1):7-19
(1998), DOI 10.1093/analys/58.1.7. Verifie firsthand 2026-08-25
(Oxford Academic + NDPR + citations concordantes) : Parity Principle,
Otto/Inga, conditions glue-and-trust (accessibilite constante,
endorsement automatique, consultation facile).
"""

from __future__ import annotations

import numpy as np

__all__ = [
    "FactWorld",
    "ExtendedAgent",
    "CompositeAgent",
    "run_case9",
]


class FactWorld:
    """n faits scalaires a derive OU : v <- phi*v + N(0, sigma).

    Le retour doux vers 0 (phi < 1) garde le processus stationnaire :
    la memoire passe de l'information (v autocorrelle) sans marche pure
    (ou l'erreur de ratage croittrait sans borne et dominerait toute
    la mesure pour la mauvaise raison).
    """

    def __init__(self, n_keys: int = 24, phi: float = 0.999,
                 sigma: float = 0.03, seed: int = 0):
        self.n_keys = n_keys
        self.phi = phi
        self.sigma = sigma
        self.rng = np.random.default_rng(seed)
        self.v = np.zeros(n_keys)
        self.queries = self.rng.choice(n_keys, size=1_000_000,
                                       replace=True)

    def step(self) -> None:
        self.v = self.phi * self.v + self.rng.normal(0.0, self.sigma,
                                                     self.n_keys)


class ExtendedAgent:
    """Otto : cache interne k cles + store externe gate en LECTURE.

    Lecture : cache = gratuite et fiable ; store = reussit avec
    probabilite ``p_read`` (accesibilite glue), valeur bruitee
    ``sigma_e`` (endorsement). Echec de consultation -> reponse 0.0
    (l'agent ne peut pas lire le carnet) et epingle la cle (pression
    d'internalisation adaptative). Ecriture : toute observation entre
    au cache (eviction par (pin, recence) minima) ET au store.
    """

    name = "otto_extended"

    def __init__(self, n_keys: int = 24, cache_k: int = 6,
                 sigma_e: float = 0.08, seed: int = 0):
        self.n_keys = n_keys
        self.k = cache_k
        self.sigma_e = sigma_e
        self.rng = np.random.default_rng(seed + 777)
        self.cache: dict[int, tuple[float, int]] = {}
        self.store: dict[int, float] = {}
        self.pins: dict[int, float] = {}
        self.p_read = 1.0
        self.last_query_class: str | None = None
        self.clock = 0

    def answer(self, key: int) -> float:
        self.clock += 1
        if key in self.cache:
            val, _ = self.cache[key]
            self.cache[key] = (val, self.clock)
            self.last_query_class = "cache_hit"
            return val
        if key in self.store and self.rng.random() < self.p_read:
            self.last_query_class = "store_consult"
            return self.store[key] + self.rng.normal(0.0, self.sigma_e)
        self.pins[key] = self.pins.get(key, 0.0) + 1.0
        self.last_query_class = "store_consult"
        return 0.0

    def observe(self, key: int, truth: float) -> None:
        self.store[key] = truth
        if key in self.cache:
            self.cache[key] = (truth, self.clock)
            return
        if len(self.cache) >= self.k:
            victim = min(self.cache,
                         key=lambda kk: (self.pins.get(kk, 0.0),
                                         self.cache[kk][1]))
            if victim != key:
                del self.cache[victim]
        if len(self.cache) < self.k:
            self.cache[key] = (truth, self.clock)


class CompositeAgent:
    """Inga : memoire monolithique n cles, rappel bruite uniforme.

    Bras temoin apparie : ``extra_noise`` permet de caler le budget
    d'erreur TOTAL post-shift sur celui d'Otto (paire par seed) -- la
    degradation est alors uniforme par construction, et la question est
    de mesurer qu'elle ne se localise PAS (rho_split_Inga < 2).
    """

    name = "inga_composite"

    def __init__(self, n_keys: int = 24, sigma_i: float = 0.05,
                 seed: int = 0):
        self.n_keys = n_keys
        self.sigma_i = sigma_i
        self.extra_noise = 0.0
        self.rng = np.random.default_rng(seed + 555)
        self.memory: dict[int, float] = {}

    def answer(self, key: int) -> float:
        base = self.memory.get(key, 0.0)
        return base + self.rng.normal(0.0,
                                      self.sigma_i + self.extra_noise)

    def observe(self, key: int, truth: float) -> None:
        self.memory[key] = truth


def _run_arm(agent, world: FactWorld, *, t_base: int, t_shift: int,
             t_end: int, on_shift=None, hot_k: int = 6) -> list[dict]:
    """Boucle requete/reponse/feedback commune aux deux bras.

    Chaque requete enregistre : erreur absolue, classe au moment de la
    requete (``cache_hit``/``store_consult`` pour Otto ; hot/cold pour
    Inga via la partition fixee au shift = les ``hot_k`` cles les plus
    recemment requetees, miroir du cache d'Otto en write-on-query),
    phase.
    """
    hot_partition: set[int] | None = None
    if not isinstance(agent, ExtendedAgent):
        recent: list[int] = []
        for k in world.queries[:t_shift]:
            k = int(k)
            if k in recent:
                recent.remove(k)
            recent.insert(0, k)
        hot_partition = set(recent[:hot_k])
    rows: list[dict] = []
    for t in range(t_end):
        if t == t_shift:
            if on_shift is not None:
                on_shift(agent)
        world.step()
        key = int(world.queries[t])
        truth = float(world.v[key])
        pred = agent.answer(key)
        agent.observe(key, truth)
        if isinstance(agent, ExtendedAgent):
            qclass = agent.last_query_class
        else:
            qclass = ("hot" if hot_partition is not None
                      and key in hot_partition else "cold")
        phase = "base" if t < t_shift else "shift"
        rows.append({"t": t, "key": key, "err": abs(pred - truth),
                     "qclass": qclass, "phase": phase})
    return rows


def _mean_err(rows, phase: str, qclass: str | None = None) -> float:
    sel = [r["err"] for r in rows
           if r["phase"] == phase and (qclass is None
                                       or r["qclass"] == qclass)]
    return float(np.mean(sel)) if sel else float("nan")


def run_case9(n_seeds: int = 5, *, t_base: int = 300, t_shift: int = 600,
              t_end: int = 900, p_read_shift: float = 0.1,
              n_keys: int = 24, cache_k: int = 6) -> dict:
    """Protocole complet case 9 : bras Otto puis bras Inga apparie.

    Par seed : Otto (baseline p_read=1 -> shift p_read=0.1), puis Inga
    avec bruit extra calibre sur l'erreur post-shift d'Otto (paire par
    seed). Agregats P1-P3 et verdict. Deterministe par seed.
    """
    rows_by_seed = []
    for s in range(n_seeds):
        # --- bras Otto ---
        world = FactWorld(n_keys=n_keys, seed=s)
        otto = ExtendedAgent(n_keys=n_keys, cache_k=cache_k, seed=s)

        def otto_shift(a: ExtendedAgent) -> None:
            a.p_read = p_read_shift

        otto_rows = _run_arm(otto, world, t_base=t_base, t_shift=t_shift,
                             t_end=t_end, on_shift=otto_shift)

        # --- bras Inga apparie en budget d'erreur ---
        err_otto_shift = _mean_err(otto_rows, "shift")

        def _inga_rows(extra: float):
            w = FactWorld(n_keys=n_keys, seed=s)
            a = CompositeAgent(n_keys=n_keys, seed=s)

            def shift(a_):
                a_.extra_noise = extra
            return _run_arm(a, w, t_base=t_base, t_shift=t_shift,
                            t_end=t_end, on_shift=shift)

        # cible : err_shift(inga) ~= err_otto_shift ; sigma_add en
        # quadrature sur la composante de bruit.
        probe0 = _inga_rows(0.0)
        base_comp = _mean_err(probe0, "shift")
        sigma_add = float(np.sqrt(max(err_otto_shift ** 2
                                      - base_comp ** 2, 0.02 ** 2)))
        inga_rows = _inga_rows(sigma_add)
        matched = _mean_err(inga_rows, "shift")

        # --- mesures Otto ---
        err_o_base = _mean_err(otto_rows, "base")
        err_i_base = _mean_err(inga_rows, "base")
        r_p = err_o_base / err_i_base

        c_before = _mean_err(otto_rows, "base", "store_consult")
        c_after = _mean_err(otto_rows, "shift", "store_consult")
        h_before = _mean_err(otto_rows, "base", "cache_hit")
        h_after = _mean_err(otto_rows, "shift", "cache_hit")
        rho_otto = (c_after / c_before) / (h_after / h_before)

        ci_before = _mean_err(inga_rows, "base", "cold")
        ci_after = _mean_err(inga_rows, "shift", "cold")
        hi_before = _mean_err(inga_rows, "base", "hot")
        hi_after = _mean_err(inga_rows, "shift", "hot")
        rho_inga = (ci_after / ci_before) / (hi_after / hi_before)

        # fenetres P3 : 100 premieres / 100 dernieres requetes
        # consult-store du shift (saturation de l'adaptation)
        shift_rows_c = [r["err"] for r in otto_rows
                        if r["phase"] == "shift"
                        and r["qclass"] == "store_consult"]
        w1 = float(np.mean(shift_rows_c[:100]))
        w3 = float(np.mean(shift_rows_c[-100:]))

        rows_by_seed.append({
            "seed": s,
            "r_p": r_p,
            "rho_split_otto": rho_otto,
            "rho_split_inga": rho_inga,
            "w3_over_w1": w3 / w1 if w1 > 0 else float("inf"),
            "matched_budget_ratio": matched / err_otto_shift,
            "otto_base_err": err_o_base,
            "inga_base_err": err_i_base,
            "consult_before": c_before,
            "consult_after": c_after,
            "n_consult_shift": len(shift_rows_c),
        })

    r_ps = [r["r_p"] for r in rows_by_seed]
    ro = [r["rho_split_otto"] for r in rows_by_seed]
    ri = [r["rho_split_inga"] for r in rows_by_seed]
    wsr = [r["w3_over_w1"] for r in rows_by_seed]

    summary = {
        "r_p_median": float(np.median(r_ps)),
        "rho_otto_median": float(np.median(ro)),
        "rho_otto_ge3_count": int(sum(x >= 3.0 for x in ro)),
        "rho_inga_median": float(np.median(ri)),
        "rho_inga_lt2": bool(np.median(ri) < 2.0),
        "w3_w1_median": float(np.median(wsr)),
        "n_seeds": n_seeds,
    }
    p1 = 0.80 <= summary["r_p_median"] <= 1.20
    p2 = (summary["rho_otto_ge3_count"] >= n_seeds - 1
          and summary["rho_inga_lt2"])
    p3 = 0.7 <= summary["w3_w1_median"] <= 1.6
    summary["P1_pass"] = bool(p1)
    summary["P2_pass"] = bool(p2)
    summary["P3_pass"] = bool(p3)
    if p1 and p2 and p3:
        summary["verdict"] = "CONFIRMED"
    elif summary["rho_otto_median"] < 2.0 or not p1:
        summary["verdict"] = "FALSIFIED"
    else:
        summary["verdict"] = "INCONCLUSIF"
    return {"rows": rows_by_seed, "summary": summary}


if __name__ == "__main__":
    import json

    out = run_case9()
    print(json.dumps(out["summary"], indent=1, ensure_ascii=False))
    for r in out["rows"]:
        print(f"seed {r['seed']}: R_p={r['r_p']:.3f} "
              f"rho_O={r['rho_split_otto']:.2f} "
              f"rho_I={r['rho_split_inga']:.2f} "
              f"w3/w1={r['w3_over_w1']:.2f} "
              f"match={r['matched_budget_ratio']:.2f}")
