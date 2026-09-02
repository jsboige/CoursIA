"""Case 8b (#8182, iceberg L4) : le canal *self* irreductible.

La case 8 (``strange_loop_selfmodel``) a rendu ``P2 FALSIFIE`` -- le
self-modele structure ne se re-adaptait pas plus vite qu'un surrogate a
capacite egale (``rho_beta`` median 1.0 au lieu de ``>= 3``). Son
diagnostic nommait la condition manquante :

    l'action ``a = pol(x)`` etant deterministe en l'etat, le canal
    "self" ne porte AUCUNE information independante de ``x``. Le lacet
    ne "travaille" que si le canal self est IRREDUCTIBLE a l'etat
    (autonomie partielle du self-modele).

Ce module teste cette condition, et rien d'autre. **Une seule variable
change** : la politique recoit un "motif" interne autonome ``m_t``
(AR(1) a bruit propre) qui n'est pas une fonction de ``x_t`` -- l'agent
connait l'action qu'il emet, mais l'etat ne la determine plus.
Dynamique, modeles, metrique, seuils, horizon et graines sont ceux de
la case 8, **importes tels quels** pour que la comparaison soit exacte
plutot que ressemblante.

Le troisieme modele -- ``NoiseChannelSurrogate`` -- est le null que la
case 8 ne POUVAIT pas avoir : tant que l'action etait deductible de
l'etat, "avoir le canal action" ne se distinguait pas de "avoir une
dimension d'entree de plus". Une fois le canal irreductible, les deux
se separent, et c'est cette separation qui isole l'*auto*-connaissance.

Pre-enregistrement scelle AVANT ce fichier :
``docs/ict/strange-loop-irreducible-pre-enregistrement.md`` (commit
anterieur -- ordre git verifiable, comme ``55d4aad9ef`` precede le
jouet de la case 8).

  P1 prime  fermeture   : d* median <= 12, >= 4/5 graines
  P2 prime  travail     : rho_beta >= 3 (>= 4/5) ET rho_alpha < 2 (mediane)
  P3 prime  specificite : kappa = T_noise / T_surrogate median dans [0.5, 2]
  Controle mesure       : residual_share > 0.30, sinon INCONCLUSIF_MANIPULATION

Grade C documentaire : on teste une CLASSE de mecanisme sur un substrat
scalaire, pas la these de Hofstadter sur le cerveau ; aucune
phenomenologie n'est mesuree, et un ``CONFIRMED`` ne dirait rien de
l'experience vecue.

References
----------
Douglas Hofstadter, *Godel, Escher, Bach*, Basic Books 1979, ISBN
978-0465026562 ; *I Am a Strange Loop*, Basic Books 2007, ISBN
978-0465003010.
"""

from __future__ import annotations

import numpy as np

from .strange_loop_selfmodel import (
    CompositeSurrogate,
    LoopSystem,
    SelfLoopModel,
    _features,
    _make_basis,
    closure_kink,
)

__all__ = [
    "AutonomousPolicy",
    "FrozenPolicyView",
    "NoiseChannelSurrogate",
    "irreducibility_share",
    "adaptation_horizon_irr",
    "run_case8b",
]


class AutonomousPolicy:
    """Politique a autonomie partielle : ``a = omega . phi(x) + m``.

    ``m`` est un "motif" interne AR(1) -- ``m <- rho m + eta`` -- avec
    son PROPRE bruit. L'agent connait l'action qu'il emet ; l'etat
    ``x_t``, lui, ne la determine plus. C'est l'unique difference avec
    ``LoopPolicy`` de la case 8, et c'est la variable sous test.

    ``motive_std`` est l'ecart-type STATIONNAIRE vise pour ``m`` (le
    bruit d'innovation en est deduit) : le reglage se lit ainsi a
    l'echelle de l'action, pas a celle de l'innovation.

    La politique est STATEFUL -- ``act`` fait avancer ``m``. Elle n'est
    donc pas reutilisable entre deux bras : chaque bras en recoit une
    fraiche, de meme graine, pour voir la MEME realisation du motif.
    """

    def __init__(self, n_feat: int = 8, seed: int = 0, rho: float = 0.9,
                 motive_std: float = 0.6):
        rng = np.random.default_rng(seed)
        self.basis = _make_basis(rng, n_feat)
        self.omega = rng.normal(0.0, 0.5, size=n_feat)
        self.rho = rho
        self.motive_std = motive_std
        self.eta_std = motive_std * np.sqrt(max(1e-12, 1.0 - rho ** 2))
        self.motive_rng = np.random.default_rng(seed + 77)
        self.m = float(self.motive_rng.normal(0.0, motive_std))

    def state_part(self, x: float) -> float:
        """Part de l'action deductible de l'etat -- sans le motif."""
        return float(self.omega @ _features(x, self.basis))

    def act(self, x: float) -> float:
        a = self.state_part(x) + self.m
        self.m = float(self.rho * self.m
                       + self.motive_rng.normal(0.0, self.eta_std))
        return a

    def frozen(self, m_value: float = 0.0) -> "FrozenPolicyView":
        return FrozenPolicyView(self, m_value)


class FrozenPolicyView:
    """Vue sans etat de la politique, pour l'iteration de fermeture.

    ``closure_depth`` itere ``R <- f_hat(R)`` : c'est une CARTE, donc
    elle exige un objet qui rende la meme action pour le meme ``x``.
    Le motif y est fige a sa moyenne stationnaire (``0``) : la
    fermeture se mesure sur la dynamique bouclee esperee, pas sur une
    realisation du bruit. Sans cela ``d*`` mesurerait la persistance de
    l'AR(1), pas la profondeur du lacet.
    """

    def __init__(self, pol: AutonomousPolicy, m_value: float = 0.0):
        self.pol = pol
        self.m_value = float(m_value)

    def act(self, x: float) -> float:
        return self.pol.state_part(x) + self.m_value


class NoiseChannelSurrogate:
    """Capacite egale + UN CANAL DE PLUS, mais un canal qui n'est pas lui.

    ``x_hat = u . [psi(x), z]`` ou ``z`` est un bruit EXOGENE de meme
    variance que l'action, tire par le modele lui-meme (il est
    independant de la dynamique par construction).

    Si l'avantage du self-modele n'etait que "une entree de plus", ce
    surrogate-ci le rattraperait. C'est le null (c) du
    pre-enregistrement, et il est **genereux** : ``[psi(x), z]`` porte
    ``n_feat + 2`` parametres la ou ``SelfLoopModel`` en a ``n_feat +
    1``. Le null a donc un parametre de plus que le modele qu'il doit
    concurrencer -- biais assume, qui joue CONTRE P3 prime.

    ``new_step()`` tire le ``z`` du pas ; il DOIT etre appele une fois
    par pas, sinon ``predict`` et ``update`` verraient deux tirages
    differents pour le meme pas.
    """

    name = "noise_channel_surrogate"

    def __init__(self, n_feat: int = 8, lr: float = 0.02, seed: int = 0,
                 z_std: float = 0.6):
        rng = np.random.default_rng(seed)
        self.basis = _make_basis(rng, n_feat)
        self.u = np.zeros(n_feat + 2)
        self.lr = lr
        self.z_std = z_std
        self.z_rng = np.random.default_rng(seed + 991)
        self._z = 0.0

    def new_step(self) -> None:
        self._z = float(self.z_rng.normal(0.0, self.z_std))

    def feats(self, x: float) -> np.ndarray:
        return np.concatenate([_features(x, self.basis), [1.0], [self._z]])

    def predict(self, x: float, action: float) -> float:
        return float(self.u @ self.feats(x))  # action non branchee

    def update(self, x: float, action: float, x_next: float) -> None:
        err = self.predict(x, action) - x_next
        self.u -= self.lr * err * self.feats(x)


def irreducibility_share(pol: AutonomousPolicy, *, n_steps: int = 2000,
                         seed: int = 0, n_feat: int = 8) -> dict:
    """Mesure la part de l'action NON explicable par l'etat.

    Regression lineaire de l'action sur ``[phi(x), 1]`` le long d'une
    trajectoire (base de sondage independante de celle de la
    politique), et ``residual_share = 1 - R2``.

    Sur la case 8 cette part vaut ``0`` PAR CONSTRUCTION -- l'action y
    etait une fonction de l'etat. La mesurer ici est ce qui atteste que
    la manipulation a pris, au lieu de le supposer : un test qui ne
    mesure pas sa propre variable ne peut ni confirmer ni falsifier.

    Elle ne vaut pas ``1`` non plus : ``m_{t-1}`` a influence ``x_t``,
    donc l'etat courant porte une trace du motif passe, qu'une
    regression peut exploiter. C'est attendu et sans consequence -- le
    seuil porte sur la part IRREDUCTIBLE, pas sur une independance
    totale.
    """
    sys_ = LoopSystem(shift_kind="beta", shift_step=n_steps + 1, seed=seed)
    probe_basis = _make_basis(np.random.default_rng(seed + 5), n_feat)
    rows, acts = [], []
    x = sys_.x
    for _ in range(n_steps):
        a = pol.act(x)
        rows.append(np.concatenate([_features(x, probe_basis), [1.0]]))
        acts.append(a)
        x = sys_.step(a)
    phi = np.asarray(rows)
    y = np.asarray(acts)
    coef, *_ = np.linalg.lstsq(phi, y, rcond=None)
    resid = y - phi @ coef
    ss_res = float(resid @ resid)
    ss_tot = float(((y - y.mean()) ** 2).sum())
    r2 = 1.0 - ss_res / max(ss_tot, 1e-12)
    return {
        "r2_action_on_state": r2,
        "residual_share": 1.0 - r2,
        "action_std": float(y.std()),
    }


def adaptation_horizon_irr(model, pol: AutonomousPolicy, *,
                           shift_kind: str = "beta", n_steps: int = 4000,
                           shift_step: int = 2000, seed: int = 0,
                           warmup: int = 1500,
                           catchup_factor: float = 1.2) -> dict:
    """Horizon de rattrapage -- identique a la case 8, politique stateful.

    Deux ecarts avec ``adaptation_horizon``, tous deux imposes par la
    variable sous test et non par un choix de metrique : la politique
    fait avancer son motif a chaque ``act`` (l'appelant lui en fournit
    donc une fraiche par bras), et ``new_step()`` est notifie aux
    modeles portant un canal exogene.

    Le seuil de rattrapage reste ``< catchup_factor x`` l'asymptote
    pre-shift **du modele lui-meme**. Ce choix joue CONTRE la
    prediction : un surrogate structurellement moins bon a une
    asymptote plus haute, donc un seuil plus lache, donc il est
    declare rattrape plus facilement (biais assume, cf.
    pre-enregistrement).
    """
    sys_ = LoopSystem(shift_step=shift_step, shift_kind=shift_kind, seed=seed)
    step_hook = getattr(model, "new_step", None)
    errs: list[float] = []
    x = sys_.x
    for _ in range(n_steps):
        if step_hook is not None:
            step_hook()
        a = pol.act(x)
        x_next = sys_.step(a)
        model.update(x, a, x_next)
        errs.append(abs(model.predict(x, a) - x_next))
        x = x_next

    pre = float(np.median(errs[warmup:shift_step]))
    tail = n_steps - shift_step
    horizon = tail
    for t in range(shift_step + 50, n_steps):
        if float(np.mean(errs[t - 50:t])) < catchup_factor * pre:
            horizon = t - shift_step
            break
    return {
        "pre_median_err": pre,
        "adaptation_horizon": int(horizon),
        "caught_up": bool(horizon < tail),
        # Plancher de l'echelle : la recherche demarre a shift_step + 50,
        # donc 50 est le plus petit horizon EXPRIMABLE. Un bras qui s'y
        # pose n'a pas ete mesure -- il a ete declare rattrape a la
        # premiere occasion. Cf. `instrument_degenerate` dans run_case8b.
        "at_floor": bool(horizon <= 50),
    }


def run_case8b(n_seeds: int = 5, n_feat: int = 8,
               motive_std: float = 0.6) -> dict:
    """Execute le protocole pre-enregistre case 8b sur ``n_seeds`` graines.

    Par graine : la part irreductible de l'action (controle de
    manipulation), les horizons des TROIS modeles sur le shift beta,
    ceux des deux modeles de la case 8 sur le shift alpha (canal non
    privilegie), puis la fermeture et son kink. Tout est deterministe
    par graine.
    """
    rows = []
    for s in range(n_seeds):
        def fresh_pol() -> AutonomousPolicy:
            return AutonomousPolicy(n_feat=n_feat, seed=s + 1000,
                                    motive_std=motive_std)

        irr = irreducibility_share(fresh_pol(), seed=s, n_feat=n_feat)
        z_std = irr["action_std"]  # "meme variance que l'action" (scelle)

        h_loop_beta = adaptation_horizon_irr(
            SelfLoopModel(n_feat=n_feat, seed=s), fresh_pol(),
            shift_kind="beta", seed=s)
        h_surr_beta = adaptation_horizon_irr(
            CompositeSurrogate(n_feat=n_feat, seed=s), fresh_pol(),
            shift_kind="beta", seed=s)
        h_noise_beta = adaptation_horizon_irr(
            NoiseChannelSurrogate(n_feat=n_feat, seed=s, z_std=z_std),
            fresh_pol(), shift_kind="beta", seed=s)
        h_loop_alpha = adaptation_horizon_irr(
            SelfLoopModel(n_feat=n_feat, seed=s), fresh_pol(),
            shift_kind="alpha", seed=s)
        h_surr_alpha = adaptation_horizon_irr(
            CompositeSurrogate(n_feat=n_feat, seed=s), fresh_pol(),
            shift_kind="alpha", seed=s)

        pol_k = fresh_pol()
        m = SelfLoopModel(n_feat=n_feat, seed=s)
        sys_ = LoopSystem(shift_kind="beta", seed=s)
        x = sys_.x
        for _ in range(2000):
            a = pol_k.act(x)
            x_next = sys_.step(a)
            m.update(x, a, x_next)
            x = x_next
        kink = closure_kink(m, x, pol_k.frozen(0.0))

        rows.append({
            "seed": s,
            "irreducibility": irr,
            "loop_beta": h_loop_beta,
            "surrogate_beta": h_surr_beta,
            "noise_beta": h_noise_beta,
            "loop_alpha": h_loop_alpha,
            "surrogate_alpha": h_surr_alpha,
            "rho_beta": h_surr_beta["adaptation_horizon"]
                        / max(1, h_loop_beta["adaptation_horizon"]),
            "rho_alpha": h_surr_alpha["adaptation_horizon"]
                         / max(1, h_loop_alpha["adaptation_horizon"]),
            "kappa": h_noise_beta["adaptation_horizon"]
                     / max(1, h_surr_beta["adaptation_horizon"]),
            "kink": kink,
        })

    rho_beta = [r["rho_beta"] for r in rows]
    rho_alpha = [r["rho_alpha"] for r in rows]
    kappa = [r["kappa"] for r in rows]
    d_stars = [r["kink"]["d_star"] for r in rows]
    resid = [r["irreducibility"]["residual_share"] for r in rows]
    kink_ok = [
        (r["kink"]["finite"]
         and r["kink"]["gain_beyond_fixpoint"]
         < 0.10 * max(r["kink"]["gain_to_fixpoint"], 1e-9))
        for r in rows
    ]

    floor_surr = sum(r["surrogate_beta"]["at_floor"] for r in rows)
    floor_noise = sum(r["noise_beta"]["at_floor"] for r in rows)
    floor_loop = sum(r["loop_beta"]["at_floor"] for r in rows)
    pre_ratio = [r["surrogate_beta"]["pre_median_err"]
                 / max(r["loop_beta"]["pre_median_err"], 1e-12) for r in rows]

    summary = {
        "n_seeds": n_seeds,
        "residual_share_median": float(np.median(resid)),
        "floor_surrogate_count": int(floor_surr),
        "floor_noise_count": int(floor_noise),
        "floor_loop_count": int(floor_loop),
        "instrument_degenerate": bool(max(floor_surr, floor_noise)
                                      > n_seeds // 2),
        "pre_err_ratio_median": float(np.median(pre_ratio)),
        "manipulation_took": bool(float(np.median(resid)) > 0.30),
        "rho_beta_median": float(np.median(rho_beta)),
        "rho_beta_ge3_count": int(sum(v >= 3.0 for v in rho_beta)),
        "rho_alpha_median": float(np.median(rho_alpha)),
        "rho_alpha_lt2": bool(float(np.median(rho_alpha)) < 2.0),
        "kappa_median": float(np.median(kappa)),
        "kappa_in_band": bool(0.5 <= float(np.median(kappa)) <= 2.0),
        "d_star_median": float(np.median(d_stars)),
        "d_star_le12_count": int(sum(1 for d in d_stars if d <= 12)),
        "kink_saturation_count": int(sum(kink_ok)),
    }

    # Ordre des verdicts, tel que scelle. Le controle de manipulation
    # PRIME : un test qui n'a pas etabli sa propre variable ne confirme
    # ni ne falsifie. La perte de fermeture vient ensuite, comme verdict
    # DISTINCT -- pas comme une confirmation degradee.
    if not summary["manipulation_took"]:
        verdict = "INCONCLUSIF_MANIPULATION"
    elif summary["instrument_degenerate"]:
        verdict = "INCONCLUSIF_INSTRUMENT"
    elif summary["d_star_le12_count"] < n_seeds - 1:
        verdict = "CLOSURE_LOST"
    elif (summary["rho_beta_ge3_count"] >= n_seeds - 1
          and summary["rho_alpha_lt2"]
          and summary["kappa_in_band"]
          and summary["kink_saturation_count"] >= n_seeds - 1):
        verdict = "CONFIRMED"
    elif (summary["rho_beta_ge3_count"] <= n_seeds // 2
          or not summary["rho_alpha_lt2"]
          or not summary["kappa_in_band"]):
        verdict = "FALSIFIED"
    else:
        verdict = "INCONCLUSIF"
    summary["verdict"] = verdict
    return {"rows": rows, "summary": summary}


if __name__ == "__main__":
    import json

    out = run_case8b()
    print(json.dumps(out["summary"], indent=1, ensure_ascii=False))
    for r in out["rows"]:
        print(f"seed {r['seed']}: "
              f"resid={r['irreducibility']['residual_share']:.2f} "
              f"rho_beta={r['rho_beta']:.2f} rho_alpha={r['rho_alpha']:.2f} "
              f"kappa={r['kappa']:.2f} d*={r['kink']['d_star']}")
