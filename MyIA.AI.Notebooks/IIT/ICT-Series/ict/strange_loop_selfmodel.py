"""Jouet d'auto-modèle en lacet pour la distillation Hofstadter (case 8, #8182 iceberg L4).

Hofstadter 1979/2007 (strange loop) en une phrase : le « soi » est une
boucle étrange -- un système qui se représente lui-même, où monter
dans la hiérarchie des niveaux de description REVIENT au point de
départ, et où cette circularité ne régresse pas à l'infini parce que
chaque niveau se représente de façon COMPRESSÉE ; le lacet ferme en un
point fixe atteignable en profondeur FINIE, et cette circularité fait
un travail que des machines de même taille sans structure
auto-référentielle ne font pas.

Ce module implémente le jouet minimal qui rend ces deux faces
falsifiables sur CPU, dans l'espace 4-objets d'ICT (le candidat fort
de l'iceberg mappe ``p̂`` / lacet persona ICT-23/25 : le self-modèle
``q̂(self)`` qui participe à sa propre réalisation) :

- ``LoopSystem`` : dynamique scalaire auto-référentielle
  ``x_{t+1} = alpha_t * x_t + beta_t * a_t + bruit`` où l'action
  ``a_t`` de l'agent ENTRE dans la dynamique qu'il doit prédire --
  prédire, c'est prédire sa propre contribution. Au mi-parcours,
  l'environnement dérive : selon l' Bras, ``beta`` OU ``alpha`` change.
- ``LoopPolicy`` : politique fixe (non apprise) ``a = omega . phi(x)``
  -- ce qui est appris est le MODÈLE de la dynamique bouclée.
- ``SelfLoopModel`` : modèle STRUCTURÉ par le lacet -- features
  ``[phi(x), a]``, le canal d'action est explicite : le modèle sait
  quelle part de la dynamique est LUI.
- ``CompositeSurrogate`` : modèle à capacité égale (même nombre de
  paramètres, même pas d'apprentissage) SANS canal d'action -- il
  apprend la carte composite ``x -> x'`` comme une boîte opaque.
- ``closure_depth`` : itère ``R <- f_hat(R)`` (le self-modèle de SA
  PROPRE dynamique bouclée, politique incluse) et compte les pas
  jusqu'au point fixe ``R*`` -- la FERMETURE du lacet (régression
  finie, pas infinie).

La double dissociation -- le cœur du pré-enregistrement :

  shift ``beta`` (le monde change la réponse à MES actions) : le
  modèle structuré ne ré-estime quasiment qu'un scalaire (le gain du
  canal action) et rattrape VITE ; le surrogate réapprend toute la
  carte composite. Avantage attendu au lacet.

  shift ``alpha`` (le monde change la dérive de MON ÉTAT, un canal
  que le modèle structuré ne possède pas plus que le surrogate) :
  l'avantage doit DISPARAÎTRE. Si le modèle structuré rattrape aussi
  vite sur ce shift-là, son avantage était de la flexibilité
  générique, pas de l'auto-connaissance -- falsifié.

Pré-enregistrement (dissociations-matrix.md, case 8) :

  P1 (fermeture) : médiane d* <= 12 itérations, >= 4/5 seeds.
  P2 (spécificité du lacet, double dissociation) :
      rho_beta = T_surrogate / T_loop >= 3 (>= 4/5 seeds)  ET
      rho_alpha < 2 (médiane).
  P3 (le kink) : l'erreur de fermeture à la profondeur 2*d* ne gagne
      plus rien (< 10% du gain de la profondeur 1 -> d*).

Nulls adversariaux :
  (a) rho_beta < 3 : le surrogate à capacité égale suffit -- l'effet
      est la capacité, pas l'auto-référence (falsifié) ;
  (b) stabilité inter-seeds : le pattern de verdict doit être le
      même sur les 5 seeds (un pattern qui saute d'un seed à l'autre
      mesure une instabilité, pas une structure).

Grade C documentaire : ce jouet teste la CLASSE de mécanisme (un
self-modèle structuré ferme en un point fixe fini et ré-adapte
spécifiquement quand le monde change la réponse à ses propres
actions), pas la thèse de Hofstadter sur le cerveau réel -- aucune
phénoménologie n'est mesurée ici.

References
----------
Douglas Hofstadter, "Godel, Escher, Bach: an Eternal Golden Braid",
Basic Books 1979, ISBN 978-0465026562 ; "I Am a Strange Loop", Basic
Books 2007, ISBN 978-0465003010. Vérifié firsthand 2026-08-25 (thèse
centrale : auto-représentation compressive qui se stabilise sans
régression infinie ; le « je » comme motif de rétro-action, pas comme
substance).
"""

from __future__ import annotations

import numpy as np

__all__ = [
    "LoopSystem",
    "LoopPolicy",
    "SelfLoopModel",
    "CompositeSurrogate",
    "closure_depth",
    "closure_kink",
    "adaptation_horizon",
    "run_case8",
]


def _features(x: float, basis: np.ndarray) -> np.ndarray:
    """Random-features tanh : phi(x) = tanh(basis @ [x, 1])."""
    return np.tanh(basis @ np.array([x, 1.0]))


def _make_basis(rng: np.random.Generator, n_feat: int) -> np.ndarray:
    return rng.normal(0.0, 1.0, size=(n_feat, 2)) / np.sqrt(2.0)


class LoopPolicy:
    """Politique fixe de l'agent : a = omega . phi_policy(x).

    La politique n'est PAS apprise : ce qui est appris est le modèle
    de la dynamique bouclée. Le lacet testé est cognitif -- la
    représentation de sa propre contribution -- pas le contrôle.
    """

    def __init__(self, n_feat: int = 8, seed: int = 0):
        rng = np.random.default_rng(seed)
        self.basis = _make_basis(rng, n_feat)
        self.omega = rng.normal(0.0, 0.5, size=n_feat)

    def act(self, x: float) -> float:
        return float(self.omega @ _features(x, self.basis))


class LoopSystem:
    """Dynamique auto-référentielle avec drift, selon ``shift_kind``.

    ``x_{t+1} = alpha_t * x_t + beta_t * a_t + w_t``. Au pas
    ``shift_step`` : ``shift_kind="beta"`` fait passer beta0 -> beta1
    (le monde change la réponse aux actions de l'agent) ;
    ``shift_kind="alpha"`` fait passer alpha0 -> alpha1 (le monde
    change la dérive de l'état -- canal NON privilégié du modèle
    structuré). Bruit gaussien iid, état borné par clip.
    """

    def __init__(self, alpha0: float = 0.6, alpha1: float = -0.3,
                 beta0: float = 0.8, beta1: float = -0.5,
                 shift_step: int = 2000, shift_kind: str = "beta",
                 noise_std: float = 0.05, seed: int = 0):
        if shift_kind not in ("beta", "alpha"):
            raise ValueError(f"shift_kind inconnu : {shift_kind!r}")
        self.alpha0, self.alpha1 = alpha0, alpha1
        self.beta0, self.beta1 = beta0, beta1
        self.shift_step = shift_step
        self.shift_kind = shift_kind
        self.noise_std = noise_std
        self.rng = np.random.default_rng(seed)
        self.x = float(self.rng.uniform(-1.0, 1.0))
        self.step_count = 0

    @property
    def alpha(self) -> float:
        return (self.alpha0 if self.step_count < self.shift_step
                else self.alpha1) if self.shift_kind == "alpha" else self.alpha0

    @property
    def beta(self) -> float:
        return (self.beta0 if self.step_count < self.shift_step
                else self.beta1) if self.shift_kind == "beta" else self.beta0

    def step(self, action: float) -> float:
        self.x = float(np.clip(
            self.alpha * self.x + self.beta * action
            + self.rng.normal(0.0, self.noise_std), -4.0, 4.0))
        self.step_count += 1
        return self.x


class SelfLoopModel:
    """Modèle structuré par le lacet : canal d'action explicite.

    ``x_hat = w . phi(x) + c * a`` où ``a`` est l'action RÉELLEMENT
    émise. Après un shift de beta, seul le gain ``c`` doit être
    ré-estimé : c'est l'hypothèse structurante mise à l'épreuve.
    """

    name = "self_loop"

    def __init__(self, n_feat: int = 8, lr: float = 0.02, seed: int = 0):
        rng = np.random.default_rng(seed)
        self.basis = _make_basis(rng, n_feat)
        self.w = np.zeros(n_feat)
        self.c = 0.0
        self.lr = lr

    def phi(self, x: float) -> np.ndarray:
        return _features(x, self.basis)

    def predict(self, x: float, action: float) -> float:
        return float(self.w @ self.phi(x) + self.c * action)

    def update(self, x: float, action: float, x_next: float) -> None:
        err = self.predict(x, action) - x_next
        self.w -= self.lr * err * self.phi(x)
        self.c -= self.lr * err * action

    def closed_map(self, x: float, pol: LoopPolicy) -> float:
        """Estimation par le modèle de SA PROPRE dynamique bouclée.

        ``f_hat(x) = w . phi(x) + c * pol(x)`` -- la carte que le
        modèle croit être la sienne, action comprise. C'est elle
        qu'on itère dans ``closure_depth`` : le self-modèle se
        représente lui-même en train d'agir sur lui-même.
        """
        return self.predict(x, pol.act(x))


class CompositeSurrogate:
    """Surrogate à capacité égale, SANS canal d'action.

    ``x_hat = v . psi(x)`` avec ``psi`` de MÊME largeur que
    ``[phi(x), a]`` (n_feat + 1) : mêmes paramètres, même pas
    d'apprentissage, même information de surface -- mais aucune
    structure qui sépare « ce que je produis » du reste.
    """

    name = "composite_surrogate"

    def __init__(self, n_feat: int = 8, lr: float = 0.02, seed: int = 0):
        rng = np.random.default_rng(seed)
        self.basis = _make_basis(rng, n_feat)
        self.v = np.zeros(n_feat + 1)
        self.lr = lr

    def psi(self, x: float) -> np.ndarray:
        return np.concatenate([_features(x, self.basis), [1.0]])

    def predict(self, x: float, action: float) -> float:
        return float(self.v @ self.psi(x))  # action non branchée

    def update(self, x: float, action: float, x_next: float) -> None:
        err = self.predict(x, action) - x_next
        self.v -= self.lr * err * self.psi(x)


def closure_depth(model: SelfLoopModel, x0: float, pol: LoopPolicy,
                  eps: float = 1e-3, k_max: int = 200) -> tuple[int, float]:
    """Itère ``R <- f_hat(R)`` depuis ``x0`` jusqu'au point fixe.

    Retourne ``(d*, R*)`` : nombre d'itérations jusqu'à
    ``|R_{k+1} - R_k| < eps``, borné à ``k_max`` si non atteint
    (lacet non fermé). La fermeture FINIE est la mesure
    anti-régression-infinie de Hofstadter.
    """
    r = x0
    for k in range(1, k_max + 1):
        r_next = model.closed_map(r, pol)
        if abs(r_next - r) < eps:
            return k, r_next
        r = r_next
    return k_max, r


def closure_kink(model: SelfLoopModel, x0: float, pol: LoopPolicy,
                 eps: float = 1e-3) -> dict:
    """Mesure le kink de saturation de la fermeture (P3).

    Itère jusqu'à ``d*`` puis ENCORE ``d*`` pas (profondeur 2d*) ;
    le gain résiduel ``|R_2d* - R_d*|`` doit être négligeable devant
    ``|R_d* - x0|`` : au-delà du point fixe, itérer n'apprend plus
    rien -- c'est la signature « boucle qui se referme », pas d'une
    pile infinie de niveaux.
    """
    d_star, r_star = closure_depth(model, x0, pol, eps=eps)
    r_end = r_star
    for _ in range(d_star):
        r_end = model.closed_map(r_end, pol)
        if not np.isfinite(r_end):
            break
    return {
        "d_star": d_star,
        "gain_to_fixpoint": abs(r_star - x0),
        "gain_beyond_fixpoint": abs(r_end - r_star),
        "finite": bool(np.isfinite(r_end)),
    }


def adaptation_horizon(model, pol: LoopPolicy, *, shift_kind: str = "beta",
                       n_steps: int = 4000, shift_step: int = 2000,
                       seed: int = 0, warmup: int = 1500,
                       catchup_factor: float = 1.2,
                       horizon_cap: int | None = None) -> dict:
    """Entraînement en ligne sur le système bouclé, avec drift.

    Retourne l'erreur médiane pré-shift (asymptote), et l'HORIZON de
    rattrapage : pas après le shift pour que la moyenne mobile (50)
    de l'erreur repasse sous ``catchup_factor x`` l'asymptote
    pré-shift. Horizon borné au reste de la trajectoire si jamais
    atteint (cap explicite, mesuré).
    """
    sys_ = LoopSystem(shift_step=shift_step, shift_kind=shift_kind, seed=seed)
    errs: list[float] = []
    x = sys_.x
    for _ in range(n_steps):
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
    if horizon_cap is not None:
        horizon = min(horizon, horizon_cap)
    return {
        "pre_median_err": pre,
        "adaptation_horizon": int(horizon),
        "caught_up": bool(horizon < tail),
    }


def run_case8(n_seeds: int = 5, n_feat: int = 8) -> dict:
    """Exécute le protocole pré-enregistré case 8 sur ``n_seeds`` seeds.

    Par seed : horizons des deux modèles sur les DEUX shifts (beta et
    alpha), profondeur de fermeture et kink, puis agrégats pour P1-P3
    et les nulls. Tout est déterministe par seed.
    """
    rows = []
    for s in range(n_seeds):
        pol = LoopPolicy(n_feat=n_feat, seed=s + 1000)

        def fresh(model_cls):
            return model_cls(n_feat=n_feat, seed=s)

        h_loop_beta = adaptation_horizon(fresh(SelfLoopModel), pol,
                                         shift_kind="beta", seed=s)
        h_surr_beta = adaptation_horizon(fresh(CompositeSurrogate), pol,
                                         shift_kind="beta", seed=s)
        h_loop_alpha = adaptation_horizon(fresh(SelfLoopModel), pol,
                                          shift_kind="alpha", seed=s)
        h_surr_alpha = adaptation_horizon(fresh(CompositeSurrogate), pol,
                                          shift_kind="alpha", seed=s)

        m = SelfLoopModel(n_feat=n_feat, seed=s)
        sys_ = LoopSystem(shift_kind="beta", seed=s)
        x = sys_.x
        for _ in range(2000):
            a = pol.act(x)
            x_next = sys_.step(a)
            m.update(x, a, x_next)
            x = x_next
        kink = closure_kink(m, x, pol)

        rows.append({
            "seed": s,
            "loop_beta": h_loop_beta, "surrogate_beta": h_surr_beta,
            "loop_alpha": h_loop_alpha, "surrogate_alpha": h_surr_alpha,
            "rho_beta": h_surr_beta["adaptation_horizon"]
                        / max(1, h_loop_beta["adaptation_horizon"]),
            "rho_alpha": h_surr_alpha["adaptation_horizon"]
                         / max(1, h_loop_alpha["adaptation_horizon"]),
            "kink": kink,
        })

    rho_beta = [r["rho_beta"] for r in rows]
    rho_alpha = [r["rho_alpha"] for r in rows]
    d_stars = [r["kink"]["d_star"] for r in rows]
    kink_ok = [
        (r["kink"]["finite"]
         and r["kink"]["gain_beyond_fixpoint"]
         < 0.10 * max(r["kink"]["gain_to_fixpoint"], 1e-9))
        for r in rows
    ]

    summary = {
        "rho_beta_median": float(np.median(rho_beta)),
        "rho_beta_ge3_count": int(sum(x >= 3.0 for x in rho_beta)),
        "rho_alpha_median": float(np.median(rho_alpha)),
        "rho_alpha_lt2": bool(np.median(rho_alpha) < 2.0),
        "d_star_median": float(np.median(d_stars)),
        "d_star_le12_count": int(sum(1 for d in d_stars if d <= 12)),
        "kink_saturation_count": int(sum(kink_ok)),
        "n_seeds": n_seeds,
    }
    summary["verdict"] = (
        "CONFIRMED" if (
            summary["d_star_le12_count"] >= n_seeds - 1
            and summary["rho_beta_ge3_count"] >= n_seeds - 1
            and summary["rho_alpha_lt2"]
            and summary["kink_saturation_count"] >= n_seeds - 1
        ) else (
            "FALSIFIED" if (
                summary["rho_beta_ge3_count"] <= n_seeds // 2
                or not summary["rho_alpha_lt2"]
            ) else "INCONCLUSIF"
        )
    )
    return {"rows": rows, "summary": summary}


if __name__ == "__main__":
    import json

    out = run_case8()
    print(json.dumps(out["summary"], indent=1, ensure_ascii=False))
    for r in out["rows"]:
        print(f"seed {r['seed']}: rho_beta={r['rho_beta']:.1f} "
              f"rho_alpha={r['rho_alpha']:.1f} d*={r['kink']['d_star']}")
