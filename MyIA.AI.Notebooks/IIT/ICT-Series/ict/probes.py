"""Sondes de lecture lineaire (mass-mean, logistique, PCA) pour ICT-Series (#13564).

Les notebooks de verite de la serie refont chacun leur propre probing lineaire
en ligne : direction ``mu_+ - mu_-``, direction logistique L2, son analogue sous
covariance classe-conditionnelle, et l'alignement de la premiere composante
principale. Ces gestes ne sont pas des objets de demonstration pedagogique :
c'est de l'outillage, identique d'un notebook a l'autre. Ce module le
factorise, dans la discipline d'architecture de la serie : numpy uniquement,
le GPU reste confine aux extractions.

* :func:`mass_mean_probe` -- direction ``mu_+ - mu_-`` (sonde de reference,
  sans parametre : elle sert d'etage bas a toutes les comparaisons).
* :func:`logistic_probe` -- direction logistique L2, reimplementation numpy de
  l'objectif de ``sklearn.linear_model.LogisticRegression``
  ``0.5 * ||w||**2 + C * sum_i log(1 + exp(-t_i (x_i . w + b)))`` (``t = +-1``),
  resolue par Newton (IRLS) : convergence quadratique, aucun tirage, aucun
  etat cache. La direction est remise a l'echelle par ``s = w.delta / (w.w)``
  (``delta = mu_+ - mu_-``), convention de la serie : la projection de
  ``mu_- + theta`` egale alors celle de ``mu_+`` -- la norme de ``theta`` porte
  donc le deplacement de frontiere, pas la norme arbitraire du fit.
* :func:`mm_iid_probe` -- mass-mean sous covariance classe-conditionnelle
  ``Sigma = cov([X_+ - mu_+, X_- - mu_-]) + ridge * I``, resolu par
  ``Sigma^{-1} delta``. Quand les classes diffèrent surtout dans des directions
  a faible variance, cette sonde est la bonne lecture ; ``MM`` y est biaisee
  par l'anisotropie.
* :func:`train_probes` -- les trois sondes ci-dessus sous leurs cles ``MM`` /
  ``LR`` / ``MMIID``, plus l'origine ``X.mean(0)`` sur laquelle
  :func:`probe_accuracy` seuille.
* :func:`probe_accuracy` -- exactitude du seuillage au point de fonctionnement
  ``mu_train`` : ``signe(X.theta - mu_train.theta)`` contre ``y == 1``.
* :func:`pca_stats` -- alignement de PC1 avec le label, la projection ``Z`` et
  les composantes ; le signe d'un vecteur propre etant arbitraire, la
  statistique est ``max(a, 1 - a)`` (invariante au signe).
* :func:`anchored_pc1` -- PC1 dont le signe est ancre par classe (projection
  moyenne des enonces ``y == 1`` positive) : sans cet ancrage, comparer deux
  PC1 n'a aucun sens, leur signe dependant du fit.

Conventions (portees des notebooks sources) :

* ``y`` est binaire ``{0, 1}`` ; ``X`` est ``[n, d]`` en float.
* Toutes les fonctions sont **deterministes** : aucun tirage, aucun etat
  global -- deux appels sur les memes donnees rendent des sorties identiques
  au bit pres.
* La source verifiee de cette factorisation est ICT-43
  (``ICT-44-GeometryOfTruth-Python.ipynb``, #16897). Le probing d'ICT-42 n'existe ni
  sur ``main`` ni sur sa branche crosscoder (#16749) : l'organe est ecrit pour
  l'accueillir tel quel (memes conventions, memes cles ``MM`` / ``LR`` /
  ``MMIID``) le jour ou il sera extrait a son tour.
"""

from __future__ import annotations

import numpy as np

__all__ = [
    "mass_mean_probe",
    "logistic_probe",
    "mm_iid_probe",
    "train_probes",
    "probe_accuracy",
    "pca_stats",
    "anchored_pc1",
]


def _check_inputs(X: "np.ndarray", y: "np.ndarray"):
    """Valide et normalise ``(X, y)`` -- frontiere publique du module.

    Leve ``ValueError`` si ``X`` n'est pas 2D, si ``y`` n'a pas une entree par
    ligne de ``X``, si ``y`` n'est pas binaire ``{0, 1}``, ou si l'une des deux
    classes est vide (une sonde compare deux classes : sur une seule, elle
    rendrait un ``NaN`` silencieux plutot qu'un verdict). Rend ``X`` en float
    et ``y`` en entier.
    """
    X = np.asarray(X, dtype=float)
    y = np.asarray(y)
    if X.ndim != 2:
        raise ValueError(f"X doit etre 2D [n, d], recu de forme {X.shape}")
    if y.ndim != 1 or y.shape[0] != X.shape[0]:
        raise ValueError(
            f"y doit etre 1D de longueur n={X.shape[0]}, recu de forme {y.shape}"
        )
    if not np.isin(y, (0, 1)).all():
        raise ValueError("y doit etre binaire {0, 1}")
    y = y.astype(int)
    if y.sum() == 0 or y.sum() == y.shape[0]:
        raise ValueError(
            "les deux classes {0, 1} doivent etre representees "
            f"(effectifs : {int((y == 1).sum())} / {int((y == 0).sum())})"
        )
    return X, y


def mass_mean_probe(X: "np.ndarray", y: "np.ndarray") -> "np.ndarray":
    """Direction mass-mean ``mu_+ - mu_-`` (sonde de reference)."""
    X, y = _check_inputs(X, y)
    return X[y == 1].mean(axis=0) - X[y == 0].mean(axis=0)


def logistic_probe(
    X: "np.ndarray",
    y: "np.ndarray",
    C: float = 1.0,
    iters: int = 100,
    tol: float = 1e-10,
) -> "np.ndarray":
    """Direction logistique L2 (Newton/IRLS), remise a l'echelle par ``s * w``.

    Minimise ``0.5 * ||w||**2 + C * sum_i log(1 + exp(-t_i (x_i . w + b)))``
    (meme objectif que ``LogisticRegression(C=C)`` de scikit-learn ; l'intercept
    n'est pas regularise, comme chez sklearn), puis rend ``s * w`` avec
    ``s = w.delta / (w.w)`` et ``delta = mu_+ - mu_-``.

    ``iters`` / ``tol`` bornent la boucle de Newton : l'arret se fait sur
    ``max|gradient| < tol``, sinon apres ``iters`` iterations. Chaque pas resout
    ``H d = -g`` par ``np.linalg.solve`` ; la diagonale porte ``+ 1e-10`` pour
    rester definie positive meme si un exemple sature la sigmoide.
    """
    X, y = _check_inputs(X, y)
    n, d = X.shape
    t = np.where(y == 1, 1.0, -1.0)
    Xb = np.concatenate([X, np.ones((n, 1))], axis=1)
    w = np.zeros(d + 1, dtype=float)
    reg = np.ones(d + 1, dtype=float)
    reg[-1] = 0.0
    for _ in range(iters):
        z = np.clip(Xb @ w, -30.0, 30.0)
        q = 1.0 / (1.0 + np.exp(-t * z))
        grad = reg * w - C * (Xb.T @ (t * (1.0 - q)))
        if np.max(np.abs(grad)) < tol:
            break
        s = np.clip(q * (1.0 - q), 1e-12, None)
        H = C * ((Xb * s[:, None]).T @ Xb)
        H[np.diag_indices_from(H)] += reg + 1e-10
        w = w - np.linalg.solve(H, grad)
    w_dir = w[:d]
    denom = float(w_dir @ w_dir)
    if denom <= 0.0:
        return np.zeros(d, dtype=float)
    delta = X[y == 1].mean(axis=0) - X[y == 0].mean(axis=0)
    s = float(w_dir @ delta) / denom
    return s * w_dir


def mm_iid_probe(
    X: "np.ndarray", y: "np.ndarray", ridge: float = 1e-3
) -> "np.ndarray":
    """Mass-mean IID : ``Sigma^{-1} (mu_+ - mu_-)``, ``Sigma`` classe-centree.

    ``Sigma`` est la covariance de ``[X_+ - mu_+, X_- - mu_-]`` (normalisation
    ``N - 1``, convention ``np.cov``) plus ``ridge * I`` -- le ridge rend le
    systeme defini meme quand ``d > n`` ou qu'une direction est morte.
    """
    X, y = _check_inputs(X, y)
    mu_p = X[y == 1].mean(axis=0)
    mu_m = X[y == 0].mean(axis=0)
    Xc = np.concatenate([X[y == 1] - mu_p, X[y == 0] - mu_m], axis=0)
    Sigma = np.atleast_2d(np.cov(Xc.T)) + ridge * np.eye(X.shape[1])
    return np.linalg.solve(Sigma, mu_p - mu_m)


def train_probes(
    X: "np.ndarray", y: "np.ndarray", C: float = 1.0, ridge: float = 1e-3
):
    """Entraine les trois sondes et rend ``({"MM", "LR", "MMIID"}, mu_train)``.

    ``mu_train = X.mean(0)`` est l'origine passee a :func:`probe_accuracy` :
    seuiller a cette origine rend l'exactitude insensible a la norme de chaque
    sonde (les trois directions n'ont pas la meme echelle).
    """
    X, y = _check_inputs(X, y)
    probes = {
        "MM": mass_mean_probe(X, y),
        "LR": logistic_probe(X, y, C=C),
        "MMIID": mm_iid_probe(X, y, ridge=ridge),
    }
    return probes, X.mean(axis=0)


def probe_accuracy(
    theta: "np.ndarray",
    mu_train: "np.ndarray",
    X: "np.ndarray",
    y: "np.ndarray",
) -> float:
    """Exactitude de ``theta`` seuille a ``mu_train`` : ``(X.theta > mu_train.theta)``."""
    X, y = _check_inputs(X, y)
    theta = np.asarray(theta, dtype=float)
    mu_train = np.asarray(mu_train, dtype=float)
    score = X @ theta - float(mu_train @ theta)
    return float(((score > 0.0) == (y == 1)).mean())


def _principal_components(Xc: "np.ndarray", n_components: int) -> "np.ndarray":
    """Composantes principales de ``Xc`` (deja centre), ordre decroissant.

    Diagonalisation de la covariance ``(N - 1)`` par ``np.linalg.eigh`` (exacte
    et deterministe, la matrice est symetrique). Le signe d'un vecteur propre
    etant arbitraire, on l'ancre par une regle fixe -- le coefficient de plus
    grande valeur absolue est rendu positif -- pour que deux appels rendent des
    projections comparables au signe pres, sans dependre de la bibliotheque.
    """
    n = Xc.shape[0]
    cov = (Xc.T @ Xc) / max(n - 1, 1)
    vals, vecs = np.linalg.eigh(cov)
    order = np.argsort(vals)[::-1][:n_components]
    comps = vecs[:, order].T
    for i in range(comps.shape[0]):
        j = int(np.argmax(np.abs(comps[i])))
        if comps[i, j] < 0.0:
            comps[i] = -comps[i]
    return comps


def pca_stats(X: "np.ndarray", y: "np.ndarray"):
    """Alignement de PC1 avec le label, projection ``Z`` et composantes.

    Rend ``(align, Z, composantes)`` avec ``Z = (X - X.mean(0)) @ composantes.T``
    et ``align = max(a, 1 - a)``, ``a`` etant l'exactitude du signe de ``Z[:, 0]``
    comme predicteur de ``y == 1``. Le ``max`` rend la statistique invariante au
    signe arbitraire de PC1 (cf. :func:`anchored_pc1` pour un signe ancre).
    """
    X, y = _check_inputs(X, y)
    Xc = X - X.mean(axis=0)
    comps = _principal_components(Xc, 2)
    Z = Xc @ comps.T
    a = float(((Z[:, 0] > 0.0) == (y == 1)).mean())
    return max(a, 1.0 - a), Z, comps


def anchored_pc1(X: "np.ndarray", y: "np.ndarray") -> "np.ndarray":
    """PC1 dont le signe est ancre : projection moyenne des ``y == 1`` positive.

    Le signe d'un vecteur propre PCA est arbitraire ; on le choisit ici pour que
    la projection moyenne des enonces vrais soit positive, sans quoi comparer
    deux PC1 (entre deux tirages, deux modeles, deux couches) n'aurait aucun
    sens -- leur signe dependrait du fit.
    """
    X, y = _check_inputs(X, y)
    Xc = X - X.mean(axis=0)
    v = _principal_components(Xc, 1)[0]
    if float(np.mean(Xc[y == 1] @ v)) < float(np.mean(Xc[y == 0] @ v)):
        v = -v
    return v