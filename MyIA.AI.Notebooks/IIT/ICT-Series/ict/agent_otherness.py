"""Mesure operationnelle d'alterite agentique (strate 6, Epic #4588, issue #7291).

La **reversibilisation** (ICT-18) et son **budget** (ICT-18b, :mod:`ict.reversibility_budget`)
mesurent la *resilience* d'une trajectoire -- sa capacite a regagner sa region de
consigne. La these unificatrice de la strate 6 (cadrage user 2026-07-18, issue #7291)
pose que la *cle* de cette reversibilite est la **collaboration agentique** : ce qui
se perd quand l'alterite est detruite (monoculture, asservissement, chambre d'echo),
ce qui se maintient quand des agents *autres* cooperent sans etre absorbes.

Pour que la these puisse **mourir honnetement** (anti-complaisance #7289/#7291, clause 3),
il faut une **mesure operationnelle d'alterite agentique** -- choisie et justifiee
*avant* de voir les donnees (clause 1 du contrat #7291). Ce module fournit trois
candidats explicites, compares honnetement (aucun privilegie a priori), chacun avec
ses limites documentees. Le contrat #7291 exige explicitement ce choix pre-enregistre.

Les trois candidats implementes (numpy uniquement, comme le reste du package leger
``ict`` -- aucun GPU requis) :

1. **Diversite des points de consigne intrinsèques** (``setpoint_diversity``) --
   dispersion des etats-cibles vers lesquels chaque agent / sous-population
   converge (pont ICT-9). L'alterite se lit comme une *separation dans l'espace
   des consignes* : une monoculture a un setpoint unique, une coalition d'agents
   distincts en a plusieurs.

2. **Information mutuelle entre politiques d'agents** (``policy_mutual_information``) --
   :math:`I(A ; B)` sur les actions co-observees. Capture l'alterite *comportementale* :
   MI elevee = politiques couplees (agents qui se coordonnent en gardant leur
   specifics), MI nulle = politiques independantes, MI *parfaite* = politiques
   identiques (absorption = alterite detruite). La these predit un *maximum
   intermediaire* (coordination sans absorption).

3. **Nombre de bassins d'attracteurs distincts occupes** (``occupied_basin_count``) --
   pont ICT-8 : une trajectoire collective peut occuper plusieurs bassins
   (alterite structurelle preservee) ou en evacuer vers un seul (monoculture
   attire tout).

Un quatrieme candidat (diversite des labellings soutenables, substrat argumentation)
releverait de :mod:`ict.argumentation` (turf po-2025, issue #7289) ; non implemente
ici pour eviter la collision -- il sera branche lors de l'integration du contrat.

Toute PR qui revendique la these de collaboration agentique DOIT satisfaire les 4
clauses du contrat #7291 (mesure pre-enregistree, deux substrats, contre-regime,
predictions pre-enregistrees). Ce module est la jambe *mesure* ; le notebook
``ICT-AgentOtherness-Contract`` pre-enregistre le reste.
"""

from __future__ import annotations

from typing import Optional, Sequence, Tuple

import numpy as np


# --------------------------------------------------------------------------- #
#  Candidat 1 -- diversite des points de consigne intrinsèques (pont ICT-9)    #
# --------------------------------------------------------------------------- #


def setpoint_diversity(
    setpoints: np.ndarray,
    metric: str = "pairwise_mean",
) -> float:
    """Diversite des points de consigne intrinsèques d'une population d'agents.

    Parametres
    ----------
    setpoints : ndarray, shape ``(n_agents, n_dims)``
        Etat-cible (point de consigne) de chaque agent dans un espace commun de
        dimension ``n_dims``. Par exemple les coefficients d'un replicateur
        strategique (ICT-13), les parametres de consigne d'un moteur de
        morphogenese (ICT-9), ou les positions d'ancrage estimees.
    metric : str
        - ``"pairwise_mean"`` (defaut) : distance euclidienne moyenne entre tous
          les couples d'agents. Lineaire en la separation absolue.
        - ``"entropy"`` : entropie de la distribution des setpoints apres
          quantification uniforme (maillage ``sqrt(n_agents)`` par dimension).
          Mesure la dispersion *independamment de l'echelle* (une monoculture
          etendue homothetiquement garde la meme entropie).

    Retour
    ------
    float
        Diversite >= 0. ``0.0`` = monoculture parfaite (tous les setpoints
        identiques). Croit avec la separation / la dispersion.

    Limites documentees (clause 1 du contrat #7291)
    -----------------------------------------------
    - **Sensibilite a l'echelle** (attenuée par ``metric="entropy"``) : une
      "grande" monoculture (setpoints proches mais étalés par homothétie)
      gonfle ``pairwise_mean`` sans gain d'alterite reel.
    - **Depend a un espace commun** : exige que les setpoints soient
      comparables dans un meme espace. Des agents heterogenes (consignes dans
      des espaces differents) ne sont pas mesurables directement -- il faut
      une projection commune, qui est un choix de modele.
    - **Alterite != valeur** : une diversite elevee n'est pas *ipso facto*
      benefique (des setpoints adverses = conflit, pas cooperation). La these
      sera testee via la *covariance* avec le budget (clause 2), non via cette
      mesure seule.
    """
    sp = np.asarray(setpoints, dtype=float)
    if sp.ndim != 2:
        raise ValueError(f"setpoints doit etre 2D (n_agents, n_dims), recu shape {sp.shape}")
    n_agents = sp.shape[0]
    if n_agents < 2:
        return 0.0

    if metric == "pairwise_mean":
        # distance euclidienne moyenne sur tous les couples (i<j)
        diffs = sp[:, None, :] - sp[None, :, :]
        dist = np.sqrt((diffs ** 2).sum(axis=-1))
        iu = np.triu_indices(n_agents, k=1)
        return float(dist[iu].mean())

    if metric == "entropy":
        # quantification uniforme : sqrt(n_agents) bins par dimension
        n_bins = max(2, int(np.sqrt(n_agents)))
        quantized = np.empty_like(sp, dtype=int)
        for d in range(sp.shape[1]):
            col = sp[:, d]
            lo, hi = col.min(), col.max()
            if hi - lo < 1e-12:
                quantized[:, d] = 0
            else:
                quantized[:, d] = np.clip(
                    ((col - lo) / (hi - lo) * n_bins).astype(int), 0, n_bins - 1
                )
        # entropie de Shannon de la distribution des setpoints quantifies
        _, counts = np.unique(quantized, axis=0, return_counts=True)
        p = counts / counts.sum()
        return float(-(p * np.log(p)).sum())

    raise ValueError(f"metric inconnu : {metric!r} (attendu 'pairwise_mean' ou 'entropy')")


# --------------------------------------------------------------------------- #
#  Candidat 2 -- information mutuelle entre politiques d'agents                 #
# --------------------------------------------------------------------------- #


def policy_mutual_information(
    joint_counts: np.ndarray,
) -> float:
    """Information mutuelle entre les politiques de deux agents (candidat 2).

    :math:`I(A ; B) = \\sum_{a,b} p(a,b) \\log \\frac{p(a,b)}{p(a)\\,p(b)}`.

    Parametres
    ----------
    joint_counts : ndarray, shape ``(n_actions_A, n_actions_B)``
        Matrice de comptage des actions co-observees : ``joint_counts[i, j]`` =
        nombre de pas ou l'agent A a pris l'action ``i`` et l'agent B l'action
        ``j`` simultanement. Convertie en distribution jointe par normalisation.

    Retour
    ------
    float
        Information mutuelle en nats, >= 0. ``0.0`` = politiques
        independantes. Croit avec le couplage.

    Limites documentees (clause 1 du contrat #7291)
    -----------------------------------------------
    - **MI elevee est ambigue** : elle peut signaler une *coordination*
      (agents distincts qui se synchronisent) OU une *absorption* (agents
      reduits a une meme politique). La these distingue les deux par la
      *covariance avec le budget* (clause 2) et le *contre-regime* (clause 3) :
      l'absorption est robuste a court terme puis s'effondre, la coordination
      reste resiliente. La MI seule ne tranche pas.
    - **Corrigee pour le biais d'echantillonnage ?** Non (MI empirique brute).
      Pour petits echantillons, utiliser un estimateur corrige (Miller-Madow)
      dans le notebook -- la mesure nue surestime la MI. Documente dans le
      notebook d'application.
    - **Actions discretes uniquement**. Pour politiques continues, passer par
      une quantification ou une estimation par k-NN (hors scope de cette
      primitive).
    """
    jc = np.asarray(joint_counts, dtype=float)
    if jc.ndim != 2:
        raise ValueError(f"joint_counts doit etre 2D, recu shape {jc.shape}")
    total = jc.sum()
    if total <= 0:
        return 0.0
    p = jc / total
    pa = p.sum(axis=1, keepdims=True)
    pb = p.sum(axis=0, keepdims=True)
    # termes ou p>0 pour eviter 0*log0
    mask = p > 0
    return float((p[mask] * (np.log(p[mask]) - np.log((pa @ pb)[mask]))).sum())


# --------------------------------------------------------------------------- #
#  Candidat 3 -- nombre de bassins d'attracteurs distincts occupes (pont ICT-8) #
# --------------------------------------------------------------------------- #


def occupied_basin_count(
    trajectory: np.ndarray,
    n_neighbors: int = 5,
) -> int:
    """Nombre de bassins d'attracteurs distincts effectivement occupes (candidat 3).

    Estime le nombre de *modes* (amas denses) occupes par une trajectoire
    collective dans l'espace d'etats, via une connectivite de plus-proches-
    voisins : deux points de la trajectoire appartiennent au meme bassin s'ils
    sont relies par une chaine de points mutuellement proches (clique de k-NN).
    Pont ICT-8 (paysages d'attracteurs, May 1977).

    Parametres
    ----------
    trajectory : ndarray, shape ``(n_steps, n_dims)``
        Trajectoire collective dans l'espace d'etats (une ligne par pas de temps).
    n_neighbors : int
        Nombre de plus proches voisins pour la connectivite (defaut 5).
        Croit = bassins plus fusionnes ; decroit = sur-segmentation.

    Retour
    ------
    int
        Nombre de composantes connexes (bassins) >= 1. ``1`` = trajectoire
        cantonnee a un seul bassin (monoculture / attracteur unique).

    Limites documentees (clause 1 du contrat #7291)
    -----------------------------------------------
    - **Sensibilite a ``n_neighbors``** : le compte depend du seuil de
      connectivite. Reporter dans le notebook une analyse de stabilite
      (compte vs ``n_neighbors``) pour distinguer un vrai multi-bassins d'un
      artefact de sur-segmentation.
    - **Bassins occupes != bassins existants** : une trajectoire peut *eviter*
      des bassins stables (alterite potentielle non realisee). Cette mesure
      ne capture que l'alterite *effectivement visitee*.
    - **Espace d'etats continu** : pas de discretisation, mais la connectivite
      k-NN peut fusionner des bassins proches dans des regimes de bruit eleve.
      Complementaire de ``setpoint_diversity`` (qui mesure la separation des
      cibles, pas l'occupation effective).
    """
    traj = np.asarray(trajectory, dtype=float)
    if traj.ndim != 2:
        raise ValueError(f"trajectory doit etre 2D (n_steps, n_dims), recu shape {traj.shape}")
    n = traj.shape[0]
    if n <= 1:
        return 1
    k = min(n_neighbors, n - 1)
    if k < 1:
        return n

    # plus proches voisins (distance euclidienne) -> graphe de connectivite
    diffs = traj[:, None, :] - traj[None, :, :]
    dist = np.sqrt((diffs ** 2).sum(axis=-1))
    np.fill_diagonal(dist, np.inf)
    # k-NN mask (symétrisé : arete si l'un est voisin de l'autre)
    knn = np.zeros((n, n), dtype=bool)
    for i in range(n):
        nn_idx = np.argpartition(dist[i], k)[:k]
        knn[i, nn_idx] = True
    adj = knn | knn.T

    # composantes connexes (BFS) -> bassins
    visited = np.zeros(n, dtype=bool)
    n_basins = 0
    for start in range(n):
        if visited[start]:
            continue
        n_basins += 1
        stack = [start]
        visited[start] = True
        while stack:
            node = stack.pop()
            for nb in np.where(adj[node])[0]:
                if not visited[nb]:
                    visited[nb] = True
                    stack.append(int(nb))
    return int(n_basins)
