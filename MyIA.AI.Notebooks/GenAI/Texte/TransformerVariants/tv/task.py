"""Tâches synthétiques pour l'étude de l'internalisation du raisonnement.

Ce module pose les **deux** tâches utilisées par TV-03 :

- :class:`MarqueurSingleHop` : un marqueur en position 0, du remplissage, un jeton de requête
  en dernière position. Le modèle doit retrouver le marqueur en sortie. Tâche **single-hop**
  (résolue trivialement par attention directe, voir TV-00b cellule 26).

- :class:`MarqueurMultiHop` : **n** marqueurs en début de séquence, puis un **jeton de
  question** indiquant lequel des marqueurs est demandé. Tâche **multi-sauts** au sens de
  Huang et al. 2026 : le modèle doit (a) reconnaître la valeur du jeton QUESTION, puis
  (b) récupérer le marqueur correspondant. C'est le discriminant H.2 du dispatch ai-01
  sur #17540 — une tâche qu'un modèle sans chaîne de pensée résout aussi bien ne démontre
  rien.

Hasard exactitude :

- :class:`MarqueurSingleHop` : 1 / ``N_MARQUEURS`` (1/8 par défaut).
- :class:`MarqueurMultiHop` : 1 / ``N_MARQUEURS`` (la cible est l'un des marqueurs,
  indépendamment de la question ; le mécanisme à apprendre est la sélection conditionnelle,
  pas la simple mémorisation).

Tell c.1493 strict fondateur nuance — **origine** : ces deux tâches sont dérivées de TV-00b
cellule 26 (la single-hop), avec extension multi-sauts. La structure est volontairement
minimale pour qu'un transformer jouet (~100K params) puisse la résoudre avec marge en
CPU, et qu'un entraînement CoT-vs-answer-only y soit discriminable.
"""
from __future__ import annotations

import math
from dataclasses import dataclass

import torch
import torch.nn.functional as F


@dataclass
class Vocab:
    """Vocabulaire d'une tâche marqueur.

    Le vocabulaire a trois couches :
    - ``N_MARQUEURS`` tokens distincts (les "objets" à récupérer).
    - ``N_REMPLISSAGE`` tokens de remplissage (les "distracteurs").
    - ``N_QUESTIONS`` tokens QUESTION(1..N_QUESTIONS) (le "selecteur").
    - 1 jeton REQUETE final (le "déclencheur de réponse").
    """

    N_MARQUEURS: int = 8
    N_REMPLISSAGE: int = 10
    N_QUESTIONS: int = 1  # 1 = single-hop (Q=0 trivial), >1 = multi-sauts

    def __post_init__(self):
        assert self.N_MARQUEURS >= 2
        assert self.N_REMPLISSAGE >= 2
        assert self.N_QUESTIONS >= 1
        self.taille_marqueurs = self.N_MARQUEURS
        self.taille_remplissage = self.N_MARQUEURS + self.N_REMPLISSAGE
        self.taille_questions = self.taille_remplissage + self.N_QUESTIONS
        self.JETON_REQUETE = self.taille_questions
        self.VOCAB = self.JETON_REQUETE + 1

    def jeton_question(self, k: int) -> int:
        """Indice du token QUESTION(k). k dans [0, N_QUESTIONS)."""
        assert 0 <= k < self.N_QUESTIONS
        return self.taille_remplissage + k


@dataclass
class Lot:
    """Un lot (batch) de séquences avec leur cible.

    - ``x`` : (B, T) tenseur d'indices.
    - ``y`` : (B,) cible = l'indice du marqueur que le modèle doit prédire à la position
      de requête.
    - ``q`` : (B,) indice de la question (quel marqueur est demandé). 0 en single-hop.
    """

    x: torch.Tensor
    y: torch.Tensor
    q: torch.Tensor


def lot_single_hop(n: int, T: int, gen: torch.Generator, vocab: Vocab) -> Lot:
    """Génère un lot single-hop : un marqueur en position 0, requête en T-1, cible = marqueur.

    Reproduit TV-00b cellule 26.
    """
    assert vocab.N_QUESTIONS == 1, "lot_single_hop exige N_QUESTIONS == 1"
    marqueur = torch.randint(0, vocab.N_MARQUEURS, (n, 1), generator=gen)
    remplissage = torch.randint(
        vocab.N_MARQUEURS,
        vocab.taille_remplissage,
        (n, T - 2),
        generator=gen,
    )
    requete = torch.full((n, 1), vocab.JETON_REQUETE)
    x = torch.cat([marqueur, remplissage, requete], dim=1)
    q = torch.zeros(n, dtype=torch.long)
    return Lot(x=x, y=x[:, 0].clone(), q=q)


def lot_multi_hop(
    n: int,
    T: int,
    gen: torch.Generator,
    vocab: Vocab,
) -> Lot:
    """Génère un lot multi-sauts : N_QUESTIONS marqueurs + jeton QUESTION(k) + requête.

    Séquence :
        [M1, M2, ..., M_Q, ..., remplissage, QUESTION(k), REQUETE]

    où ``M_k`` est la cible que le modèle doit prédire à la position de requête.
    Le discriminateur : ``QUESTION(k)`` force le modèle à ignorer les ``Q-1`` autres
    marqueurs ; un modèle qui se contente d'extraire le dernier marqueur est en
    échec quand ``k != Q-1``.
    """
    Q = vocab.N_QUESTIONS
    assert Q >= 2, "lot_multi_hop exige N_QUESTIONS >= 2"

    # Marqueurs en début (Q positions)
    marqueurs = torch.randint(0, vocab.N_MARQUEURS, (n, Q), generator=gen)

    # Question choisie par item (uniforme sur [0, Q))
    q_idx = torch.randint(0, Q, (n,), generator=gen)

    # Remplissage (entre les marqueurs et la zone question/requete)
    n_remplissage = T - Q - 2
    assert n_remplissage >= 0, f"T={T} trop court pour Q={Q} marqueurs + 2 jetons"
    remplissage = torch.randint(
        vocab.N_MARQUEURS,
        vocab.taille_remplissage,
        (n, n_remplissage),
        generator=gen,
    )

    # Jetons QUESTION et REQUETE
    questions = torch.tensor(
        [vocab.jeton_question(k.item()) for k in q_idx],
        dtype=torch.long,
    ).unsqueeze(1)
    requete = torch.full((n, 1), vocab.JETON_REQUETE)

    x = torch.cat([marqueurs, remplissage, questions, requete], dim=1)

    # Cible = marqueur q_idx[k] pour l'item k
    y = marqueurs.gather(1, q_idx.unsqueeze(1)).squeeze(1)

    return Lot(x=x, y=y, q=q_idx)


@torch.no_grad()
def evaluer_single_hop(modele, vocab: Vocab, T: int, n: int = 512, graine: int = 99) -> tuple[float, float]:
    """Exactitude et perplexite à la position de requête (single-hop)."""
    gen = torch.Generator().manual_seed(graine)
    lot = lot_single_hop(n, T, gen, vocab)
    logits = modele(lot.x)[:, -1]
    perte = F.cross_entropy(logits, lot.y)
    exactitude = (logits.argmax(-1) == lot.y).float().mean()
    return exactitude.item(), math.exp(perte.item())


@torch.no_grad()
def evaluer_multi_hop(modele, vocab: Vocab, T: int, n: int = 512, graine: int = 99) -> tuple[float, float]:
    """Exactitude et perplexite à la position de requête (multi-sauts)."""
    gen = torch.Generator().manual_seed(graine)
    lot = lot_multi_hop(n, T, gen, vocab)
    logits = modele(lot.x)[:, -1]
    perte = F.cross_entropy(logits, lot.y)
    exactitude = (logits.argmax(-1) == lot.y).float().mean()
    return exactitude.item(), math.exp(perte.item())


def entrainer(
    modele,
    vocab: Vocab,
    T: int,
    multi_hop: bool,
    graine: int,
    pas: int = 200,
    batch: int = 32,
    lr: float = 3e-3,
) -> tuple[float, float, float]:
    """Entraîne un modèle sur la tâche choisie, renvoie (exactitude, perplexite, secondes).

    Tell c.1493 strict fondateur nuance — multi-seed : cette fonction utilise UNE graine.
    La mesure multi-seed (≥4) est dans le grain de mesure suivant (TV-03 v2).
    """
    import time

    torch.manual_seed(graine)
    opt = torch.optim.Adam(modele.parameters(), lr=lr)
    gen = torch.Generator().manual_seed(1234 + graine)
    debut = time.perf_counter()
    for _ in range(pas):
        lot = lot_multi_hop(batch, T, gen, vocab) if multi_hop else lot_single_hop(batch, T, gen, vocab)
        perte = F.cross_entropy(modele(lot.x)[:, -1], lot.y)
        opt.zero_grad()
        perte.backward()
        opt.step()
    secondes = time.perf_counter() - debut
    if multi_hop:
        acc, ppl = evaluer_multi_hop(modele, vocab, T)
    else:
        acc, ppl = evaluer_single_hop(modele, vocab, T)
    return acc, ppl, secondes
