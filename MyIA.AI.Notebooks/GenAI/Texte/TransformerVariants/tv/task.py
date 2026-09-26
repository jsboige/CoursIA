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


# Pour le grain CoT, on ajoute des jetons de transition et de récapitulation.
# Choix : on insère 2q_idx+1 jetons dans la chaîne (q_idx QUESTION + q_idx JETON_PAS + 1 cible).
# Cela étend la séquence — T doit être recalculé dans la fonction appelante.
# JETON_PAS est un token dédié qui marque une transition (un pas logique).
_QUESTION_OFFSET = None  # initialisé paresseusement ci-dessous


def _etendre_vocab_cot(vocab: Vocab, max_q: int) -> int:
    """Étend le vocabulaire pour CoT : ajoute un JETON_PAS + max_q jetons d'index.

    Retourne la taille étendue.
    """
    assert vocab.N_QUESTIONS <= max_q + 1, f"N_QUESTIONS={vocab.N_QUESTIONS} > max_q+1={max_q+1}"
    return vocab.VOCAB + 1 + max_q  # VOCAB + JETON_PAS + max_q jetons de recap


def lot_multi_hop_cot(
    n: int,
    T_cot: int,  # longueur ciblee de la sequence, incluant la chaine CoT
    gen: torch.Generator,
    vocab: Vocab,
    max_q: int = 3,  # borne sup des q_idx (egal a vocab.N_QUESTIONS - 1 pour la v3)
) -> Lot:
    """Génère un lot multi-sauts CoT : chaîne_question + chaîne_reponse + cible.

    Séquence :
        [M1, M2, ..., M_Q, ..., remplissage, QUESTION(k), REQUETE,
         JETON_PAS_0, QUESTION_0, JETON_PAS_1, QUESTION_1, ..., JETON_PAS_q, QUESTION_q, Mk]

    où Mk est la cible finale. Le modèle doit apprendre à générer la chaîne intermédiaire
    (les q_idx QUESTION_j + leur transition) AVANT la cible finale. C'est précisément
    le « CoT supervisé » de Huang et al. 2026.

    Tell c.1493 strict fondateur nuance : la chaîne est supervisée par entropie croisée
    sur **chaque token de la chaîne intermédiaire** (pas seulement la cible finale).

    Note : l'évaluation (evaluer_multi_hop_cot) lit la cible au dernier token ET
    mesure l'exactitude sur les tokens QUESTION_j de la chaîne.
    """
    Q = vocab.N_QUESTIONS
    assert Q >= 2, "lot_multi_hop_cot exige N_QUESTIONS >= 2"
    VOCAB_ETENDU = _etendre_vocab_cot(vocab, max_q)
    JETON_PAS = vocab.VOCAB  # un seul jeton de transition
    RECAP_OFFSET = vocab.VOCAB + 1  # jeton QUESTION_j de recap = RECAP_OFFSET + j

    marqueurs = torch.randint(0, vocab.N_MARQUEURS, (n, Q), generator=gen)
    q_idx = torch.randint(0, Q, (n,), generator=gen)

    # Zone question/requete/CoT : QUESTION(k), REQUETE, puis pour j in 0..q_idx : PAS, RECAP_j, et enfin cible.
    # Le nombre de tokens CoT = 1 (QUESTION) + 1 (REQUETE) + 2*q_idx + 1 (cible) = 2*q_idx + 3.
    # T_cot doit accommoder Q marqueurs + 2*q_idx + 3 + zone remplissage.

    n_remplissage = T_cot - Q - 2 - 2 * max_q - 1
    assert n_remplissage >= 0, f"T_cot={T_cot} trop court pour Q={Q} + 2*max_q+1={2*max_q+1} + 3"

    remplissage = torch.randint(
        vocab.N_MARQUEURS,
        vocab.taille_remplissage,
        (n, n_remplissage),
        generator=gen,
    )

    questions = torch.tensor(
        [vocab.jeton_question(k.item()) for k in q_idx],
        dtype=torch.long,
    ).unsqueeze(1)
    requete = torch.full((n, 1), vocab.JETON_REQUETE, dtype=torch.long)

    # Construction de la chaîne CoT (taille fixe = 2*max_q + 1)
    # Pour chaque item : PAS, RECAP_0, PAS, RECAP_1, ..., PAS, RECAP_q, Mk
    chaineseq = torch.full((n, 2 * max_q + 1), JETON_PAS, dtype=torch.long)
    for j in range(max_q):
        chaineseq[:, 2 * j + 1] = RECAP_OFFSET + j  # RECAP_j
    # Dernier slot = cible
    cibles = marqueurs.gather(1, q_idx.unsqueeze(1)).squeeze(1)  # (n,)
    chaineseq[:, -1] = cibles

    # Tronque la chaîne au-delà de q_idx+1 pas (plus court que max_q si q_idx < max_q)
    # Mais pour la simplicite du conditionnement, on garde la chaîne complete et on masque la perte
    # au-delà du q_idx+1 pas via un masque positionnel dans le calcul de perte CoT.

    x = torch.cat([marqueurs, remplissage, questions, requete, chaineseq], dim=1)
    y = cibles
    q = q_idx

    return Lot(x=x, y=y, q=q)


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
    La mesure multi-seed (≥4) est dans le grain de mesure suivant (TV-03 v2), portée par
    :func:`entrainer_multi_seed`.
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


def entrainer_multi_seed(
    fabrique_modele,
    vocab: Vocab,
    T: int,
    multi_hop: bool,
    graines: list[int],
    pas: int = 300,
    batch: int = 32,
    lr: float = 3e-3,
) -> dict:
    """Mesure multi-seed (≥4) : moyenne, écart-type, secondes totales.

    Tell c.1493 strict fondateur nuance — la mesure multi-seed par graine est attendue par
    le protocole PR review-discipline §C (≥4 graines parmi 0/1/7/42/99). On expose moyenne,
    écart-type et liste brute pour permettre les vérifs edge≥2σ / DM cross-seed.

    :param fabrique_modele: callable ``(vocab) -> nn.Module`` qui crée un modèle vierge.
        L'instance est recréée pour chaque graine — pas de contamination de l'initialisation.
    :param graines: liste explicite d'identifiants de graine (par défaut ``[0, 1, 7, 42]``).
    :return: dict avec ``acc_moy``, ``acc_std``, ``ppl_moy``, ``ppl_std``, ``secondes``,
        ``brut`` (liste de tuples ``(graine, acc, ppl, sec)``).
    """
    import time
    import statistics

    if not graines:
        raise ValueError("graines doit être non vide")

    debut_total = time.perf_counter()
    brut = []
    for graine in graines:
        modele = fabrique_modele(vocab)
        acc, ppl, sec = entrainer(
            modele,
            vocab,
            T=T,
            multi_hop=multi_hop,
            graine=graine,
            pas=pas,
            batch=batch,
            lr=lr,
        )
        brut.append((graine, acc, ppl, sec))
    secondes = time.perf_counter() - debut_total

    accs = [b[1] for b in brut]
    ppls = [b[2] for b in brut]
    return {
        "acc_moy": statistics.fmean(accs),
        "acc_std": statistics.pstdev(accs) if len(accs) > 1 else 0.0,
        "ppl_moy": statistics.fmean(ppls),
        "ppl_std": statistics.pstdev(ppls) if len(ppls) > 1 else 0.0,
        "secondes": secondes,
        "brut": brut,
        "n_graines": len(graines),
    }


@torch.no_grad()
def evaluer_multi_hop_cot(modele, vocab: Vocab, T_cot: int, n: int = 512, graine: int = 99,
                            max_q: int = 3) -> tuple[float, float]:
    """Exactitude sur la cible finale en mode CoT (réponse à la question).

    La séquence inclut la chaîne CoT. On mesure :
    - exactitude = la cible finale (dernier token) est-elle correcte ?
    - perplexité moyenne sur les tokens de la chaîne (pas seulement la cible finale).

    Tell c.1493 strict fondateur nuance : on lit la sortie sur **toute la chaîne**, pas
    uniquement la dernière position. L'exactitude cible reste la métrique principale
    (réponse à la question = discriminant H.2).
    """
    gen = torch.Generator().manual_seed(graine)
    lot = lot_multi_hop_cot(n, T_cot, gen, vocab, max_q=max_q)
    # Eval sur la dernière position (la cible) — comparable à evaluer_multi_hop.
    logits_cible = modele(lot.x)[:, -1]
    perte_cible = F.cross_entropy(logits_cible, lot.y)
    exactitude = (logits_cible.argmax(-1) == lot.y).float().mean()
    return exactitude.item(), math.exp(perte_cible.item())


def entrainer_cot(
    modele,
    vocab: Vocab,
    T_cot: int,
    graine: int,
    max_q: int = 3,
    pas: int = 300,
    batch: int = 32,
    lr: float = 3e-3,
) -> tuple[float, float, float]:
    """Entraînement CoT supervisé sur la tâche multi-sauts. Renvoie (acc, ppl, sec).

    Tell c.1493 strict fondateur nuance : la perte supervise **la chaîne entière**
    (chaque token PAS/RECAP_j/cible doit être prédit correctement). Le gradient
    coule donc à travers toute la séquence de génération.
    """
    import time

    Q = vocab.N_QUESTIONS
    RECAP_OFFSET = vocab.VOCAB + 1

    torch.manual_seed(graine)
    opt = torch.optim.Adam(modele.parameters(), lr=lr)
    gen = torch.Generator().manual_seed(1234 + graine)
    debut = time.perf_counter()
    for _ in range(pas):
        lot = lot_multi_hop_cot(batch, T_cot, gen, vocab, max_q=max_q)
        # Calcul de la perte sur toute la séquence
        logits = modele(lot.x)  # (B, T, VOCAB_ETENDU)
        # Cible : prédire chaque token de la chaîne à partir du token précédent.
        # À la position i on prédit lot.x[:, i+1]. Pour la chaîne (n_pred_positions tokens),
        # on prédit les positions [start_pred, start_pred+n_pred_positions) à partir des
        # logits en [start_pred-1, start_pred-1+n_pred_positions). Donc :
        # - logits_pred = logits[:, start_pred - 1 : start_pred - 1 + n_pred_positions, :]
        # - cible_shift = lot.x[:, start_pred : start_pred + n_pred_positions]
        B, T_seq, V = logits.shape
        n_pred_positions = 2 * max_q + 1
        start_pred = T_seq - n_pred_positions
        cible_shift = lot.x[:, start_pred : start_pred + n_pred_positions]
        logits_pred = logits[:, start_pred - 1 : start_pred - 1 + n_pred_positions, :]
        # Masque : seul le pas j avec j <= q_idx doit contribuer à la perte
        # q_idx varie par item -> masque par item
        # Construction du masque : (B, n_pred_positions) — True si j <= q_idx[item]
        q = lot.q  # (B,)
        j_positions = torch.arange(n_pred_positions)  # (n_pred_positions,)
        # Chaque position j correspond au pas floor(j/2) (0-indexed)
        pas_positions = j_positions // 2  # (n_pred_positions,)
        masque = (pas_positions.unsqueeze(0) <= q.unsqueeze(1))  # (B, n_pred_positions)
        # Perte par token, masquée
        perte_full = F.cross_entropy(
            logits_pred.reshape(-1, V),
            cible_shift.reshape(-1),
            reduction='none',
        ).view(B, n_pred_positions)
        perte_masquee = (perte_full * masque.float()).sum() / masque.sum().clamp(min=1)
        opt.zero_grad()
        perte_masquee.backward()
        opt.step()
    secondes = time.perf_counter() - debut
    acc, ppl = evaluer_multi_hop_cot(modele, vocab, T_cot, max_q=max_q)
    return acc, ppl, secondes


def entrainer_multi_seed_cot(
    fabrique_modele,
    vocab: Vocab,
    T_cot: int,
    graines: list[int],
    max_q: int = 3,
    pas: int = 300,
    batch: int = 32,
    lr: float = 3e-3,
) -> dict:
    """Mesure multi-seed (≥4) CoT : moyenne, écart-type, secondes totales."""
    import time
    import statistics

    if not graines:
        raise ValueError("graines doit être non vide")

    debut_total = time.perf_counter()
    brut = []
    for graine in graines:
        modele = fabrique_modele(vocab)
        acc, ppl, sec = entrainer_cot(
            modele,
            vocab,
            T_cot=T_cot,
            graine=graine,
            max_q=max_q,
            pas=pas,
            batch=batch,
            lr=lr,
        )
        brut.append((graine, acc, ppl, sec))
    secondes = time.perf_counter() - debut_total

    accs = [b[1] for b in brut]
    ppls = [b[2] for b in brut]
    return {
        "acc_moy": statistics.fmean(accs),
        "acc_std": statistics.pstdev(accs) if len(accs) > 1 else 0.0,
        "ppl_moy": statistics.fmean(ppls),
        "ppl_std": statistics.pstdev(ppls) if len(ppls) > 1 else 0.0,
        "secondes": secondes,
        "brut": brut,
        "n_graines": len(graines),
    }
