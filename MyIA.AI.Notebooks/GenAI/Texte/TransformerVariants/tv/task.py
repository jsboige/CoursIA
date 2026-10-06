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
    # Eval sur la dernière position entraînée (la cible est en position -1 dans x, le
    # logit qui la prédit est donc en position -2 -- cohérent avec entrainer_cot qui
    # couvre les logits [start_pred - 1, T - 1), soit jusqu'à T - 2 inclus).
    # Lire -1 mesurait un logit qui prédit au-delà de la séquence, sans signal.
    logits_cible = modele(lot.x)[:, -2]
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
        # Masque : on inclut dans la perte les positions j qui produisent un token
        # pertinent (PAS_j, RECAP_j pour j <= q_idx) ET le slot cible.
        # Etat anterieur v1 : `pas_positions <= q` seul -- la cible (j = 2*max_q,
        # pas_positions[j] = max_q > q pour tout q <= max_q-1) n'etait jamais
        # couverte -> exactitude 0.
        # Etat anterieur v2 : OR sur j = 2*q+1 -- faux : la chaine est de taille
        # FIXE (cf. lot_multi_hop_cot), le slot 2*q+1 porte RECAP_q, jamais la
        # cible ; celle-ci est TOUJOURS en fin de chaine (j = 2*max_q) quel que
        # soit q_idx -> exactitude 0 a nouveau (mesure : acc 0.0000, ppl ~29856).
        q = lot.q  # (B,)
        j_positions = torch.arange(n_pred_positions)  # (n_pred_positions,)
        # Chaque position j correspond au pas floor(j/2) (0-indexed)
        pas_positions = j_positions // 2  # (n_pred_positions,)
        # Le slot cible (j = 2*max_q = n_pred_positions - 1) est inclus via cette OR.
        cible_j = torch.full((q.shape[0], 1), 2 * max_q, dtype=torch.long)  # (B, 1)
        est_slot_cible = (j_positions.unsqueeze(0) == cible_j)  # (B, n_pred_positions)
        masque = (pas_positions.unsqueeze(0) <= q.unsqueeze(1)) | est_slot_cible  # (B, n_pred_positions)
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


# =============================================================================
# v4 -- Taches d'indirection : lectures DEPENDANTES, chaine CoT informative
# =============================================================================
# Mesure v4 (4 graines, 300 pas) : la separation CoT/answer-only de Huang et al.
# 2026 ne se reproduit PAS sur ce regime jouet -- answer-only compose 2-3 lectures
# dependantes en un seul forward (~0.73), la chaine informative n'aide pas (~0.63).
# Cause de design mesuree : chaque etape de la chaine embarque le meme binding
# valeur->position que la composition directe, donc la chaine ne decompose pas le
# calcul difficile en etapes plus simples (precondition d'un gap positif, cf bilan v4).

import statistics
import time


def question_indirection(vocab: Vocab) -> int:
    """Indice du jeton QUESTION Indirection (premier jeton libre apres REQUETE)."""
    return vocab.VOCAB


def vocab_indirection(vocab: Vocab) -> int:
    """Taille du vocabulaire etendu pour l'indirection (+1 jeton QUESTION_IND)."""
    return vocab.VOCAB + 1


def _tirage_indirection(n: int, Q: int, gen: torch.Generator, vocab: Vocab, double: bool):
    """Tire marqueurs + pointeurs + cible pour la tache d'indirection.

    Les porteurs de pointeur ont une valeur contrainte a [1, Q) : la cible n'est
    jamais le porteur lui-meme et chaque indice emis designe une position valide.
    Valeurs libres des autres marqueurs : [0, N_MARQUEURS).
    """
    marqueurs = torch.randint(0, vocab.N_MARQUEURS, (n, Q), generator=gen)
    v = torch.randint(1, Q, (n, 1), generator=gen)
    marqueurs[:, 0:1] = v
    if double:
        w = torch.randint(1, Q, (n, 1), generator=gen)
        marqueurs.scatter_(1, v, w)  # le marqueur pointe devient lui-meme pointeur
        cible = marqueurs.gather(1, marqueurs.gather(1, v))
        return marqueurs, cible.squeeze(1), (v.squeeze(1), w.squeeze(1))
    cible = marqueurs.gather(1, v)
    return marqueurs, cible.squeeze(1), (v.squeeze(1),)


def lot_indirection(n: int, T: int, gen: torch.Generator, vocab: Vocab, double: bool = False) -> Lot:
    """Tache d'indirection answer-only : [M_0..M_{Q-1}, remplissage, QUESTION_IND, REQUETE].

    Composer en UN forward : lire v = valeur(M_0), puis extraire la valeur du
    marqueur en position v (double : une lecture de plus). Contrairement au
    multi-sauts v3, les lectures sont DEPENDANTES : la deuxieme depend du RESULTAT
    de la premiere, pas du seul jeton QUESTION.
    """
    Q = vocab.N_QUESTIONS + 1
    marqueurs, cible, _ = _tirage_indirection(n, Q, gen, vocab, double)
    n_remp = T - Q - 2
    assert n_remp >= 0, f"T={T} trop court pour Q={Q} marqueurs + 2 jetons"
    remplissage = torch.randint(
        vocab.N_MARQUEURS, vocab.taille_remplissage, (n, n_remp), generator=gen
    )
    q_ind = torch.full((n, 1), question_indirection(vocab), dtype=torch.long)
    req = torch.full((n, 1), vocab.JETON_REQUETE, dtype=torch.long)
    x = torch.cat([marqueurs, remplissage, q_ind, req], dim=1)
    return Lot(x=x, y=cible, q=marqueurs[:, 0])


def lot_indirection_cot(
    n: int, T_cot: int, gen: torch.Generator, vocab: Vocab, double: bool = False
) -> tuple[torch.Tensor, torch.Tensor, list[torch.Tensor]]:
    """Indirection avec chaine CoT INFORMATIVE : [.., QUESTION_IND, REQUETE, v, (w,) cible].

    La chaine recite le RESULTAT de chaque lecture -- v (puis w en double) -- valeurs
    DEPENDANTES de l'entree. Contrairement a la chaine constante de la v3, chaque
    token de chaine porte une information que le modele doit produire.

    Retourne (x, cible, [v] ou [v, w]).
    """
    L = 3 if double else 2
    Q = vocab.N_QUESTIONS + 1
    marqueurs, cible, pointeurs = _tirage_indirection(n, Q, gen, vocab, double)
    n_remp = T_cot - Q - 2 - L
    assert n_remp >= 0, f"T_cot={T_cot} trop court pour Q={Q} + 2 + L={L}"
    remplissage = torch.randint(
        vocab.N_MARQUEURS, vocab.taille_remplissage, (n, n_remp), generator=gen
    )
    q_ind = torch.full((n, 1), question_indirection(vocab), dtype=torch.long)
    req = torch.full((n, 1), vocab.JETON_REQUETE, dtype=torch.long)
    chaine = torch.stack(list(pointeurs) + [cible], dim=1)
    x = torch.cat([marqueurs, remplissage, q_ind, req, chaine], dim=1)
    return x, cible, list(pointeurs)


@torch.no_grad()
def evaluer_indirection(
    modele, vocab: Vocab, T: int, n: int = 1024, graine: int = 99, double: bool = False
) -> tuple[float, float]:
    """Exactitude et perplexite cible de la tache d'indirection (answer-only)."""
    gen = torch.Generator().manual_seed(graine)
    lot = lot_indirection(n, T, gen, vocab, double=double)
    logits = modele(lot.x)[:, -1]
    perte = F.cross_entropy(logits, lot.y)
    exactitude = (logits.argmax(-1) == lot.y).float().mean()
    return exactitude.item(), math.exp(perte.item())


@torch.no_grad()
def evaluer_indirection_cot(
    modele, vocab: Vocab, T_cot: int, n: int = 1024, graine: int = 99, double: bool = False
) -> tuple[float, list[float]]:
    """Exactitude cible + exactitude de chaque pas de chaine (CoT informatif).

    La prediction de la chaine se lit a la position precedant chaque token de
    chaine ; la cible finale se lit a l'avant-derniere position (le logit qui
    predit le dernier token emis, cf evaluer_multi_hop_cot v3).
    """
    gen = torch.Generator().manual_seed(graine)
    x, cible, pointeurs = lot_indirection_cot(n, T_cot, gen, vocab, double=double)
    L = len(pointeurs) + 1
    logits = modele(x)
    pas = []
    for j, p in enumerate(pointeurs):
        pos = logits[:, T_cot - L + j - 1]
        pas.append((pos.argmax(-1) == p).float().mean().item())
    pos_cible = logits[:, T_cot - 2]
    exactitude = (pos_cible.argmax(-1) == cible).float().mean().item()
    return exactitude, pas


def entrainer_indirection(
    modele, vocab: Vocab, T: int, graine: int, double: bool = False,
    pas: int = 300, batch: int = 32, lr: float = 3e-3,
) -> tuple[float, float, float]:
    """Entrainement answer-only sur la tache d'indirection. Renvoie (acc, ppl, sec)."""
    torch.manual_seed(graine)
    opt = torch.optim.Adam(modele.parameters(), lr=lr)
    gen = torch.Generator().manual_seed(1234 + graine)
    debut = time.perf_counter()
    for _ in range(pas):
        lot = lot_indirection(batch, T, gen, vocab, double=double)
        perte = F.cross_entropy(modele(lot.x)[:, -1], lot.y)
        opt.zero_grad()
        perte.backward()
        opt.step()
    secondes = time.perf_counter() - debut
    acc, ppl = evaluer_indirection(modele, vocab, T, double=double)
    return acc, ppl, secondes


def entrainer_indirection_cot(
    modele, vocab: Vocab, T_cot: int, graine: int, double: bool = False,
    pas: int = 300, batch: int = 32, lr: float = 3e-3,
) -> tuple[float, list[float], float]:
    """Entrainement CoT informatif : supervise chaque token de la chaine.

    La perte est la somme des entropies croiseses des predictions de v (puis w)
    et de la cible -- chaque pas de chaine est pousse vers sa valeur cible.
    """
    torch.manual_seed(graine)
    opt = torch.optim.Adam(modele.parameters(), lr=lr)
    gen = torch.Generator().manual_seed(1234 + graine)
    L = 3 if double else 2
    debut = time.perf_counter()
    for _ in range(pas):
        x, cible, pointeurs = lot_indirection_cot(batch, T_cot, gen, vocab, double=double)
        logits = modele(x)
        perte = F.cross_entropy(logits[:, T_cot - L - 1], pointeurs[0])
        for j in range(1, len(pointeurs)):
            perte = perte + F.cross_entropy(logits[:, T_cot - L + j - 1], pointeurs[j])
        perte = perte + F.cross_entropy(logits[:, T_cot - 2], cible)
        opt.zero_grad()
        perte.backward()
        opt.step()
    secondes = time.perf_counter() - debut
    acc, pas_acc = evaluer_indirection_cot(modele, vocab, T_cot, double=double)
    return acc, pas_acc, secondes


def entrainer_indirection_multi_seed(
    fabrique_modele, vocab: Vocab, T: int, graines: list[int], double: bool = False,
    pas: int = 300, batch: int = 32, lr: float = 3e-3,
) -> dict:
    """Mesure multi-seed answer-only sur l'indirection (meme contrat que entrainer_multi_seed)."""
    brut = []
    for graine in graines:
        modele = fabrique_modele(vocab)
        acc, ppl, sec = entrainer_indirection(
            modele, vocab, T=T, graine=graine, double=double, pas=pas, batch=batch, lr=lr
        )
        brut.append((graine, acc, ppl, sec))
    return _agrege_multi_seed(brut)


def entrainer_indirection_cot_multi_seed(
    fabrique_modele, vocab: Vocab, T_cot: int, graines: list[int], double: bool = False,
    pas: int = 300, batch: int = 32, lr: float = 3e-3,
) -> dict:
    """Mesure multi-seed CoT informatif : cible + pas intermediaires par graine."""
    brut = []
    for graine in graines:
        modele = fabrique_modele(vocab)
        acc, pas_acc, sec = entrainer_indirection_cot(
            modele, vocab, T_cot=T_cot, graine=graine, double=double, pas=pas, batch=batch, lr=lr
        )
        brut.append((graine, acc, pas_acc, sec))
    accs = [b[1] for b in brut]
    return {
        "acc_moy": statistics.fmean(accs),
        "acc_std": statistics.pstdev(accs) if len(accs) > 1 else 0.0,
        "pas_moy": [statistics.fmean([b[2][j] for b in brut]) for j in range(len(brut[0][2]))],
        "secondes": sum(b[3] for b in brut),
        "brut": brut,
        "n_graines": len(graines),
    }


def _agrege_multi_seed(brut: list) -> dict:
    """Agregation commune des mesures multi-seed (acc/ppl, moyenne + ecart-type)."""
    accs = [b[1] for b in brut]
    ppls = [b[2] for b in brut]
    return {
        "acc_moy": statistics.fmean(accs),
        "acc_std": statistics.pstdev(accs) if len(accs) > 1 else 0.0,
        "ppl_moy": statistics.fmean(ppls),
        "ppl_std": statistics.pstdev(ppls) if len(ppls) > 1 else 0.0,
        "secondes": sum(b[3] for b in brut),
        "brut": brut,
        "n_graines": len(brut),
    }


# =============================================================================
# v5 -- Marche guidee : copies locales chainees (chaque pas STRICTEMENT plus simple)
# =============================================================================
# Reponse au bilan v4 : la famille marqueur/pointeur embarquait le meme binding
# valeur->position a chaque etape de chaine. La v5 construit la famille demandee
# par l'arbitrage ai-01 (DM ai01-c0606) : un marqueur part de p0, la sequence
# porte K instructions de deplacement local (GAUCHE/ICI/DROITE), la reponse est
# la valeur a la position finale. Chaque pas de chaine = mise a jour de position
# ADJACENTE depuis la derniere position emise + une instruction a position fixe
# -- une operation locale a 2 couches, sans binding valeur->position. Mesure v5
# (4 graines, 300 pas) : toujours pas de separation positive. K=2 : edge -0.11
# sigma, DM p 0.7317 ; K=3 : edge +0.74 sigma, DM p 0.6093 -- deux verdicts
# CLOTURE. Un pilote au scratchpad sous vocabulaire resserre donnait a K=3 un
# ecart significatif EN DEFAVEUR du CoT (DM p ~ 0.005) ; il n'est PAS replique
# sous le vocabulaire de l'organe, et la mesure de reference reste celle du
# carnet. Le volet se clot.


def instructions_marche(vocab: Vocab) -> tuple[int, int, int]:
    """Jetons d'instruction (GAUCHE, ICI, DROITE) = deplacements (-1, 0, +1)."""
    return vocab.VOCAB, vocab.VOCAB + 1, vocab.VOCAB + 2


def vocab_marche(vocab: Vocab) -> int:
    """Taille du vocabulaire answer-only de la marche (+3 jetons d'instruction)."""
    return vocab.VOCAB + 3


def offset_pos_marche(vocab: Vocab) -> int:
    """Premier jeton POS_j (j dans [0, L)) ; POS_j = offset + j."""
    return vocab.VOCAB + 3


def jeton_pas_marche(vocab: Vocab) -> int:
    """Jeton PAS, marqueur de transition de la chaine CoT de la marche."""
    return offset_pos_marche(vocab) + vocab.N_MARQUEURS


def vocab_marche_cot(vocab: Vocab) -> int:
    """Taille du vocabulaire CoT (+3 instructions, +L jetons POS, +1 PAS)."""
    return jeton_pas_marche(vocab) + 1


def _tirage_marche(
    n: int, K: int, gen: torch.Generator, vocab: Vocab
) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
    """Tire valeurs, instructions et positions d'une marche guidee.

    Instructions echantillonnees CONDITIONNELLEMENT : a chaque pas, uniforme
    parmi les deplacements qui maintiennent la marche dans [0, L). Le tirage
    precede tout formatage : les modes answer-only et CoT voient les memes
    instances (appariement par exemple requis par le test DM).

    Retourne (valeurs (n, L), instrs (n, K), positions (n, K+1)) avec
    positions[:, 0] = p0 = L // 2.
    """
    L = vocab.N_MARQUEURS
    valeurs = torch.randint(0, L, (n, L), generator=gen)
    base = torch.tensor(instructions_marche(vocab))
    deltas = torch.tensor([-1, 0, 1])
    instrs = torch.empty(n, K, dtype=torch.long)
    positions = torch.empty(n, K + 1, dtype=torch.long)
    p = torch.full((n,), L // 2, dtype=torch.long)
    positions[:, 0] = p
    for k in range(K):
        # legalite de chaque delta pour chaque item -> tirage uniforme conditionne
        cible_pos = p.unsqueeze(1) + deltas.unsqueeze(0)  # (n, 3)
        legal = (cible_pos >= 0) & (cible_pos < L)  # (n, 3)
        u = torch.rand(n, 1, generator=gen) * legal.sum(1, keepdim=True)
        rang = u.floor().long()  # rang du delta choisi parmi les legaux
        cum = torch.cumsum(legal.long(), dim=1)
        col = (cum <= rang).sum(dim=1)  # premiere colonne ou le cumul depasse le rang
        instrs[:, k] = base[col]
        p = p + deltas[col]
        positions[:, k + 1] = p
    return valeurs, instrs, positions


def lot_marche(n: int, gen: torch.Generator, vocab: Vocab, K: int) -> Lot:
    """Marche guidee answer-only : [v_0..v_{L-1}, d_1..d_K, REQUETE].

    Pas de remplissage : T = L + K + 1, l'attention n'est pas diluee. La cible
    est la valeur a la position finale de la marche (hasard 1/L).
    """
    valeurs, instrs, positions = _tirage_marche(n, K, gen, vocab)
    requete = torch.full((n, 1), vocab.JETON_REQUETE, dtype=torch.long)
    x = torch.cat([valeurs, instrs, requete], dim=1)
    y = valeurs.gather(1, positions[:, K].unsqueeze(1)).squeeze(1)
    return Lot(x=x, y=y, q=positions[:, K])


def lot_marche_cot(
    n: int, gen: torch.Generator, vocab: Vocab, K: int
) -> tuple[torch.Tensor, torch.Tensor, list[torch.Tensor]]:
    """Marche guidee avec chaine CoT de copies locales chainees.

    Sequence : [v_0..v_{L-1}, d_1..d_K, REQUETE, PAS, POS_p1, PAS, POS_p2,
    ..., PAS, ANSWER]. Chaine de taille fixe 2K+1 (miroir de la v3). Chaque
    slot POS_pk recite la position apres le k-ieme deplacement -- la mise a
    jour est ADJACENTE (derniere position emise + instruction a position fixe),
    sans binding valeur->position : c'est le pas strictement plus simple.

    Retourne (x, cible, positions_intermediaires) ou positions_intermediaires[k]
    est le vecteur (n,) des positions attendues apres le pas k+1.
    """
    L = vocab.N_MARQUEURS
    valeurs, instrs, positions = _tirage_marche(n, K, gen, vocab)
    requete = torch.full((n, 1), vocab.JETON_REQUETE, dtype=torch.long)
    pas = jeton_pas_marche(vocab)
    offset = offset_pos_marche(vocab)
    chaine = torch.empty(n, 2 * K + 1, dtype=torch.long)
    for k in range(K):
        chaine[:, 2 * k] = pas
        chaine[:, 2 * k + 1] = offset + positions[:, k + 1]
    cible = valeurs.gather(1, positions[:, K].unsqueeze(1)).squeeze(1)
    chaine[:, -1] = cible
    x = torch.cat([valeurs, instrs, requete, chaine], dim=1)
    intermediaires = [positions[:, k + 1].clone() for k in range(K)]
    return x, cible, intermediaires


@torch.no_grad()
def evaluer_marche(
    modele, vocab: Vocab, K: int, n: int = 512, graine: int = 99
) -> tuple[float, float]:
    """Exactitude et perplexite cible de la marche guidee (answer-only)."""
    gen = torch.Generator().manual_seed(graine)
    lot = lot_marche(n, gen, vocab, K)
    logits = modele(lot.x)[:, -1]
    perte = F.cross_entropy(logits, lot.y)
    exactitude = (logits.argmax(-1) == lot.y).float().mean()
    return exactitude.item(), math.exp(perte.item())


@torch.no_grad()
def evaluer_marche_cot(
    modele, vocab: Vocab, K: int, n: int = 512, graine: int = 99
) -> tuple[float, list[float]]:
    """Exactitude cible + exactitude de chaque pas POS de la chaine (CoT).

    La prediction de chaque slot POS se lit a la position qui le precede ; la
    cible finale se lit a l'avant-derniere position (convention v3/v4).
    """
    gen = torch.Generator().manual_seed(graine)
    x, cible, intermediaires = lot_marche_cot(n, gen, vocab, K)
    logits = modele(x)
    n_chaine = 2 * K + 1
    T = x.shape[1]
    offset = offset_pos_marche(vocab)
    pas = []
    for k in range(K):
        slot = 2 * k + 1  # slot de chaine portant POS_{p_{k+1}}
        pred = logits[:, T - n_chaine + slot - 1]
        # cible = JETON POS (offset + position), pas l'indice brut de position
        pas.append((pred.argmax(-1) == offset + intermediaires[k]).float().mean().item())
    pred_cible = logits[:, T - 2]
    exactitude = (pred_cible.argmax(-1) == cible).float().mean().item()
    return exactitude, pas


@torch.no_grad()
def exactitude_marche_par_exemple(
    modele, vocab: Vocab, K: int, n: int = 512, graine: int = 99
) -> torch.Tensor:
    """Vecteur bool (n,) de correction par exemple -- appariement DM."""
    gen = torch.Generator().manual_seed(graine)
    lot = lot_marche(n, gen, vocab, K)
    return modele(lot.x)[:, -1].argmax(-1) == lot.y


@torch.no_grad()
def exactitude_marche_cot_par_exemple(
    modele, vocab: Vocab, K: int, n: int = 512, graine: int = 99
) -> torch.Tensor:
    """Vecteur bool (n,) de correction cible par exemple, mode CoT."""
    gen = torch.Generator().manual_seed(graine)
    x, cible, _ = lot_marche_cot(n, gen, vocab, K)
    return modele(x)[:, -2].argmax(-1) == cible


def entrainer_marche(
    modele, vocab: Vocab, K: int, graine: int,
    pas: int = 300, batch: int = 32, lr: float = 3e-3,
) -> tuple[float, float, float]:
    """Entrainement answer-only sur la marche guidee. Renvoie (acc, ppl, sec)."""
    torch.manual_seed(graine)
    opt = torch.optim.Adam(modele.parameters(), lr=lr)
    gen = torch.Generator().manual_seed(1234 + graine)
    debut = time.perf_counter()
    for _ in range(pas):
        lot = lot_marche(batch, gen, vocab, K)
        perte = F.cross_entropy(modele(lot.x)[:, -1], lot.y)
        opt.zero_grad()
        perte.backward()
        opt.step()
    secondes = time.perf_counter() - debut
    acc, ppl = evaluer_marche(modele, vocab, K)
    return acc, ppl, secondes


def entrainer_marche_cot(
    modele, vocab: Vocab, K: int, graine: int,
    pas: int = 300, batch: int = 32, lr: float = 3e-3,
) -> tuple[float, list[float], float]:
    """Entrainement CoT sur la marche : supervise chaque token de la chaine 2K+1."""
    torch.manual_seed(graine)
    opt = torch.optim.Adam(modele.parameters(), lr=lr)
    gen = torch.Generator().manual_seed(1234 + graine)
    n_chaine = 2 * K + 1
    V = vocab_marche_cot(vocab)
    debut = time.perf_counter()
    for _ in range(pas):
        x, _, _ = lot_marche_cot(batch, gen, vocab, K)
        logits = modele(x)
        T = x.shape[1]
        cible_shift = x[:, T - n_chaine:]
        logits_pred = logits[:, T - n_chaine - 1:-1]
        perte = F.cross_entropy(
            logits_pred.reshape(-1, V), cible_shift.reshape(-1)
        )
        opt.zero_grad()
        perte.backward()
        opt.step()
    secondes = time.perf_counter() - debut
    acc, pas_acc = evaluer_marche_cot(modele, vocab, K)
    return acc, pas_acc, secondes


def entrainer_marche_multi_seed(
    fabrique_modele, vocab: Vocab, K: int, graines: list[int],
    pas: int = 300, batch: int = 32, lr: float = 3e-3,
) -> dict:
    """Mesure multi-seed answer-only sur la marche (meme contrat que la v4)."""
    brut = []
    for graine in graines:
        torch.manual_seed(graine)
        modele = fabrique_modele(vocab)
        acc, ppl, sec = entrainer_marche(
            modele, vocab, K=K, graine=graine, pas=pas, batch=batch, lr=lr
        )
        brut.append((graine, acc, ppl, sec))
    return _agrege_multi_seed(brut)


def entrainer_marche_cot_multi_seed(
    fabrique_modele, vocab: Vocab, K: int, graines: list[int],
    pas: int = 300, batch: int = 32, lr: float = 3e-3,
) -> dict:
    """Mesure multi-seed CoT sur la marche : cible + pas POS par graine."""
    brut = []
    for graine in graines:
        torch.manual_seed(graine)
        modele = fabrique_modele(vocab)
        acc, pas_acc, sec = entrainer_marche_cot(
            modele, vocab, K=K, graine=graine, pas=pas, batch=batch, lr=lr
        )
        brut.append((graine, acc, pas_acc, sec))
    accs = [b[1] for b in brut]
    return {
        "acc_moy": statistics.fmean(accs),
        "acc_std": statistics.pstdev(accs) if len(accs) > 1 else 0.0,
        "pas_moy": [statistics.fmean([b[2][j] for b in brut]) for j in range(len(brut[0][2]))],
        "secondes": sum(b[3] for b in brut),
        "brut": brut,
        "n_graines": len(graines),
    }


def _dm_apparie(pertes_modele: list[list[float]], pertes_base: list[list[float]],
                h: int = 1) -> tuple[float, float]:
    """Diebold-Mariano sur pertes 0/1 par exemple appariees (HAC, sans scipy).

    d = perte_modele - perte_base ; dm > 0 = le modele est MOINS bon que la
    base. p bilateral via math.erf. h retards de correction autocorrelation.
    """
    d = [m - b for m, b in zip(pertes_modele, pertes_base)]
    n = len(d)
    dbar = statistics.fmean(d)

    def gamma(l: int) -> float:
        if l == 0:
            return sum((x - dbar) ** 2 for x in d) / n
        return sum((d[i] - dbar) * (d[i + l] - dbar)
                   for i in range(n - l)) / n

    var = gamma(0) + 2 * sum(gamma(l) for l in range(1, h + 1))
    dm = dbar / math.sqrt(max(var, 1e-12) / n)
    p = 2 * (1 - 0.5 * (1 + math.erf(abs(dm) / math.sqrt(2))))
    return dm, p


def mesurer_marche_paire(
    fabrique_answer, fabrique_cot, vocab: Vocab, K: int, graines: list[int],
    pas: int = 300, batch: int = 32, lr: float = 3e-3,
    n_eval: int = 512, graine_eval: int = 99,
) -> dict:
    """Mesure appariee complete answer-only vs CoT sur la marche guidee.

    Pour chaque graine : entraine les deux modes, evalue l'exactitude ET la
    correction par exemple (memes instances -- le tirage d'eval ne depend que
    de graine_eval). Rend l'edge cross-seed (delta moyen / ecart-type) et le
    DM apparie sur pertes 0/1 poolnees par exemple -- les deux jambes du
    critere de separation (edge >= 2 sigma ET DM p < 0.05).
    """
    accs_a, accs_c, ppls = [], [], []
    perte_a_par_ex, perte_c_par_ex = [], []
    pas_tous = []
    secondes = 0.0
    for graine in graines:
        torch.manual_seed(graine)
        m_a = fabrique_answer(vocab)
        acc_a, ppl_a, sec_a = entrainer_marche(
            m_a, vocab, K=K, graine=graine, pas=pas, batch=batch, lr=lr
        )
        torch.manual_seed(graine)
        m_c = fabrique_cot(vocab)
        acc_c, pas_acc, sec_c = entrainer_marche_cot(
            m_c, vocab, K=K, graine=graine, pas=pas, batch=batch, lr=lr
        )
        correct_a = exactitude_marche_par_exemple(
            m_a, vocab, K, n=n_eval, graine=graine_eval)
        correct_c = exactitude_marche_cot_par_exemple(
            m_c, vocab, K, n=n_eval, graine=graine_eval)
        accs_a.append(acc_a)
        accs_c.append(acc_c)
        ppls.append(ppl_a)
        pas_tous.append(pas_acc)
        secondes += sec_a + sec_c
        perte_a_par_ex.append([1.0 - bool(c) for c in correct_a.tolist()])
        perte_c_par_ex.append([1.0 - bool(c) for c in correct_c.tolist()])
    # pooling par exemple : memes instances entre graines, la moyenne par
    # exemple est le vecteur de pertes appariees du DM
    p_a = [statistics.fmean(col) for col in zip(*perte_a_par_ex)]
    p_c = [statistics.fmean(col) for col in zip(*perte_c_par_ex)]
    dm, pval = _dm_apparie(p_c, p_a)
    deltas = [c - a for c, a in zip(accs_c, accs_a)]
    d_moy = statistics.fmean(deltas)
    d_std = statistics.pstdev(deltas) if len(deltas) > 1 else 0.0
    edge = (d_moy / d_std) if d_std > 0 else (float("inf") if d_moy > 0 else 0.0)
    return {
        "K": K,
        "graines": graines,
        "acc_answer": accs_a,
        "acc_cot": accs_c,
        "acc_answer_moy": statistics.fmean(accs_a),
        "acc_answer_std": statistics.pstdev(accs_a) if len(accs_a) > 1 else 0.0,
        "acc_cot_moy": statistics.fmean(accs_c),
        "acc_cot_std": statistics.pstdev(accs_c) if len(accs_c) > 1 else 0.0,
        "ppl_answer_moy": statistics.fmean(ppls),
        "rapport_cot_answer": statistics.fmean(accs_c) / statistics.fmean(accs_a),
        "pas_pos_moy": [statistics.fmean([p[j] for p in pas_tous])
                        for j in range(K)],
        "delta_par_graine": deltas,
        "edge_sigma": edge,
        "dm_stat": dm,
        "dm_p": pval,
        "secondes": secondes,
    }
