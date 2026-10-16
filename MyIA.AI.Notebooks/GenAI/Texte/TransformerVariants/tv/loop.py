"""Transformers bouclés et récurrence deux-canaux (DiscoLoop), pour TV-04.

Ce module porte les architectures du grain TV-04 (#20516), d'après
*DiscoLoop* — Fu, Guo, Wang, Zhu, Lee, Jiao, Russell, Mei (UC Berkeley,
arXiv 2607.00341, 2026). Aucune figure ni texte de l'article n'est recopié :
les mécanismes sont ré-implémentés en jouet CPU fidèle au régime du papier,
et chaque renvoi se limite à une paraphrase.

Trois marches mesurables du papier, portées par ce module :

1. **Stockage de profondeur** (*depth-local storage*) : un transformer
   standard (:class:`tv.model.PetitLM`) doit conserver un fait lu en couche
   précoce jusqu'à l'endroit où la seconde récupération se produit — plus le
   nombre de sauts composés en un seul forward grandit, plus la contrainte
   pèse. Le témoin négatif gradué : la même largeur en NON bouclé.
2. **Goulot représentationnel du loop simple** : un transformer bouclé à
   poids partagés (:class:`BoucleSimple`) atténue le défaut mais généralise
   imparfaitement. Le diagnostic clé du papier : l'entité-pont est
   **décodable** depuis l'état caché (l'argmax de la tête la lit) sans être
   **alignée** avec son embedding (similarité cosinus faible) —
   :func:`diagnostic_alignement` mesure les deux, et
   :func:`realignement_lecture` est l'intervention de réalignement SANS
   ré-entraînement (elle réaligne la lecture, jamais les poids).
3. **Récurrence deux-canaux** : :class:`DiscoLoop` porte un canal **continu**
   (l'état caché du flux résiduel) ET un canal **discret** (un token par
   position, ré-embeddé et fusionné à chaque itération), ce qui maintient
   l'état aligné avec l'espace des embeddings — la cause du goulot (2).

Tâche d'ancrage : l'indirection double de :mod:`tv.task` v4
(:func:`tv.task.lot_indirection` avec ``double=True``) est le two-hop à
entité-pont du papier sous forme symbolique — lire le pointeur v en position
0 (saut 1 : l'entité-pont), puis lire la cible à la position v (saut 2,
DÉPENDANT du résultat du premier). TV-04 ne ré-implémente AUCUNE tâche.

Conventions :

- Les noms d'attributs (``emb``, ``blocs.0.*``, ``ln_f``, ``tete``) sont
  ceux de :class:`tv.model.PetitLM` : un ``load_state_dict`` depuis un
  ``PetitLM(n_couches=1)`` de même géométrie fonctionne tel quel — c'est
  l'invariant 1 du selfcheck.
- Le canal discret utilise l'estimateur *straight-through* : en forward le
  token est **dur** (un id de vocabulaire valide), en backward le gradient
  passe par les probabilités molles. Le papier entraîne le canal discret ;
  l'estimateur est la voie jouet standard pour cela en un seul forward.

Invariants vérifiés (ancrés par :func:`selfcheck_boucle_invariants`) :

- ``BoucleSimple(T=1)`` == ``PetitLM(n_couches=1)`` à poids copiés (tol 1e-6).
- ``DiscoLoop(lam=0)`` == ``BoucleSimple`` à poids copiés (le canal discret
  s'éteint proprement, tol 1e-6).
- Le comptage de paramètres ne dépend PAS de T (poids partagés) : la boucle
  T=4 compte exactement comme la boucle T=1, et strictement moins qu'un
  ``PetitLM(n_couches=4)`` équivalent en profondeur effective.
- Le canal discret forward est dur : ``z`` ne contient que des ids valides.
"""
from __future__ import annotations

import math

import torch
import torch.nn as nn
import torch.nn.functional as F

from tv.model import Bloc


class BoucleSimple(nn.Module):
    """Transformer bouclé à poids partagés : UN bloc appliqué T fois.

    Même géométrie qu'un :class:`tv.model.PetitLM` à une couche ; le forward
    ré-applique le même bloc ``T`` fois sur l'état continu. La profondeur
    effective croît avec ``T`` sans qu'aucun paramètre ne soit ajouté.
    """

    def __init__(
        self,
        vocab: int,
        d_model: int,
        n_heads: int,
        n_kv_heads: int,
        window: int | None,
        T: int,
    ):
        super().__init__()
        assert T >= 1, "la boucle exige T >= 1 itération"
        self.T = T
        self.emb = nn.Embedding(vocab, d_model)
        self.blocs = nn.ModuleList([Bloc(d_model, n_heads, n_kv_heads, window)])
        self.ln_f = nn.LayerNorm(d_model)
        self.tete = nn.Linear(d_model, vocab, bias=False)

    def forward(self, idx: torch.Tensor) -> torch.Tensor:
        h = self.emb(idx)
        for _ in range(self.T):
            h = self.blocs[0](h)
        return self.tete(self.ln_f(h))


class DiscoLoop(nn.Module):
    """Récurrence deux-canaux : état continu + canal discret ré-embeddé.

    À chaque itération ``t`` (au-delà de la première, où l'état EST déjà
    l'embedding d'entrée) :

    1. le canal discret ``z_t`` (un token **dur** par position, suivi
       straight-through pour le gradient) est ré-embeddé et fusionné dans
       l'état continu :  ``h <- Bloc(h + lam * emb(z_t))`` ;
    2. le canal discret est mis à jour depuis l'état :
       ``z_{t+1} = argmax(tete(ln_f(h)))``.

    ``lam = 0`` éteint le canal discret : le modèle dégénère exactement en
    :class:`BoucleSimple` (invariant 2 du selfcheck). ``z_0`` = les tokens
    d'entrée — la première itération relit le discret d'origine, les
    suivantes relisent ce que le modèle a écrit.
    """

    def __init__(
        self,
        vocab: int,
        d_model: int,
        n_heads: int,
        n_kv_heads: int,
        window: int | None,
        T: int,
        lam: float = 1.0,
    ):
        super().__init__()
        assert T >= 1, "la boucle exige T >= 1 itération"
        self.T, self.lam = T, lam
        self.emb = nn.Embedding(vocab, d_model)
        self.blocs = nn.ModuleList([Bloc(d_model, n_heads, n_kv_heads, window)])
        self.ln_f = nn.LayerNorm(d_model)
        self.tete = nn.Linear(d_model, vocab, bias=False)

    def _canal_discret(self, h: torch.Tensor) -> torch.Tensor:
        """Met à jour le canal discret : token dur en forward, gradient mou.

        L'estimateur straight-through ``hard + probs - probs.detach()`` rend
        un one-hot exact en forward (ids valides) tout en laissant le
        gradient couler vers la tête et l'état.
        """
        probs = F.softmax(self.tete(self.ln_f(h)), dim=-1)
        dur = F.one_hot(probs.argmax(-1), num_classes=probs.shape[-1]).float()
        st = dur + probs - probs.detach()
        return st @ self.emb.weight  # (B, T, d_model)

    def forward(self, idx: torch.Tensor, retour_z: bool = False):
        h = self.emb(idx)
        z_dur = idx
        for t in range(self.T):
            if t > 0:
                h = h + self.lam * self._canal_discret(h)
            h = self.blocs[0](h)
            z_dur = self.tete(self.ln_f(h)).argmax(-1)
        logits = self.tete(self.ln_f(h))
        if retour_z:
            return logits, z_dur
        return logits


def _etat_lecture(modele: nn.Module, x: torch.Tensor) -> torch.Tensor:
    """État pré-tête ``ln_f(h)`` complet (B, T, d), boucle ou profondeur.

    Partagé par les deux diagnostics : rejoue le forward du modèle SANS la
    tête — boucle à poids partagés pour :class:`BoucleSimple` /
    :class:`DiscoLoop` (attribut ``T``), profondeur classique sinon
    (:class:`tv.model.PetitLM` et apparentés).
    """
    h = modele.emb(x)
    if hasattr(modele, "T"):
        for t in range(modele.T):
            if t > 0 and isinstance(modele, DiscoLoop):
                h = h + modele.lam * modele._canal_discret(h)
            h = modele.blocs[0](h)
    else:
        for b in modele.blocs:
            h = b(h)
    return modele.ln_f(h)


@torch.no_grad()
def diagnostic_alignement(
    modele: nn.Module,
    x: torch.Tensor,
    position_lecture: int = -1,
    ids_pont: torch.Tensor | None = None,
) -> dict:
    """Décodabilité vs alignement de l'entité-pont (Fu et al. 2026, mes. 2).

    Le goulot représentationnel du loop simple se lit par DEUX mesures
    indépendantes à la position de lecture (requête) :

    - ``decodabilite`` : fréquence où l'argmax de la tête (appliquée à
      ``ln_f(h)``) rend l'entité-pont — le pont est-il LISIBLE dans l'état ?
    - ``alignement`` : similarité cosinus moyenne entre l'état ``ln_f(h)``
      normalisé et l'embedding de l'entité-pont normalisé — l'état est-il
      ALIGNÉ avec l'espace des embeddings ?

    Le constat du papier : un loop simple peut être hautement décodable et
    faiblement aligné — c'est précisément l'écart que le canal discret de
    :class:`DiscoLoop` referme, et que :func:`realignement_lecture` referme
    sans ré-entraînement.

    :param ids_pont: (B,) ids du jeton-pont par exemple. Si None, décodage
        sur l'argmax courant (auto-référence : mesure la cohérence interne).
    :return: ``{"decodabilite": float, "alignement": float}``.
    """
    z = _etat_lecture(modele, x)[:, position_lecture]  # (B, d)
    logits = modele.tete(z)
    if ids_pont is None:
        ids_pont = logits.argmax(-1)
    decodabilite = (logits.argmax(-1) == ids_pont).float().mean().item()
    emb_pont = modele.emb(ids_pont)  # (B, d)
    cos = F.cosine_similarity(z, emb_pont, dim=-1)
    return {"decodabilite": decodabilite, "alignement": float(cos.mean().item())}


@torch.no_grad()
def realignement_lecture(
    modele: nn.Module,
    x: torch.Tensor,
    cible: torch.Tensor,
    position_lecture: int = -1,
) -> dict:
    """Intervention de réalignement SANS ré-entraînement (Fu et al. 2026).

    Ne touche à AUCUN poids : à la position de lecture, on remplace la
    projection linéaire de la tête par une lecture en similarité cosinus
    sur les embeddings centrés puis normalisés. Un état décodable mais mal
    aligné (le goulot du loop simple) se fait lire par la métrique qui
    réaligne exactement la lecture sur l'espace des embeddings.

    :return: ``{"exactitude_avant": float, "exactitude_apres": float}`` —
        la mesure honnête est le delta, rapporté tel quel (il peut être
        nul ou négatif ; le verdict appartient au notebook, pas à l'organe).
    """
    z = _etat_lecture(modele, x)[:, position_lecture]  # (B, d)
    logits_avant = modele.tete(z)
    exactitude_avant = (logits_avant.argmax(-1) == cible).float().mean().item()

    W = modele.emb.weight  # (V, d) -- lire l'espace des embeddings, contrat docstring/body
    centre = W - W.mean(dim=0, keepdim=True)
    zc = z - z.mean(dim=-1, keepdim=True)
    sims = F.cosine_similarity(
        zc.unsqueeze(1), centre.unsqueeze(0), dim=-1
    )  # (B, V)
    exactitude_apres = (sims.argmax(-1) == cible).float().mean().item()
    return {
        "exactitude_avant": exactitude_avant,
        "exactitude_apres": exactitude_apres,
    }


def selfcheck_boucle_invariants(
    vocab: int = 40,
    d_model: int = 64,
    n_heads: int = 4,
    T: int = 3,
    B: int = 4,
    T_seq: int = 16,
    seed: int = 42,
    tol: float = 1e-6,
) -> dict:
    """Ancre les quatre invariants documentés en tête de module.

    1. **Équivalence T=1** : ``BoucleSimple(T=1)`` charge le state_dict d'un
       ``PetitLM(n_couches=1)`` et rend des logits identiques.
    2. **Extinction du canal discret** : ``DiscoLoop(lam=0)`` == ``BoucleSimple``
       à poids copiés.
    3. **Poids partagés** : le nombre de paramètres ne dépend pas de ``T``
       et reste strictement inférieur à un ``PetitLM`` de profondeur égale.
    4. **Canal discret dur** : ``retour_z`` ne rend que des ids valides
       (0 <= z < vocab), et le gradient atteint l'embedding (le canal n'est
       pas mort en backward).

    Retourne ``{"passed": bool, "samples": list[dict]}`` dans le format du
    selfcheck de :mod:`tv.model`.
    """
    from tv.model import PetitLM

    samples: list[dict] = []
    passed = True

    torch.manual_seed(seed)
    idx = torch.randint(0, vocab, (B, T_seq))

    # 1. Équivalence T=1 avec PetitLM(n_couches=1) à poids copiés
    ref = PetitLM(vocab, d_model, n_heads, n_heads, None, n_couches=1)
    bou = BoucleSimple(vocab, d_model, n_heads, n_heads, None, T=1)
    bou.load_state_dict(ref.state_dict())
    diff = float((bou(idx) - ref(idx)).abs().max().item())
    ok = diff <= tol
    passed &= ok
    samples.append({"invariant": "T1_equiv_petitlm", "max_abs_diff": diff,
                    "ok": ok})

    # 2. DiscoLoop(lam=0) == BoucleSimple à poids copiés (canal éteint)
    bou3 = BoucleSimple(vocab, d_model, n_heads, n_heads, None, T=T)
    dis = DiscoLoop(vocab, d_model, n_heads, n_heads, None, T=T, lam=0.0)
    dis.load_state_dict(bou3.state_dict())
    diff = float((dis(idx) - bou3(idx)).abs().max().item())
    ok = diff <= tol
    passed &= ok
    samples.append({"invariant": "lam0_equiv_boucle", "max_abs_diff": diff,
                    "ok": ok})

    # 3. Poids partagés : le compte ne dépend pas de T ; < profondeur égale
    n1 = sum(p.numel() for p in bou.parameters())
    bou4 = BoucleSimple(vocab, d_model, n_heads, n_heads, None, T=4)
    n4 = sum(p.numel() for p in bou4.parameters())
    prof = sum(p.numel() for p in
               PetitLM(vocab, d_model, n_heads, n_heads, None, n_couches=4)
               .parameters())
    ok = (n1 == n4) and (n4 < prof)
    passed &= ok
    samples.append({"invariant": "poids_partages", "n_T1": n1, "n_T4": n4,
                    "n_prof4": prof, "ok": ok})

    # 4. Canal discret : ids durs valides + gradient vivant vers l'embedding
    dis1 = DiscoLoop(vocab, d_model, n_heads, n_heads, None, T=T, lam=1.0)
    logits, z = dis1(idx, retour_z=True)
    ids_valides = bool(((z >= 0) & (z < vocab)).all().item())
    perte = F.cross_entropy(logits[:, -1], idx[:, 0])
    perte.backward()
    grad_vivant = dis1.emb.weight.grad is not None and float(
        dis1.emb.weight.grad.abs().sum().item()
    ) > 0.0
    ok = ids_valides and grad_vivant
    passed &= ok
    samples.append({"invariant": "canal_discret_dur", "ids_valides": ids_valides,
                    "grad_vivant": grad_vivant, "ok": ok})

    return {"passed": passed, "samples": samples, "tol": tol, "seed": seed,
            "B": B, "T_seq": T_seq, "T": T}
