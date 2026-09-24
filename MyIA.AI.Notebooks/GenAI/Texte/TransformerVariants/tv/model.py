"""Briques canoniques d'un mini-transformer, extraites de TV-00b.

Ce module isole les pièces qui vivent dans les cellules du notebook
``TV-00b-Attention-Variants-from-scratch.ipynb`` pour les rendre importables
par un autre notebook ou un test, sans dépendance au reste du notebook.

Trois classes principales :

- :class:`VariantAttn` : attention unifiée (MHA / MQA / GQA / SWA).
- :class:`Bloc`        : bloc pré-norm résiduel.
- :class:`PetitLM`     : transformer canonique (embedding + N blocs + LN + tête).

Quatre helpers :

- :func:`build_kv_heads`     : étale les têtes KV sur les têtes Q (GQA / MQA).
- :func:`attn_masked`        : attention masquée (causale + fenêtre) O(T^2).
- :func:`attn_banded`        : attention en bande SWA O(T * W).
- :func:`causal_window_mask` : masque booléen (T, T) partagé par les deux fonctions.

Origine : cellules 12 (VariantAttn + build_kv_heads), 4 (causal_window_mask +
attn_masked), 15 (attn_banded), 26 (Bloc + PetitLM) de TV-00b.

Invariants vérifiés (cf TV-00b cellules 12-15) :

- L'étalement KV utilise ``repeat_interleave`` (vues partagées, pas de copie).
- Le coût en paramètres des projections K/V décroît avec ``n_kv_heads``.
- ``attn_banded`` et ``attn_masked`` rendent le même tenseur pour les mêmes (q, k, v, W).
"""
from __future__ import annotations

import math

import torch
import torch.nn as nn
import torch.nn.functional as F


def causal_window_mask(T: int, window: int | None = None, device: torch.device | str = "cpu") -> torch.Tensor:
    """Masque booléen (T, T) : True si la requête i a le droit de lire la clé j.

    window=None : causal pur (j <= i).
    window=W    : causal ET bande locale (i - j < W), au plus W clés par requête.
    """
    i = torch.arange(T, device=device).view(T, 1)
    j = torch.arange(T, device=device).view(1, T)
    mask = j <= i
    if window is not None:
        mask = mask & ((i - j) < window)
    return mask


def attn_masked(q: torch.Tensor, k: torch.Tensor, v: torch.Tensor, window: int | None = None) -> torch.Tensor:
    """Attention sur (B, H, T, dh). Forme lisible ; reste O(T^2) même en fenêtre."""
    scores = q @ k.transpose(-2, -1) / math.sqrt(q.shape[-1])
    scores = scores.masked_fill(~causal_window_mask(q.shape[-2], window, q.device), float("-inf"))
    return torch.softmax(scores, dim=-1) @ v


def attn_banded(q: torch.Tensor, k: torch.Tensor, v: torch.Tensor, window: int) -> torch.Tensor:
    """SWA en bande : ne matérialise que les W colonnes utiles → O(T*W).

    On décale les clés de W-1 vers la droite (remplissage à gauche), puis on
    découpe une fenêtre glissante de largeur W le long de l'axe des positions.
    La requête i voit alors les positions décalées relatives 0..W-1, dont la
    dernière (offset W-1) est la position i.
    """
    B, H, T, dh = q.shape
    W = min(window, T)
    k_win = F.pad(k, (0, 0, W - 1, 0)).unfold(2, W, 1)
    v_win = F.pad(v, (0, 0, W - 1, 0)).unfold(2, W, 1)
    scores = torch.einsum("bhtd,bhtdw->bhtw", q, k_win) / math.sqrt(dh)
    decalage = torch.arange(W, device=q.device)
    positions = torch.arange(T, device=q.device)
    keep = decalage.view(1, 1, 1, W) >= (W - 1 - positions).view(1, 1, T, 1)
    scores = scores.masked_fill(~keep, float("-inf"))
    return torch.einsum("bhtw,bhtdw->bhtd", torch.softmax(scores, dim=-1), v_win)


def build_kv_heads(kv: torch.Tensor, n_heads: int, n_kv_heads: int) -> torch.Tensor:
    """Étale les têtes KV sur les têtes Q.

    MHA (n_kv_heads == n_heads) : identité, on ne touche pas au tenseur.
    MQA (n_kv_heads == 1)       : l'unique tête KV est répétée n_heads fois.
    GQA                         : la tête Q h reçoit la tête KV h // (n_heads / n_kv_heads).

    Retourne des **vues** (``repeat_interleave``) : les poids restent partagés.
    """
    if n_kv_heads == n_heads:
        return kv
    return kv.repeat_interleave(n_heads // n_kv_heads, dim=1)


class VariantAttn(nn.Module):
    """Les quatre variantes d'un seul tenant : les leviers sont (n_kv_heads, window).

    n_kv_heads == n_heads    -> MHA        | window is not None -> SWA
    n_kv_heads == 1          -> MQA        | banded=True        -> SWA en bande O(T*W)
    1 < n_kv_heads < n_heads -> GQA        | sinon              -> masque O(T^2)
    """

    def __init__(
        self,
        d_model: int,
        n_heads: int,
        n_kv_heads: int | None = None,
        window: int | None = None,
        banded: bool = False,
    ):
        super().__init__()
        n_kv_heads = n_heads if n_kv_heads is None else n_kv_heads
        assert n_heads % n_kv_heads == 0, "les têtes Q doivent se répartir en groupes égaux"
        self.h, self.g, self.window, self.banded = n_heads, n_kv_heads, window, banded
        self.dh = d_model // n_heads
        self.q_proj = nn.Linear(d_model, n_heads * self.dh, bias=False)
        self.k_proj = nn.Linear(d_model, n_kv_heads * self.dh, bias=False)
        self.v_proj = nn.Linear(d_model, n_kv_heads * self.dh, bias=False)
        self.o_proj = nn.Linear(n_heads * self.dh, d_model, bias=False)

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        B, T, _ = x.shape
        q = self.q_proj(x).view(B, T, self.h, self.dh).transpose(1, 2)
        k = self.k_proj(x).view(B, T, self.g, self.dh).transpose(1, 2)
        v = self.v_proj(x).view(B, T, self.g, self.dh).transpose(1, 2)
        k = build_kv_heads(k, self.h, self.g)
        v = build_kv_heads(v, self.h, self.g)
        if self.banded and self.window is not None:
            o = attn_banded(q, k, v, self.window)
        else:
            o = attn_masked(q, k, v, self.window)
        return self.o_proj(o.transpose(1, 2).reshape(B, T, self.h * self.dh))


class Bloc(nn.Module):
    """Bloc pré-norm résiduel : x = x + attn(LN(x)); x = x + MLP(LN(x))."""

    def __init__(self, d_model: int, n_heads: int, n_kv_heads: int, window: int | None):
        super().__init__()
        self.ln1, self.ln2 = nn.LayerNorm(d_model), nn.LayerNorm(d_model)
        self.attn = VariantAttn(d_model, n_heads, n_kv_heads=n_kv_heads, window=window)
        self.mlp = nn.Sequential(
            nn.Linear(d_model, 4 * d_model),
            nn.GELU(),
            nn.Linear(4 * d_model, d_model),
        )

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        x = x + self.attn(self.ln1(x))
        return x + self.mlp(self.ln2(x))


class PetitLM(nn.Module):
    """Transformer minimal : embedding + N blocs pré-norm + LN final + tête linéaire."""

    def __init__(
        self,
        vocab: int,
        d_model: int,
        n_heads: int,
        n_kv_heads: int,
        window: int | None,
        n_couches: int,
    ):
        super().__init__()
        self.emb = nn.Embedding(vocab, d_model)
        self.blocs = nn.ModuleList(
            [Bloc(d_model, n_heads, n_kv_heads, window) for _ in range(n_couches)]
        )
        self.ln_f = nn.LayerNorm(d_model)
        self.tete = nn.Linear(d_model, vocab, bias=False)

    def forward(self, idx: torch.Tensor) -> torch.Tensor:
        x = self.emb(idx)
        for b in self.blocs:
            x = b(x)
        return self.tete(self.ln_f(x))
