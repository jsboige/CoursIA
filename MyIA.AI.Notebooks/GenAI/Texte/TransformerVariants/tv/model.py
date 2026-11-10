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
  Ancré en continu par :func:`selfcheck_attn_equivalence` (B=2, H=4, T=64, dh=64,
  W in (8, 16, 32), seed 42, tol float32 1e-5). Mesure typique ~1.2e-07 (cf
  TV-00b cellules 16 et 31).
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


def attn_pleine(q: torch.Tensor, k: torch.Tensor, v: torch.Tensor) -> torch.Tensor:
    """Attention sans aucun masque : chaque requête lit toutes les clés.

    C'est la brique de l'encodeur bidirectionnel (BERT) : la requête i voit
    les jetons des deux côtés, y compris ceux qui suivent. C'est aussi la
    forme de l'attention croisée encodeur-décodeur — la différence entre les
    deux n'est pas dans la formule mais dans la provenance de (q, k, v) :
    même tenseur pour l'auto-attention bidirectionnelle, décodeur pour q et
    mémoire d'encodeur pour (k, v) pour la croisée.
    """
    scores = q @ k.transpose(-2, -1) / math.sqrt(q.shape[-1])
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
        bidirectionnel: bool = False,
    ):
        super().__init__()
        n_kv_heads = n_heads if n_kv_heads is None else n_kv_heads
        assert n_heads % n_kv_heads == 0, "les têtes Q doivent se répartir en groupes égaux"
        assert not (bidirectionnel and (window is not None or banded)), (
            "bidirectionnel exclut la fenêtre glissante : l'encodeur lit tout"
        )
        self.h, self.g, self.window, self.banded = n_heads, n_kv_heads, window, banded
        self.bidirectionnel = bidirectionnel
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
        if self.bidirectionnel:
            o = attn_pleine(q, k, v)
        elif self.banded and self.window is not None:
            o = attn_banded(q, k, v, self.window)
        else:
            o = attn_masked(q, k, v, self.window)
        return self.o_proj(o.transpose(1, 2).reshape(B, T, self.h * self.dh))


class Bloc(nn.Module):
    """Bloc pré-norm résiduel : x = x + attn(LN(x)); x = x + MLP(LN(x))."""

    def __init__(self, d_model: int, n_heads: int, n_kv_heads: int, window: int | None,
                 bidirectionnel: bool = False):
        super().__init__()
        self.ln1, self.ln2 = nn.LayerNorm(d_model), nn.LayerNorm(d_model)
        self.attn = VariantAttn(d_model, n_heads, n_kv_heads=n_kv_heads, window=window,
                                bidirectionnel=bidirectionnel)
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


def selfcheck_attn_equivalence(B: int = 2, H: int = 4, T: int = 64, dh: int = 64,
                               windows: tuple[int, ...] = (8, 16, 32),
                               seed: int = 42, tol: float = 1e-5) -> dict:
    """Ancre l'invariant documente dans la docstring du module.

    Pour chaque fenetre W dans ``windows``, mesure ``max|attn_banded - attn_masked|``
    sur des tenseurs (q, k, v) tires aleatoirement avec la graine ``seed``. Le
    resultat est borne par ``tol`` (float32, juste en deca de la limite pratique
    mesuree dans TV-00b cellules 16 et 31, ~1.2e-07).

    Retourne ``{"max_abs_diff": float, "passed": bool, "samples": list[dict]}``
    ou chaque sample porte ``{"window": int, "max_abs_diff": float}``.

    Le test est strictement CPU (le device suit ``q.device``), pas de gradient
    necessaire. Si un echantillon echoue, le dictionnaire le signale dans
    ``samples`` et ``passed = False``.
    """
    g = torch.Generator(device="cpu").manual_seed(seed)
    samples: list[dict] = []
    worst = 0.0
    for W in windows:
        q = torch.randn(B, H, T, dh, generator=g) * 0.5
        k = torch.randn(B, H, T, dh, generator=g) * 0.5
        v = torch.randn(B, H, T, dh, generator=g) * 0.5
        with torch.no_grad():
            o_band = attn_banded(q, k, v, W)
            o_mask = attn_masked(q, k, v, W)
        diff = float((o_band - o_mask).abs().max().item())
        samples.append({"window": W, "max_abs_diff": diff})
        worst = max(worst, diff)
    return {"max_abs_diff": worst, "passed": worst <= tol, "samples": samples,
            "tol": tol, "B": B, "H": H, "T": T, "dh": dh, "seed": seed}


# ---------------------------------------------------------------------------
# Les deux autres familles Transformer (TV-00d, #22699) : encodeur
# bidirectionnel et encodeur-décodeur. Le décodeur causal reste PetitLM.
# ---------------------------------------------------------------------------

class AttnCroisee(nn.Module):
    """Attention croisée encodeur-décodeur : Q vient du décodeur, K/V de l'encodeur.

    Chaque position du décodeur interroge **toute** la séquence source — aucun
    masque : la mémoire d'encodeur est déjà bidirectionnelle, il n'y a pas de
    fuite du futur à empêcher côté source (le futur à cacher est celui du
    décodeur, et c'est l'auto-attention causale du :class:`BlocDecodeur` qui
    s'en charge). Attention multi-têtes simple (pas de partage KV : ce levier
    est celui de TV-00b, hors sujet ici).
    """

    def __init__(self, d_model: int, n_heads: int):
        super().__init__()
        self.h = n_heads
        self.dh = d_model // n_heads
        self.q_proj = nn.Linear(d_model, n_heads * self.dh, bias=False)
        self.k_proj = nn.Linear(d_model, n_heads * self.dh, bias=False)
        self.v_proj = nn.Linear(d_model, n_heads * self.dh, bias=False)
        self.o_proj = nn.Linear(n_heads * self.dh, d_model, bias=False)

    def forward(self, x: torch.Tensor, mem: torch.Tensor) -> torch.Tensor:
        """x : (B, T_dec, d) requêtes du décodeur ; mem : (B, T_enc, d) mémoire d'encodeur."""
        B, T_dec, _ = x.shape
        T_enc = mem.shape[1]
        q = self.q_proj(x).view(B, T_dec, self.h, self.dh).transpose(1, 2)
        k = self.k_proj(mem).view(B, T_enc, self.h, self.dh).transpose(1, 2)
        v = self.v_proj(mem).view(B, T_enc, self.h, self.dh).transpose(1, 2)
        o = attn_pleine(q, k, v)
        return self.o_proj(o.transpose(1, 2).reshape(B, T_dec, self.h * self.dh))

    def poids(self, x: torch.Tensor, mem: torch.Tensor) -> torch.Tensor:
        """Poids d'attention (B, H, T_dec, T_enc) pour visualiser l'alignement source-cible."""
        B, T_dec, _ = x.shape
        T_enc = mem.shape[1]
        q = self.q_proj(x).view(B, T_dec, self.h, self.dh).transpose(1, 2)
        k = self.k_proj(mem).view(B, T_enc, self.h, self.dh).transpose(1, 2)
        scores = q @ k.transpose(-2, -1) / math.sqrt(self.dh)
        return torch.softmax(scores, dim=-1)


class BlocDecodeur(nn.Module):
    """Bloc pré-norm résiduel du décodeur : self-attention causale, puis attention croisée, puis MLP.

    x = x + self_attn(LN(x))            — le futur du décodeur reste caché
    x = x + croisee(LN(x), mem)         — toute la source devient lisible
    x = x + mlp(LN(x))
    """

    def __init__(self, d_model: int, n_heads: int, window: int | None = None):
        super().__init__()
        self.ln1, self.ln2, self.ln3 = (nn.LayerNorm(d_model) for _ in range(3))
        self.self_attn = VariantAttn(d_model, n_heads, window=window)
        self.croisee = AttnCroisee(d_model, n_heads)
        self.mlp = nn.Sequential(
            nn.Linear(d_model, 4 * d_model),
            nn.GELU(),
            nn.Linear(4 * d_model, d_model),
        )

    def forward(self, x: torch.Tensor, mem: torch.Tensor) -> torch.Tensor:
        x = x + self.self_attn(self.ln1(x))
        x = x + self.croisee(self.ln2(x), mem)
        return x + self.mlp(self.ln3(x))


class PetitEncodeur(nn.Module):
    """Encodeur seul bidirectionnel (style BERT) : embedding + N blocs bidirectionnels + LN + tête.

    La tête prédit un jeton **par position** — c'est l'entrée du masquage MLM :
    seules les positions masquées comptent dans la perte, mais toutes les
    positions participent à la représentation.
    """

    def __init__(self, vocab: int, d_model: int, n_heads: int, n_couches: int):
        super().__init__()
        self.emb = nn.Embedding(vocab, d_model)
        self.blocs = nn.ModuleList(
            [Bloc(d_model, n_heads, n_kv_heads=n_heads, window=None, bidirectionnel=True)
             for _ in range(n_couches)]
        )
        self.ln_f = nn.LayerNorm(d_model)
        self.tete = nn.Linear(d_model, vocab, bias=False)

    def forward(self, idx: torch.Tensor) -> torch.Tensor:
        x = self.emb(idx)
        for b in self.blocs:
            x = b(x)
        return self.tete(self.ln_f(x))

    def n_parametres(self) -> int:
        return sum(p.numel() for p in self.parameters())


class EncodeurDecodeur(nn.Module):
    """Seq2seq Transformer complet (style T5) : encodeur bidirectionnel + décodeur causal croisé.

    Le décodeur consomme la séquence cible décalée à droite (teacher forcing
    à l'entraînement) et la mémoire d'encodeur ; sa tête prédit le jeton
    suivant de la cible à chaque position.
    """

    def __init__(self, vocab: int, d_model: int, n_heads: int, n_couches: int):
        super().__init__()
        self.emb = nn.Embedding(vocab, d_model)
        self.enc_blocs = nn.ModuleList(
            [Bloc(d_model, n_heads, n_kv_heads=n_heads, window=None, bidirectionnel=True)
             for _ in range(n_couches)]
        )
        self.ln_enc = nn.LayerNorm(d_model)
        self.dec_blocs = nn.ModuleList(
            [BlocDecodeur(d_model, n_heads) for _ in range(n_couches)]
        )
        self.ln_dec = nn.LayerNorm(d_model)
        self.tete = nn.Linear(d_model, vocab, bias=False)

    def forward(self, src: torch.Tensor, tgt: torch.Tensor) -> torch.Tensor:
        """src : (B, T_enc) ; tgt : (B, T_dec) cible décalée à droite. Logits (B, T_dec, vocab)."""
        mem = self.emb(src)
        for b in self.enc_blocs:
            mem = b(mem)
        mem = self.ln_enc(mem)
        x = self.emb(tgt)
        for b in self.dec_blocs:
            x = b(x, mem)
        return self.tete(self.ln_dec(x))

    def memoire(self, src: torch.Tensor) -> torch.Tensor:
        """Mémoire d'encodeur (B, T_enc, d) — réutilisable à chaque pas de décodage."""
        mem = self.emb(src)
        for b in self.enc_blocs:
            mem = b(mem)
        return self.ln_enc(mem)

    def pas_decodage(self, tgt_prefixe: torch.Tensor, mem: torch.Tensor) -> torch.Tensor:
        """Un pas de décodage : logits (B, vocab) du jeton suivant après le préfixe donné."""
        x = self.emb(tgt_prefixe)
        for b in self.dec_blocs:
            x = b(x, mem)
        return self.tete(self.ln_dec(x))[:, -1, :]

    def n_parametres(self) -> int:
        return sum(p.numel() for p in self.parameters())


def selfcheck_encodeurs(d_model: int = 32, n_heads: int = 4, seed: int = 7,
                        tol: float = 1e-6) -> dict:
    """Ancre les invariants des deux nouvelles familles (TV-00d, #22699).

    (a) L'encodeur bidirectionnel et le même bloc causal **diffèrent** sur la
    même entrée : retirer le masque causal change la sortie dès la première
    position (la requête 0 lit les jetons suivants).
    (b) L'attention croisée sans masque est invariante à la permutation des
    positions du décodeur entre elles (chaque requête est traitée
    indépendamment). Elle l'est de même à la permutation de la mémoire :
    `attn_pleine` ne code aucune position sur les clés, donc la sortie est une
    somme pondérée sur le multiensemble des jetons sources — l'ordre de la
    mémoire n'entre pas dans le calcul. Le selfcheck ancre la première
    invariance ; la seconde est une propriété de l'implémentation (aucun
    encodage positionnel sur la mémoire), pas une hypothèse testée.
    """
    g = torch.Generator(device="cpu").manual_seed(seed)
    res: dict = {}

    x = torch.randn(2, 12, d_model, generator=g)
    bloc_bi = Bloc(d_model, n_heads, n_kv_heads=n_heads, window=None, bidirectionnel=True)
    bloc_causal = Bloc(d_model, n_heads, n_kv_heads=n_heads, window=None, bidirectionnel=False)
    bloc_causal.load_state_dict(bloc_bi.state_dict())
    with torch.no_grad():
        d0 = (bloc_bi(x) - bloc_causal(x)).abs().max().item()
    res["a_ecart_bi_vs_causal_pos0"] = d0
    res["a_passe"] = d0 > tol

    croisee = AttnCroisee(d_model, n_heads)
    x_dec = torch.randn(2, 5, d_model, generator=g)
    mem = torch.randn(2, 9, d_model, generator=g)
    perm = torch.randperm(5, generator=g)
    with torch.no_grad():
        o = croisee(x_dec, mem)
        o_perm = croisee(x_dec[:, perm], mem)[:, perm]
    res["b_ecart_permutation_decodeur"] = float((o - o_perm).abs().max().item())
    res["b_passe"] = res["b_ecart_permutation_decodeur"] <= 1e-5
    res["passed"] = bool(res["a_passe"] and res["b_passe"])
    return res
