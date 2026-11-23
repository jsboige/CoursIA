"""Petit transformer hookable pour le pilote de triangulation causale (#15480).

Confinement torch/transformers dans ``scripts/`` (architecture #15475/#15479) :
ce module sait entrainer un petit decoder-only sur les sequences tokenisees du
banc factorise et capturer les panneaux du residual stream (pre/post LayerNorm,
par couche) que consomment les instruments numpy-only du paquet ``ict/`` (SAE,
probes, moteur causal). Il ne fait aucune mesure lui-meme.

Tokenisation : le banc produit des observations jointes (a_t, b_t) ; ``a``
(emission continue du premier generateur, ex. Mess3) est discretisee sur une
grille fixe de ``n_bins`` tranches, ``b`` (bit RRXOR ou re-discretise) sur 2
tranches. Token joint = bin_a * 2 + bin_b, alphabet 2*n_bins.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Sequence, Tuple

import numpy as np

import torch
import torch.nn as nn
import torch.nn.functional as F

Array = np.ndarray


class ProcessValueError(ValueError):
    """Erreur de parametrage du harnais transformer."""


@dataclass(frozen=True)
class TokenizerConfig:
    """Grille de discretisation gelee, derivee des parametres du banc.

    La grille est construite sur les bornes des moyennes d'emission du
    generateur A, elargies de ``bin_margin`` ecarts-types : elle ne depend
    d'aucun echantillon (protocole gele, pas de fuite train/eval).
    """

    n_bins: int = 8
    bin_margin: float = 4.0

    def grid(self, means: Sequence[float], std: float) -> Array:
        lo = min(means) - self.bin_margin * std
        hi = max(means) + self.bin_margin * std
        return np.linspace(lo, hi, self.n_bins + 1)


def tokenize_joint(
    obs_a: Array,
    obs_b: Array,
    grid: Array,
) -> Array:
    """Observations jointes -> tokens entiers dans [0, 2*n_bins)."""
    if obs_a.ndim != 1 or obs_b.ndim != 1 or len(obs_a) != len(obs_b):
        raise ProcessValueError("obs_a/obs_b doivent etre 1D de meme longueur")
    n_bins = len(grid) - 1
    bin_a = np.clip(np.digitize(obs_a, grid[1:-1]), 0, n_bins - 1)
    b = (obs_b > 0.5).astype(np.int64)
    return (bin_a.astype(np.int64) * 2 + b).astype(np.int64)


class TinyTransformer(nn.Module):
    """Decoder-only minimal : embeddings + blocs pre-LN + tete lineaire.

    La capture distingue le residuel AVANT la LayerNorm d'entree de chaque
    bloc (``pre``) et le residuel APRES ajout de la sortie du bloc
    (``post``) — l'acceptance #15480 exige la distinction explicite.
    """

    def __init__(self, vocab: int, d_model: int = 64, n_layers: int = 2,
                 n_heads: int = 4, d_mlp: int = 256, max_len: int = 128,
                 seed: int = 0) -> None:
        super().__init__()
        torch.manual_seed(seed)
        self.d_model = d_model
        self.embed = nn.Embedding(vocab, d_model)
        self.pos = nn.Embedding(max_len, d_model)
        self.blocks = nn.ModuleList([
            nn.TransformerEncoderLayer(
                d_model=d_model, nhead=n_heads, dim_feedforward=d_mlp,
                dropout=0.0, activation="gelu", batch_first=True,
                norm_first=True,
            )
            for _ in range(n_layers)
        ])
        self.final_ln = nn.LayerNorm(d_model)
        self.head = nn.Linear(d_model, vocab)
        self.register_buffer(
            "causal", torch.triu(torch.ones(max_len, max_len, dtype=torch.bool),
                                 diagonal=1)
        )

    def forward_with_panels(
        self, tokens: torch.Tensor
    ) -> Tuple[torch.Tensor, Dict[str, torch.Tensor]]:
        """Logits next-token + panneaux residuels par couche.

        Retourne ``(logits, panels)`` avec ``panels["L{i}_pre"]`` et
        ``panels["L{i}_post"]`` de forme ``(B, T, d_model)``. ``pre`` est le
        residuel en entree du bloc i (apres embeddings+positions et sorties
        des blocs precedents, AVANT sa LayerNorm) ; ``post`` est le residuel
        en sortie du bloc i.
        """
        b, t = tokens.shape
        tokens = tokens.to(self.embed.weight.device)
        h = self.embed(tokens) + self.pos(torch.arange(t, device=tokens.device))
        mask = self.causal[:t, :t]
        panels: Dict[str, torch.Tensor] = {}
        for i, blk in enumerate(self.blocks):
            panels[f"L{i}_pre"] = h.detach().clone()
            h = blk(h, src_mask=mask, is_causal=True)
            panels[f"L{i}_post"] = h.detach().clone()
        logits = self.head(self.final_ln(h))
        return logits, panels

    @torch.no_grad()
    def forward_patched(
        self,
        tokens: torch.Tensor,
        patches: Dict[str, torch.Tensor],
    ) -> torch.Tensor:
        """Forward avec panneaux residuels REMPLACES, logits seuls.

        Le point d'entree causal du pilote : les instruments numpy-only
        (moteur causal, J-Lens) transforment un panneau capture, puis ce
        forward re-injecte la version modifiee a son point de prelevement
        (``L{i}_pre`` remplace le residuel en entree du bloc i, ``L{i}_post``
        en sortie) et propage jusqu'aux logits. Sans patch, le forward est
        l'identite — c'est le bras intact par la meme voie de code.
        """
        b, t = tokens.shape
        tokens = tokens.to(self.embed.weight.device)
        h = self.embed(tokens) + self.pos(torch.arange(t, device=tokens.device))
        mask = self.causal[:t, :t]
        for i, blk in enumerate(self.blocks):
            if f"L{i}_pre" in patches:
                h = patches[f"L{i}_pre"].to(device=h.device, dtype=h.dtype)
            h = blk(h, src_mask=mask, is_causal=True)
            if f"L{i}_post" in patches:
                h = patches[f"L{i}_post"].to(device=h.device, dtype=h.dtype)
        return self.head(self.final_ln(h))


@dataclass
class TrainConfig:
    steps: int = 3000
    batch: int = 64
    seq_len: int = 64
    lr: float = 3e-4
    weight_decay: float = 0.01
    eval_every: int = 500
    log: List[Tuple[int, float, float]] = field(default_factory=list)


def train_tiny(
    model: TinyTransformer,
    token_seqs: Array,
    cfg: TrainConfig,
    device: str = "cpu",
) -> TrainConfig:
    """Entrainement next-token sur des sequences pre-tokenisees (N, L).

    Le protocole vary-one du banc fournit les sequences ; aucune donnee
    d'evaluation n'entre ici (la mesure se fait ailleurs sur decoupe gelee).
    """
    model.to(device)
    tokens_all = torch.from_numpy(token_seqs).to(device)
    n, total_len = tokens_all.shape
    opt = torch.optim.AdamW(model.parameters(), lr=cfg.lr,
                            weight_decay=cfg.weight_decay)
    model.train()
    for step in range(cfg.steps):
        idx = torch.randint(0, n, (cfg.batch,), device=device)
        starts = torch.randint(0, total_len - cfg.seq_len - 1, (cfg.batch,),
                               device=device)
        cols = starts.unsqueeze(1) + torch.arange(
            cfg.seq_len + 1, device=device).unsqueeze(0)
        rows = idx.unsqueeze(1).expand(-1, cfg.seq_len + 1)
        windows = tokens_all[rows, cols]
        x = windows[:, :-1]
        y = windows[:, 1:]
        logits, _ = model.forward_with_panels(x)
        loss = F.cross_entropy(logits.reshape(-1, logits.shape[-1]),
                               y.reshape(-1))
        opt.zero_grad(set_to_none=True)
        loss.backward()
        torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
        opt.step()
        if step % cfg.eval_every == 0 or step == cfg.steps - 1:
            with torch.no_grad():
                model.eval()
                vrows = tokens_all[: min(256, n), : cfg.seq_len + 1]
                vlogits, _ = model.forward_with_panels(vrows[:, :-1])
                vloss = F.cross_entropy(
                    vlogits.reshape(-1, vlogits.shape[-1]),
                    vrows[:, 1:].reshape(-1),
                ).item()
                model.train()
            cfg.log.append((step, loss.item(), vloss))
    return cfg


def capture_panels(
    model: TinyTransformer,
    token_seqs: Array,
    seq_len: int,
    device: str = "cpu",
    batch: int = 128,
) -> Dict[str, Array]:
    """Panneaux residuels numpy (N, seq_len, d) par cle L{i}_pre/post."""
    model.to(device).eval()
    out: Dict[str, List[Array]] = {}
    with torch.no_grad():
        for s in range(0, len(token_seqs), batch):
            chunk = torch.from_numpy(
                token_seqs[s: s + batch, :seq_len]
            ).to(device)
            _, panels = model.forward_with_panels(chunk)
            for k, v in panels.items():
                out.setdefault(k, []).append(v.cpu().numpy())
    return {k: np.concatenate(vs, axis=0) for k, vs in out.items()}


def sequences_from_bench(
    token_of_seq: Array,
    seq_len: int,
    hop: int = 32,
) -> Array:
    """Decoupe une longue sequence tokenisee en fenetres (N, seq_len)."""
    n = len(token_of_seq)
    if n < seq_len:
        raise ProcessValueError("sequence plus courte que seq_len")
    return np.stack([
        token_of_seq[s: s + seq_len] for s in range(0, n - seq_len + 1, hop)
    ])
