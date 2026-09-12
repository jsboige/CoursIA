"""POC S-Lens (#15481) — entrainement des bancs synthetiques + capture numpy.

Confine torch (regle d'architecture de la serie : ``ict/`` reste numpy-only).
Un run = un triplet (task, arch, seed) :

* entraine un micro-transformer sur le banc ``copy_offset`` ou
  ``variable_binding`` (ground truth exacte, oracles de ``ict.slens``) ;
* evalue l'exactitude comportementale, par position de reference ;
* capture, pour un jeu held-out, les sorties par couche/tete a la position de
  requete (matiere du probe de self-location) et les residuels de couche ;
* execute la jambe causale : patching apparié du residual au token d'offset
  entre deux exemples qui partagent leur bloc de valeurs et ne different que
  par l'offset — avec sham (auto-echange) et cible aleatoire non appariée — et
  mesure le dommage general via :mod:`ict.causal_engine` ;
* ecrit un npz + un manifeste POC-local (``ict.slens.slens_manifest``).

Architectures comparees (#15481) — trois bras, dont DEUX requis par l'issue :

* ``rope`` : encodage positionnel rotatif sur Q/K (distance relative
  accessible nativement) ;
* ``abs`` (variante « position derivee du contenu » au sens du POC) : encodage
  positionnel ABSOLU appris — dans les deux bras, la *reference* est resolue
  depuis le contenu (le symbole d'offset ou la variable interrogee), seules la
  structure positionnelle et sa generalisation relative different ;
* ``none`` : AUCUNE information positionnelle — plancher de controle qui
  documente que l'information de position doit venir de quelque part.

Interpretation consignee (mode non supervise, CLAUDE.md principe 1) : l'issue
#15481 demande « une architecture RoPE et une variante ou la position est
derivee du contenu ». Toutes les variantes resolvent la reference depuis le
contenu ; c'est la *fourniture* de la structure positionnelle qui differe
(``rope`` relative vs ``abs`` absolue vs ``none`` plancher). Un ecart
``rope``/``abs`` est donc un resultat sur la generalisation relative, pas une
différence de banc.

Usage :
    python scripts/slens_poc.py --task copy_offset --arch rope --seed 0 \
        --stage full --out traces/slens_copy_offset_rope_s0.npz
"""
from __future__ import annotations

import argparse
import dataclasses
import datetime as _dt
import json
import math
import sys
import time
from pathlib import Path
from typing import Sequence

import numpy as np
import torch
import torch.nn as nn
import torch.nn.functional as F

# Le package ``ict/`` reste numpy-only : on l'importe pour les bancs/oracles et
# le moteur commun d'intervention (pures fonctions numpy, testables sans GPU).
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from ict import causal_engine, slens  # noqa: E402


# --------------------------------------------------------------------------- #
# Micro-transformer (attention explicite : capture par tete requise)
# --------------------------------------------------------------------------- #

class MicroTransformer(nn.Module):
    """Transformer minimal, 2 couches, attention multi-tete explicite.

    L'attention est ecrite a la main (pas ``nn.MultiheadAttention``) parce que
    le POC doit capturer et patcher la sortie de CHAQUE tete separement.
    """

    def __init__(self, vocab_size: int, d_model: int = 64, n_heads: int = 4,
                 n_layers: int = 2, arch: str = "rope", max_len: int = 32) -> None:
        super().__init__()
        if d_model % n_heads:
            raise ValueError("d_model doit etre divisible par n_heads")
        if arch not in ("rope", "abs", "none"):
            raise ValueError(f"arch {arch!r} hors POC (rope|abs|none)")
        self.arch = arch
        self.d_model = d_model
        self.n_heads = n_heads
        self.n_layers = n_layers
        self.head_dim = d_model // n_heads
        self.embed = nn.Embedding(vocab_size, d_model)
        self.pos = nn.Embedding(max_len, d_model) if arch == "abs" else None
        self.blocks = nn.ModuleList(
            [_Block(d_model, n_heads, arch) for _ in range(n_layers)]
        )
        self.ln_f = nn.LayerNorm(d_model)
        self.head = nn.Linear(d_model, vocab_size, bias=False)

    def rope_tables(self, t: int, device) -> tuple[torch.Tensor, torch.Tensor]:
        half = self.head_dim // 2
        inv = torch.exp(
            -math.log(10000.0)
            * torch.arange(half, device=device, dtype=torch.float32)
            / max(half, 1)
        )
        pos = torch.arange(t, device=device, dtype=torch.float32)
        ang = torch.outer(pos, inv)                       # (t, half)
        return torch.cos(ang), torch.sin(ang)

    def forward(self, tokens: torch.Tensor, capture: bool = False,
                patch: tuple[int, int, torch.Tensor] | None = None):
        """``patch`` = (couche, position, valeurs) applique APRES la couche."""
        b, t = tokens.shape
        h = self.embed(tokens)
        if self.pos is not None:
            idx = torch.arange(t, device=tokens.device)
            h = h + self.pos(idx)[None]
        cos = sin = None
        if self.arch == "rope":
            cos, sin = self.rope_tables(t, tokens.device)
        caps_head: dict[str, torch.Tensor] = {}
        caps_layer: dict[str, torch.Tensor] = {}
        for li, block in enumerate(self.blocks):
            if capture:
                caps_layer[f"L{li}"] = h.detach().cpu().numpy()
            h, per_head = block(h, cos, sin, capture=capture)
            if capture:
                for hi, out in enumerate(per_head):
                    caps_head[f"L{li}H{hi}"] = out.detach().cpu().numpy()
            if patch is not None and patch[0] == li:
                h = h.clone()
                h[:, patch[1], :] = patch[2]
        h = self.ln_f(h)
        if capture:
            # residuel POST-pile : c'est la seule vue ou la propagation aval
            # d'un patch est visible (une capture avant la derniere couche ne
            # montre que la coordonnee patchee elle-meme).
            caps_layer[f"post_stack"] = h.detach().cpu().numpy()
        logits = self.head(h)
        if capture:
            return logits, caps_head, caps_layer
        return logits, None, None


class _Block(nn.Module):
    def __init__(self, d_model: int, n_heads: int, arch: str) -> None:
        super().__init__()
        self.n_heads = n_heads
        self.arch = arch
        self.head_dim = d_model // n_heads
        self.ln1 = nn.LayerNorm(d_model)
        self.qkv = nn.Linear(d_model, 3 * d_model)
        self.proj = nn.Linear(d_model, d_model)
        self.ln2 = nn.LayerNorm(d_model)
        self.mlp = nn.Sequential(
            nn.Linear(d_model, 4 * d_model), nn.GELU(),
            nn.Linear(4 * d_model, d_model),
        )

    @staticmethod
    def _rope(x: torch.Tensor, cos: torch.Tensor, sin: torch.Tensor) -> torch.Tensor:
        # x : (b, h, t, dh) ; rotation des paires (x0, x1)
        x0, x1 = x[..., 0::2], x[..., 1::2]
        c, s = cos[None, None], sin[None, None]
        return torch.stack([x0 * c - x1 * s, x0 * s + x1 * c], dim=-1).flatten(-2)

    def forward(self, h: torch.Tensor, cos, sin, capture: bool = False):
        b, t, d = h.shape
        x = self.ln1(h)
        qkv = self.qkv(x).view(b, t, 3, self.n_heads, self.head_dim)
        qkv = qkv.permute(0, 3, 2, 1, 4)                   # (b, h, 3, t, dh)
        q, k, v = qkv.unbind(2)
        if self.arch == "rope":
            q = self._rope(q, cos, sin)
            k = self._rope(k, cos, sin)
        att = (q @ k.transpose(-1, -2)) / math.sqrt(self.head_dim)
        mask = torch.triu(torch.ones(t, t, device=h.device, dtype=torch.bool), 1)
        att = att.masked_fill(mask, float("-inf")).softmax(dim=-1)
        per_head = att @ v                                  # (b, h, t, dh)
        merged = per_head.transpose(1, 2).reshape(b, t, d)
        h = h + self.proj(merged)
        h = h + self.mlp(self.ln2(h))
        if capture:
            return h, [per_head[:, i] for i in range(self.n_heads)]
        return h, []


# --------------------------------------------------------------------------- #
# Donnees : bancs de ``ict.slens`` (oracle exact partage avec les tests)
# --------------------------------------------------------------------------- #

def task_config(task: str):
    if task == "copy_offset":
        return slens.CopyOffsetConfig(seq_values=12, n_symbols=16)
    if task == "variable_binding":
        return slens.VarBindingConfig(n_pairs=5, n_vars=8, n_vals=8)
    raise ValueError(f"task {task!r} inconnue (copy_offset|variable_binding)")


def generate(task: str, rng, n: int) -> dict:
    cfg = task_config(task)
    if task == "copy_offset":
        return slens.generate_copy_offset(rng, n, cfg)
    return slens.generate_variable_binding(rng, n, cfg)


def oracle(task: str, tokens: np.ndarray):
    cfg = task_config(task)
    if task == "copy_offset":
        return slens.oracle_copy_offset(tokens, cfg)
    return slens.oracle_variable_binding(tokens, cfg)


def oracle_position_of(batch: dict) -> np.ndarray:
    return batch["target_pos"].astype(np.int64)


# --------------------------------------------------------------------------- #
# Entrainement / evaluation
# --------------------------------------------------------------------------- #

def to_torch(batch: dict, device) -> tuple[torch.Tensor, torch.Tensor]:
    x = torch.as_tensor(batch["tokens"], dtype=torch.long, device=device)
    y = torch.as_tensor(_target_index(batch), dtype=torch.long, device=device)
    return x, y


def _target_index(batch: dict) -> np.ndarray:
    # La cible de lecture est l'ID DE TOKEN a la position de reference (passe
    # par l'oracle pour rester coherent avec la ground truth).
    return batch["target_value"].astype(np.int64)


def train_model(model: MicroTransformer, task: str, seed: int, steps: int,
                batch_size: int, lr: float, device) -> list[float]:
    rng = np.random.default_rng(1000 + seed)
    opt = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=0.01)
    losses: list[float] = []
    model.train()
    for step in range(steps):
        batch = generate(task, rng, batch_size)
        x, y = to_torch(batch, device)
        logits, _, _ = model(x)
        loss = F.cross_entropy(logits[:, -1, :], y)
        opt.zero_grad()
        loss.backward()
        opt.step()
        if step % max(1, steps // 20) == 0:
            losses.append(float(loss.item()))
    return losses


@torch.no_grad()
def evaluate(model: MicroTransformer, task: str, seed: int, n: int, device):
    model.eval()
    rng = np.random.default_rng(9000 + seed)
    batch = generate(task, rng, n)
    x, y = to_torch(batch, device)
    logits, _, _ = model(x)
    pred = logits[:, -1, :].argmax(dim=-1).cpu().numpy()
    acc = float(np.mean(pred == batch["target_value"]))
    by_pos = slens.copy_success_by_position(
        pred, batch["target_value"], batch["target_pos"], task_config(task).n_tokens
    )
    return batch, pred, acc, by_pos


# --------------------------------------------------------------------------- #
# Jambe causale : patching apparie au token d'offset
# --------------------------------------------------------------------------- #

@torch.no_grad()
def patch_experiment(model: MicroTransformer, task: str, seed: int, n_pairs: int,
                     patch_layer: int, device) -> dict:
    """Patching apparie du residual a la position pivot, avec controles.

    Hote et donneur partagent tout le contexte et ne different que par la
    reference : offset du banc ``copy_offset`` (:func:`ict.slens.paired_by_offset`),
    variable interrogee du banc ``variable_binding``
    (:func:`ict.slens.paired_by_query`). Si la sortie patchee suit la reference
    du donneur, elle suit la REFERENCE, pas une correlation de surface.

    Controles : sham = auto-echange (le modele recoit sa propre valeur, la
    prediction doit rester celle de l'hote) ; cible aleatoire = donneur decale
    d'un rang (non apparie, doit retomber au niveau du hasard). Le dommage
    general est mesure sur le residuel FINAL via
    :func:`ict.causal_engine.damage_metrics` : une intervention chirurgicale
    n'y laisse que ce que la propagation aval emporte.
    """
    rng = np.random.default_rng(4242 + seed)
    if task == "copy_offset":
        cfg = slens.CopyOffsetConfig(seq_values=12, n_symbols=16)
        pairs = slens.paired_by_offset(cfg, rng, n_pairs)
        pivot = cfg.seq_values                     # position du token d'offset
    else:
        cfg = slens.VarBindingConfig(n_pairs=5, n_vars=8, n_vals=8)
        pairs = slens.paired_by_query(cfg, rng, n_pairs)
        pivot = cfg.n_tokens - 2                   # marqueur de requete QB
    target_a = pairs["target_value_a"]
    target_b = pairs["target_value_b"]

    xa = torch.as_tensor(pairs["tokens_a"], dtype=torch.long, device=device)
    xb = torch.as_tensor(pairs["tokens_b"], dtype=torch.long, device=device)
    key = f"L{patch_layer}"

    # etats internes : hote et donneur, a la position pivot
    _, _, caps_a = model(xa, capture=True)
    _, _, caps_b = model(xb, capture=True)
    host_vals = torch.as_tensor(caps_a[key][:, pivot, :], device=device)
    donor_vals = torch.as_tensor(caps_b[key][:, pivot, :], device=device)

    base_pred = model(xa)[0][:, -1, :].argmax(-1).cpu().numpy()
    patched_pred = model(xa, patch=(patch_layer, pivot, donor_vals))[0][:, -1, :]
    patched_pred = patched_pred.argmax(-1).cpu().numpy()
    # sham : le modele recoit sa propre valeur par la meme voie de code
    sham_pred = model(xa, patch=(patch_layer, pivot, host_vals))[0][:, -1, :]
    sham_pred = sham_pred.argmax(-1).cpu().numpy()
    # cible aleatoire : donneur decale (jamais apparie a l'hote)
    shift = max(1, n_pairs // 7)
    unpaired = np.roll(np.arange(n_pairs), shift)
    rand_donor = torch.as_tensor(caps_b[key][unpaired, pivot, :], device=device)
    rand_pred = model(xa, patch=(patch_layer, pivot, rand_donor))[0][:, -1, :]
    rand_pred = rand_pred.argmax(-1).cpu().numpy()

    # dommage general sur le residuel final
    _, _, caps_final_a = model(xa, capture=True)
    _, _, caps_final_patched = model(xa, patch=(patch_layer, pivot, donor_vals),
                                     capture=True)
    final_layer = "post_stack"
    damages = []
    for i in range(n_pairs):
        # l'intervention est un ECHANGE apparie hote<->donneur : on declare
        # ``interchange`` (et non ``patch``, qui exige un donneur explicite) —
        # la mesure de dommage porte sur le panneau de l'hote avant/apres.
        spec = causal_engine.InterventionSpec(
            operation="interchange", instrument="slens", layer=patch_layer,
            positions=(pivot,), features=tuple(range(caps_final_a[final_layer].shape[-1])),
            run="host", paired_run="donor", seed=seed,
        )
        damages.append(causal_engine.damage_metrics(
            caps_final_a[final_layer][i], caps_final_patched[final_layer][i], spec))

    def _agg(name: str) -> float:
        return float(np.mean([d[name] for d in damages]))

    return {
        "follow_donor": float(np.mean(patched_pred == target_b)),
        "sham": float(np.mean(sham_pred == target_a)),
        "random_target": float(np.mean(rand_pred == target_b[unpaired])),
        "base_accuracy": float(np.mean(base_pred == target_a)),
        "pivot": int(pivot),
        "target_rel": _agg("target_rel"),
        "off_target_rel": _agg("off_target_rel"),
        "selectivity_ratio": _agg("selectivity_ratio"),
    }


# --------------------------------------------------------------------------- #
# Programme principal
# --------------------------------------------------------------------------- #

def _jsonable(value):
    """Convertit recursivement les scalaires numpy en types JSON natifs."""
    if isinstance(value, dict):
        return {str(k): _jsonable(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [_jsonable(v) for v in value]
    if isinstance(value, (np.floating, np.integer)):
        return value.item()
    if isinstance(value, np.bool_):
        return bool(value)
    if isinstance(value, np.ndarray):
        return value.tolist()
    return value


def aggregate(paths: Sequence[str]) -> dict:
    """Reduit des npz de runs en matrice agregee + verdict de promotion.

    C'est l'artefact COMMITTE (``traces/slens_matrix.json``) : les npz bruts
    pesent ~1 MiB piece et restent locaux, mais les runs sont entierement
    specifiés par ``(task, arch, seed, stage)`` dans le manifeste — la
    commande de regeneration est ecrite dans le JSON lui-meme.
    """
    runs = [slens.load_run(p) for p in paths]
    evidence, rows = slens.evidence_from_runs(runs)
    return {
        "contract": "slens_poc",
        "generated": _dt.datetime.now(_dt.timezone.utc).isoformat(timespec="seconds"),
        "n_runs": len(runs),
        "runs": [
            {"file": Path(p).name, "task": r["meta"]["task"],
             "arch": r["meta"]["arch"], "seed": r["meta"]["seed"],
             "stage": r["meta"].get("stage"), "steps": r["meta"].get("steps"),
             "n_test": r["meta"].get("n_test")}
            for p, r in zip(paths, runs)
        ],
        "per_run": _jsonable(rows),
        "evidence": dataclasses.asdict(evidence),
        "verdict": slens.promotion_verdict(evidence),
        "regenerate": (
            "python scripts/slens_poc.py --task <task> --arch <arch> --seed <seed> "
            "--stage full --out traces/slens_<task>_<arch>_s<seed>.npz"
        ),
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--task", default="copy_offset",
                    choices=["copy_offset", "variable_binding"])
    ap.add_argument("--arch", default="rope", choices=["rope", "abs", "none"])
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--stage", default="smoke", choices=["smoke", "full"])
    ap.add_argument("--out", default=None)
    ap.add_argument("--aggregate", nargs="+", default=None, metavar="NPZ",
                    help="agrege des npz de runs en matrice JSON (pas d'entrainement)")
    ap.add_argument("--d-model", type=int, default=64)
    ap.add_argument("--n-heads", type=int, default=4)
    ap.add_argument("--n-layers", type=int, default=2)
    ap.add_argument("--patch-layer", type=int, default=0)
    ap.add_argument("--device", default="cuda" if torch.cuda.is_available() else "cpu")
    args = ap.parse_args()

    if args.aggregate is not None:
        if not args.out:
            ap.error("--out requis avec --aggregate (chemin du JSON de matrice)")
        payload = aggregate(sorted(args.aggregate))
        out = Path(args.out)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8")
        print(f"[matrix] {out} — {payload['n_runs']} runs — verdict "
              f"{payload['verdict']}")
        print(f"[evidence] {json.dumps(payload['evidence'], ensure_ascii=False)}")
        return
    if not args.out:
        ap.error("--out requis (chemin du npz de run)")

    steps = 300 if args.stage == "smoke" else 3000
    n_eval = 256 if args.stage == "smoke" else 1024
    n_patch = 64 if args.stage == "smoke" else 512
    torch.manual_seed(args.seed)
    torch.cuda.manual_seed_all(args.seed)

    cfg = task_config(args.task)
    model = MicroTransformer(
        vocab_size=cfg.vocab_size, d_model=args.d_model, n_heads=args.n_heads,
        n_layers=args.n_layers, arch=args.arch,
    ).to(args.device)

    t0 = time.time()
    losses = train_model(model, args.task, args.seed, steps, 128, 3e-3, args.device)

    # ---- controles de banc : le generateur est valide par l'oracle ----------
    probe_batch = generate(args.task, np.random.default_rng(1), 128)
    val, pos = oracle(args.task, probe_batch["tokens"])
    assert np.array_equal(val, probe_batch["target_value"]), "oracle != generateur"
    assert np.array_equal(pos, probe_batch["target_pos"]), "oracle positions != generateur"

    batch, pred, acc, by_pos = evaluate(model, args.task, args.seed, n_eval, args.device)

    # ---- capture par couche/tete a la position de requete ------------------
    x = torch.as_tensor(batch["tokens"], dtype=torch.long, device=args.device)
    _, caps_head, caps_layer = model(x, capture=True)
    last = x.shape[1] - 1
    acts_head = {f"{k}_q": v[:, last, :] for k, v in caps_head.items()}
    acts_layer = {f"{k}_q": v[:, last, :] for k, v in caps_layer.items()}
    acts_layer[f"L{args.n_layers - 1}_finalq"] = caps_layer[
        f"L{args.n_layers - 1}"][:, last, :]

    patch_stats = patch_experiment(
        model, args.task, args.seed, n_patch, args.patch_layer, args.device
    )

    manifest = slens.slens_manifest(
        task=args.task, arch=args.arch, run=f"slens_{args.task}_{args.arch}",
        seed=args.seed, layer=args.patch_layer, d_model=args.d_model,
        n_heads=args.n_heads, n_layers=args.n_layers, n_test=int(batch["tokens"].shape[0]),
        prompt_set=f"synthetic_{args.task}",
        stage=args.stage, steps=steps, device=args.device,
        losses_head=losses[-1] if losses else None,
        date=_dt.datetime.now(_dt.timezone.utc).isoformat(timespec="seconds"),
    )

    arrays: dict[str, np.ndarray] = {
        "__meta__": np.array(json.dumps(manifest, ensure_ascii=False)),
        "tokens": batch["tokens"],
        "target_value": batch["target_value"],
        "target_pos": batch["target_pos"],
        "pred": pred,
        "predictions_accuracy": np.array(acc),
        "success_by_pos": by_pos,
        "patch_stats": np.array(json.dumps(patch_stats, ensure_ascii=False)),
    }
    arrays.update(acts_head)
    arrays.update(acts_layer)
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    np.savez_compressed(out, **arrays)
    print(f"[out] {out} ({out.stat().st_size / 2**20:.2f} MiB)")
    print(f"[acc] {args.task}/{args.arch}/s{args.seed} = {acc:.3f} "
          f"(loss finale {losses[-1]:.3f}) en {time.time() - t0:.0f}s")
    print(f"[patch] {json.dumps(patch_stats, ensure_ascii=False)}")
    print(f"[dmg] off_target_rel={patch_stats['off_target_rel']:.4f}")


if __name__ == "__main__":
    main()
