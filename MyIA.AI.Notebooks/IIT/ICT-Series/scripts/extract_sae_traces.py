"""Extraction de trajectoires SAE pour ICT-21 (#5101) — Qwen3.5-9B-Base x Qwen-Scope.

Pipeline GPU (le SEUL de la serie : `ict/` reste numpy-only, ce script confine
torch/transformers). Pour chaque prompt d'un jeu contrastif (>=5 jeux), capture le
residual stream (`resid_post`) a une couche donnee, l'encode avec le SAE officiel
Qwen-Scope (top-k, k=50) et stocke la representation SPARSE EXHAUSTIVE par token :
(indices, valeurs) du top-50. Toute activation hors top-50 vaut exactement 0 par
construction du SAE top-k, donc ce stockage subsume le schema amende de #5101
(commentaire 4903813757) : `acts_topk` K~64 continu ET le panel binarise ~10
features se derivent exactement, GPU-free, dans le notebook ICT-21.

Conventions d'encodage = demo officielle Qwen-Scope (app.py du repo HF) :
    sae = torch.load("layer{L}.sae.pt", weights_only=True)   # dict W_enc/b_enc/...
    pre = hidden @ W_enc.T + b_enc ; acts = topk(relu(pre), k=50)
(pas de soustraction b_dec a l'encodage, pas de normalisation du hidden.)

Modele-controle (sanctionne par le corps de #5101) : permutation seedee des lignes
de la matrice d'input embeddings — meme architecture, meme statistique marginale
des embeddings, semantique detruite.

Hook de clamp (Gate 24 de #5635, phase 2 — NON exECUTE dans cette issue) :
`--clamp-ids` force un sous-ensemble de features SAE a zero en soustrayant leur
contribution decodeur du residual stream (necessite W_dec dans le checkpoint).

Usage (GPU 2 d'ai-01 STRICT — vLLM tient GPU 0-1) :
    CUDA_VISIBLE_DEVICES=2 PYTORCH_CUDA_ALLOC_CONF=expandable_segments:True \
      python extract_sae_traces.py --stage smoke
    ... --stage full --variant trained
    ... --stage full --variant control
"""
from __future__ import annotations

import argparse
import datetime as _dt
import json
import sys
import time
from pathlib import Path

import numpy as np
import torch

# ---------------------------------------------------------------------------
# Jeux de prompts contrastifs (>=5 jeux = multi-graines du Gate 12, cf #5102).
# Textes volontairement heterogenes : le panel differentiel en aval cherche des
# features qui discriminent les regimes.
# ---------------------------------------------------------------------------
PROMPT_SETS: dict[str, list[str]] = {
    "code_python": [
        (
            "def dijkstra(graph, source):\n"
            "    import heapq\n"
            "    dist = {v: float('inf') for v in graph}\n"
            "    dist[source] = 0\n"
            "    heap = [(0, source)]\n"
            "    while heap:\n"
            "        d, u = heapq.heappop(heap)\n"
            "        if d > dist[u]:\n"
            "            continue\n"
            "        for v, w in graph[u].items():\n"
            "            nd = d + w\n"
            "            if nd < dist[v]:\n"
            "                dist[v] = nd\n"
            "                heapq.heappush(heap, (nd, v))\n"
            "    return dist\n\n"
            "# Test sur un petit graphe pondere\n"
            "g = {'a': {'b': 2, 'c': 5}, 'b': {'c': 1, 'd': 4}, 'c': {'d': 1}, 'd': {}}\n"
            "print(dijkstra(g, 'a'))\n"
        ),
        (
            "class LRUCache:\n"
            "    def __init__(self, capacity: int):\n"
            "        from collections import OrderedDict\n"
            "        self.capacity = capacity\n"
            "        self.cache = OrderedDict()\n\n"
            "    def get(self, key):\n"
            "        if key not in self.cache:\n"
            "            return -1\n"
            "        self.cache.move_to_end(key)\n"
            "        return self.cache[key]\n\n"
            "    def put(self, key, value):\n"
            "        if key in self.cache:\n"
            "            self.cache.move_to_end(key)\n"
            "        self.cache[key] = value\n"
            "        if len(self.cache) > self.capacity:\n"
            "            self.cache.popitem(last=False)\n"
        ),
        (
            "import numpy as np\n\n"
            "def gray_scott_step(u, v, du, dv, f, k, dt=1.0):\n"
            "    lap_u = (np.roll(u, 1, 0) + np.roll(u, -1, 0)\n"
            "             + np.roll(u, 1, 1) + np.roll(u, -1, 1) - 4 * u)\n"
            "    lap_v = (np.roll(v, 1, 0) + np.roll(v, -1, 0)\n"
            "             + np.roll(v, 1, 1) + np.roll(v, -1, 1) - 4 * v)\n"
            "    uvv = u * v * v\n"
            "    u_new = u + dt * (du * lap_u - uvv + f * (1 - u))\n"
            "    v_new = v + dt * (dv * lap_v + uvv - (f + k) * v)\n"
            "    return u_new, v_new\n"
        ),
        (
            "-- Requete SQL : les 10 clients au plus fort chiffre d'affaires 2025\n"
            "SELECT c.customer_id, c.name, SUM(o.amount) AS total\n"
            "FROM customers c\n"
            "JOIN orders o ON o.customer_id = c.customer_id\n"
            "WHERE o.order_date >= '2025-01-01' AND o.order_date < '2026-01-01'\n"
            "GROUP BY c.customer_id, c.name\n"
            "HAVING SUM(o.amount) > 10000\n"
            "ORDER BY total DESC\n"
            "LIMIT 10;\n"
        ),
    ],
    "prose_fr": [
        (
            "La conscience demeure l'un des problemes les plus redoutables de la "
            "philosophie de l'esprit. Deux grandes familles de theories s'affrontent "
            "aujourd'hui : d'un cote, la theorie de l'information integree soutient "
            "que l'experience subjective correspond a la capacite d'un systeme a "
            "integrer de l'information de maniere irreductible ; de l'autre, la "
            "theorie de l'espace de travail global avance que la conscience d'acces "
            "nait de la diffusion selective d'une representation a l'ensemble des "
            "processeurs specialises du cerveau. Ces deux lectures, longtemps tenues "
            "pour rivales, pourraient bien decrire deux faces du meme phenomene."
        ),
        (
            "Le vieux port s'eveillait lentement sous la brume d'octobre. Les "
            "chalutiers rentraient un a un, charges de caisses ou luisaient encore "
            "les ecailles des sardines. Sur le quai, Marthe comptait les cageots "
            "d'une main distraite, l'esprit occupe par la lettre recue la veille : "
            "son fils annoncait son retour apres dix ans d'absence, sans un mot "
            "d'explication. Elle regarda la mer, grise et etale, comme si la surface "
            "pouvait lui rendre les annees perdues."
        ),
        (
            "L'architecture gothique represente une rupture profonde avec l'art "
            "roman qui la precede. La ou le roman cherchait la masse et la penombre, "
            "le gothique poursuit la hauteur et la lumiere : croisees d'ogives, "
            "arcs-boutants et vitraux immenses permettent d'evider les murs et de "
            "faire entrer le ciel dans la nef. La cathedrale devient un livre de "
            "pierre et de verre ou se lit toute la theologie medievale de la clarte."
        ),
        (
            "La transition energetique impose de repenser l'ensemble du reseau "
            "electrique europeen. L'intermittence du solaire et de l'eolien exige "
            "des capacites de stockage massives, des interconnexions renforcees "
            "entre pays et une gestion fine de la demande. Les batteries, les "
            "stations de pompage-turbinage et l'hydrogene vert forment un triptyque "
            "complementaire dont l'equilibre economique reste, pour l'heure, "
            "largement dependant des politiques publiques."
        ),
    ],
    "dialogue": [
        (
            "Client : Bonjour, j'ai commande un ordinateur portable il y a dix "
            "jours et je n'ai toujours rien recu.\n"
            "Conseiller : Bonjour, je suis navre pour ce retard. Pouvez-vous me "
            "donner votre numero de commande ?\n"
            "Client : Oui, c'est la commande 78-4412-K.\n"
            "Conseiller : Merci. Je vois que le colis est bloque au centre de tri "
            "de Lyon depuis vendredi. Je lance une reclamation aupres du "
            "transporteur immediatement.\n"
            "Client : Et si le colis est perdu ?\n"
            "Conseiller : Dans ce cas nous vous renvoyons un exemplaire neuf sous "
            "48 heures ou nous vous remboursons integralement, a votre convenance.\n"
        ),
        (
            "Alice : Tu as lu le rapport du GIEC publie ce matin ?\n"
            "Bruno : Pas encore, il dit quoi de nouveau ?\n"
            "Alice : Que la fenetre pour rester sous 1,5 degre se referme plus "
            "vite que prevu. Ils insistent sur le methane cette fois.\n"
            "Bruno : Le methane ? Je croyais que le CO2 restait le principal "
            "levier.\n"
            "Alice : Sur le long terme oui, mais le methane a un effet immediat : "
            "le reduire maintenant ferait baisser la temperature des 2040.\n"
            "Bruno : Donc il faudrait s'attaquer aux fuites des gazoducs et a "
            "l'elevage en priorite ?\n"
            "Alice : Exactement, c'est le levier le plus rapide dont on dispose.\n"
        ),
        (
            "Le juge : Maitre, votre client reconnait-il les faits ?\n"
            "L'avocate : Il reconnait sa presence sur les lieux, monsieur le "
            "president, mais conteste toute participation active.\n"
            "Le juge : Les images de videosurveillance le montrent pourtant "
            "ouvrant la porte de service.\n"
            "L'avocate : Ouvrir une porte n'est pas un delit ; mon client "
            "ignorait les intentions des deux autres prevenus.\n"
            "Le juge : Nous entendrons les experts sur ce point cet apres-midi.\n"
        ),
        (
            "Etudiant : Je ne comprends pas pourquoi mon gradient explose a la "
            "dixieme epoque.\n"
            "Encadrante : Quel taux d'apprentissage utilises-tu ?\n"
            "Etudiant : 0,01 avec un optimiseur SGD classique.\n"
            "Encadrante : Essaie d'abord un clipping de gradient a 1,0, puis "
            "regarde la norme des activations couche par couche. Si une couche "
            "diverge avant les autres, le probleme vient de son initialisation.\n"
            "Etudiant : D'accord, et si tout diverge en meme temps ?\n"
            "Encadrante : Alors baisse le taux d'apprentissage d'un facteur dix "
            "et ajoute un warmup progressif sur les mille premiers pas.\n"
        ),
    ],
    "math": [
        (
            "Theoreme (inegalite de Cauchy-Schwarz). Pour tous vecteurs u et v "
            "d'un espace prehilbertien reel, |<u, v>| <= ||u|| ||v||, avec egalite "
            "si et seulement si u et v sont colineaires.\n"
            "Preuve. Si v = 0 le resultat est immediat. Sinon, pour tout reel t, "
            "0 <= ||u + t v||^2 = ||u||^2 + 2 t <u, v> + t^2 ||v||^2. Ce trinome "
            "en t est positif ou nul pour tout t, donc son discriminant est "
            "negatif ou nul : 4 <u, v>^2 - 4 ||u||^2 ||v||^2 <= 0, d'ou "
            "l'inegalite. L'egalite force un discriminant nul, donc une racine "
            "double t0 avec u = -t0 v. CQFD.\n"
        ),
        (
            "Probleme. Une urne contient 5 boules rouges et 3 boules bleues. On "
            "tire deux boules sans remise. Quelle est la probabilite d'obtenir "
            "exactement une boule rouge ?\n"
            "Solution. Deux cas disjoints : rouge puis bleue, de probabilite "
            "(5/8) x (3/7) = 15/56 ; bleue puis rouge, de probabilite "
            "(3/8) x (5/7) = 15/56. Total : 30/56 = 15/28.\n"
        ),
        (
            "Calculons la limite de (1 + 1/n)^n quand n tend vers l'infini. En "
            "passant au logarithme, n ln(1 + 1/n) = n (1/n - 1/(2n^2) + o(1/n^2)) "
            "= 1 - 1/(2n) + o(1/n), qui tend vers 1. Par continuite de "
            "l'exponentielle, la suite converge vers e. Plus generalement, "
            "(1 + x/n)^n tend vers exp(x) pour tout reel x, resultat qui fonde la "
            "definition de l'exponentielle par la methode d'Euler.\n"
        ),
        (
            "Soit f(x) = x^3 - 3x + 1. Sa derivee f'(x) = 3x^2 - 3 s'annule en "
            "x = -1 et x = 1. On a f(-1) = 3 > 0 et f(1) = -1 < 0 : f admet donc "
            "un maximum local positif et un minimum local negatif, et comme f "
            "tend vers -infini en -infini et +infini en +infini, le theoreme des "
            "valeurs intermediaires garantit exactement trois racines reelles, "
            "situees dans ]-2, -1[, ]0, 1[ et ]1, 2[.\n"
        ),
    ],
    "narrative_en": [
        (
            "The lighthouse keeper had not spoken to another soul in forty days "
            "when the boat appeared. It came in low against the swell, its single "
            "sail patched with what looked like flour sacks, and for a long while "
            "he simply watched it through the salt-streaked glass, unsure whether "
            "he wanted it to reach the island or to turn away. Company meant "
            "questions, and questions meant remembering, and he had climbed these "
            "one hundred and twelve steps precisely so that he would never have "
            "to remember again."
        ),
        (
            "By the third week of the drought, the river had shrunk to a bright "
            "thread among the stones, and the children discovered things in the "
            "exposed mud that no one could name. Old Mrs. Ferreira said the "
            "objects were ship nails from the century before, but the schoolmaster "
            "measured them, photographed them, and mailed his notes to the "
            "university, where they sat unopened on a desk through the whole of "
            "August while the town below grew stranger every day."
        ),
        (
            "The chess club met on Thursdays in the basement of the municipal "
            "library, and for eleven years the same eight members had played the "
            "same cautious openings. Then the girl arrived. She was perhaps "
            "twelve, carried her own board under one arm, and defeated the club "
            "champion in nineteen moves while explaining, politely and without "
            "pause, why each of his choices had been the second-best available. "
            "Nobody remembered inviting her, and nobody dared to ask her name."
        ),
        (
            "When the archive finally burned, it was not the fire that people "
            "remembered but the snow of paper that followed: ten thousand "
            "half-charred index cards drifting across the harbor district, "
            "settling on awnings and in coffee cups, each one carrying a "
            "fragment of a life — a date of birth, a debt, a marriage annulled — "
            "so that for one strange morning the whole city read itself, "
            "shivering, in the handwriting of clerks dead for a hundred years."
        ),
    ],
}

DEFAULT_MODEL = "Qwen/Qwen3.5-9B-Base"
DEFAULT_SAE_REPO = "Qwen/SAE-Res-Qwen3.5-9B-Base-W64K-L0_50"


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    p.add_argument("--stage", choices=["smoke", "full"], default="smoke")
    p.add_argument("--variant", choices=["trained", "control"], default="trained",
                   help="control = permutation seedee des lignes d'input embeddings")
    p.add_argument("--layer", type=int, default=16,
                   help="couche du resid_post capture (defaut 16 = mi-reseau, 0-31)")
    p.add_argument("--model", default=DEFAULT_MODEL)
    p.add_argument("--sae-repo", default=DEFAULT_SAE_REPO)
    p.add_argument("--out-dir", default=str(Path(__file__).resolve().parent.parent / "traces"))
    p.add_argument("--seed", type=int, default=42)
    p.add_argument("--clamp-ids", default="",
                   help="ids de features SAE a forcer a zero dans le residual stream "
                        "(Gate 24 #5635, phase 2) — liste separee par des virgules")
    p.add_argument("--attn", default=None,
                   help="attn_implementation a forcer (ex: eager) si le defaut echoue")
    return p.parse_args()


def guard_single_gpu() -> torch.device:
    """Garde-fou HARD : exactement 1 GPU visible (CUDA_VISIBLE_DEVICES=2 sur ai-01)."""
    if not torch.cuda.is_available():
        sys.exit("ERREUR: CUDA indisponible — ce pipeline exige un GPU.")
    n = torch.cuda.device_count()
    if n != 1:
        sys.exit(f"ERREUR: {n} GPUs visibles — lancer avec CUDA_VISIBLE_DEVICES=2 "
                 "(GPU 0-1 = vLLM, interdits).")
    name = torch.cuda.get_device_name(0)
    total = torch.cuda.get_device_properties(0).total_memory / 2**30
    print(f"[gpu] 1 GPU visible : {name} ({total:.1f} GiB)")
    return torch.device("cuda:0")


def find_decoder_layers(model: torch.nn.Module, n_layers_hint: int | None) -> torch.nn.ModuleList:
    """Localise la ModuleList des couches decodeur TEXTE, robuste aux wrappers.

    Qwen3_5ForConditionalGeneration peut imbriquer un language_model ET une tour
    vision (image_token_id present dans la config) : on score les candidates au
    lieu de prendre la plus longue aveuglement."""
    candidates = []
    for name, module in model.named_modules():
        if isinstance(module, torch.nn.ModuleList) and len(module) >= 8:
            cls0 = type(module[0]).__name__
            score = 0
            if "DecoderLayer" in cls0:
                score += 4
            if any(t in name for t in ("language_model", "text_model")):
                score += 2
            if "visual" in name or "vision" in name or "Vision" in cls0:
                score -= 4
            if n_layers_hint and len(module) == n_layers_hint:
                score += 2
            candidates.append((score, len(module), name, module))
    if not candidates:
        sys.exit("ERREUR: impossible de localiser les couches decodeur.")
    score, n, name, layers = max(candidates, key=lambda c: (c[0], c[1]))
    print(f"[model] couches decodeur : '{name}' ({n} couches, "
          f"classe={type(layers[0]).__name__}, score={score})")
    return layers


def load_sae(sae_repo: str, layer: int, device: torch.device):
    """Telecharge et charge le checkpoint SAE de la couche demandee.

    Convention Qwen-Scope (app.py officiel) : dict avec W_enc [d_sae, d_model],
    b_enc [d_sae] (+ W_dec/b_dec pour la reconstruction/le clamp)."""
    from huggingface_hub import hf_hub_download
    path = hf_hub_download(sae_repo, f"layer{layer}.sae.pt")
    sae = torch.load(path, map_location="cpu", weights_only=True)
    print(f"[sae] {sae_repo} layer{layer} — cles : "
          f"{ {k: tuple(v.shape) for k, v in sae.items() if hasattr(v, 'shape')} }")
    w_enc = sae["W_enc"].to(torch.float32)          # [d_sae, d_model]
    b_enc = sae["b_enc"].to(torch.float32)          # [d_sae]
    w_dec = sae.get("W_dec")
    if w_dec is not None:
        w_dec = w_dec.to(torch.float32)
    return {"W_enc": w_enc, "b_enc": b_enc, "W_dec": w_dec, "path": path}


def sae_encode_topk(hidden: torch.Tensor, sae: dict, k: int = 50):
    """Encode top-k fidele a app.py : pre = h @ W_enc.T + b_enc ; relu ; top-k.

    hidden : [T, d_model] float32 (CPU). Retourne (ids [T,k] int32, vals [T,k] float32),
    tries par activation decroissante ; les valeurs nulles marquent un L0 < k."""
    pre = hidden @ sae["W_enc"].T + sae["b_enc"]     # [T, d_sae]
    acts = torch.relu(pre)
    vals, ids = torch.topk(acts, k, dim=-1)
    return ids.to(torch.int32), vals


def apply_control_permutation(model: torch.nn.Module, seed: int) -> None:
    """Modele-controle : permute les lignes de l'input embedding (seedee).

    Detruit l'appariement token->sens en preservant l'architecture entrainee et
    la distribution marginale des embeddings (controle sanctionne par #5101)."""
    emb = model.get_input_embeddings()
    g = torch.Generator(device="cpu").manual_seed(seed)
    perm = torch.randperm(emb.weight.shape[0], generator=g)
    with torch.no_grad():
        emb.weight.copy_(emb.weight[perm.to(emb.weight.device)])
    print(f"[control] input embeddings permutes ({emb.weight.shape[0]} lignes, seed={seed})")


class ResidCapture:
    """Hook forward sur une couche decodeur : capture le resid_post et,
    optionnellement, clampe des features SAE (Gate 24) en soustrayant leur
    contribution decodeur du residual stream."""

    def __init__(self, sae: dict | None = None, clamp_ids: list[int] | None = None):
        self.hidden: torch.Tensor | None = None
        self.clamp_ids = clamp_ids or []
        self.sae = sae
        if self.clamp_ids and (sae is None or sae["W_dec"] is None):
            sys.exit("ERREUR: --clamp-ids exige W_dec dans le checkpoint SAE.")

    def __call__(self, module, inputs, output):
        out = output[0] if isinstance(output, tuple) else output   # [B, T, d]
        self.hidden = out.detach()[0].to(torch.float32).cpu()      # [T, d]
        if not self.clamp_ids:
            return output
        # Clamp causal : h' = h - somme_i acts_i * W_dec[i]  (features forcees a 0)
        h32 = out.detach().to(torch.float32).cpu()                 # [B, T, d]
        w_enc = self.sae["W_enc"][self.clamp_ids]                  # [C, d]
        b_enc = self.sae["b_enc"][self.clamp_ids]                  # [C]
        acts = torch.relu(h32 @ w_enc.T + b_enc)                   # [B, T, C]
        delta = acts @ self.sae["W_dec"][self.clamp_ids]           # [B, T, d]
        h_new = (h32 - delta).to(out.dtype).to(out.device)
        if isinstance(output, tuple):
            return (h_new,) + tuple(output[1:])
        return h_new


def main() -> None:
    args = parse_args()
    t0 = time.time()
    torch.manual_seed(args.seed)
    device = guard_single_gpu()
    clamp_ids = [int(x) for x in args.clamp_ids.split(",") if x.strip()]

    from transformers import AutoConfig, AutoModelForCausalLM, AutoTokenizer

    print(f"[load] {args.model} (bf16, forward-only) ...")
    cfg = AutoConfig.from_pretrained(args.model)
    text_cfg = getattr(cfg, "text_config", cfg)
    n_layers = getattr(text_cfg, "num_hidden_layers", None)
    d_model = getattr(text_cfg, "hidden_size", None)
    print(f"[model] model_type={cfg.model_type} n_layers={n_layers} d_model={d_model}")

    tokenizer = AutoTokenizer.from_pretrained(args.model)
    kwargs: dict = {"dtype": torch.bfloat16}
    if args.attn:
        kwargs["attn_implementation"] = args.attn
    model = AutoModelForCausalLM.from_pretrained(args.model, **kwargs).to(device)
    model.eval()
    print(f"[model] classe={type(model).__name__} "
          f"vram={torch.cuda.memory_allocated() / 2**30:.1f} GiB")

    if args.variant == "control":
        apply_control_permutation(model, args.seed)

    sae = load_sae(args.sae_repo, args.layer, device)
    assert sae["W_enc"].shape[1] == d_model, \
        f"d_model SAE {sae['W_enc'].shape[1]} != modele {d_model}"

    layers = find_decoder_layers(model, n_layers)
    capture = ResidCapture(sae=sae, clamp_ids=clamp_ids)
    handle = layers[args.layer].register_forward_hook(capture)

    sets = PROMPT_SETS
    if args.stage == "smoke":
        sets = {"code_python": PROMPT_SETS["code_python"][:1],
                "prose_fr": PROMPT_SETS["prose_fr"][:1]}

    arrays: dict[str, np.ndarray] = {}
    l0_all, tok_total = [], 0
    for set_name, prompts in sets.items():
        for i, text in enumerate(prompts):
            enc = tokenizer(text, return_tensors="pt").to(device)
            with torch.no_grad():
                model(**enc)
            hidden = capture.hidden                      # [T, d_model] fp32 CPU
            ids, vals = sae_encode_topk(hidden, sae, k=50)
            l0 = (vals > 0).sum(dim=-1).float()
            l0_all.append(l0)
            tok_total += hidden.shape[0]
            key = f"{set_name}__{i}"
            arrays[f"{key}__topk_ids"] = ids.numpy()
            arrays[f"{key}__topk_vals"] = vals.to(torch.float16).numpy()
            toks = tokenizer.convert_ids_to_tokens(enc["input_ids"][0].tolist())
            # dtype unicode fixe (pas object) : le .npz committe se recharge sans
            # allow_pickle=True cote notebooks GPU-free.
            arrays[f"{key}__tokens"] = np.array(toks, dtype=str)
            print(f"[trace] {key}: T={hidden.shape[0]} L0 moy={l0.mean():.1f} "
                  f"act max={vals.max():.2f}")
            if args.stage == "smoke":
                top5 = [(int(a), float(b)) for a, b in zip(ids[-1, :5], vals[-1, :5])]
                print(f"        top-5 features (dernier token) : {top5}")

    handle.remove()

    if args.stage == "smoke" and args.variant == "trained" and not clamp_ids:
        # Sanity semantique : une generation greedy courte attrape un chargement
        # de poids errone (mapping de classe, shards manquants) que les stats
        # d'activation seules ne detecteraient pas.
        probe = tokenizer("La capitale de la France est", return_tensors="pt").to(device)
        with torch.no_grad():
            gen = model.generate(**probe, max_new_tokens=12, do_sample=False)
        print(f"[sanity] greedy: {tokenizer.decode(gen[0], skip_special_tokens=True)!r}")

    l0_cat = torch.cat(l0_all)
    print(f"\n[sanity] {tok_total} tokens, L0 moyen={l0_cat.mean():.2f} "
          f"(attendu ~50), min={l0_cat.min():.0f}, max={l0_cat.max():.0f}")
    print(f"[sanity] vram pic={torch.cuda.max_memory_allocated() / 2**30:.1f} GiB")

    if args.stage == "full":
        out_dir = Path(args.out_dir)
        out_dir.mkdir(parents=True, exist_ok=True)
        suffix = f"_clamp{len(clamp_ids)}" if clamp_ids else ""
        out = out_dir / f"ict21_sae_layer{args.layer}_{args.variant}{suffix}.npz"
        meta = {
            "model": args.model, "sae_repo": args.sae_repo, "layer": args.layer,
            "k": 50, "d_sae": int(sae["W_enc"].shape[0]), "d_model": int(d_model),
            "variant": args.variant, "seed": args.seed, "clamp_ids": clamp_ids,
            "encode_convention": "pre = h @ W_enc.T + b_enc ; relu ; topk(50) "
                                 "(app.py officiel Qwen-Scope, pas de b_dec a l'encode)",
            "control_convention": "permutation seedee des lignes d'input embeddings",
            "prompt_sets": {k: len(v) for k, v in sets.items()},
            "n_tokens_total": tok_total,
            "date": _dt.datetime.now(_dt.timezone.utc).isoformat(timespec="seconds"),
        }
        arrays["__meta__"] = np.array(json.dumps(meta, ensure_ascii=False))
        np.savez_compressed(out, **arrays)
        print(f"[out] {out} ({out.stat().st_size / 2**20:.2f} MiB)")

    print(f"[done] stage={args.stage} variant={args.variant} "
          f"en {time.time() - t0:.0f}s")


if __name__ == "__main__":
    main()
