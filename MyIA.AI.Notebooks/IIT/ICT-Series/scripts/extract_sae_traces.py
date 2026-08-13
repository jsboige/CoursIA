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

Deux echelles (#5105 / #7396) : le couple de reference est 9B-Base x W64K, mais
l'arc post-training PT-12 lit aussi Qwen3.5-2B(-Base) x W32K. Les deux profondeurs
different (32 vs 24 couches), donc `--layer 16` ne designe PAS la meme position
relative : passer `--layer-frac 0.5` pour une intention transposable. Les gardes
correspondantes vivent dans `ict/sae_traces.py` (pures, testables sans GPU) et
sont appliquees ici AVANT tout chargement de poids.

Deux largeurs SAE par modele cible (#10289 etape 2) : le meme depot
`Qwen/SAE-Res-Qwen3.5-2B-Base-W32K` est publie en deux versions, `L0_50` et
`L0_100`, qui different par le top-k d'encodage (50 vs 100). Le k est lu
depuis le `config.json` du depot ; `--k` explicite DOIT y correspondre, la
garde `assert_sae_topk_compatible` refuse tout desaccord (un `topk(50)`
sur un SAE `L0_100` produirait une mesure a moitie de la release
officielle, silencieusement).

Usage (GPU 2 d'ai-01 STRICT — vLLM tient GPU 0-1) :
    CUDA_VISIBLE_DEVICES=2 PYTORCH_CUDA_ALLOC_CONF=expandable_segments:True \
      python extract_sae_traces.py --stage smoke
    ... --stage full --variant trained
    ... --stage full --variant control
    # echelle 2B, mi-reseau, SAE L0_50 (defaut auto-detecte depuis config.json) :
    ... --model Qwen/Qwen3.5-2B-Base --layer-frac 0.5 \
        --sae-repo Qwen/SAE-Res-Qwen3.5-2B-Base-W32K-L0_50 --stage full
    # echelle 2B, SAE L0_100 (meme modele, top-k=100 detecte auto) :
    ... --model Qwen/Qwen3.5-2B-Base --layer-frac 0.5 \
        --sae-repo Qwen/SAE-Res-Qwen3.5-2B-Base-W32K-L0_100 --stage full
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

# Le package ``ict/`` reste numpy-only : l'importer ici ne fait PAS entrer torch
# dans la bibliotheque — c'est ce script qui confine torch (cf docstring). Les
# garde-fous cross-echelle vivent la-bas precisement pour etre testables sans GPU.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from ict.sae_traces import (  # noqa: E402  (necessairement apres sys.path)
    assert_bf16_readout,
    assert_sae_topk_compatible,
    check_sae_model_match,
    resolve_capture_layer,
    trace_filename,
)

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
DEFAULT_LAYER = 16


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    p.add_argument("--stage", choices=["smoke", "full"], default="smoke")
    p.add_argument("--variant", choices=["trained", "control"], default="trained",
                   help="control = permutation seedee des lignes d'input embeddings")
    # --layer et --layer-frac s'excluent : passer les deux serait une intention
    # ambigue, et la resolution vit dans ict.sae_traces.resolve_capture_layer
    # (qui refuse aussi le cas, pour l'appel bibliotheque hors CLI).
    depth = p.add_mutually_exclusive_group()
    depth.add_argument("--layer", type=int, default=None,
                      help=f"index absolu du resid_post capture (defaut "
                           f"{DEFAULT_LAYER}, valide pour un modele 32 couches). "
                           "Un index n'est PAS comparable d'une echelle a "
                           "l'autre : preferer --layer-frac pour un modele "
                           "d'une autre profondeur.")
    depth.add_argument("--layer-frac", type=float, default=None,
                      help="profondeur RELATIVE dans [0, 1] (0.5 = mi-reseau). "
                           "Transposable entre echelles : 0.5 donne 16 sur un "
                           "32 couches, 12 sur un 24 couches.")
    p.add_argument("--model", default=DEFAULT_MODEL)
    p.add_argument("--sae-repo", default=DEFAULT_SAE_REPO)
    p.add_argument("--out-dir", default=str(Path(__file__).resolve().parent.parent / "traces"))
    p.add_argument("--seed", type=int, default=42)
    p.add_argument("--clamp-ids", default="",
                   help="ids de features SAE a forcer a zero dans le residual stream "
                        "(Gate 24 #5635, phase 2) — liste separee par des virgules")
    p.add_argument("--attn", default=None,
                   help="attn_implementation a forcer (ex: eager) si le defaut echoue")
    p.add_argument("--allow-quantized-readout", action="store_true",
                   help="autorise la lecture SAE d'un checkpoint quantifie. Par "
                        "defaut refusee : les SAE sont entraines sur le residual "
                        "stream pleine precision, donc un differentiel mesure en "
                        "4-bit melangerait l'effet cherche et l'arrondi NF4.")
    p.add_argument("--k", type=int, default=None,
                   help="top-k d'encodage SAE. Si omis, lu depuis "
                        "config.json du depot --sae-repo (defaut officiel : "
                        "50 pour L0_50, 100 pour L0_100). Doit correspondre "
                        "au k officiel — la garde assert_sae_topk_compatible "
                        "refuse tout desaccord sans --allow-k-override.")
    p.add_argument("--allow-k-override", action="store_true",
                   help="autorise --k a desobeir au k officiel du SAE. "
                        "INTERDIT en pratique : un top-k explicite inferieur "
                        "tronque silencieusement un L0_100, le resultat n'est "
                        "plus comparable a la release officielle. Reserve a "
                        "l'exploration assumee et documentee.")
    p.add_argument("--overwrite", action="store_true",
                   help="autorise l'ecrasement d'une trace existante (refuse par defaut)")
    return p.parse_args()


def _guard(fn, *a, **kw):
    """Traduit une ``ValueError`` de garde-fou en sortie CLI actionnable.

    Les garde-fous d':mod:`ict.sae_traces` levent des exceptions (testables,
    reutilisables hors CLI) ; en ligne de commande, une trace Python nue est un
    mauvais message d'erreur. Ce wrapper garde les deux usages.
    """
    try:
        return fn(*a, **kw)
    except ValueError as exc:
        sys.exit(f"ERREUR: {exc}")


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


def fetch_sae_config(sae_repo: str) -> dict:
    """Telcharge le ``config.json`` du depot SAE et rend ses champs-cles.

    Le depot Qwen-Scope publie un ``config.json`` a la racine (cf ``app.py``
    officiel) avec au moins ``d_model``, ``d_sae``, ``k``, ``num_layers``,
    ``hook_point``. On isole ces quatre champs-ci : le script d'extraction
    n'en a besoin que pour verifier la compatibilite top-k (ce depot =
    L0_50 ou L0_100 ?) et le d_model (deja couvert par
    :func:`ict.sae_traces.check_sae_model_match`, mais ici on en a besoin
    avant le telechargement du ``layer{L}.sae.pt``).

    Echec reseau : la garde ``assert_sae_topk_compatible`` devient
    inapplicable, donc on le dit a l'appelant plutot que de deriver en
    silence sur un defaut hardcode (k=50) — c'est precisement le defaut
    silencieux que la garde ferme.
    """
    from huggingface_hub import hf_hub_download
    try:
        cfg_path = hf_hub_download(sae_repo, "config.json")
    except Exception as exc:
        raise FileNotFoundError(
            f"impossible de telecharger config.json du depot SAE {sae_repo!r} : "
            f"{exc}. La detection automatique du k officiel necessite ce "
            f"fichier ; sans lui, --k doit etre passe en CLI explicitement "
            f"et --allow-k-override active (cf etape 2 PT-12, #10289)."
        ) from exc
    with open(cfg_path) as f:
        cfg = json.load(f)
    return {
        "d_model": int(cfg["d_model"]),
        "d_sae": int(cfg["d_sae"]),
        "k": int(cfg.get("k", cfg.get("top_k", 50))),
        "num_layers": int(cfg.get("num_layers", cfg.get("n_layers", 0))),
    }


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

    ``k`` est explicite : la valeur par defaut (50) reflete le depot de
    reference ``W64K-L0_50``, mais un appelant qui passe un SAE
    ``W32K-L0_100`` DOIT specifier ``k=100`` — la garde
    :func:`ict.sae_traces.assert_sae_topk_compatible` refuse le
    desaccord avant d'arriver ici.
    """
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

    print(f"[load] config {args.model} ...")
    cfg = AutoConfig.from_pretrained(args.model)
    text_cfg = getattr(cfg, "text_config", cfg)
    n_layers = getattr(text_cfg, "num_hidden_layers", None)
    d_model = getattr(text_cfg, "hidden_size", None)
    print(f"[model] model_type={cfg.model_type} n_layers={n_layers} d_model={d_model}")

    # --- Gardes cross-echelle, AVANT tout chargement de poids -------------- #
    # Toutes echouent sur la seule config (quelques Ko) : un mauvais couple
    # couche/echelle, un checkpoint quantifie ou une trace deja presente sont
    # detectes en secondes, pas apres 20 GiB de poids et une passe complete.
    depth = _guard(resolve_capture_layer, n_layers, args.layer, args.layer_frac) \
        if (args.layer is not None or args.layer_frac is not None) \
        else _guard(resolve_capture_layer, n_layers, DEFAULT_LAYER, None)
    layer = depth["layer"]
    print(f"[depth] couche {layer}/{n_layers - 1} "
          f"(profondeur relative {depth['layer_frac']:.3f})")

    _guard(assert_bf16_readout,
           getattr(cfg, "quantization_config", None),
           args.allow_quantized_readout)

    # --- Garde cross-L0 (L0_50 vs L0_100) : le k encode DOIT etre le k ---- #
    # officiel du SAE. Defaut silencieux ferme ici, cf etape 2 PT-12 #10289.
    # On recupere le k officiel via config.json (qq Ko) avant tout chargement
    # de poids — un refus ici ne coute rien.
    sae_cfg = _guard(fetch_sae_config, args.sae_repo)
    k_official = int(sae_cfg["k"])
    if args.k is None:
        k = k_official
        print(f"[k] auto-detecte depuis {args.sae_repo} : k={k}")
    else:
        k = int(args.k)
        if not args.allow_k_override:
            _guard(assert_sae_topk_compatible, k_official, k)
            print(f"[k] explicite {k} = officiel {args.sae_repo} : OK")
        else:
            print(f"[k] OVERRIDE explicite {k} != officiel {k_official} : "
                  f"sortie non comparable a la release officielle")

    out_path: Path | None = None
    if args.stage == "full":
        out_dir = Path(args.out_dir)
        out_dir.mkdir(parents=True, exist_ok=True)
        out_path = out_dir / trace_filename(
            args.variant, layer, model=args.model, default_model=DEFAULT_MODEL,
            n_layers=n_layers, n_clamp=len(clamp_ids))
        if out_path.exists() and not args.overwrite:
            sys.exit(f"ERREUR: {out_path} existe deja. Deux runs d'echelles "
                     "differentes ne doivent jamais partager un nom : verifier "
                     "que --model/--layer sont ceux voulus, puis --overwrite "
                     "pour ecraser deliberement.")
        print(f"[out] cible {out_path.name}")

    print(f"[load] {args.model} (bf16, forward-only) ...")
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

    sae = load_sae(args.sae_repo, layer, device)
    # Remplace un ``assert`` nu : il disparaissait sous ``python -O`` et son
    # message ne disait pas quoi apparier.
    _guard(check_sae_model_match, int(sae["W_enc"].shape[1]), int(d_model),
           args.sae_repo, args.model)

    layers = find_decoder_layers(model, n_layers)
    capture = ResidCapture(sae=sae, clamp_ids=clamp_ids)
    handle = layers[layer].register_forward_hook(capture)

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
            ids, vals = sae_encode_topk(hidden, sae, k=k)
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
          f"(attendu ~{k}), min={l0_cat.min():.0f}, max={l0_cat.max():.0f}")
    print(f"[sanity] vram pic={torch.cuda.max_memory_allocated() / 2**30:.1f} GiB")

    if args.stage == "full":
        out = out_path                       # resolu et verifie avant le chargement
        meta = {
            "model": args.model, "sae_repo": args.sae_repo, "layer": layer,
            # Profondeur RELATIVE : c'est elle, pas l'index absolu, qui rend deux
            # traces d'echelles differentes comparables (#5105 / #7396).
            "n_layers": int(n_layers), "layer_frac": depth["layer_frac"],
            # d_sae EST la largeur du SAE (65536 pour W64K, 32768 pour W32K) :
            # pas de second champ synonyme, qui divergerait un jour. k EST le
            # top-k d'encodage (50 ou 100) capture ici, PAS recalcule a la lecture.
            "k": int(k), "k_official": int(k_official),
            "d_sae": int(sae["W_enc"].shape[0]), "d_model": int(d_model),
            "quantized_readout": bool(args.allow_quantized_readout),
            "variant": args.variant, "seed": args.seed, "clamp_ids": clamp_ids,
            "encode_convention": f"pre = h @ W_enc.T + b_enc ; relu ; topk({k}) "
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
