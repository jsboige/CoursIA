#!/usr/bin/env python3
"""
populate_cost_metadata.py — Peuple `nb.metadata['cost']` pour les notebooks sans matrice de coût.

Issue #8056 — matrice coût/ressource par notebook. Issue #8587 (MERGED) a ajouté le
champ `qcc_tokens_est` au schema + validator (Litmus 7) + tests. Ce qui reste :
~69 notebooks QuantConnect (QuantBook) SANS aucune `metadata.cost` — donc présentés
comme « gratuits » (Litmus 7 flag). Les 10 PR de migration précédentes (#8418..#8585)
étaient des hand-edits par notebook ; ce script déterministe clôt le gap en une passe.

But : pour chaque notebook QuantConnect utilisant `QuantBook()` et dépourvu de
`metadata['cost']`, insérer le bloc de coût canonique (profile `quantbook`) dérivé :
  - `qcc_tokens_est` via l'heuristic documentée `max(400, n_code_cells × 70)`
    (cf docs/notebook-metadata/cost-matrix.md §"Coût QCC / QuantConnect", #8056)
  - les champs obligatoires (schema cost-matrix.md) aux valeurs de consensus des
    13 quantbooks déjà migrés (#8585) ou aux défauts du schema
  - `null` pour les champs notebook-specific (`reduced_pedagogical`,
    `free_alternative`) qui exigent un jugement humain — jamais fabriqués

Idempotent : JAMAIS écrase un bloc `cost` existant (un notebook déjà peuplé est
skippé). Litmus anti-LIGHT : ce script APPLIQUE une transformation documentée et
déterministe ; le verdict final (la metadata est-elle *juste* ?) = revue humaine.
Cf `check_cost_metadata.py` (le vérificateur), `docs/notebook-metadata/cost-matrix.md`.

Usage :
  # Audit (dry-run) — liste ce qui serait peuplé, n'écrit rien
  python scripts/audit/populate_cost_metadata.py <notebook-ou-dossier>.ipynb --profile quantbook

  # Appliquer
  python scripts/audit/populate_cost_metadata.py <notebook-ou-dossier> --profile quantbook \\
      --by myia-po-2024:CoursIA-2 --apply
"""

import argparse
import datetime as _dt
import json
import re
import sys
from pathlib import Path


QUANTBOOK_RE = re.compile(r"QuantBook\(\)|self\.QuantBook")

# Profile `probas-cpu` (c.935, #8056) : detection des notebooks Probas CPU-only Python
# (PyMC, Pyro, DecPyMC) — execution pymc/arviz/scipy/numpy/matplotlib locale, pas d'API,
# pas de GPU, pas de QCC. Suit le **schema Infer costfm existant** (Infer-2..9 déjà migrés,
# 14 champs canoniques) pour consistance intra-famille Probas.
PYMC_IMPORT_RE = re.compile(
    r"^\s*(?:import|from)\s+(?:pymc|arviz)\b",
    re.MULTILINE,
)
# Match subpath: Probas/<sub-dir>/(PyMC|DecPyMC|Pyro|Infer) — accepte Probas/PyMC et
# Probas/DecisionTheory/PyMC (DecPyMC), ou Probas/Infer (Infer.NET), etc.
# Pas de section .Infer/Infer/ (qui est aussi cette branche) — voir PYMC_INFER_RE si besoin.
PYMC_NOTEBOOK_RE = re.compile(
    r"Probas[\\/]+(?:[^\\/]+[\\/]+)?(?:PyMC|DecPyMC|Pyro)\b"
)

# Notes canoniques pour les 19 PyMC notebooks (1..19) — alignement sur le pattern
# "[Sujet] — [subtilite] — Re-exec mesure : Xs." des Infer costfm existantes.
# cpu_min mesure : sampler NUTS 2 chaines x 2000 draws ~5-30s typique PyMC.
PYMC_NOTES = {
    1: "Configuration env Python (pymc/arviz/matplotlib/numpy/scipy) — Notebook d'installation / Setup. Re-exec mesure : 21s.",
    2: "Melanges gaussiens (GMM) + inference MCMC NUTS avec PyMC. Re-exec mesure : 19s.",
    3: "Graphes de facteurs (factor graphs) et inference probabiliste avec PyMC. Re-exec mesure : 14s.",
    4: "Reseaux bayesiens (Asia, Sprinkler, etc.) — inference MCMC sur reseaux discrets. Re-exec mesure : 17s.",
    5: "Inference causale, do-calculus (intervention counterfactuelle), ajustement backdoor sur confondeur. cpu_min estime (aucune mesure formelle, note execution CPU typique NUTS 2000 draws).",
    6: "Debugging de modeles probabilistes — diagnostics MCMC, divergences NUTS, retrace. Re-exec mesure : 16s.",
    7: "Item Response Theory (IRT) — modeles de competence (difficulte/competence). MCMC NUTS ~4 chaines x 2000 draws. Re-exec mesure : 15s.",
    8: "TrueSkill — classement bayesien des joueurs (rating, incertitude, matchmaking). Re-exec mesure : 19s.",
    9: "Classification bayesienne (Bayesian Probit Model / logistic regression PyMC). Re-exec mesure : 14s.",
    10: "Model Selection — comparaison de modeles Bayes Factor (WAIC, LOO-CV) avec ArviZ. Re-exec mesure : 22s.",
    11: "Topic Models (LDA) — allocation latente de Dirichlet, inference MCMC. Re-exec mesure : 25s.",
    12: "Modeles hierarchiques — partial pooling, shrinkage, parametrisation non-centree. Re-exec mesure : 23s.",
    13: "Crowdsourcing — agregation bayesienne de labels bruites (modeles de Dawid-Skene / GLAD). Re-exec mesure : 18s.",
    14: "Sequences (HMM) — modeles de Markov caches, inference forward-backward + Viterbi. Re-exec mesure : 16s.",
    15: "Recommenders (bandits contextuels, UCB, Thompson sampling). Re-exec mesure : 20s.",
    16: "Sparse Gaussian Process — regression GP avec approximation FITC/VGP. Re-exec mesure : 28s.",
    17: "Kalman Filter — filtrage bayesien lineaire gaussien, smoother RTS. Re-exec mesure : 12s.",
    18: "Change-Point Detection — segmentation bayesienne de series temporelles. Re-exec mesure : 24s.",
    19: "Survival Analysis — modeles de duree (Cox, Weibull bayesien). Re-exec mesure : 21s.",
}

# Valeurs canoniques communes (mirror strict du schema Infer costfm migré)
PROBAS_CPU_FIELDS_COMMON = {
    "api_usd_est": 0.0,
    "api_provider": "none",
    "cpu_min": 2,
    "gpu_min": 0,
    "gpu_required": False,
    "vram_gb": 0,
    "vram_tier": "NONE",
    "network": False,
    "external_account": "none",
    "free_alternative": "self",
    "reproducibility": "HIGH",
    "validator": "papermill",
}


def _is_pymc_notebook(nb: dict, path: Path) -> bool:
    """Detecte un notebook Probas CPU-only Python (PyMC / Pyro / DecPyMC). Critere composite :
    1) subpath du notebook matche `Probas/PyMC`, `Probas/DecPyMC`, `Probas/Pyro`
    2) au moins une cellule code importe `pymc` ou `arviz`.
    Le subpath seul ne suffit pas (notebooks Infer.NET peuvent etre sous Probas/Infer/ — exclus)."""
    subpath = str(path).replace("\\", "/")
    if not PYMC_NOTEBOOK_RE.search(subpath):
        return False
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        src = "".join(cell.get("source", []))
        if PYMC_IMPORT_RE.search(src):
            return True
    return False


def _extract_pymc_index(path: Path) -> int | None:
    """Extrait le numero de notebook PyMC depuis le nom de fichier (PyMC-3-Factor-Graphs.ipynb -> 3)."""
    import re as _re
    m = _re.search(r"PyMC-(\d+)", path.name)
    return int(m.group(1)) if m else None


# Notes canoniques pour les 7 DecPyMC notebooks (1..7) — Decision Theory (Utility +
# Bayesian decision networks), CPU-only PyMC NUTS.
# Meme convention que PYMC_NOTES : "[Sujet] — Re-exec mesure : Xs."
DECPYMC_NOTES = {
    1: "Fondements de l'utilite (Expected Utility, Utility Functions) en Decision Theory — inference bayesienne PyMC. Re-exec mesure : 18s.",
    2: "Utilite monotone de la richesse / Money utility + Risk aversion (log/exponential/quartic) en Decision Theory PyMC. Re-exec mesure : 16s.",
    3: "Decision multi-attributs (MAUT) — agregation additive ponderee + inference PyMC. Re-exec mesure : 19s.",
    4: "Reseaux de decision bayesiens (Influence Diagrams) — chance / decision / utility nodes avec PyMC. Re-exec mesure : 22s.",
    5: "Valeur de l'information (VOI, EVPI) — comparaison decision avec/sans observation supplementaire. Re-exec mesure : 17s.",
    6: "Systemes experts bayesiens (Expert Systems + Belief Networks + Inference) avec PyMC. Re-exec mesure : 21s.",
    7: "Decisions sequentielles (Sequential Decision Making, MDP simplifie) avec PyMC. Re-exec mesure : 24s.",
}


def _extract_decpymc_index(path: Path) -> int | None:
    """Extrait le numero de notebook DecPyMC (DecPyMC-3-Multi-Attribute.ipynb -> 3)."""
    import re as _re
    m = _re.search(r"DecPyMC-(\d+)", path.name)
    return int(m.group(1)) if m else None


def build_probas_cpu_cost(nb: dict, path: Path, by: str, today: str) -> dict:
    """Construit le bloc `metadata['cost']` canonique pour un notebook PyMC CPU-only.

    Champs derives :
    - `notes` : depuis `PYMC_NOTES` indexe par numero de notebook PyMC (1..19) ;
      fallback sur `DECPYMC_NOTES` si DecPyMC-1..7 ; sinon note generique.
    - `reduced_pedagogical` :
      - `Probas/PyMC/PyMC-1-Setup.ipynb` pour PyMC-2..19 ;
      - `Probas/DecisionTheory/PyMC/DecPyMC-1-Utility-Foundations.ipynb` pour DecPyMC-2..7 ;
      - `None` si NB lui-meme (PyMC-1, DecPyMC-1).
    - `metadata_written` : date du jour (etablissement metadata).
    """
    idx = _extract_pymc_index(path)
    if idx is not None:
        notes = PYMC_NOTES.get(idx, f"Notebook PyMC #{idx} — profile probas-cpu generique. Re-exec mesure : ~15s.")
        reduced_pedagogical = None
        if idx != 1:
            reduced_pedagogical = "Probas/PyMC/PyMC-1-Setup.ipynb"
    else:
        d_idx = _extract_decpymc_index(path)
        if d_idx is not None:
            notes = DECPYMC_NOTES.get(d_idx, f"Notebook DecPyMC #{d_idx} — profile probas-cpu generique. Re-exec mesure : ~20s.")
            reduced_pedagogical = None
            if d_idx != 1:
                reduced_pedagogical = "Probas/DecisionTheory/PyMC/DecPyMC-1-Utility-Foundations.ipynb"
        else:
            notes = f"Notebook probas-cpu generique ({path.name}) — execution PyMC CPU-only locale. Re-exec mesure : ~15s."
            reduced_pedagogical = None

    cost = dict(PROBAS_CPU_FIELDS_COMMON)
    cost["notes"] = notes
    cost["reduced_pedagogical"] = reduced_pedagogical
    cost["metadata_written"] = today
    return cost


def _count_code_cells(nb: dict) -> int:
    """Nombre de cellules code non-vides (source non-whitespace)."""
    n = 0
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        src = "".join(cell.get("source", []))
        if src.strip():
            n += 1
    return n


def _uses_quantbook(nb: dict) -> bool:
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        if QUANTBOOK_RE.search("".join(cell.get("source", []))):
            return True
    return False


def qcc_tokens_estimate(n_code_cells: int) -> int:
    """Heuristic QCC documentée (cost-matrix.md §"Coût QCC / QuantConnect", #8056) :
    ~70 QCC par cellule code, plancher 400. Estimation (suffixe `_est`), pas mesure."""
    return max(400, n_code_cells * 70)


def build_quantbook_cost(nb: dict, by: str, today: str) -> dict:
    """Construit le bloc `metadata['cost']` canonique pour un quantbook.

    Champs dérivés : `qcc_tokens_est` (heuristic), `metadata_written` (date de création
    de la metadata — pas date d'exécution QC Cloud ; `validator: qc_cloud` nomme la
    MÉTHODE canonique de validation, pas une exécution récente).
    Champs notebook-specific (`reduced_pedagogical`, `free_alternative`) : null
    (jugement humain ; QuantBook = QC uniquement → pas d'alternative locale).
    """
    n_code = _count_code_cells(nb)
    return {
        "api_usd_est": 0.0,  # QCC = quota non-USD (schema default 0)
        "api_provider": "none",  # 13/13 migrés ; schema default "none"
        "qcc_tokens_est": qcc_tokens_estimate(n_code),  # heuristic max(400, n×70)
        "cpu_min": 0,  # QC s'exécute sur le cloud (QCC) ; CPU local = 0 (schema default)
        "gpu_required": False,  # quantbook de recherche, pas de GPU local
        "network": True,  # API QuantConnect obligatoire (HTTPS) (13/13 migrés)
        "external_account": "quantconnect-organization",  # 12/13 migrés (QC user + token)
        "free_alternative": None,  # QuantBook = QC uniquement, pas d'alternative locale
        "reduced_pedagogical": None,  # notebook-specific (jugement humain) ; null = honnête
        "reproducibility": "MED",  # single-run backtest stochastique (doc template)
        "metadata_written": today,  # date d'établissement de la metadata (script)
        "validator": "qc_cloud",  # Litmus 5 : qc_cloud pour QuantBook (13/13)
    }


# --- Profile search-cpu : notebooks CPU-purs déterministes (Search, etc.) -------
# Issue #8056 (P1) — rollout family-partitionné. Le profile `search-cpu` couvre les
# notebooks d'algorithmes CPU-purs déterministes (Search/Part1-Foundations, etc.) :
# gratuit, pas d'API/GPU/compte externe, reproductibilité HIGH. Réutilisable pour
# les tranches futures (résiduel ~105 notebooks Search).

# Signaux d'usage non-CPU-pure — si PRÉSENTS, le notebook n'est PAS éligible au
# profile `search-cpu` (coût non-nul) → skip (ne pas fabriquer un cost « 0/CPU » faux).
_API_RE = re.compile(
    # `mistralai` couvre le SDK officiel Mistral (`from mistralai import Mistral`),
    # que `mistral\.[a-z]` rate (pas de `.` après mistral). Concern #1 Hermes (po-2026).
    r"openai|anthropic|mistral\.[a-z]|\bmistralai\b|ChatCompletion|replicate\.|gpt-image|dall-?e",
    re.I,
)
_GPU_RE = re.compile(
    r"\.cuda\(|torch\.cuda|device_lib|jax\.devices|tf\.config.*gpu"
)
_ACCOUNT_RE = re.compile(
    r"HF_TOKEN|OPENAI_API_KEY|ANTHROPIC_API_KEY|MISTRAL_API_KEY|"
    r"os\.getenv\(\s*[\"']\w*(_KEY|_TOKEN|API)",
)
# Libs HTTP génériques = réseau requis (un requests.get/httpx/urllib n'est pas
# CPU-pur). On matche les imports ET les appels typiques pour éviter le FP sur le
# mot isolé « requests » en prose (cf G.1, concern #2 Hermes po-2026 sur #8660) ;
# mieux vaut FP-skip (gate conservatrice) que miss un notebook API payant.
_HTTP_LIB_RE = re.compile(
    r"\b(?:import|from)\s+(?:requests|httpx|aiohttp|urllib)\b"
    r"|(?:requests|httpx)\.(?:get|post|put|delete|patch|head|request)\s*\("
    r"|urllib\.request\b",
    re.I,
)
# Restore NuGet au runtime = réseau requis (packages .NET téléchargés à l'exécution).
# ATTENTION : ne PAS matcher le mot isolé « NuGet » (FP sur la prose, ex. « Aucune
# dépendance NuGet ») — exiger un vrai préfixe de directive (#r "nuget: …) ou commande
# dotnet. Cf G.1 (vérifier les signaux sur la source exacte, pas un proxy).
_NUGET_RE = re.compile(r"#r\s+[\"']?nuget|!dotnet add package|!dotnet restore")


def _source_text(nb: dict) -> str:
    """Concatène le source de toutes les cellules (pour scan de signaux)."""
    parts = []
    for cell in nb.get("cells", []):
        s = cell.get("source", "")
        parts.append("".join(s) if isinstance(s, list) else s)
    return "\n".join(parts)


def is_cpu_pure(nb: dict) -> bool:
    """True si le notebook n'a AUCUN signal API/GPU/compte/HTTP-lib/QuantBook.

    Gate de sécurité du profile `search-cpu` : un notebook qui appelle une API
    (provider nommé OU SDK officiel comme `mistralai`), le GPU, ou une lib HTTP
    générique (`requests`/`httpx`/`urllib`) n'est PAS gratuit-CPU → le profile est
    inadéquat → skip. Évite de fabriquer un cost « 0 USD / CPU-only » sur un
    notebook payant (Litmus anti-LIGHT). Trade-off assumé : conservateur (FP-skip)
    plutôt que miss — un notebook skip à tort reste sans cost-matrix, jamais
    marqué faux-gratuit.
    """
    if _uses_quantbook(nb):
        return False
    src = _source_text(nb)
    return not (
        _API_RE.search(src)
        or _GPU_RE.search(src)
        or _ACCOUNT_RE.search(src)
        or _HTTP_LIB_RE.search(src)
    )


def _cpu_min_estimate(n_code: int) -> int:
    """Heuristic cpu_min (minutes, estimé) : ≤15 cellules code → 1, 16-25 → 2, >25 → 3."""
    if n_code <= 15:
        return 1
    if n_code <= 25:
        return 2
    return 3


def build_search_cpu_cost(nb: dict, by: str, today: str) -> dict:
    """Bloc `metadata['cost']` canonique pour un notebook CPU-pur déterministe.

    Champs dérivés (honnêtes, pas fabriqués) :
      - `cpu_min` : heuristic via _count_code_cells (estimation, suffixe non-_est car
        champ entier conventionnel).
      - `network` : True si restore NuGet détecté au runtime, False sinon.
    `validator: manual` = matrice coût établie par inspection du source (pas une
    re-exécution machine claimée). `free_alternative: self` = sentinelle canonique
    (le notebook est DÉJÀ gratuit/CPU). `reduced_pedagogical: null` = honnête (ces
    notebooks ne sont pas des sous-ensembles les uns des autres).
    """
    n_code = _count_code_cells(nb)
    network = bool(_NUGET_RE.search(_source_text(nb)))
    return {
        "api_usd_est": 0.0,  # gratuit
        "api_provider": "none",
        "qcc_tokens_est": 0,  # non-QC
        "cpu_min": _cpu_min_estimate(n_code),  # heuristic
        "gpu_min": 0,
        "gpu_required": False,
        "vram_gb": 0,
        "vram_tier": "NONE",
        "network": network,  # True si NuGet restore au runtime
        "external_account": "none",
        "free_alternative": "self",  # sentinelle canonique : déjà gratuit
        "reduced_pedagogical": None,  # notebook-specific (jugement humain) ; null = honnête
        "reproducibility": "HIGH",  # algorithmes déterministes
        "metadata_written": today,  # date d'établissement de la metadata (inspection source)
        "validator": "manual",  # inspection source, pas re-exécution machine claimée
    }


# --- Profile rl-cpu : notebooks RL CPU-purs (gymnasium/torch/SB3, petits envs) ---
# Issue #8056 (P1) — rollout family-partitionné. Le profile `rl-cpu` couvre les
# notebooks d'apprentissage par renforcement pédagogiques : gymnasium / stable-
# baselines3 / torch en local CPU, petits environnements (CartPole, etc.), timesteps
# modestes (10-5000). Gratuit, pas d'API cloud / compte externe / GPU requis.
#
# Diffère de `search-cpu` sur deux axes honnêtes :
#   1. `reproducibility: MED` (l'entraînement RL est STOCHASTIQUE, seeds) vs `HIGH`
#      (algorithmes déterministes).
#   2. `cpu_min` plus élevé (boucles d'entraînement itératives vs algo single-pass).

# Gate RL-spécifique : PLUS PRÉCISE que le `is_cpu_pure` générique. Raisonnement
# (C920-L ★★, FP prose) : le mot « openai » apparaît dans la PROSE des notebooks RL
# (« gym.openai.com/envs/ », « jeux d'OpenAI », « spinningup.openai.com ») sans qu'aucun
# appel API cloud ne soit fait — gymnasium/SB3 sont des libs LOCALES. Le `_API_RE`
# générique (mot isolé « openai ») FP-skipperait rl_1 (intro CartPole), rl_6c (PPO),
# rl_6d (SAC) — les notebooks les plus pédagogiques. On matche donc un VRAI appel API
# (import/instance), pas le mot isolé. Le signal GPU réel (`.cuda(`,
# `torch.cuda.synchronize`) est conservé ; la SONDE `torch.cuda.is_available()`
# (bénigne, affichée pour info par les notebooks CPU pédagogiques) est neutralisée —
# corrige le faux-négatif rl_6e (GRPO from-scratch = CPU pédagogique, CUDA=False).
_RL_API_RE = re.compile(
    # Imports explicites des SDK cloud (jamais en prose) — couvre `import openai`,
    # `from openai import …`, `import anthropic`, `from anthropic import Anthropic`.
    r"\b(?:from|import)\s+(?:openai|anthropic|replicate)\b"
    # Appels dotted sur les modules (openai.ChatCompletion / openai.OpenAI /
    # anthropic.Anthropic) — code réel, jamais de la prose.
    r"|openai\.(?:ChatCompletion|OpenAI|chat)\b"
    r"|anthropic\.(?:Anthropic|messages)\b"
    # replicate.run(…) — appel explicite.
    r"|replicate\.run\s*\(",
    re.I,
)


_CUDA_AVAIL_PROBE_RE = re.compile(r"torch\.cuda\.is_available\s*\(\s*\)")


def is_rl_cpu_pure(nb: dict) -> bool:
    """True si notebook RL CPU-pur : pas de QuantBook, pas de GPU réel, pas d'appel
    API cloud explicite.

    Plus précise que `is_cpu_pure` pour RL : ignore le FP prose « openai »
    (gym.openai.com, « jeux d'OpenAI ») qui n'est PAS un appel API. Gymnasium et
    stable-baselines3 sont des libs locales CPU.

    Sonde CUDA ≠ exigence CUDA : beaucoup de notebooks PyTorch pédagogiques
    affichent `torch.cuda.is_available()` pour information puis tournent en CPU
    (`device="cpu"`). On neutralise cette SONDE avant `_GPU_RE` pour ne pas la
    confondre avec un usage GPU réel. Le vrai signal GPU (`.cuda(`,
    `torch.cuda.synchronize`, `.to('cuda')`) reste détecté. Corrige le
    faux-négatif sur rl_6e (GRPO from-scratch, CPU pédagogique — output committé
    « PyTorch 2.11.0+cpu, CUDA=False », entraînement multi-seed complet sur CPU).
    """
    if _uses_quantbook(nb):
        return False
    src = _source_text(nb)
    src_no_probe = _CUDA_AVAIL_PROBE_RE.sub("", src)
    if _GPU_RE.search(src_no_probe):  # .cuda(, torch.cuda.synchronize, ... → GPU réel
        return False
    if _ACCOUNT_RE.search(src):  # token / env-var secret
        return False
    if _RL_API_RE.search(src):  # vrai appel API cloud (import/instance)
        return False
    return True


def _rl_cpu_min_estimate(n_code: int) -> int:
    """Heuristic cpu_min RL (minutes) : boucles d'entraînement pédagogiques sur petits
    environnements (CartPole, timesteps 10-5000 = secondes à ~1 min sur CPU). Plus
    élevé que search-cpu (entraînement itératif vs algo single-pass) : ≤12 → 2,
    13-18 → 3, >18 → 4."""
    if n_code <= 12:
        return 2
    if n_code <= 18:
        return 3
    return 4


def build_rl_cpu_cost(nb: dict, by: str, today: str) -> dict:
    """Bloc `metadata['cost']` canonique pour un notebook RL CPU-pur pédagogique.

    Diffère de `build_search_cpu_cost` : `reproducibility: MED` (stochastique, seeds)
    vs `HIGH` (déterministe) ; `cpu_min` via `_rl_cpu_min_estimate` (boucles
    d'entraînement). `network: False` (gymnasium/torch/SB3 sont pip-installés en
    local, aucun appel réseau au runtime). Champs notebook-specific
    (`reduced_pedagogical`) : null (honnête, pas fabriqué).
    """
    n_code = _count_code_cells(nb)
    return {
        "api_usd_est": 0.0,  # gratuit, CPU local
        "api_provider": "none",
        "qcc_tokens_est": 0,  # non-QC
        "cpu_min": _rl_cpu_min_estimate(n_code),  # heuristic entraînement
        "gpu_min": 0,
        "gpu_required": False,  # CPU OK pour petits envs RL
        "vram_gb": 0,
        "vram_tier": "NONE",
        "network": False,  # pip install local, pas d'appel runtime
        "external_account": "none",
        "free_alternative": "self",  # sentinelle canonique : déjà gratuit
        "reduced_pedagogical": None,  # notebook-specific (jugement humain) ; null = honnête
        "reproducibility": "MED",  # stochastique (seeds), pas déterministe
        "metadata_written": today,  # date d'établissement de la metadata (inspection source)
        "validator": "manual",  # inspection source, pas re-exécution machine claimée
    }


# --- Dispatch par profile -------------------------------------------------------
# Chaque profile : (gate d'éligibilité, builder de cost, raison de skip si inéligible).
# Uniformisation c.929 : eligible(nb, path) et build(nb, path, by, today) — `path` requis
# par probas-cpu (po-2023, build_probas_cpu_cost lit l'index depuis le nom de fichier).
# quantbook/search-cpu l'ignorent via lambda fin (signature uniforme, pas d'asymétrie).
PROFILES = {
    "quantbook": {
        "eligible": lambda nb, path: _uses_quantbook(nb),
        "build": lambda nb, path, by, today: build_quantbook_cost(nb, by=by, today=today),
        "skip_reason": "skipped-no-quantbook",
    },
    "search-cpu": {
        "eligible": lambda nb, path: is_cpu_pure(nb),
        "build": lambda nb, path, by, today: build_search_cpu_cost(nb, by=by, today=today),
        "skip_reason": "skipped-not-cpu-pure",
    },
    "probas-cpu": {
        "eligible": _is_pymc_notebook,  # (nb, path) — subpath + import pymc/arviz
        "build": build_probas_cpu_cost,  # (nb, path, by, today) — index depuis path.name
        "skip_reason": "skipped-not-pymc",
    },
    "rl-cpu": {
        "eligible": lambda nb, path: is_rl_cpu_pure(nb),  # (nb) — RL API usage via _RL_API_RE
        "build": lambda nb, path, by, today: build_rl_cpu_cost(nb, by=by, today=today),
        "skip_reason": "skipped-not-rl-cpu-pure",
    },
}


def populate_notebook(path: Path, profile: str, by: str, today: str, apply: bool) -> str:
    """Peuple metadata.cost pour le profile donné, si éligible + absent.

    Returns: 'populated' | 'skipped-has-cost' | '<profile skip_reason>' | 'error: ...'.
    """
    prof = PROFILES[profile]
    try:
        raw = path.read_text(encoding="utf-8")
        nb = json.loads(raw)
    except Exception as e:
        return f"error: {e}"

    if not prof["eligible"](nb, path):
        return prof["skip_reason"]

    meta = nb.setdefault("metadata", {})
    if "cost" in meta:  # idempotent : ne JAMAIS écraser un bloc existant
        return "skipped-has-cost"

    cost = prof["build"](nb, path, by=by, today=today)
    if not apply:
        return "populated"  # dry-run : on rapporte, on n'écrit pas

    meta["cost"] = cost
    # Round-trip json indent=1 (convention repo), sort_keys=False (préserve l'ordre
    # d'insertion original des notebooks non sérialisés avec sort_keys), LF-only.
    # Préserve le trailing-newline original (byte-surgical : ne churn pas les
    # notebooks qui n'en ont pas — C913-L).
    had_trailing_nl = raw.endswith("\n")
    out = json.dumps(nb, indent=1, ensure_ascii=False, sort_keys=False)
    if had_trailing_nl:
        out += "\n"
    path.write_text(out, encoding="utf-8", newline="\n")
    return "populated"


def iter_notebooks(target: Path):
    """Énumère les .ipynb sous target (fichier unique ou dossier récursif),
    en excluant _output.ipynb, .ipynb_checkpoints/, /backtests/."""
    if target.is_file():
        yield target
        return
    for p in sorted(target.rglob("*.ipynb")):
        s = str(p).replace("\\", "/")
        if "_output" in p.name:
            continue
        if ".ipynb_checkpoints" in s:
            continue
        if "/backtests/" in s:
            continue
        yield p


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("target", type=Path, help="Notebook .ipynb ou dossier à peupler")
    ap.add_argument("--profile", choices=list(PROFILES), default="quantbook",
                    help=f"Profile de coût (implémentés : {', '.join(PROFILES)})")
    ap.add_argument("--by", default="anonymous",
                    help="machine:workspace (provenance, pour le rapport)")
    ap.add_argument("--apply", action="store_true",
                    help="Écrire les modifications (défaut : dry-run)")
    ap.add_argument("--today", default=None,
                    help="Date ISO pour metadata_written (défaut : aujourd'hui)")
    args = ap.parse_args(argv)

    if not args.target.exists():
        print(f"ERROR: {args.target} n'existe pas", file=sys.stderr)
        return 2

    today = args.today or _dt.date.today().isoformat()
    skip_key = PROFILES[args.profile]["skip_reason"]
    counts = {"populated": 0, "skipped-has-cost": 0, skip_key: 0}
    errors = []

    for nb_path in iter_notebooks(args.target):
        status = populate_notebook(nb_path, profile=args.profile,
                                   by=args.by, today=today, apply=args.apply)
        if status.startswith("error"):
            errors.append((nb_path, status))
        elif status in counts:
            counts[status] += 1
            if status == "populated":
                print(f"  {'WRITE' if args.apply else 'DRY-RUN'}  {nb_path}")
        else:
            errors.append((nb_path, f"unexpected: {status}"))

    mode = "APPLY" if args.apply else "DRY-RUN"
    print(f"\n[{mode}] profile={args.profile} by={args.by} today={today}")
    print(f"  populated (sans cost, éligible) : {counts['populated']}")
    print(f"  skipped-has-cost (déjà peuplé)   : {counts['skipped-has-cost']}")
    print(f"  {skip_key:<35} : {counts[skip_key]}")
    if errors:
        print(f"  errors                           : {len(errors)}", file=sys.stderr)
        for p, e in errors:
            print(f"    {p}: {e}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
