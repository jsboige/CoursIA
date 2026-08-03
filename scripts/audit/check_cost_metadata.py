#!/usr/bin/env python3
"""
check_cost_metadata.py — Vérificateur cohérence matrice de coût `cost:`.

Issue #8056 (P1) — matrice coût/ressource par notebook.

Forme CANONIQUE (design-gate c.866) : `nb.metadata['cost']` (JSON, invisible au
rendu markdown). La cellule markdown `---YAML---` est LÉGACY, RETIREE du mandat
(markdown-it promeut le bloc `---` en setext-H2 supersize = guard #8352 ERROR).
Ce vérificateur lit `metadata['cost']` D'ABORD, retombe sur le scan cellule
`---...---` en backward-compat pendant la migration de masse (ordre non-bloquant).

But : extraire pour un notebook :
  - La matrice `cost:` — depuis `nb.metadata['cost']` (canonical) ou, à défaut,
    le bloc YAML `---...---` d'une cellule markdown (legacy fallback)
  - Les usages réels : appels API, .cuda(), HF_TOKEN, QuantBook, etc.
  - Signaler les :
      (1) gpu_required: false mais cellule code lance torch.cuda / tensorflow GPU
      (2) api_usd_est: 0.0 mais cellule appelle openai.ChatCompletion / anthropic / mistral
      (3) external_account: none mais cellule demande HF_TOKEN / OPENAI_API_KEY
      (4) free_alternative pointe vers un notebook inexistant
      (5) Notebook QC sans qc_cloud validator
      (6) Notebook GPU sans sk_visual validator
      (7) QuantBook détecté sans estimation qcc_tokens_est (#8376)
      (8) api_cost_breakdown dont la somme != api_usd_est (design-gate #8056)
      (9) validator affirmant une exécution alors que des cellules code
          non vides portent execution_count: null

Litmus anti-LIGHT : ce script EXTRACT, il ne DÉCIDE pas. Le verdict final
= revue humaine/agent compétent. Cf docs/notebook-metadata/cost-matrix.md.

Mode flotte (c.58)
------------------
Jusqu'ici le vérificateur ne prenait QU'UN notebook positionnel : les neuf
litmus étaient donc appliqués un notebook à la fois, à la main, par quiconque y
pensait. Personne n'avait jamais agrégé le résultat sur la flotte — de sorte
que le compte réel de findings (86 au moment de l'écriture, sur 6 patterns)
n'était connu de personne, et qu'un litmus vert (le 9, #8790) ne pouvait pas
être distingué d'un litmus jamais exécuté. `--all` / `--family` ferment cet
écart : même prédicat, marcheur canonique `notebook_walk` (#8650), sortie
agrégée par pattern ET recensement par validator.

Ce que ce mode ne fait PAS, délibérément :
  - pas de `--check` / exit non nul sur findings, et aucun câblage CI. Les 86
    findings sont PRÉ-EXISTANTS : un gate posé dessus serait rouge à l'arrivée,
    donc ignoré dès le premier jour (décision « ne se câble pas sur rouge
    pré-existant », cf organe Slides #8817). L'ordre est : agréger, résorber,
    PUIS gater — pas l'inverse.
  - pas de correction automatique : ce script EXTRACT (litmus anti-LIGHT
    ci-dessus). Résorber un pattern est un grain de substance séparé.

Usage :
  python scripts/audit/check_cost_metadata.py <notebook>.ipynb [--out <fichier.yml>]
  python scripts/audit/check_cost_metadata.py --all                # toute la flotte
  python scripts/audit/check_cost_metadata.py --family QuantConnect # une famille
  python scripts/audit/check_cost_metadata.py --all --json         # sortie machine

Exit codes :
  0 — audit produit (findings ou non : la sortie est advisory)
  1 — erreur (notebook introuvable, famille inexistante, lecture impossible)
"""

import argparse
import json
import re
import sys
from collections import Counter
from pathlib import Path

import nbformat
import yaml


# === Patterns de détection ===

# Cellule code GPU
# Note FP-c.831 : `torch.cuda.is_available()` est une SONDE bénigne (affichée pour
# info par les notebooks PyTorch CPU pédagogiques, ex rl_6e GRPO — output committé
# « CUDA=False », tourne en CPU). On l'exonère via lookahead négatif ; les vrais
# signaux GPU (`torch.cuda.synchronize`, `torch.cuda.empty_cache`, `.cuda()`,
# `.to("cuda")`) restent détectés.
GPU_PATTERNS = [
    r'\.cuda\(\)',
    r'\.to\("cuda"\)',
    r'torch\.cuda\.(?!is_available\b)',
    r'tensorflow\.gpu',
    r'with\s+tf\.device\(["\']/gpu',
]

# API payantes (litmus 2 : api_usd_est = 0 mais cellule appelle API)
# Note FP-c.912 : `anthropic.` matchait la ponctuation de fin de phrase
# ("OpenAI/Anthropic.") et `claude`/`gemini` nus prenaient des panos SOTA
# en prose. On resserre `anthropic.` en `anthropic.\w` (préserve
# `anthropic.Anthropic(...)`, élimine le faux positif typographique).
API_PATTERNS = {
    'openai': r'openai\.ChatCompletion|openai\.Image|openai\.Audio|from openai',
    'anthropic': r'anthropic\.\w|from anthropic|claude',
    'mistral': r'mistralai|from mistral',
    'google': r'google\.generativeai|gemini',
    'replicate': r'replicate\.',
    'hf_inference_api': r'huggingface_hub\.InferenceClient',
}

# Tokens requis (litmus 3 : external_account=none mais cellule demande token)
TOKEN_PATTERNS = {
    'hf': r'os\.getenv\(["\']HF_TOKEN|os\.environ\[["\']HF_TOKEN',
    'openai': r'os\.getenv\(["\']OPENAI_API_KEY',
    'anthropic': r'os\.getenv\(["\']ANTHROPIC_API_KEY',
    'qc': r'os\.getenv\(["\']QC_USER|os\.getenv\(["\']QC_API_TOKEN',
    'comfyui': r'os\.getenv\(["\']COMFYUI',
}


def strip_commented_lines(code_source: str) -> str:
    r"""Filtre les lignes commentées (Python) et les triple-quoted strings
    avant que les regex `API_PATTERNS`/`TOKEN_PATTERNS` ne soient appliquées.

    Avant c.912 (#8618), les regex étaient appliquées sur la source brute des
    cellules code, sans distinguer une ligne de code d'une ligne de commentaire
    ou de prose de cellule markdown. Conséquence :
    `anthropic.` matchait la ponctuation de fin de phrase ("OpenAI/Anthropic.")
    en commentaire d'avertissement, et `claude`/`gemini` nus prenaient des
    panoramas SOTA en prose (print multi-ligne avec triple-quoted).

    Le filtre fait 2 passes :
    1. Retrait des triple-quoted strings (les plus fréquents en docstring).
       Un panorama SOTA type "Gemini 2.0, GPT-5, Claude 3.5" à l'intérieur d'un
       print multi-ligne matche gemini/claude sans être un appel d'API.
    2. Filtrage des lignes dont le strip() commence par le caractère Python
       de commentaire.

    Trade-off (volontairement borné) : on ne retire PAS les littéraux
    simple/double-quoted parce qu'un appel d'API authentique passe souvent par
    argument string (os.getenv(TOKEN), model_id=anthropic/...). Conséquence :
    une config-dict littérale qui mentionne anthropic/claude-... peut subsister
    comme signal — c'est un cas rare et le coût (1 finding résiduel) reste
    inférieur au coût de destruction d'un appel API authentique.

    Le filtre triple-quoted est appliqué sur le bloc entier (et pas ligne par
    ligne) parce qu'un triple-quoted peut s'étendre sur N lignes.
    """
    # 1. Retrait des triple-quoted strings (les plus fréquents en docstring).
    no_triple = _TRIPLE_QUOTED_RE.sub('', code_source)
    # 2. Filtrage des lignes commentées.
    out_lines = []
    for line in no_triple.splitlines():
        if line.lstrip().startswith('#'):
            continue
        out_lines.append(line)
    return '\n'.join(out_lines)


_TRIPLE_QUOTED_RE = re.compile(r'"""[\s\S]*?"""|\'\'\'[\s\S]*?\'\'\'')


def parse_cost_frontmatter(cell_source: str) -> dict:
    """Parse le bloc YAML `--- ... ---` d'une cellule markdown (LÉGACY fallback).

    Forme canonique = `nb.metadata['cost']` (cf check_notebook). Cette fonction ne
    sert qu'au backward-compat pour les notebooks pas encore migrés (convention
    c.800 = cell[1], après le titre markdown cell[0]).
    """
    # Pattern : début de cellule = `---`, lignes YAML, `---` final
    pattern = r'^---\s*\n(.*?)\n---\s*\n'
    match = re.match(pattern, cell_source, re.DOTALL)
    if not match:
        return {}
    try:
        return yaml.safe_load(match.group(1)) or {}
    except yaml.YAMLError:
        return {}


def detect_gpu_usage(code_source: str) -> bool:
    """Litmus 1 : cellule code utilise GPU."""
    for pattern in GPU_PATTERNS:
        if re.search(pattern, code_source):
            return True
    return False


def detect_api_usage(code_source: str) -> list:
    """Litmus 2 : cellule code appelle API payante.

    Filtre les lignes commentées (`#`) avant regex (cf c.912, issue #8618)
    pour éviter qu'une ligne de prose `"OpenAI/Anthropic."` matche
    `anthropic.` (ponctuation) ou que `claude`/`gemini` nus prennent
    un panorama SOTA en prose.
    """
    filtered = strip_commented_lines(code_source)
    found = []
    for provider, pattern in API_PATTERNS.items():
        if re.search(pattern, filtered, re.IGNORECASE):
            found.append(provider)
    return found


def detect_token_usage(code_source: str) -> list:
    """Litmus 3 : cellule code lit token externe.

    Filtre les lignes commentées (`#`) avant regex (cf c.912, issue #8618).
    Les tokens sont peu probables en commentaire mais l'uniformité du
    filtre (litmus 2 + litmus 3) simplifie la discipline d'audit.
    """
    filtered = strip_commented_lines(code_source)
    found = []
    for provider, pattern in TOKEN_PATTERNS.items():
        if re.search(pattern, filtered):
            found.append(provider)
    return found


def detect_quantbook_usage(code_source: str) -> bool:
    """Litmus 5 : QC notebook utilise QuantBook."""
    return bool(re.search(r'QuantBook\(\)|self\.QuantBook', code_source))


def check_notebook(notebook_path: Path, repo_root: Path) -> dict:
    """Audit complet d'un notebook."""
    with notebook_path.open('r', encoding='utf-8') as f:
        nb = nbformat.read(f, as_version=4)

    findings = []
    cost_meta = {}
    cost_source = None  # provenance: 'metadata' (canonical) | 'markdown_cell' (legacy fallback)
    code_cells_source = []

    # Extraction de la matrice de coût.
    # PR A (#8056, design-gate c.866) : la forme CANONIQUE est `nb.metadata['cost']`
    # (JSON, invisible au rendu markdown). La cellule markdown `---YAML---` est la
    # forme LÉGACY, RETIREE du mandat : markdown-it promeut le bloc `---` en
    # setext-H2 supersize (guard #8352 ERROR). On lit metadata d'abord, puis on
    # retombe sur le scan cellule en backward-compat (les deux formes coexistent
    # pendant la migration de masse ; l'ordre est non-bloquant).
    # Cf docs/notebook-metadata/cost-matrix.md, PR exemplar #8323 (Infer-3/4).
    nb_metadata = nb.metadata or {}
    md_cost = nb_metadata.get('cost')
    if isinstance(md_cost, dict) and md_cost:
        cost_meta = dict(md_cost)
        cost_source = 'metadata'

    # Fallback LÉGACY : scan de TOUTES les cellules markdown pour un bloc
    # `---...---` contenant `cost:` (convention c.800 = cell[1]). Backward-compat
    # pour les notebooks pas encore migrés vers metadata.cost.
    if not cost_meta:
        for cell in nb.cells:
            if cell.get('cell_type') != 'markdown':
                continue
            source = cell.get('source', '')
            if isinstance(source, list):
                source = ''.join(source)
            parsed = parse_cost_frontmatter(source)
            if 'cost' in parsed:
                cost_meta = parsed.get('cost', {})
                cost_source = 'markdown_cell'
                break

    # Agrégation cellules code
    for idx, cell in enumerate(nb.cells):
        if cell.get('cell_type') != 'code':
            continue
        source = cell.get('source', '')
        if isinstance(source, list):
            source = ''.join(source)
        code_cells_source.append((idx, source))

    # Litmus 1 : GPU_required: false mais GPU usage
    uses_gpu = any(detect_gpu_usage(src) for _, src in code_cells_source)
    if uses_gpu and not cost_meta.get('gpu_required', False):
        findings.append({
            'pattern': 'gpu_used_but_not_declared',
            'detail': 'Cellule code utilise GPU (.cuda(), torch.cuda) mais cost.gpu_required: false',
            'severity': 'MAJOR',
        })

    # Litmus 2 : api_usd_est: 0 mais API usage.
    # FP guard: quand cost.api_provider declare une inference locale/gratuite
    # (local, hf, huggingface, ollama), la presence du keyword 'openai'/
    # 'replicate' reflete un client OpenAI-compatible pointant vers un serveur
    # local (vLLM, Ollama, endpoint HF Inference) — pas un appel API payant en
    # USD. cost.api_usd_est: 0.0 est alors correct, le flag CRITICAL = faux
    # positif (5 FP fleet-wide avant ce fix : notebooks 'Local'/HF avec
    # provider=local/hf). On ne flag QUE si le provider est un payant cloud ou
    # absent/none (cas ambigu a investiguer, cf litmus 3 pour le compte).
    FREE_API_PROVIDERS = ('local', 'hf', 'huggingface', 'ollama')
    api_provider_val = str(cost_meta.get('api_provider', '')).lower()
    api_used = set()
    for _, src in code_cells_source:
        api_used.update(detect_api_usage(src))
    if api_used and cost_meta.get('api_usd_est', 0.0) == 0.0 \
            and api_provider_val not in FREE_API_PROVIDERS:
        for provider in api_used:
            findings.append({
                'pattern': 'api_used_but_cost_zero',
                'detail': f'Cellule code appelle {provider} mais cost.api_usd_est: 0.0',
                'severity': 'CRITICAL',
            })

    # Litmus 3 : external_account: none mais token usage
    tokens_required = set()
    for _, src in code_cells_source:
        tokens_required.update(detect_token_usage(src))
    declared_account = cost_meta.get('external_account', 'none')
    if tokens_required and declared_account == 'none':
        for provider in tokens_required:
            findings.append({
                'pattern': 'token_required_but_no_account',
                'detail': f'Cellule code lit token {provider} mais cost.external_account: none',
                'severity': 'MAJOR',
            })

    # Litmus 4 : free_alternative pointe vers un notebook inexistant.
    # Le champ admet deux natures (design-gate tranche sur #8056) : un path
    # relatif vers un notebook/.md alternative gratuit, OU un sentinel
    # semantique. Un sentinel est canonique quand il porte une information que
    # `null` detruit : 'self' = ce notebook EST l'alternative gratuite (oppose
    # de `null` = « aucune alternative connue ») ; 'ollama' = un moteur local
    # gratuit couvre le sujet, ce qu'aucun chemin du depot n'exprime ; 'n/a' =
    # non-applicable, synonyme tolere de `null`.
    #
    # On ne verifie l'existence QUE des valeurs path-shaped : un sentinel n'est
    # pas un fichier, le flagger = faux positif. Avant #8588 le litmus produisait
    # 101 FP fleet-wide (55x 'self', 18x '10_LocalLlama.ipynb' base fausse,
    # 13x 'ollama', 5x 'N/A'...). Les valeurs path-shaped sont cherchees en
    # dual-base (repo root OU MyIA.AI.Notebooks/, convention majoritaire).
    #
    # 'openai' n'est PAS un sentinel : c'est precisement le service payant dont
    # on cherche a s'affranchir. Le nommer comme alternative gratuite est une
    # erreur de saisie -- desormais flaggee (voir plus bas), au lieu d'etre
    # silencieusement toleree parce qu'elle ne ressemble pas a un chemin.
    SENTINELS = ('self', 'ollama', 'none', 'null', 'n/a', '')
    # Services payants : ne peuvent pas etre l'alternative *gratuite*.
    PAID_SERVICES = (
        'openai', 'anthropic', 'azure', 'replicate', 'runway',
        'midjourney', 'gpt', 'claude', 'gemini',
    )
    free_alt = cost_meta.get('free_alternative')
    if free_alt and str(free_alt).lower() not in SENTINELS:
        free_alt_str = str(free_alt)
        looks_like_path = ('/' in free_alt_str) or ('\\' in free_alt_str) \
            or free_alt_str.lower().endswith(('.ipynb', '.md'))
        if free_alt_str.lower() in PAID_SERVICES:
            findings.append({
                'pattern': 'free_alternative_is_paid_service',
                'detail': (
                    f"cost.free_alternative vaut '{free_alt}' : c'est un service "
                    f"payant, il ne peut pas etre l'alternative gratuite. "
                    f"Attendu : 'self' si ce notebook est deja gratuit, un "
                    f"chemin repo-relatif, un moteur local ('ollama'), ou null."
                ),
                'severity': 'MAJOR',
            })
        elif looks_like_path:
            candidates = [
                repo_root / free_alt,
                repo_root / 'MyIA.AI.Notebooks' / free_alt,
            ]
            if not any(p.exists() for p in candidates):
                findings.append({
                    'pattern': 'free_alternative_missing',
                    'detail': f'cost.free_alternative pointe vers {free_alt} mais fichier absent',
                    'severity': 'MAJOR',
                })
        else:
            # Ni sentinel canonique, ni chemin, ni service payant connu : la
            # valeur ne resout vers rien que le lecteur puisse suivre.
            findings.append({
                'pattern': 'free_alternative_unresolvable',
                'detail': (
                    f"cost.free_alternative vaut '{free_alt}' : ni sentinel "
                    f"canonique ({', '.join(s for s in SENTINELS if s)}), ni "
                    f"chemin repo-relatif. Le lecteur ne peut pas le suivre."
                ),
                'severity': 'MINOR',
            })

    # Litmus 5 : QC notebook sans qc_cloud validator
    uses_qc = any(detect_quantbook_usage(src) for _, src in code_cells_source)
    validator = cost_meta.get('validator', 'manual')
    if uses_qc and validator != 'qc_cloud':
        findings.append({
            'pattern': 'qc_notebook_no_validator',
            'detail': 'Notebook QuantConnect (QuantBook) mais cost.validator != qc_cloud',
            'severity': 'MAJOR',
        })

    # Litmus 6 : GPU sans sk_visual validator (cf #5780 sweep)
    if cost_meta.get('gpu_required', False) and validator not in ('sk_visual', 'papermill'):
        findings.append({
            'pattern': 'gpu_no_visual_validator',
            'detail': 'Notebook GPU sans sk_visual validator (cf sweep #5780)',
            'severity': 'MINOR',
        })

    # Litmus 7 : QuantBook détecté sans estimation QCC (cf #8376/#8056)
    # QCC (QuantConnect Cloud compute tokens) = quota non-USD consommé par tout
    # quantbook exécuté via QC Cloud. api_usd_est: 0.0 est techniquement correct
    # (pas de USD) mais trompeur : le notebook n'est PAS gratuit. Le champ dédié
    # cost.qcc_tokens_est (~70 QCC/cellule, plancher max(400, n_cells x 70))
    # rend la dépense visible. Absent/0 sur un QuantBook = lacune de coût.
    if uses_qc and not cost_meta.get('qcc_tokens_est'):
        findings.append({
            'pattern': 'qc_notebook_no_qcc_estimate',
            'detail': 'Notebook QuantConnect (QuantBook) mais cost.qcc_tokens_est absent ou 0 (cf #8376/#8056)',
            'severity': 'MAJOR',
        })

    # Litmus 8 : api_cost_breakdown incoherent avec api_usd_est (design-gate #8056).
    # `api_usd_est` est le scalaire AUTORITATIF (obligatoire, lu par les 327
    # notebooks deja migres et les agregats). `api_cost_breakdown` est OPTIONNEL :
    # un notebook mono-fournisseur ne l'ecrit pas (il dupliquerait son total pour
    # zero information). Quand un multi-fournisseur l'ecrit, sum(valeurs) DOIT
    # egaler api_usd_est — sinon la ventilation ment (gate FALSIFIABLE, decision
    # ai-01 #8056 issuecomment 5106409423). Une ventilation libre serait
    # decorative : personne ne peut la contredire, elle se perime en silence. Une
    # ventilation dont la somme doit egaler le total casse le jour ou elle derive
    # — meme lecon que #8678 (un compteur nu se perime) et #8680 (un gate incapable
    # d'echouer n'est pas un gate).
    breakdown = cost_meta.get('api_cost_breakdown')
    if breakdown is not None:
        if not isinstance(breakdown, dict) or not breakdown:
            findings.append({
                'pattern': 'api_cost_breakdown_malformed',
                'detail': (
                    'cost.api_cost_breakdown present mais pas un dict non-vide. '
                    'Attendu : {"openai": 0.30, "anthropic": 0.12} sommant a '
                    'api_usd_est, ou absent (mono-fournisseur).'
                ),
                'severity': 'MAJOR',
            })
        else:
            # api_usd_est doit etre numerique pour pouvoir comparer la somme.
            try:
                total = float(cost_meta.get('api_usd_est'))
            except (TypeError, ValueError):
                findings.append({
                    'pattern': 'api_usd_est_not_numeric',
                    'detail': (
                        'cost.api_usd_est absent ou non-numerique alors que '
                        'api_cost_breakdown est present — le scalaire autoritatif '
                        'manque (design-gate #8056).'
                    ),
                    'severity': 'MAJOR',
                })
                total = None
            if total is not None:
                # bool est subclass de int en Python (float(True) == 1.0) : un
                # montant USD n'est jamais un booleen. Rejeter explicitement
                # AVANT la sommation, sinon {"openai": true} passerait le gate
                # en silence (NIT Hermes review #8688).
                bool_keys = sorted(k for k, v in breakdown.items() if isinstance(v, bool))
                if bool_keys:
                    findings.append({
                        'pattern': 'api_cost_breakdown_non_numeric',
                        'detail': (
                            f'cost.api_cost_breakdown contient une valeur '
                            f'booleenne (true/false) pour : {bool_keys}. '
                            f'Chaque cle (provider) doit avoir une valeur '
                            f'float USD, pas un bool (float(True)==1.0 trompe la sommation).'
                        ),
                        'severity': 'MAJOR',
                    })
                else:
                    try:
                        breakdown_sum = sum(float(v) for v in breakdown.values())
                    except (TypeError, ValueError):
                        findings.append({
                            'pattern': 'api_cost_breakdown_non_numeric',
                            'detail': (
                                f'cost.api_cost_breakdown contient des valeurs '
                                f'non-numeriques : {sorted(breakdown.keys())}. '
                                f'Chaque cle (provider) doit avoir une valeur float USD.'
                            ),
                            'severity': 'MAJOR',
                        })
                    else:
                        # Tolerance 1 cent (arrondi USD) : evite les FP de precision
                        # float (0.1+0.2 != 0.3 en binaire) sans tolerer un vrai
                        # desequilibre. round(..., 2) serait equivalent.
                        if abs(breakdown_sum - total) > 0.01:
                            findings.append({
                                'pattern': 'api_cost_breakdown_sum_mismatch',
                                'detail': (
                                    f'cost.api_cost_breakdown somme '
                                    f'{breakdown_sum:.2f} != api_usd_est {total:.2f} '
                                    f'(delta {breakdown_sum - total:+.2f}). La '
                                    f'ventilation doit sommer au total autoritatif '
                                    f'(design-gate #8056).'
                                ),
                                'severity': 'MAJOR',
                            })

    # Litmus 9 : le validator AFFIRME une execution que le notebook contredit.
    #
    # Avant ce litmus, `validator` etait le seul champ de la matrice que RIEN
    # ne pouvait contredire ; les populators ecrivaient
    # `last_validated: _dt.date.today()` au peuplement (jamais relu, jamais
    # falsifiable, etrange de fait — un notebook dont AUCUNE cellule n'a
    # jamais tourne pouvait le porter sans mentir, ce qui en faisait un champ
    # decoratif et a permis ecriture d'un faux gate — cf #8841). Le champ a
    # ete renomme `metadata_written` (#8843) : sa seule semantique reelle
    # (date d'etablissement de la metadata) a son nom, et ce litmus ne s'en
    # sert plus.
    #
    # Ce qui reste a falsifier, c'est donc `validator` seul : nbclient/papermill
    # executent CHAQUE cellule code non vide, y compris celles qui echouent
    # (`--allow-errors` ne change que le comportement d'arret, pas
    # l'attribution du compteur). Donc `execution_count: null` sur une cellule
    # code non vide PROUVE que la cellule n'a pas ete executee — et contredit
    # un validator qui affirme l'avoir ete.
    #
    # Perimetre : seuls les validators qui affirment une EXECUTION DE CELLULES.
    # Sont exclus, et ce n'est pas un oubli :
    #   - `manual`   : un humain a relu — aucune affirmation d'execution ;
    #   - `qc_cloud` : carve-out documente (H.3) — le runtime research QC
    #                  n'existe sur aucune machine worker ;
    #   - `lean_build`: `lake build` SUCCESS, qui porte sur le lake, pas sur
    #                  les cellules du notebook ;
    #   - `sk_agent` : perimetre ambigu, pas d'affirmation nette.
    # `dotnet-interactive` est retenu bien qu'absent de la liste canonique de
    # cost-matrix.md (4 notebooks l'emploient) : il affirme une execution du
    # kernel .NET local, exigee par l'advisory #5214.
    #
    # Echappatoire honnete : une cellule deliberement non executable (code de
    # reference destine a un autre runtime) se declare par un tag de skip. Le
    # notebook cesse alors d'etre contredit — sans mentir, et de facon visible
    # dans le fichier. Fleet-wide au moment de l'ecriture : 0 cellule taguee.
    EXECUTION_ASSERTING_VALIDATORS = ('papermill', 'sk_visual', 'dotnet-interactive')
    SKIP_EXECUTION_TAGS = {'skip-execution', 'skip', 'no-execute'}
    if validator in EXECUTION_ASSERTING_VALIDATORS:
        unexecuted = []
        for idx, cell in enumerate(nb.cells):
            if cell.get('cell_type') != 'code':
                continue
            source = cell.get('source', '')
            if isinstance(source, list):
                source = ''.join(source)
            # Une cellule code VIDE n'est pas executee par nbclient (skip
            # explicite sur `not cell.source.strip()`) : son `execution_count`
            # reste null apres un run complet. La flagger serait un faux
            # positif qui pousse a modifier un notebook sain.
            if not source.strip():
                continue
            tags = set((cell.get('metadata') or {}).get('tags') or [])
            if tags & SKIP_EXECUTION_TAGS:
                continue
            if cell.get('execution_count') is None:
                unexecuted.append(idx)
        if unexecuted:
            shown = ', '.join(str(i) for i in unexecuted[:5])
            more = f', +{len(unexecuted) - 5}' if len(unexecuted) > 5 else ''
            seen_at = cost_meta.get('metadata_written') or 'unknown'
            findings.append({
                'pattern': 'validator_asserts_execution_but_cells_unexecuted',
                'detail': (
                    f"cost.validator: '{validator}' affirme une execution, mais "
                    f"{len(unexecuted)} cellule(s) code non vides ont "
                    f"execution_count: null (index {shown}{more}). "
                    f"cost.metadata_written={seen_at} (date d'etablissement de "
                    f"la metadata, pas une validation). La declaration contredit "
                    f"le notebook — un validator qui "
                    f"affirme l'execution ne tient pas si une cellule code n'a "
                    f"pas tourne. Corriger la DECLARATION (validator: manual "
                    f"si le notebook n'est pas executable localement) ou "
                    f"re-executer — jamais editer les sorties a la main."
                ),
                'severity': 'MAJOR',
            })

    return {
        'notebook': str(notebook_path),
        'cost_meta_found': bool(cost_meta),
        'cost_source': cost_source,
        'cost_meta': cost_meta,
        'uses_gpu': uses_gpu,
        'api_used': sorted(api_used),
        'tokens_required': sorted(tokens_required),
        'uses_quantbook': uses_qc,
        'findings': findings,
    }


# === Mode flotte (c.58) ===

NOTEBOOKS_DIRNAME = 'MyIA.AI.Notebooks'


def _iter_fleet(repo_root: Path, family=None):
    """Énumère les notebooks pédagogiques via le marcheur canonique (#8650).

    Import différé : le mode notebook-unique n'a aucune raison de dépendre de
    `scripts/notebook_tools/`, et les tests chargent ce module par
    `spec_from_file_location` (un import de package cassé au niveau module
    ferait tomber toute la suite, pas seulement le mode flotte).
    """
    walk_dir = Path(__file__).resolve().parent.parent / 'notebook_tools'
    if str(walk_dir) not in sys.path:
        sys.path.insert(0, str(walk_dir))
    from notebook_walk import iter_notebooks  # noqa: PLC0415 (import différé, cf docstring)

    yield from iter_notebooks(repo_root / NOTEBOOKS_DIRNAME, family=family)


def aggregate_fleet(notebook_paths, repo_root: Path) -> dict:
    """Applique `check_notebook` à chaque chemin et agrège le résultat.

    Retourne : scanned, errors, `validators` (recensement — combien de notebooks
    déclarent chaque validator), `patterns` (combien de findings par pattern),
    et `notebooks` (le détail, notebooks sans finding exclus).

    Un notebook illisible est compté dans `errors` et n'interrompt pas la
    marche : un audit de flotte qui s'arrête au premier .ipynb corrompu ne
    mesure rien (cf `ESGF-2026/.../research.ipynb`, gitignored et non
    parsable). L'erreur reste VISIBLE dans le rapport — elle n'est pas avalée.
    """
    validators: Counter = Counter()
    patterns: Counter = Counter()
    errors: list = []
    notebooks: list = []
    scanned = 0

    for nb_path in notebook_paths:
        try:
            rel = nb_path.resolve().relative_to(repo_root.resolve()).as_posix()
        except (ValueError, OSError):
            rel = str(nb_path).replace('\\', '/')
        try:
            result = check_notebook(nb_path, repo_root)
        except Exception as exc:  # noqa: BLE001 — un notebook cassé ne stoppe pas l'audit
            errors.append({'notebook': rel, 'error': f'{type(exc).__name__}: {exc}'})
            continue
        scanned += 1
        cost_meta = result.get('cost_meta') or {}
        if cost_meta.get('validator'):
            validators[str(cost_meta['validator'])] += 1
        findings = result.get('findings') or []
        for finding in findings:
            patterns[finding['pattern']] += 1
        if findings:
            notebooks.append({'notebook': rel, 'findings': findings})

    return {
        'scanned': scanned,
        'errors': errors,
        'validators': dict(validators.most_common()),
        'patterns': dict(patterns.most_common()),
        'notebooks': notebooks,
    }


def format_fleet_report(agg: dict) -> str:
    """Rapport humain agrégé. Le DÉTAIL complet de chaque finding est en
    `--json` : ici on donne pattern + sévérité par notebook, pour que la vue
    reste scannable (86 details de 3 lignes noieraient les comptes, qui sont
    précisément ce que le mode flotte apporte)."""
    total_findings = sum(agg['patterns'].values())
    lines = [
        f"Notebooks scannes        : {agg['scanned']}",
        f"Notebooks avec finding   : {len(agg['notebooks'])}",
        f"Findings                 : {total_findings}",
        f"Erreurs de lecture       : {len(agg['errors'])}",
        "",
    ]
    if agg['errors']:
        lines.append("--- erreurs de lecture ---")
        for err in agg['errors']:
            lines.append(f"  {err['notebook']}: {err['error']}")
        lines.append("")

    lines.append("--- validators declares (recensement) ---")
    if agg['validators']:
        for name, count in agg['validators'].items():
            lines.append(f"  {name:24s} {count}")
    else:
        lines.append("  (aucun)")
    lines.append("")

    lines.append("--- findings par pattern ---")
    if agg['patterns']:
        for pattern, count in agg['patterns'].items():
            lines.append(f"  {pattern:52s} {count}")
    else:
        lines.append("  (aucun)")
    lines.append("")

    if agg['notebooks']:
        lines.append("--- notebooks concernes ---")
        for entry in agg['notebooks']:
            lines.append(f"## {entry['notebook']}")
            for finding in entry['findings']:
                lines.append(f"  - [{finding['severity']}] {finding['pattern']}")
        lines.append("")

    lines.append(
        "NOTE: ce script EXTRACT, il ne DECIDE pas. Chaque finding se verifie "
        "firsthand avant correction — et la correction se fait a la SOURCE "
        "(re-executer, corriger la declaration), jamais en editant une sortie "
        "de cellule a la main. Detail complet des findings : --json."
    )
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('notebook', type=Path, nargs='?',
                        help='Chemin du .ipynb à auditer (défaut si ni --all ni --family)')
    parser.add_argument('--all', action='store_true',
                        help='Auditer toute la flotte pédagogique (MyIA.AI.Notebooks/)')
    parser.add_argument('--family',
                        help='Auditer une famille (ex: QuantConnect, Probas) — implique le mode flotte')
    parser.add_argument('--json', action='store_true',
                        help='Sortie JSON machine-readable (détail complet des findings)')
    parser.add_argument('--out', type=Path, help='Fichier de sortie (default: stdout)')
    parser.add_argument('--repo-root', type=Path, default=Path('.'),
                        help='Racine du repo (pour résoudre free_alternative)')
    args = parser.parse_args()

    fleet = args.all or bool(args.family)
    if fleet and args.notebook:
        print("ERROR: <notebook> et --all/--family sont exclusifs", file=sys.stderr)
        return 1
    if not fleet and not args.notebook:
        print("ERROR: fournir un notebook, ou --all / --family <nom>", file=sys.stderr)
        return 1

    if fleet:
        return _run_fleet(args)

    if not args.notebook.exists():
        print(f"ERROR: notebook {args.notebook} introuvable", file=sys.stderr)
        return 1

    try:
        result = check_notebook(args.notebook, args.repo_root)
    except Exception as e:
        print(f"ERROR: {e}", file=sys.stderr)
        return 1

    if args.json:
        return _emit(json.dumps(result, ensure_ascii=False, indent=2, default=str), args.out)

    # Sortie YAML
    lines = [
        f"notebook: {result['notebook']}",
        f"cost_meta_found: {result['cost_meta_found']}",
        f"cost_source: {result['cost_source']!r}",
        f"uses_gpu: {result['uses_gpu']}",
        f"api_used: {result['api_used']}",
        f"tokens_required: {result['tokens_required']}",
        f"uses_quantbook: {result['uses_quantbook']}",
        "cost_meta:",
    ]
    for k, v in (result['cost_meta'] or {}).items():
        lines.append(f"  {k}: {v!r}")
    lines.append("findings:")
    for f in result['findings']:
        lines.append(f"  - pattern: {f['pattern']}")
        lines.append(f"    severity: {f['severity']}")
        lines.append(f"    detail: {f['detail']!r}")

    return _emit('\n'.join(lines), args.out)


def _emit(output: str, out_path) -> int:
    if out_path:
        out_path.write_text(output, encoding='utf-8')
        print(f"Audit écrit: {out_path}")
    else:
        print(output)
    return 0


def _run_fleet(args) -> int:
    repo_root = args.repo_root
    if args.family:
        family_dir = repo_root / NOTEBOOKS_DIRNAME / args.family
        if not family_dir.is_dir():
            print(f"ERROR: famille introuvable: {family_dir}", file=sys.stderr)
            return 1

    agg = aggregate_fleet(_iter_fleet(repo_root, family=args.family), repo_root)
    if args.json:
        return _emit(json.dumps(agg, ensure_ascii=False, indent=2, default=str), args.out)
    return _emit(format_fleet_report(agg), args.out)


if __name__ == '__main__':
    sys.exit(main())
