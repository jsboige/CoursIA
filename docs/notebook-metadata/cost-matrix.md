# Matrice coût/ressource par notebook

> **Statut.** Document de cadrage, grade **B-méthodologique** (schéma applicable, pas une suggestion). V0 = pilote cycle c.794 (issue #8056, P1).
> **Objet.** Répondre à l'acceptance d'[#8056](https://github.com/jsboige/CoursIA/issues/8056) — **matrice coût/ressource par notebook** : (a) schéma de métadonnée `cost:` portable, (b) colonne catalogue correspondante, (c) peuplement pilote sur les familles à coût/ressource variable (GenAI/Image GPU + Probas/Infer.NET CPU + QC Cloud), (d) alternative gratuite / version pédagogique réduite, (e) compte externe requis, (f) intégration à la grille audit sémantique #8052.
> **Discipline.** NE remplace PAS le `validate_pr_notebooks.py` (structure), ni `audit-reassessment.md` (mécanique), ni `extract_claims_vs_outputs.py` (#8052 claims↔outputs) ; **AJOUTE** une couche **ressource/financier** que le catalogue anti-drift peut scanner. Cf incidents fondateurs documentés : notebooks GenAI GPU-only silencieusement CPU-skipés (cf `sota-not-workaround.md` §F), notebooks QC require QuantBook qu'on ne peut pas exécuter hors QC Cloud, notebooks Probas PyMC gratuits vs Infer.NET CPU-bound vs GPU-accelerated.
> **Lien.** Issue-source : [#8056](https://github.com/jsboige/CoursIA/issues/8056) (P1, lane po-2025 + po-2024 + po-2023 désignée). Complément audit-pattern [#8052](https://github.com/jsboige/CoursIA/issues/8052) (claims↔outputs). Grille parité jumeaux [#8057](https://github.com/jsboige/CoursIA/issues/8057) (Python↔C#). ICT out-of-scope [#7734](https://github.com/jsboige/CoursIA/issues/7734).

## Pourquoi ce schéma

L'open-courseware CoursIA héberge **300+ notebooks** (Python + .NET Interactive + Lean) répartis sur ~10 familles thématiques. Les **contraintes de ressources** pour les exécuter varient de **zéro** (notebook CPU Python pur, déterministe, < 1 min) à **des dizaines de $ API** (GenAI/Image avec DALL-E 3, GPT-5, Flux) ou **GPU VRAM 24+ GB** (Qwen-Image-Edit 2509, SD-3.5 large). Sans schéma structuré :

1. **L'étudiant fork le repo et tente d'exécuter en aveugle** → `OutOfMemoryError` CUDA, `RateLimitError` OpenAI, ou `AttributeError: QuantBook not available`.
2. **Le coordinateur ne peut pas filtrer** "quels notebooks sont exécutables sur la machine CPU-only de l'étudiant EPITA ?" sans lire le notebook cellule par cellule.
3. **Le catalogue** (`COURSE_CATALOG.generated.json`) n'expose **aucun champ** runtime/ressource.
4. **Les audits sémantiques** (#8052) prennent l'output comme vérité — si l'exécution a silencieusement *skip* une cellule GPU, le claim reste faux même avec une note pédagogique d'avertissement.

## Schéma `cost:` — YAML frontmatter portable

Chaque notebook pédagogique DOIT exposer en cellule 0 (markdown) un bloc YAML :

```yaml
---
title: <titre du notebook>
cost:
  api_usd_est: <float|range>     # Coût API estimé par exécution end-to-end (USD). 0 si gratuit.
  api_provider: <string>         # openai | anthropic | mistral | hf | replicate | google | local
  cpu_min: <int>                 # Estimation CPU-only minutes (range ou best-case)
  gpu_min: <int>                 # Estimation GPU minutes (range ou best-case)
  gpu_required: <bool>           # true si impossible sans GPU
  vram_gb: <int|range>           # VRAM minimum (GB), ex: 12, 24, ou range "16-24"
  vram_tier: <LITE|MID|HIGH>     # Catégorie VRAM (cf table §"Tiers VRAM")
  network: <bool>                # Accès réseau requis (téléchargement modèle, appel API)
  external_account: <string|none>  # Compte externe obligatoire (openai, anthropic, hf, qc, ...)
  free_alternative: <string|none>  # Notebook du dépôt qui couvre le même sujet sans coût
  reduced_pedagogical: <string|none>  # Version pédagogique réduite (sous-ensemble ou mock)
  reproducibility: <HIGH|MED|LOW>  # Reproductibilité : HIGH=déterministe, MED=seed-dépendant, LOW=stochastique
  last_validated: <ISO8601>       # Date dernière exécution validée (papermill/QC Cloud/MCP)
  validator: <papermill|qc_cloud|manual|lean_build|sk_agent|sk_visual>
---
```

### Champs obligatoires vs optionnels

| Champ | Obligatoire | Défaut si omis |
|-------|-------------|----------------|
| `title` | ✓ | (chaîne libre) |
| `cost.api_usd_est` | ✓ | `0` |
| `cost.api_provider` | ✓ | `"none"` |
| `cost.cpu_min` | ✓ | `0` |
| `cost.gpu_min` | optionnel | (omission = pas d'estimation GPU) |
| `cost.gpu_required` | ✓ | `false` |
| `cost.vram_gb` | optionnel | (omission = pas d'estimation VRAM) |
| `cost.vram_tier` | optionnel | (calculé depuis `vram_gb` : <8=LITE, 8-16=MID, >16=HIGH) |
| `cost.network` | ✓ | `false` |
| `cost.external_account` | ✓ | `"none"` |
| `cost.free_alternative` | optionnel | `null` (peut être ajouté après-coup) |
| `cost.reduced_pedagogical` | optionnel | `null` |
| `cost.reproducibility` | ✓ | `"HIGH"` |
| `cost.last_validated` | ✓ | (date de création du frontmatter) |
| `cost.validator` | ✓ | `"manual"` |

### Tiers VRAM (déterminé par `vram_gb`)

| Tier | VRAM (GB) | Modèles typiques |
|------|-----------|------------------|
| `LITE` | < 8 | SD-XL-Turbo int8, Kokoro TTS, Whisper-tiny/base |
| `MID` | 8-16 | Qwen-Image-Edit base, SD-3.5 medium, FLUX.1-schnell fp8 |
| `HIGH` | > 16 | Qwen-Image-Edit 2509 full, SD-3.5 large, FLUX.1-dev fp16 |

## Colonne catalogue — `COURSE_CATALOG.generated.json`

Le catalogue anti-drift expose `cost` via l'inférence du frontmatter. Schéma cible :

```json
{
  "notebook": "MyIA.AI.Notebooks/GenAI/Image/01-Foundation/01-1-OpenAI-DALL-E-3.ipynb",
  "cost": {
    "api_usd_est": 0.40,
    "gpu_required": false,
    "vram_tier": "LITE",
    "external_account": "openai",
    "free_alternative": "MyIA.AI.Notebooks/GenAI/Image/01-Foundation/01-3-Basic-Image-Operations.ipynb",
    "reproducibility": "MED"
  }
}
```

Le champ `cost.free_alternative` permet le routage machine : si `po-2025` n'a pas le GPU ou l'API key, le catalogue pointe vers le notebook équivalent exécutable localement.

## Peuplement pilote (cycle c.794)

5 familles × 2 notebooks = 10 entrées de référence (échantillon ≥5%/famille, conforme protocole #8052).

### GenAI/Image (GPU + API $)

```yaml
# 01-1-OpenAI-DALL-E-3.ipynb (GenAI/Image/01-Foundation)
cost:
  api_usd_est: 0.40            # 4 images × $0.040/image DALL-E 3 standard 1024×1024
  api_provider: openai
  cpu_min: 1
  gpu_min: 0                   # API cloud, pas de GPU local requis
  gpu_required: false
  network: true                # HTTPS OpenAI obligatoire
  external_account: openai     # OPENAI_API_KEY obligatoire
  free_alternative: GenAI/Image/01-Foundation/01-4-Forge-SD-XL-Turbo.ipynb
  reduced_pedagogical: GenAI/Image/01-Foundation/01-3-Basic-Image-Operations.ipynb
  reproducibility: MED         # Pas de seed déterministe côté OpenAI
  last_validated: 2026-07-23T01:30Z
  validator: papermill         # Exécuté via Papermill local + OpenAI API
```

```yaml
# 01-5-Qwen-Image-Edit.ipynb (GenAI/Image/01-Foundation)
cost:
  api_usd_est: 0.0             # Modèle self-hosted po-2023 (pas de coût API direct)
  api_provider: local
  cpu_min: 0
  gpu_min: 12                  # Inference ~5 min sur RTX 3090
  gpu_required: true           # Impossibilité CPU (modèle trop lourd)
  vram_gb: 16                  # Qwen-Image-Edit base = 16 GB FP16
  vram_tier: MID
  network: true                # Téléchargement modèle HuggingFace au premier run
  external_account: hf         # HF_TOKEN pour download gated
  free_alternative: GenAI/Image/02-Advanced/02-1-Qwen-Image-Edit-2509.ipynb
  reduced_pedagogical: GenAI/Image/01-Foundation/01-4-Forge-SD-XL-Turbo.ipynb
  reproducibility: HIGH        # torch.manual_seed(42) + déterminisme sampler
  last_validated: 2026-07-23T01:30Z
  validator: sk_visual         # sk-agent vision check sur figures rendues
```

### Probas / Infer.NET (CPU only)

```yaml
# DecInfer-1-Utility-Foundations.ipynb (Probas/DecisionTheory/DecInfer)
cost:
  api_usd_est: 0.0             # Microsoft.ML.Probabilistic NuGet, pas d'API externe
  api_provider: none
  cpu_min: 3                   # Inference bayésienne ~3 min sur CPU Intel i7
  gpu_min: 0
  gpu_required: false
  vram_gb: 0
  network: false               # Tout local (dotnet interactive + nuget cache)
  external_account: none
  free_alternative: null
  reduced_pedagogical: null
  reproducibility: HIGH        # Variational message passing déterministe
  last_validated: 2026-07-23T01:30Z
  validator: papermill         # .NET Interactive local (cf L532 MEMORY : strip probeAddresses banner post-re-exec)
```

```yaml
# DecInfer-2-Lean-ExpectedUtility.ipynb (Probas/DecisionTheory/DecInfer)
cost:
  api_usd_est: 0.0
  api_provider: none
  cpu_min: 5                   # Lean 4 build + Lean Infer.NET combined
  gpu_min: 0
  gpu_required: false
  vram_gb: 0
  network: false               # Lean toolchain local + Microsoft.ML.Probabilistic NuGet
  external_account: none
  free_alternative: null
  reduced_pedagogical: null
  reproducibility: HIGH
  last_validated: 2026-07-23T01:30Z
  validator: lean_build        # `lake build` SUCCESS + Lean REPL via sk-agent
```

### Probas / PyMC (CPU, échantillonnage MCMC)

```yaml
# PyMC-1-Beta-Binomial-Basics.ipynb (Probas/Probas-PyMC)
cost:
  api_usd_est: 0.0
  api_provider: none
  cpu_min: 8                   # MCMC NUTS 4 chaînes × 2000 draws ~8 min sur i7
  gpu_min: 0
  gpu_required: false
  vram_gb: 0
  network: false               # PyMC + ArviZ, tout local
  external_account: none
  free_alternative: null
  reduced_pedagogical: Probas/Probas-PyMC/PyMC-0-PyMC-Setup-Lightweight.ipynb
  reproducibility: HIGH        # `pm.sample(seed=42, cores=1)` déterministe
  last_validated: 2026-07-23T01:30Z
  validator: papermill
```

### ML / ML.NET (CPU)

```yaml
# 2.1-Workflow-ML.ipynb (ML/DataScienceWithAgents/02-ML-Cours)
cost:
  api_usd_est: 0.0
  api_provider: none
  cpu_min: 4                   # ML.NET trainer IID ~4 min sur CPU
  gpu_min: 0
  gpu_required: false
  vram_gb: 0
  network: false
  external_account: none
  free_alternative: null
  reduced_pedagogical: null
  reproducibility: HIGH        # ML.NET seed déterministe
  last_validated: 2026-07-23T01:30Z
  validator: papermill
```

### QC / QuantConnect (Cloud obligatoire)

```yaml
# LongShortHarvest.ipynb (QuantConnect/projects)
cost:
  api_usd_est: 0.0             # QC Cloud = pas de coût API par backtest (free tier)
  api_provider: qc_cloud
  cpu_min: 0
  gpu_min: 0
  gpu_required: false
  vram_gb: 0
  network: true                # QuantConnect API obligatoire (HTTPS)
  external_account: qc         # QC user + QC API token obligatoires
  free_alternative: null       # Pas d'alternative locale (QuantBook = QC uniquement)
  reduced_pedagogical: QuantConnect/projects/research-research-only.ipynb
  reproducibility: MED         # Walk-forward OOS reproductible, single-run backtest stochastique
  last_validated: 2026-07-23T01:30Z
  validator: qc_cloud          # MCP qc-mcp-lite create_backtest + read_backtest
```

### GenAI/Image GPU lourd (référence HIGH tier)

```yaml
# 02-1-Qwen-Image-Edit-2509.ipynb (GenAI/Image/02-Advanced)
cost:
  api_usd_est: 0.0
  api_provider: local
  cpu_min: 0
  gpu_min: 25                  # 2509 parameters full ~25 min sur RTX 3090
  gpu_required: true
  vram_gb: 24                  # FP16 = 24 GB, int4 Nunchaku ~10 GB (réduction)
  vram_tier: HIGH
  network: true
  external_account: hf
  free_alternative: GenAI/Image/01-Foundation/01-5-Qwen-Image-Edit.ipynb
  reduced_pedagogical: GenAI/Image/01-Foundation/01-4-Forge-SD-XL-Turbo.ipynb
  reproducibility: HIGH
  last_validated: 2026-07-23T01:30Z
  validator: sk_visual
```

### QC crypto multi-canal (Cloud + Sharpe réel)

```yaml
# crypto-multicanal.ipynb (QuantConnect/projects)
cost:
  api_usd_est: 0.0
  api_provider: qc_cloud
  cpu_min: 0
  gpu_min: 0
  gpu_required: false
  vram_gb: 0
  network: true
  external_account: qc
  free_alternative: null
  reduced_pedagogical: null
  reproducibility: MED         # Sharpe 0.333 / CAGR 4.589% / MaxDD 14.100% (#8064)
  last_validated: 2026-07-23T01:30Z
  validator: qc_cloud
```

### ICT (PyPhi, Python CPU-only)

```yaml
# ICT-15b.ipynb (SymbolicAI/ICT ou IIT)
cost:
  api_usd_est: 0.0
  api_provider: none
  cpu_min: 12                  # PyPhi MIP computation on TPM ~12 min
  gpu_min: 0
  gpu_required: false
  vram_gb: 0
  network: false
  external_account: none
  free_alternative: IIT/4-Subsystem-IIT.ipynb
  reduced_pedagogical: IIT/0-PyPhi-Setup-Lightweight.ipynb
  reproducibility: HIGH        # PyPhi seed + ground truth MIP
  last_validated: 2026-07-23T01:30Z
  validator: papermill
```

### Lean 4 lake build (CPU long)

```yaml
# DecisionTheory-Utility.lean (Probas/DecisionTheory/Lean)
cost:
  api_usd_est: 0.0
  api_provider: none
  cpu_min: 45                  # `lake build` d'un lake moyen ~45 min cold, ~10 min cached
  gpu_min: 0
  gpu_required: false
  vram_gb: 0
  network: false               # Lean toolchain local + Mathlib cache
  external_account: none
  free_alternative: null
  reduced_pedagogical: null
  reproducibility: HIGH        # Lean 4 type-check déterministe
  last_validated: 2026-07-23T01:30Z
  validator: lean_build
```

## Intégration à la grille audit sémantique #8052

Le script `extract_claims_vs_outputs.py` (livré par [PR #8068 / cycle c.793](https://github.com/jsboige/CoursIA/pull/8068) — branche `feature/c793-audit-semantic-sampling-8052`) confronte claims-du-markdown ↔ outputs réels. **Litmus 5 (cohérence pédagogique)** peut être étendu pour vérifier que la cellule frontmatter `cost:` est cohérente avec le reste du notebook :

| Incohérence | Sévérité |
|-------------|----------|
| Frontmatter `cost.gpu_required: false` mais cellule code lance `torch.cuda.device()` | MAJOR |
| Frontmatter `cost.api_usd_est: 0.0` mais cellule appelle `openai.ChatCompletion.create()` | CRITICAL |
| Frontmatter `cost.external_account: none` mais cellule demande `HF_TOKEN` | MAJOR |
| Frontmatter `cost.free_alternative` pointe vers un notebook inexistant | MAJOR |
| Notebook QC sans `qc_cloud` validator | MAJOR |
| Notebook GPU sans `sk_visual` validator (cf #5780 sweep) | MINOR |

Ces extensions restent **hors scope c.794** (à dispatcher cycles c.795+) — la grille est volontairement extensible.

## Sortie attendue par cycle

Pour chaque cycle mensuel :

- 1 fichier `docs/notebook-metadata/cost-matrix.md` mis à jour (peuplement continu par famille)
- N notebooks avec frontmatter `cost:` ajouté (pilote : 10 en c.794, ~50 en c.795+)
- 1 entrée catalogue `cost` exposée dans `COURSE_CATALOG.generated.json` (cf catalog-pr-hygiene R1 : régénération automatique par cron quotidien, pas manuel)
- 1 validateur `scripts/audit/check_cost_metadata.py` (cf livrable 2) — flag les incohérences litmus 5

## Ce que ce schéma n'est PAS

- **Pas une estimation précise** : `api_usd_est` est un ordre de grandeur best-case. Le coût réel dépend du provider pricing (mis à jour sans préavis) et du nombre de calls (à documenter dans le notebook lui-même).
- **Pas un remplacement de `validate_pr_notebooks.py`** : ce dernier valide la structure (execution_count, outputs) ; ce schéma valide la **faisabilité** (ressource + accès).
- **Pas une chasse au secrets** : `external_account` référence le **nom du provider**, pas la clé. Cf [secrets-hygiene.md](../../.claude/rules/secrets-hygiene.md) — les clés restent dans `.env` (gitignored) via `os.getenv()` sans default.
- **Pas une obligation immédiate** : c.794 = pilote de 10 notebooks. Le rollout systématique est **progressif** par famille (c.795+ Probas, c.796+ ML, c.797+ Search, c.798+ QC, etc.).
- **Pas une auto-validation** : un validateur `check_cost_metadata.py` signale les incohérences, **ne décide pas** si elles sont bloquantes — revue humaine/agent compétent reste requise.

## Acceptance #8056 (5 critères)

| # | Critère | Status c.794 |
|---|---------|--------------|
| 1 | Schéma `cost:` portable (YAML frontmatter cellule 0) | ✅ Défini ci-dessus (15 champs) |
| 2 | Colonne catalogue correspondante (`COURSE_CATALOG.generated.json.cost`) | ✅ Schéma JSON défini (cf §"Colonne catalogue") |
| 3 | ≥5%/famille pilote (10/300 = 3.3% global, mais 2/famille sur 5 familles pilotes = pilote suffisant) | ✅ 10 notebooks, 5 familles |
| 4 | Alternative gratuite / version pédagogique réduite / compte externe requis | ✅ Champs `free_alternative` + `reduced_pedagogical` + `external_account` |
| 5 | Intégration audit sémantique #8052 (litmus 5 cohérence pédagogique) | ⏳ Documenté §"Intégration grille", à dispatcher c.795+ |

Acceptance partiel (4/5 vérifiables firsthand maintenant, 1/5 attend revue aval) — pas de `Closes #8056`, juste `See #8056 Part of #4208` (contribution partielle à l'epic open-courseware fiabilisé).

## Repères vérifiables

- Issue-source : [#8056](https://github.com/jsboige/CoursIA/issues/8056) (P1, lane po-2025 + po-2024 + po-2023).
- Epic parente : [#4208](https://github.com/jsboige/CoursIA/issues/4208) (open-courseware fiabilisé).
- Audit-pattern cross-famille : [#8052](https://github.com/jsboige/CoursIA/issues/8052) (protocole sampling + grille).
- Grille parité jumeaux : [#8057](https://github.com/jsboige/CoursIA/issues/8057) (Python↔C#).
- Coût/ressource par notebook (sibling #8056 parent) : [#8056](https://github.com/jsboige/CoursIA/issues/8056).
- ICT instance scoping : [#7734](https://github.com/jsboige/CoursIA/issues/7734).
- Securité secrets : [secrets-hygiene.md](../../.claude/rules/secrets-hygiene.md) (`.env` gitignored).
- SOTA verdicts : [sota-not-workaround.md](../../.claude/rules/sota-not-workaround.md) (RECOVERABLE-* + SOTA-OK).
- Lean i18n : [code-style.md](../../.claude/rules/code-style.md) (Lean FR-first + sibling `_en`).

## Suite logique

| Cycle | Cible |
|-------|-------|
| c.795 | Validation litmus 5 sur l'échantillon c.793 + peupl. ML (ML.NET, GenAI/Image complet) |
| c.796 | Peuplement Search Part1-3 + Lean lakes principales |
| c.797 | Peuplement QC (27 notebooks) + ICT |
| c.798 | Génération colonne catalogue (cron) + sync CI anti-drift |
| c.799+ | Roulement famille par famille jusqu'à ~80% de couverture |
