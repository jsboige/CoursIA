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

## Schéma `cost:` — `nb.metadata['cost']` (JSON, forme canonique)

**Forme canonique (design-gate c.866, #8056).** Chaque notebook pédagogique DOIT
exposer sa matrice de coût dans **`nb.metadata['cost']`** (objet JSON, invisible
au rendu markdown). C'est la seule forme propre : une cellule markdown portant un
bloc `---\n...\n---` est promue par markdown-it en **setext-H2 supersize**
(défaut de rendu que le guard `#8352` bloque en ERROR). L'exemplar de référence =
[`Infer-3-Factor-Graphs`](../../MyIA.AI.Notebooks/Probas/Infer/Infer-3-Factor-Graphs.ipynb)
+ `Infer-4-Bayesian-Networks` (PR #8323).

```json
// nb.metadata["cost"] — l'objet JSON sérialisé par le notebook (.ipynb = JSON).
{
  "api_usd_est": 0.40,            // Coût API estimé par exécution end-to-end (USD). 0 si gratuit, null si inconnu. Cf §"Attribution multi-fournisseur".
  "api_provider": "openai",       // openai | anthropic | mistral | hf | replicate | google | local | none
  "api_cost_breakdown": null,     // OPTIONNEL. Ventilation provider→USD, somme == api_usd_est (gate falsifiable). Cf §"Attribution multi-fournisseur".
  "qcc_tokens_est": 0,            // QuantConnect Cloud compute tokens (QCC) estimés par exécution end-to-end. 0 si non-QC. Cf §"Coût QCC / QuantConnect".
  "cpu_min": 1,                   // Estimation CPU-only minutes (range ou best-case)
  "gpu_min": 0,                   // Estimation GPU minutes (range ou best-case)
  "gpu_required": false,          // true si impossible sans GPU
  "vram_gb": 0,                   // VRAM minimum (GB), ex: 12, 24, ou range "16-24"
  "vram_tier": "LITE",            // Catégorie VRAM (cf table §"Tiers VRAM")
  "network": true,                // Accès réseau requis (téléchargement modèle, appel API)
  "external_account": "openai",   // Compte externe obligatoire (openai, anthropic, hf, qc, ...) | "none"
  "free_alternative": null,       // Chemin repo-relatif vers un notebook équivalent sans coût, sentinel canonique, ou null. Cf §"Sentinels de `free_alternative`".
  "reduced_pedagogical": null,    // Version pédagogique réduite (sous-ensemble ou mock) | null
  "reproducibility": "HIGH",      // HIGH=déterministe, MED=seed-dépendant, LOW=stochastique
  "metadata_written": "2026-07-24", // Date d'établissement de la metadata (ISO8601), pas la date de validation
  "validator": "papermill",       // papermill | qc_cloud | manual | lean_build | sk_agent | sk_visual
}
```

> Le champ `title` (présent dans l'ancienne forme YAML) est **retiré** : redondant
> avec le titre H1 du notebook. Les valeurs sont identiques à l'ancien schéma YAML
> (seul le **lieu de stockage** change : JSON metadata au lieu de cellule markdown).

### Migration & backward-compat

La migration de masse des ~100 notebooks existants se fait **par tranches famille**
(rollout c.795/796/797 pattern), chaque lane migrant sa famille opportuniste. Le
vérificateur [`check_cost_metadata.py`](../../scripts/audit/check_cost_metadata.py)
lit **`metadata['cost']` d'abord**, retombe sur le scan de cellule `---...---` en
**fallback** (backward-compat) — les deux formes coexistent pendant la transition,
l'ordre de migration est non-bloquant. À terme, toutes les cellules `---`-YAML
sont retirées (elles déclenchent le guard `#8352`).

**Divulguation coût côté étudiant (OPTIONNELLE).** La matrice `metadata.cost` est
machine-only (invisible). Si on souhaite la surface à l'étudiant, une **petite
table markdown rendue** ou un **badge** suffit — jamais reproduire le YAML brut :

```markdown
> 💰 **Coût** : gratuit (CPU local, ~3 min). Pas de compte externe requis.
```

Ne pas sur-scoper 100 notebooks avec une table rendue — `metadata.cost` reste la
source de vérité, le badge est un confort de lecture.

### Champs obligatoires vs optionnels

| Champ | Obligatoire | Défaut si omis |
|-------|-------------|----------------|
| `cost.api_usd_est` | ✓ | `0` |
| `cost.api_provider` | ✓ | `"none"` |
| `cost.api_cost_breakdown` | optionnel | `null` (multi-fournisseur seulement ; `sum == api_usd_est` vérifié) |
| `cost.qcc_tokens_est` | optionnel | `0` (0 = non-QC ; à peupler pour tout quantbook QC Cloud) |
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
| `cost.metadata_written` | ✓ | (date d'établissement de la metadata) |
| `cost.validator` | ✓ | `"manual"` |

### Attribution multi-fournisseur (`api_cost_breakdown`)

**Décision de schéma (design-gate #8056, issuecomment 5106409423) : scalaire
autoritatif + ventilation optionnelle et falsifiable.**

`api_usd_est` reste **le** champ autoritatif — c'est lui que lisent les
consommateurs (agrégats, catalogue, badges). `api_cost_breakdown` est un champ
**optionnel** qui ventile le coût par fournisseur quand cette information est
réellement connue (plusieurs endpoints payants dans le même notebook) :

```json
"api_usd_est": 0.42,                 // TOTAL autoritatif, obligatoire
"api_cost_breakdown": {              // optionnel
  "openai": 0.30,
  "anthropic": 0.12
}
```

**Règle falsifiable (la seule qui compte) :** quand `api_cost_breakdown` est
présent, `sum(valeurs)` **doit égaler** `api_usd_est`. Vérifié par
`check_cost_metadata.py` (Litmus 8) — un écart > 1 cent déclenche le finding
`api_cost_breakdown_sum_mismatch`.

Pourquoi exiger la somme plutôt que laisser la ventilation libre ? Une
ventilation libre est **décorative** : personne ne peut la contredire, elle se
périme en silence au premier drift. Une ventilation dont la somme doit égaler
le total est **falsifiable** — elle casse le jour où elle ment. Même leçon que
le README central (`#8678` : un compteur nu se périme ; un compteur avec son
dénominateur se contredit tout seul) et que le gate de preuve Lean (`#8680` :
un gate incapable d'échouer n'est pas un gate).

**Quand l'écrire :**
- Notebook multi-fournisseur dont les sous-totaux par provider sont réellement
  mesurés (ex : un notebook qui appelle GPT-5 pour le raisonnement **et**
  Claude pour la vérification, coûts séparés dans les logs).

**Quand NE PAS l'écrire (règles d'or) :**
- **Mono-fournisseur** : écrire la ventilation dupliquerait le total pour zéro
  information, et fabriquerait 327 occasions de drift. On laisse `null`.
- **Sous-totaux reconstitués à la louche** : une fausse précision sur une
  estimation `validator: "manual"` est pire que l'absence. On laisse `null` et
  on documente la raison dans `notes` si pertinent.

**`0.0` vs `null` sur `api_usd_est` (corollaire) :**
- `0.0` **affirme** la gratuité (notebook local, pas d'appel facturé). C'est un
  énoncé positif.
- `null` (+ raison) = coût **inconnu**. Ne pas confondre : `0.0` n'est pas un
  défaut pour « je ne sais pas », l'absence se lirait à tort comme gratuite.

### `validator` / `metadata_written` — la seconde règle falsifiable (Litmus 9)

> **Note terminologique (#8843)** : ce champ s'appelait `last_validated` jusqu'au
> 2026-07-29. Le nom suggérait à tort une date de validation, alors que les
> populators écrivent `metadata_written: date.today()` au moment du *peuplement*
> — pas au moment d'une validation. Le nouveau nom (`metadata_written`) reflète
> honnêtement la sémantique : c'est la date d'établissement de la metadata, pas
> un horodatage de validation. La règle falsifiable du Litmus 9 reste la même :
> c'est `validator` qui affirme l'exécution, et c'est contre `validator` que
> s'applique le prédicat, pas contre `metadata_written` (qui est décoratif).

Ces deux champs s'articulent ainsi : `validator` *affirme* qu'une validation a
eu lieu (papermill, QC Cloud, manuel, etc.), `metadata_written` *horodate*
l'établissement de la metadata. Jusqu'au Litmus 9, **rien dans le dépôt ne
pouvait contredire `validator`** : aucun consommateur ne relisait son affirmation
contre l'état réel du notebook. Un champ `validator` que rien ne peut contredire
est **décoratif** : il porterait la même valeur sur un notebook dont *aucune*
cellule n'a jamais tourné.

**Règle falsifiable :** quand `validator` affirme une **exécution de cellules**
(`papermill`, `sk_visual`, `dotnet-interactive`), aucune cellule code non vide ne
doit porter `execution_count: null`. Le fondement est mécanique : nbclient/papermill
exécutent **toute** cellule code non vide — y compris celles qui échouent
(`--allow-errors` ne change que le comportement d'arrêt, pas l'attribution du
compteur). Donc `execution_count: null` **prouve** la non-exécution. Vérifié par
`check_cost_metadata.py` (Litmus 9) → finding `validator_asserts_execution_but_cells_unexecuted`
(MAJOR).

**Validators hors périmètre, délibérément :**

| Validator | Pourquoi il n'est pas contredit |
|---|---|
| `manual` | un humain a relu — aucune affirmation d'exécution. C'est aussi **la valeur de correction** pour un notebook non exécutable localement |
| `qc_cloud` | carve-out H.3 documenté — le runtime research QC n'existe sur aucune machine worker |
| `lean_build` | `lake build` SUCCESS porte sur le lake, pas sur les cellules |
| `sk_agent` | périmètre ambigu, pas d'affirmation nette |

**Échappatoire honnête (tag de skip).** Une cellule délibérément non exécutable —
code de référence destiné à un autre runtime — se **déclare** par un tag de cellule
(`skip-execution`, `skip`, `no-execute`). Le notebook cesse alors d'être contredit
sans mentir, et l'exemption est **visible dans le fichier**, contrairement à une
exception codée en dur dans l'outil. La contrepartie est la même que partout
ailleurs : on corrige la **déclaration**, ou on ré-exécute — **jamais** on n'édite
une sortie de cellule à la main (Stop & Repair, cf
[secrets-hygiene.md](../../.claude/rules/secrets-hygiene.md) règle 6).

> **Mesure à l'introduction (2026-07-29, 1020 notebooks scannés) :** 13 findings,
> tous `validator: papermill`, tous dans `QuantConnect/Python` — série dont chaque
> cellule code est du `[REFERENCE QC]` important `AlgorithmImports`, qui n'existe
> que dans le runtime QC. Ces notebooks sont couverts par le carve-out H.3 **par
> chemin** (`QC_CLOUD_PATHS`) alors qu'ils échappent au prédicat de contenu partagé
> (`QuantBook()`) : le carve-out excuse l'**absence** d'exécution, il n'autorise pas
> à en **affirmer** une. Correction attendue : `validator: manual`. Zéro finding sur
> les autres validators, y compris sur la tranche .NET en attente d'harmonisation
> (`Probas/Infer.NET`, `ML/ML.NET`) — ceux-là *ont* été exécutés, leur défaut est une
> étiquette inexacte, pas une exécution fantôme.

#### Mode flotte — agréger avant de résorber

Les neuf litmus n'avaient jusqu'ici qu'un mode **un notebook à la fois** : chacun
était donc appliqué à la main, par quiconque y pensait, et **personne n'avait
jamais agrégé le résultat**. Conséquence directe : un litmus vert ne pouvait pas
être distingué d'un litmus *jamais exécuté* — c'est le même angle mort que
« vert hors-cible ». `--all` / `--family` ferment cet écart (même prédicat,
marcheur canonique [`notebook_walk`](../../scripts/notebook_tools/notebook_walk.py), #8650) :

```bash
python scripts/audit/check_cost_metadata.py --all                 # flotte entière
python scripts/audit/check_cost_metadata.py --family QuantConnect # une famille
python scripts/audit/check_cost_metadata.py --all --json          # sortie machine
```

**Mesure d'introduction du mode (2026-07-29) : 941 notebooks scannés, 71 porteurs
d'au moins un finding, 86 findings sur 6 patterns** — `gpu_used_but_not_declared`
31, `gpu_no_visual_validator` 18, `token_required_but_no_account` 17,
`api_used_but_cost_zero` 13, `qc_notebook_no_qcc_estimate` 4,
`qc_notebook_no_validator` 3. Le **litmus 9 est à zéro** : les 13 findings mesurés
ci-dessus ont bien été corrigés en `validator: manual`, ils n'ont pas été
escamotés par le marcheur (contrôle indépendant sur `--family QuantConnect` :
`manual: 13`).

**Écart de population assumé, 1020 vs 941 :** la mesure du litmus 9 ci-dessus
parcourait le disque brut ; le mode flotte passe par `notebook_walk`, qui restreint
aux fichiers **suivis par git** (`tracked_only=True`) et écarte `_output.ipynb`,
`_archives/`, `.ipynb_checkpoints/`, `.lake/`. Les ~79 de différence sont des
sorties d'exécution, des archives et des notebooks non suivis — hors périmètre
d'un audit de métadonnées déclarées.

**Pas de `--check`, pas de câblage CI, délibérément.** Les 86 findings sont
**pré-existants** : un gate posé dessus naîtrait rouge et serait ignoré dès le
premier jour. L'ordre est *agréger → résorber → gater*, jamais l'inverse. C'est
d'ailleurs ce que dit déjà « [Ce que ce schéma n'est PAS](#ce-que-ce-schéma-nest-pas) » :
le validateur **signale**, il ne décide pas si l'incohérence est bloquante.
Résorber un pattern est un grain de substance séparé — et la correction se fait
**à la source** (ré-exécuter, ou corriger la déclaration), jamais en éditant une
sortie de cellule à la main.

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

### Sentinels de `free_alternative`

Le champ admet **deux natures** : un chemin repo-relatif, ou un **sentinel sémantique**. Le critère qui décide qu'un sentinel est canonique : **il porte une information que `null` détruit** (design-gate tranché sur #8056).

| Valeur | Statut | Sens |
|---|---|---|
| `<chemin repo-relatif>` | forme nominale | Un notebook du dépôt couvre le même sujet sans coût. Résolu en dual-base (racine du dépôt **ou** `MyIA.AI.Notebooks/`). |
| `self` | **canonique** | Ce notebook **est** l'alternative gratuite. Opposé de `null` — ne jamais normaliser vers `null`, ce serait lire 55 réponses positives comme 55 absences de réponse. |
| `ollama` | **canonique** | Un moteur local gratuit couvre le sujet. Aucun chemin du dépôt ne l'exprime. |
| `n/a` | toléré | Synonyme de `null`. Traité à l'identique par le checker ; pas de migration (coût non nul, gain nul). |
| `null` | forme nominale | Aucune alternative gratuite connue. |
| **service payant** (`openai`, `anthropic`, `replicate`, …) | **erreur** | C'est précisément le service dont on cherche à s'affranchir. Flaggé `free_alternative_is_paid_service` (MAJOR). |
| autre valeur non-chemin | **erreur** | Ne résout vers rien que le lecteur puisse suivre. Flaggé `free_alternative_unresolvable` (MINOR). |

Un **basename nu** (`10_LocalLlama.ipynb`) est un chemin imprécis, pas un sentinel : le lecteur ne peut pas le suivre et la dual-base ne le résout pas. Le checker ne le résout **pas** par `glob` sur l'arbre — ça ferait taire le finding sans corriger la référence, et deviendrait ambigu au premier basename partagé. **On répare la donnée, pas le détecteur.**

Implémentation : `scripts/audit/check_cost_metadata.py`, litmus 4.

## Peuplement pilote (cycle c.794)

5 familles × 2 notebooks = 10 entrées de référence (échantillon ≥5%/famille, conforme protocole #8052).

> **Note — syntaxe des exemples.** Les blocs ci-dessous sont en **YAML commenté**
> pour la lisibilité (le JSON canonique de `metadata['cost']` ne supporte pas les
> commentaires inline). Les **valeurs des champs** sont strictement identiques entre
> l'ancienne forme YAML cellule et la nouvelle forme `metadata.cost` JSON — seul le
> **lieu de stockage** change. En pratique, ces valeurs vont dans
> `nb.metadata['cost']` (objet JSON sérialisé par le `.ipynb`).

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
  metadata_written: 2026-07-23T01:30Z
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
  metadata_written: 2026-07-23T01:30Z
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
  metadata_written: 2026-07-23T01:30Z
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
  metadata_written: 2026-07-23T01:30Z
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
  metadata_written: 2026-07-23T01:30Z
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
  metadata_written: 2026-07-23T01:30Z
  validator: papermill
```

### .NET Interactive (profil canonique, cpu-only)

Un notebook **.NET Interactive** (kernel `.net-csharp` / `.net-fsharp`) sans
appel API n'a **pas le profil** d'un notebook Python appelant OpenAI. Le profil
canonique ci-dessous est celui à appliquer aux familles .NET cpu-only pures
(Sudoku solveurs, Search CSP, GameTheory twins C#) — il diffère du profil
Python+API sur trois points : `validator`, `vram_tier`, `free_alternative`.

```yaml
# Profil canonique .NET Interactive cpu-only (ex: Sudoku solveur, Search CSP)
cost:
  api_usd_est: 0.0
  api_provider: none
  cpu_min: 1
  gpu_min: 0
  gpu_required: false
  vram_gb: 0
  vram_tier: NONE              # cpu-only — c.888 canonical (PAS LITE)
  network: false
  external_account: none
  free_alternative: self       # le notebook local sans API EST son alternative gratuite
  reduced_pedagogical: null
  reproducibility: HIGH        # solveurs .NET déterministes (MEDIUM si stochastique)
  metadata_written: "2026-07-28T15:45Z"   # UTC obligatoire (cf leçon TZ : jamais local+Z)
  validator: manual
```

**`validator: manual` est la valeur canonique pour .NET.** Le kernel
`.net-csharp` s'exécute via `dotnet-interactive` headless local, **pas** via
papermill (qui ne pilote pas les kernels .NET Interactive par défaut). Écrire
`validator: papermill` suggère une validation automatisée absente — `manual`
est honnête : la re-exécution se fait via `dotnet-interactive` sur chaque
machine worker (cf `docs/reference/kernels-runtime.md`), le résultat est vérifié
à la main. La CI ne peut pas Papermill-exécuter les notebooks .NET (advisory
`#5214`) — `manual` reflète cette réalité.

**`vram_tier: NONE` pour cpu-only** (leçon c.888) : un notebook sans GPU doit
porter `NONE`, pas `LITE`. `LITE` décrit un besoin VRAM faible mais **réel**
(< 8 GB) ; un notebook cpu-only n'a **aucun** besoin VRAM. La table générale
« <8=LITE » s'applique aux notebooks GPU à faible VRAM, pas au cpu-only.

**`free_alternative: self`** : un notebook .NET local sans API payante **EST**
déjà gratuit — le sentinel `self` le dit (`null` signifierait à tort « aucune
alternative gratuite connue », cf §"Sentinels de `free_alternative`").

> **Note d'harmonisation (hors scope de ce PR).** Les profils historiques
> `Probas/Infer.NET` et `ML/ML.NET` ci-dessus portent `validator: papermill` et
> omettent `vram_tier: NONE`/`free_alternative: self`. Ils ont été migrés avant
> la formalisation de ce profil canonique. Leur harmonisation vers
> `validator: manual` se fait en tranche dédiée (pas un blanket-sweep — chaque
> notebook vérifié `api_provider: none` au passage).

### QC / QuantConnect (Cloud obligatoire)

```yaml
# LongShortHarvest.ipynb (QuantConnect/projects)
cost:
  api_usd_est: 0.0             # QC Cloud = pas de coût API par backtest (free tier)
  api_provider: qc_cloud
  qcc_tokens_est: 840          # ~70 QCC/cellule code (cf §"Coût QCC / QuantConnect")
  cpu_min: 0
  gpu_min: 0
  gpu_required: false
  vram_gb: 0
  network: true                # QuantConnect API obligatoire (HTTPS)
  external_account: qc         # QC user + QC API token obligatoires
  free_alternative: null       # Pas d'alternative locale (QuantBook = QC uniquement)
  reduced_pedagogical: QuantConnect/projects/research-research-only.ipynb
  reproducibility: MED         # Walk-forward OOS reproductible, single-run backtest stochastique
  metadata_written: 2026-07-23T01:30Z
  validator: qc_cloud          # MCP qc-mcp-lite create_backtest + read_backtest
```

#### Coût QCC / QuantConnect — pourquoi un champ dédié

QuantConnect Cloud facture l'exécution des quantbooks en **QCC tokens** (QuantConnect
Compute), une monnaie de quota propre au cloud QC — **non convertible en USD** et
**non gratuite** au-delà du free tier. Le champ `api_usd_est: 0.0` est donc
techniquement correct (pas de coût API *en USD*) mais **trompeur** sans
`qcc_tokens_est` : il présente le quantbook comme « gratuit » alors qu'il consomme
du quota QCC. `qcc_tokens_est` ferme ce gap en exposant le coût réel en quota QC.

**Estimation** (acceptance [#8056](https://github.com/jsboige/CoursIA/issues/8056) :
« sessions QuantConnect ≈ 800-1200 QCC tokens pour un notebook de 14 cellules ») :
heuristic dérivable **~70 QCC par cellule code**, plancher `max(400, n_code_cells × 70)`.
C'est une **estimation** (le suffixe `_est` l'atteste), pas une mesure — ré-estimer
après une exécution QC Cloud réelle (`read_backtest` retourne le QCC consommé). Le
litmus correspondant dans `check_cost_metadata.py` signale tout quantbook
(`QuantBook()` détecté) dont `qcc_tokens_est` est absent ou `0`.

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
  metadata_written: 2026-07-23T01:30Z
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
  metadata_written: 2026-07-23T01:30Z
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
  metadata_written: 2026-07-23T01:30Z
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
  metadata_written: 2026-07-23T01:30Z
  validator: lean_build
```

## Intégration à la grille audit sémantique #8052

Le script `extract_claims_vs_outputs.py` (livré par [PR #8068 / cycle c.793](https://github.com/jsboige/CoursIA/pull/8068) — branche `feature/c793-audit-semantic-sampling-8052`) confronte claims-du-markdown ↔ outputs réels. **Litmus 5 (cohérence pédagogique)** vérifie que la matrice `metadata['cost']` est cohérente avec le reste du notebook :

| Incohérence | Sévérité |
|-------------|----------|
| `metadata.cost.gpu_required: false` mais cellule code lance `torch.cuda.device()` | MAJOR |
| `metadata.cost.api_usd_est: 0.0` mais cellule appelle `openai.ChatCompletion.create()` | CRITICAL |
| `metadata.cost.external_account: none` mais cellule demande `HF_TOKEN` | MAJOR |
| `metadata.cost.free_alternative` pointe vers un notebook inexistant | MAJOR |
| `metadata.cost.free_alternative` nomme un **service payant** (`openai`, `anthropic`, …) | MAJOR |
| `metadata.cost.free_alternative` : valeur ni sentinel canonique ni chemin | MINOR |
| Notebook QC sans `qc_cloud` validator | MAJOR |
| Notebook GPU sans `sk_visual` validator (cf #5780 sweep) | MINOR |
| `metadata.cost.validator` affirme une exécution mais des cellules code portent `execution_count: null` (Litmus 9) | MAJOR |

Ces extensions restent **hors scope c.794** (à dispatcher cycles c.795+) — la grille est volontairement extensible.

## Sortie attendue par cycle

Pour chaque cycle mensuel :

- 1 fichier `docs/notebook-metadata/cost-matrix.md` mis à jour (peuplement continu par famille)
- N notebooks avec `metadata['cost']` ajouté (pilote : 10 en c.794, ~50 en c.795+)
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
| 1 | Schéma `cost:` canonique (`nb.metadata['cost']` JSON, cellule `---`-YAML retirée du mandat guard #8352) | ✅ Défini ci-dessus (14 champs, `title` retiré) |
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
