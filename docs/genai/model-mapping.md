# Inventaire et table de correspondance — modèles GenAI/OpenAI (issue #14755, tranche 1)

> **Statut** : tranche 1/5 de #14755. Cadrage uniquement. Aucune substitution de notebook dans cette PR — la substitution était gelée tant que la table n'était pas validée contre l'API du fournisseur. **Gel levé le 2026-09-09** par la validation API (section 8).

## 1. Périmètre de mesure

Mesure firsthand sur `origin/main@c59dac98e` (2026-09-07) par `git grep -oE 'gpt-[0-9a-z.-]+'` filtré sur les répertoires `MyIA.AI.Notebooks/{GenAI,ML,SymbolicAI}` avec exclusion des fichiers `.md` (pour exclure la prose de catalogage et conserver les usages code) :

| Métrique | Valeur |
|---|---:|
| Fichiers GenAI/ML/SymbolicAI touchés | **124** |
| Occurrences `gpt-*` (toutes familles confondues, hors .md) | **~770** |

Le body initial de #14755 (rédigé 2026-09-05) annonçait 657 occurrences ; l'écart (~+110) provient des fichiers ré-exécutés qui ont capturé de nouveaux modèles en sortie — cohérent avec la dynamique rapide du paysage OpenAI septembre 2026.

## 2. Familles d'usage identifiées

| Famille | Endpoint API | Modèles dominants observés |
|---|---|---|
| **Chat principal** | `/v1/chat/completions` | `gpt-5-mini` (214), `gpt-5.2` (62), `gpt-5` (27), `gpt-5.5` (23), `gpt-5.1` (10), `gpt-5-nano` (17), `gpt-5-pro` (6) |
| **Chat legacy** | `/v1/chat/completions` | `gpt-4o-mini` (97), `gpt-4o` (72), `gpt-4.1-mini` (14), `gpt-4.1` (10), `gpt-4-turbo` (3), `gpt-4` (7), `gpt-3.5-turbo` (22) |
| **Image** | `/v1/images/generations` | `gpt-image-1` (151), `gpt-image` (21), `gpt-image-2` (2) |
| **STT (transcription)** | `/v1/audio/transcriptions` | `gpt-4o-transcribe` (23), `whisper-1` (~hors mesure — non préfixé `gpt-`) |
| **TTS** | `/v1/audio/speech` | `gpt-4o-mini-tts` (12), `gpt-4o-mini-tts-2025-03-20`, `gpt-4o-mini-tts-2025-12-15` |
| **Realtime** | `/v1/realtime` | `gpt-4o-realtime-preview` (10) |
| **Codex / code** | `/v1/chat/completions` (mode code) | `gpt-5.3-codex` (3), `gpt-5.1-codex-mini` (1), `gpt-5.1-codex-max` (1), `gpt-5.1-codex` (1), `gpt-5.2-codex` (1) |
| **OpenRouter (passerelle)** | `https://openrouter.ai/api/v1` | `openai/gpt-5.5-pro`, `openai/gpt-5.4-pro`, `openai/gpt-5.4-image-2`, `openai/gpt-5.3-codex`, `openai/gpt-5.2-codex`, etc. (~26 modèles `gpt-5*` listés dans `01-2-GPT-5-Image-Generation.ipynb`) |

> **Note sur la nomenclature OpenRouter** : OpenRouter préfixe chaque identifiant par `openai/` et expose parfois des **variantes non-officielles** (sous-numérotation `.5`, `.5.5`, suffixes `codex-max`, `image-2`). Le paysage officiel OpenAI n'expose pas toutes ces variantes ; une vérification contre `GET https://api.openai.com/v1/models` est indispensable avant toute substitution.

## 3. Table de correspondance — état actuel et cibles pressenties

> **Légende** :
> - **OBS** = obsolète pressenti (à substituer après validation API)
> - **CUR-OFF** = courant officiel OpenAI (à conserver)
> - **CUR-OR** = courant OpenRouter (passerelle, nomenclature non-officielle)
> - **PED** = conservation pédagogique délibérée (modèles historiques dans le cadre d'un cours)

| Identifiant | Famille | Hits | Statut | Cible pressentie | Action tranche 2+ |
|---|---|---:|---|---|---|
| `gpt-5-mini` | Chat | 214 | CUR-OFF | (canonique) | Conserver |
| `gpt-image-1` | Image | 151 | CUR-OFF | (canonique) | Conserver |
| `gpt-5.2` | Chat | 62 | CUR-OFF* | à valider | Vérifier API |
| `gpt-5.5` | Chat | 23 | CUR-OR* | à valider | Vérifier OpenRouter ET API |
| `gpt-5` | Chat | 27 | CUR-OFF | (canonique) | Conserver |
| `gpt-5-nano` | Chat | 17 | CUR-OFF* | à valider | Vérifier API |
| `gpt-5.1` | Chat | 10 | CUR-OR* | à valider | Vérifier OpenRouter |
| `gpt-5-pro` | Chat | 6 | CUR-OFF* | à valider | Vérifier API |
| `gpt-5-thinking` | Chat | 5 | CUR-OR | à valider | Vérifier OpenRouter |
| `gpt-5.4-pro` | Chat OR | 2 | CUR-OR | à valider | Vérifier OpenRouter |
| `gpt-5.4-image-2` | Image OR | 2 | CUR-OR | à valider | Vérifier OpenRouter |
| `gpt-5.4-mini` | Chat OR | 2 | CUR-OR | à valider | Vérifier OpenRouter |
| `gpt-5.4-nano` | Chat OR | 1 | CUR-OR | à valider | Vérifier OpenRouter |
| `gpt-5.4` | Chat OR | 1 | CUR-OR | à valider | Vérifier OpenRouter |
| `gpt-5.3-codex` | Codex | 3 | CUR-OR | à valider | Vérifier OpenRouter |
| `gpt-5.3-chat` | Chat OR | 1 | CUR-OR | à valider | Vérifier OpenRouter |
| `gpt-5.2-pro` | Chat OR | 1 | CUR-OR | à valider | Vérifier OpenRouter |
| `gpt-5.2-codex` | Codex OR | 1 | CUR-OR | à valider | Vérifier OpenRouter |
| `gpt-5.2-chat` | Chat OR | 1 | CUR-OR | à valider | Vérifier OpenRouter |
| `gpt-5.1-codex-mini` | Codex OR | 1 | CUR-OR | à valider | Vérifier OpenRouter |
| `gpt-5.1-codex-max` | Codex OR | 1 | CUR-OR | à valider | Vérifier OpenRouter |
| `gpt-5.1-codex` | Codex OR | 1 | CUR-OR | à valider | Vérifier OpenRouter |
| `gpt-5.5-pro` | Chat OR | 3 | CUR-OR | à valider | Vérifier OpenRouter |
| `gpt-5-2025-08-07` | Chat | 8 | CUR-OFF | (snapshot daté) | Conserver (point de version) |
| `gpt-5-chat-latest` | Chat | 2 | CUR-OFF* | à valider | Vérifier API |
| `gpt-5-pro` | Chat | 6 | CUR-OFF* | à valider | Vérifier API |
| `gpt-5o-mini` | Chat | 5 | OBS probable | `gpt-5-mini` | Coquille `5o` au lieu de `5` ? à confirmer |
| `gpt-image-1.` | Image | 2 | OBS | `gpt-image-1` | Faute de frappe (point surnuméraire) |
| `gpt-image-2` | Image | 2 | CUR-OFF | (canonique) | Conserver |
| `gpt-4o-mini` | Chat legacy | 97 | OBS | `gpt-5-mini` | Substituer sauf contexte pédagogique |
| `gpt-4o` | Chat legacy | 72 | OBS | `gpt-5` | Substituer sauf contexte pédagogique |
| `gpt-4.1-mini` | Chat legacy | 14 | OBS | `gpt-5-mini` | Substituer |
| `gpt-4.1` | Chat legacy | 10 | OBS | `gpt-5` | Substituer |
| `gpt-4-turbo` | Chat legacy | 3 | OBS | `gpt-5` | Substituer |
| `gpt-4` | Chat legacy | 7 | OBS | `gpt-5` | Substituer sauf PED |
| `gpt-3.5-turbo` | Chat legacy | 22 | OBS | `gpt-5-mini` | Substituer sauf PED |
| `gpt-4o-transcribe` | STT | 23 | CUR-OFF | (canonique) | Conserver |
| `gpt-4o-mini-tts` | TTS | 12 | CUR-OFF | (canonique) | Conserver |
| `gpt-4o-realtime-preview` | Realtime | 10 | CUR-OFF preview | à vérifier | Snapshot à geler ou substituer |
| `gpt-image` (sans `-1`) | Image legacy | 21 | OBS probable | `gpt-image-1` | Vérifier (DALL-E résiduel ?) |
| `gpt-invalid-model` | — | 6 | PLACEHOLDER | à retirer | Probablement fixture de test |
| `gpt-realtime-d-openai-supporte-mcp-et-sip-97770.html` | — | 4 | FAUX POSITIF | — | URL dans prose, hors scope |

## 4. Conservations pédagogiques pressenties

Modèles à conserver **délibérément** même après substitution automatique, parce qu'ils enseignent une époque :

- `gpt-3.5-turbo` dans `MyIA.AI.Notebooks/GenAI/Texte/02-*` (chapitres sur l'évolution historique des LLM)
- `gpt-4-turbo` dans les notebooks de comparaison `gpt-4-turbo` vs `gpt-4o` (étude de la transition 2024)
- `dall-e-3` (DALL-E retiré, remplacé par `gpt-image-1`) — citations historiques uniquement

Liste à finaliser en tranche 2 par lecture cellule par cellule.

## 5. Vérifications à faire en tranche 2

1. **Lookup API OpenAI officielle** : `GET https://api.openai.com/v1/models` avec une clé active — lister les `id` commençant par `gpt-` ; pour chacun, marquer `CUR-OFF` confirmé, `OBS` confirmé, ou `INDÉTERMINÉ`.
2. **Lookup OpenRouter** : `GET https://openrouter.ai/api/v1/models` — vérifier la présence et le statut des 26 variantes `openai/gpt-5*` observées. Certaines peuvent être des alias d'OpenAI officiels, d'autres des fork de fournisseurs tiers (`openai/` est un préfixe de fournisseur dans la nomenclature OpenRouter).
3. **Coquilles confirmées** : `gpt-5o-mini` (5 occurrences) et `gpt-image-1.` (2 occurrences) — vérifier en lisant le contexte qu'il s'agit bien de fautes de frappe et non d'identifiants délibérés.
4. **Placeholders** : `gpt-invalid-model` (6 occurrences) — fixture de test, à exclure de la substitution.

## 6. Périmètre exclu de cette tranche

- **Substitution** : aucune (PR tranche 2+).
- **Re-exécution** : aucune (chaque PR tranche 2+ exécutera les notebooks substitués en aval).
- **Notebooks QC + Sudoku** : 3 fichiers mentionnés dans le body initial — périmètre étendu possible en tranche 5 (Config + scripts + QuantConnect).
- **Modèles non-OpenAI** (Anthropic, Qwen, Mistral) : hors scope (référencés dans d'autres issues de portée).

## 7. Liens

- Issue parente : #14755
- Claim lane : `myia-po-2023:CoursIA-2 -- paths: docs/genai/**` (2026-09-05T15:18:09Z)
- Découpage proposé : `GenAI/Texte + SemanticKernel` (tranche 2), `GenAI/Audio` (tranche 3), `ML + SymbolicAI` (tranche 4), `Config + scripts + QC` (tranche 5)
- PRs connexes observées :
  - #14851 MERGED 2026-09-06 : `fix(genai,#14838): prepare_for_api garantit max_size_kb` — gel des substitutions de modèle tant que la table canonique n'est pas publiée.
  - #15018 OPEN : `feature/14664-local-llama-coherence` — concerne `GenAI/Texte/10_LocalLlama.ipynb`, hors `docs/genai/**`, ne bloque pas la tranche 1.

## 8. Validation API — tranche 2, 2026-09-09 (gel levé)

Lookups exécutés firsthand le 2026-09-09 : `GET https://api.openai.com/v1/models` (HTTP 200, clé du `.secrets/master.env`) → **99 identifiants `gpt-*`** ; `GET https://openrouter.ai/api/v1/models` (HTTP 200, endpoint public) → **82 variantes `openai/gpt-*`**.

### 8.1 Ligne courante — la famille `gpt-5.6` confirme le mandat user

L'API officielle sert **`gpt-5.6-luna`**, `gpt-5.6-sol`, `gpt-5.6-terra` (chacun doublé d'une variante `-pro` ; toutes présentes aussi sur OpenRouter). Le mandat user (« On en est à 5.6 pour OpenAI, version Luna pour la taille mini ») est donc confirmé au sens propre :

| Tier | Cible validée | Note |
|---|---|---|
| Mini (ex-`gpt-4o-mini`) | **`gpt-5.6-luna`** | désignée par le mandat user lui-même |
| Standard (ex-`gpt-4o`) | `gpt-5.6-sol` pressenti | à trancher à la première substitution en lecture pédagogique (luna/sol/terra = mini/standard/large est l'ordonnancement attendu, non une donnée de l'API — les deux lookups ne portent pas de métadonnée de tier) |

Les cibles « pressenties » de la section 3 (`gpt-5-mini`, `gpt-5`) restent **servies** par l'API mais ne sont plus la ligne courante : elles deviennent des cibles de repli pour les contextes où un alias stable prime sur la fraîcheur (ce choix reste pédagogique, par notebook).

### 8.2 Statuts « à valider » — verdicts

Tous les `CUR-OFF*` de la section 3 sont **confirmés présents** sur l'API officielle : `gpt-5.2` (+`-pro`, `-codex`, `-chat-latest`), `gpt-5.5` (+`-pro` — donc aussi officiel, pas seulement OpenRouter), `gpt-5` famille complète, `gpt-5.1` famille complète, `gpt-5.3` (`-chat-latest`, `-codex`), `gpt-5.4` famille complète, `gpt-5-pro`, `gpt-5-nano`, `gpt-5-chat-latest`, `gpt-5-2025-08-07`, `gpt-image-1`/`-1-mini`/`-1.5`/`-2`, `gpt-realtime-*` (dont `gpt-realtime-2.1`, `-translate`, `-whisper`). Les variantes notées `CUR-OR` existent bien sur OpenRouter (`openai/gpt-5.4-image-2`, `openai/gpt-5.2-chat`, etc.).

### 8.3 Correction de la table tranche 1 — deux lignes résolues

- **`gpt-5o-mini` (5 hits) = coquille confirmée** : toutes les occurrences sont `"openai/gpt-5o-mini"` dans `GenAI/Image/01-Foundation/01-3-Basic-Image-Operations.ipynb` (et son `_output`) ; aucun `gpt-5o*` n'existe ni côté OpenAI ni côté OpenRouter. Correction : `openai/gpt-5-mini`. **Hors tranche 2** (famille Image) — à corriger dans la tranche qui couvre Image.
- **`gpt-image-1.` (2 hits) = FAUX POSITIF de la mesure tranche 1** : les deux occurrences sont le **point final d'une phrase française** en prose (« … l'exécution réelle utilisant gpt-image-1. ») — pas un identifiant. La ligne est retirée du périmètre ; aucun identifiant `gpt-image-1.` n'existe dans le dépôt.

### 8.4 Nuance d'honnêteté sur « OBS »

`gpt-4o`, `gpt-4o-mini`, `gpt-4.1*`, `gpt-4-turbo`, `gpt-4`, `gpt-3.5-turbo` sont **toujours servis** par `/v1/models` au 2026-09-09. « OBS » signifie donc ici **supplanté pédagogiquement** (mandat user : ne pas enseigner des modèles de 2024), **pas** retiré de l'API. Les substitutions restent donc motivées par le mandat, et une cellule substituée qui échouerait sur l'ancien identifiant n'est pas un scénario attendu.

### 8.5 Inventaire tranche 2 — `GenAI/Texte + GenAI/SemanticKernel`

Compte strict des identifiants OBS (hors conservations §4) par fichier, `origin/main@e6ddf5828` :

| Fichier | Hits OBS |
|---|---:|
| `SemanticKernel/07-SemanticKernel-MultiModal.ipynb` | 8 |
| `SemanticKernel/10b-SemanticKernel-NotebookMaker-batch-parameterized.ipynb` | 8 |
| `SemanticKernel/10-SemanticKernel-NotebookMaker.ipynb` | 5 |
| `SemanticKernel/10a-SemanticKernel-NotebookMaker-batch.ipynb` | 5 |
| `Texte/7_Code_Interpreter.ipynb` | 5 |
| `SemanticKernel/03-SemanticKernel-Agents.ipynb` | 4 |
| `SemanticKernel/01-SemanticKernel-Intro.ipynb` | 4 |
| `Texte/6_PDF_Web_Search.ipynb` | 3 |
| `Texte/19_OWUI_Orchestration.ipynb` | 2 |
| `SemanticKernel/02-SemanticKernel-Advanced.ipynb` | 2 |
| `Texte/22_Evaluating_Generated_Text.ipynb` | 1 |
| `Texte/1_OpenAI_Intro.ipynb` | 1 |

Exclusions de périmètre : `SemanticKernel/semantic-fleet/**` (sous-module — commit dedans + bump pointeur, tranche dédiée), `Texte/10_LocalLlama.ipynb` (PR #15018 ouverte), `*_output.ipynb` (artefacts d'exécution non trackés), placeholders `gpt-invalid-model` (fixtures). La lecture cellule par cellule (§4, conservations pédagogiques) reste due **avant chaque substitution** — les compteurs ci-dessus situent la charge, ils ne qualifient pas chaque occurrence.
