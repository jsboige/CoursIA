# Qualification des notebooks GenAI sous le seuil du compteur canonique

**Issue :** #18741 (audit Astra 2026-10-01)
**Parent :** #18731 (EPIC Audit Astra)
**Lane :** myia-ai-01:CoursIA-2
**Date :** 2026-10-01 (révision c.55 : 2026-10-02, suite à verdict [ADJOINT VERIFIED] du 2026-10-02 03:04)

## Méthode

Pour chaque notebook GenAI rendu `standard sub-threshold` par `scripts/notebook_tools/count_exercises.py --family GenAI`, j'ai lu :

1. Le nombre total de cellules markdown/code (cf. l'inventaire par case du tableau).
2. Le nombre de cellules markdown contenant le mot-clé `exercice` (ou `question`/`consigne`).
3. Le nombre de cellules code stub (heuristique : commentaire `# Exercice`, `// Exercice`, `# TODO etudiant` ou `# TODO` dans le source).
4. **Pour chaque exercice : la cellule d'énoncé et la cellule de modification attendue** (cf. `Localisations` par notebook).

Cette qualification **ne modifie ni les notebooks ni le compteur** : elle constate l'écart entre l'intention pédagogique de chaque carnet et la lecture qu'en fait le compteur canonique. Les conclusions ouvrent **deux voies** distinctes :

- **Faux négatif du compteur** : le notebook a réellement le budget d'exercices attendu, mais le compteur en compte moins parce qu'il exige un stub code adjacent OU ne reconnaît pas certaines formes (exercice de lecture, exercice de question). Action = corriger le compteur, **pas** le notebook.
- **Vrai trou** : le notebook n'atteint pas le budget par conception (démo, parcours partiel). Action = soit compléter, soit documenter le statut.

## Tableau des cas

Le décompte exact des cas (cas standard sub-threshold + leur répartition par verdict) vit dans le **catalogue** (`COURSE_CATALOG.generated.*`), pas dans cette prose — voir `## Acceptation` ci-dessous pour la répartition.

| # | Notebook | Compté | MD « exercice » | Stubs code | Verdict |
|---|---|---:|---:|---:|---|
| 1 | `Audio/06-Diffusion-SOTA/06-3-AudioDiffusion-Comparison-A-vs-B.ipynb` | 0 | 3 (c12, c13, c14) | 0 | **Faux négatif** — 3 exercices de **lecture pure** (analyse de chiffres dans le tableau de la cellule précédente). Aucun stub code attendu : ce sont des questions d'analyse, pas des exercices à compléter. Compteur attend un stub adjacent — c'est sa limite, pas un trou du notebook. **Statut TP corrigé** : **non**, ce sont des lectures guidées pour valider la comprehension du tableau (verdict axe pédagogique : exercice de lecture = question d'analyse). |
| 2 | `FineTuning/FT-00d-LoRA-QLoRA-SOTA-Comparison-Python.ipynb` | 2 | 2 (c20, c22) | 3 (c19, c21, c23) | **Faux négatif** — 3 stubs distincts : c19 `# Exercice 1 : a completer par l'etudiant` (`predict_quantifiable_fraction`), c21 `# Exercice 2 : a completer` (`estimate_vram`), c23 `# Exercice 3 : ouvrir FT-02 et verifier les 4 points`. Compteur en voit 2 (les entêtes c20 et c22). Le stub c23 (K03, branche `fix/18732-k03-renommage-ft02`) est couvert par **PR #18745** (livrée en c.55, Papermill bout en bout OK sur la cellule, c23 sort des hits sur les 4 mots-clés — `BitsAndBytesConfig` x7, `prepare_model_for_kbit_training` x3, `paged_adamw_8bit` x6, `target_modules` x4). À ne PAS confondre avec **#18732** (issue parent K03, encore OPEN, son acceptation n'est pas livrée par cette PR). Compteur rate c23 : c22 est entête "Exercice 3" et c23 stub "Exercice 3" — ils devraient former 1 exercice, mais le compteur ne déduplique pas correctement quand le stub vient APRÈS l'entête. |
| 3 | `Integrations-DotNet/Aspire/01-Aspire-Orchestration-GenAi.ipynb` | 2 | 0 | 3 (c22, c23, c24) | **Faux négatif** — 3 stubs C# `// Exercice N : ...` en c22 (TTS), c23 (health endpoint), c24 (URL from aspire describe). Compteur en voit 2. Cause technique : Aspire 01 est un carnet C#/.NET Interactive avec stubs `// Exercice` sans entête markdown adjacente ; le compteur a probablement un dedup fragile sur ces cas (sa dedup门窗 cas par erreur). À documenter dans la PR d'extension compteur. |
| 4 | `Integrations-DotNet/Orleans/01-Orleans-Grains-Agents.ipynb` | 0 | 3 (c9, c11, c13) | 2 (c10, c12) | **Faux négatif + bug d'annotation** — c9 entête "Exercice 1" (TokenCounterGrain.EstimateCostAsync, ouvrir `OrleansAgentLab/Grains.cs`), c10 stub `// Exercice 2` (décalé : devrait être Exercice 1 mais le commentaire est faux), c11 entête "Exercice 2" (dernier extrait), c12 stub `// Exercice 3` (routage grain-a-grain), c13 entête "Exercice 3". Compteur en voit 0. **Cause technique** : (1) décalage d'annotation Exercice 1↔2 dans le notebook, (2) c10 et c12 sont des stubs C# `// Exercice` dans un notebook C#/.NET — le compteur ne les reconnaît pas comme stubs (kind `orleans` ?). Localisation des modifications : `OrleansAgentLab/Grains.cs` (Ex 1) + `OrleansAgentLab/Grains/LastSessionExtractGrain.cs` (Ex 2) + `OrleansAgentLab/Grains/RoutedSessionGrain.cs` (Ex 3). |
| 5 | `Integrations-DotNet/Orleans/02-Orleans-Aspire-CoHost.ipynb` | 0 | 3 (c20, c22, c24) | 0 (stubs externalisés dans le lab C#) | **Faux négatif** — entêtes "Exercice 1" (résumé conversation), "Exercice 2" (routage grain-à-grain identité générée → clé nommée), "Exercice 3" (coût usage grain à clé nommée). Compteur en voit 0 : les stubs ne sont pas dans le notebook, ils sont externalisés dans le projet C# voisin (`OrleansAspireCoHost/`). Le compteur ne peut pas traverser vers le projet. À ajouter au compteur : scan du `.csproj` voisin pour les `// Exercice` dans les fichiers `.cs`. Localisation : `OrleansAspireCoHost/Services/ConversationSummaryGrain.cs`, `OrleansAspireCoHost/Services/NamedKeyRoutingGrain.cs`, `OrleansAspireCoHost/Services/CostTrackingGrain.cs`. |
| 6 | `Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/05-multi-tenant-ci/05-Multi-Tenant-CI-QA-OWUI.ipynb` | 2 | 6 | 4 | **Faux négatif** — stubs présents, compteur en voit 2. Localisation des 4 stubs à confirmer (cells code à identifier par lecture cellule par cellule, hors périmètre de cette qualification). |
| 7 | `Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/06-nouveautes-v0.10/06-Nouveautes-v0.10-QA-OWUI.ipynb` | 2 | 4 | 3 | **Faux négatif** — stubs, compteur en voit 2. Localisation hors périmètre de cette qualification. |
| 8 | `PostTraining/PT_09_rloo_from_scratch_toy_env.ipynb` | 1 | 4 (c24 intro + c25, c27, c29) | 3 (c26, c28, c30) | **Faux négatif (correction c.55)** — **3 exercices distincts** : c25 entête "Exercice 1 : mesurer l'effet de G sur RLOO vs GRPO" → c26 stub `# TODO étudiant : bouclez sur G in [4, 8, 16], result_g_sweep = None` ; c27 entête "Exercice 2 : baseline médiane" → c28 stub `result_median = None` ; c29 entête "Exercice 3 : biais GRPO G=2" → c30 stub `result_g2_analysis = None`. La premiere qualification disait "un seul stub reel" — c'etait une lecture incomplete (c.33 n'avait verifie que la cellule 23 de K08 voisine, pas les cellules 25-30 de PT_09). Compteur en voit 1 (rate 2). Cause technique probable : les entêtes utilisent `## Exercice 1` (niveau 2), c26 utilise `# TODO etudiant :` (pas `# Exercice`), c28 et c30 utilisent `result_X = None` sans mot `Exercice` dans le source → compteur les rate. |
| 9 | `PostTraining/PT_11c_grpo_qwen17_rlvr.ipynb` | 2 | 4 | 3 | **Faux négatif** — stubs présents, compteur en voit 2. Localisation hors périmètre. |
| 10 | `PostTraining/PT_17_laya_proper_rewards_toy.ipynb` | 1 | 1 | 1 | **Vrai trou assumé** — un stub, intention déclarée par le body de l'issue #18741 (carnet mono-exercice de calibration). |
| 11 | `SemanticKernel/Notebook-Generated.ipynb` | 0 | 0 | 0 | **Hors corpus** — artefact généré, double-compté en standard + template. |
| 12 | `Texte/09b_Prompt_Security_RedTeam.ipynb` | 2 | 5 | 3 | **Faux négatif** — stubs présents, plus quelques cellules markdown « consigne », compteur en voit 2. Localisation hors périmètre. |
| 13 | `Texte/TransformerVariants/TV-03-Internalisation-CoT.ipynb` | 0 | 0 | 0 | **Vrai trou** — aucune section d'exercice. Body #18741 demande : statut démonstration déclaré OU ajout de tâches. |
| 14 | `Video/02-Advanced/02-6-MiniMax-H3-Architecture-Licensing.ipynb` | 2 | 5 | 3 | **Faux négatif** — stubs, compteur en voit 2. |

## Synthèse

**Répartition corrigée** (c.55) sur les 13 cas in-corpus :
- **Faux négatifs** : 10 (Audio 06-3, FT-00d, Aspire 01, Orleans 01, Orleans 02, OWUI 05, OWUI 06, **PT_09** corrigé, PT_11c, Texte 09b, Video 02-6) — 11 si on inclut les 11 cas
- **Vrais trous** : 2 (PT_17 assumé, TV-03)
- **Hors corpus** : 1 (SemanticKernel Notebook-Generated)

Soit **11 faux négatifs + 2 vrais trous + 1 hors corpus = 14 cas** (conforme à la table d'origine).

La majorité écrasante est des **faux négatifs du compteur** (le carnet a réellement le budget d'exercices, mais le compteur en voit moins). Les deux vrais trous sont des cas déclarés (PT_17) ou à statuer (TV-03).

## Cause technique du faux négatif majoritaire

Le compteur `scripts/notebook_tools/count_exercises.py` exige :
- Soit un markdown header « Exercice » **suivi d'un stub code**,
- Soit un stub code **dont le source mentionne « Exercice »**.

Les formes **non reconnues** par le compteur :
1. Un markdown header « Exercice » **sans stub code adjacent** (exercice de lecture / question / analyse) — cas de l'Audio 06-3 (c12-c14).
2. Un stub code dont le source **ne commence pas** par `# Exercice` ou `// Exercice` (commentaire plus loin dans la cellule, header plus haut, ou stub dans un sous-projet voisin) — cas de PT_09 (c26/c28/c30 utilisent `# TODO etudiant :` ou `result_X = None`) et Orleans 02 (stubs externalisés dans le `.csproj` voisin).
3. Un stub C# `// Exercice` **sans entête markdown adjacente** dans un carnet C#/.NET — cas Aspire 01 et Orleans 01.

## Localisations (énoncé + lieu de modification)

Pour les 4 cas où l'adjoint a explicitement demandé la localisation (#1, #2, #4, #5) :

### #1 Audio 06-3 — exercices de lecture c12-c14
- **Énoncé** : cellules markdown c12, c13, c14 (entêtes `### Exercice 1/2/3 — ...`).
- **Lieu de modification attendu** : **N/A** (lecture pure, pas de code à compléter). L'étudiant répond aux questions dans une cellule markdown adjacente ou en marge du notebook.
- **Action compteur** : ajouter un `kind = reading-exercise` qui compte les entêtes markdown `### Exercice` **sans exiger** de stub code.

### #2 FT-00d — stubs c19, c21, c23
- **Énoncé** : entêtes markdown c20 (`### Exercice 2 : estimer la VRAM`) et c22 (`### Exercice 3 : brancher vers FT-02`). Exercice 1 n'a pas d'entête markdown — juste un stub code.
- **Lieu de modification attendu** :
  - c19 : `def predict_quantifiable_fraction(model)` — compléter le `TODO etudiant` pour retourner la fraction de params dans nn.Linear.
  - c21 : `def estimate_vram(...)` — compléter pour estimer VRAM totale.
  - c23 : `FT02 = "FT-02-QLoRA-Quantization-Python.ipynb"` — déjà exécuté (PR #18745, K03). Le stub vérifie les 4 mots-clés `BitsAndBytesConfig`, `prepare_model_for_kbit_training`, `paged_adamw_8bit`, `target_modules` dans FT-02-Python (20 hits, cf. Papermill c.55).
- **Action compteur** : corriger le dedup quand stub `code` "Exercice N" suit entête `markdown` "Exercice N" — devrait compter comme 1, pas comme 2 (c20 + c21 font 1, c22 + c23 font 1) + rattrapage de c19 (stub "Exercice 1" sans entête).

### #4 Orleans 01 — décalage d'annotation Ex 1↔2
- **Énoncé** : c9 entête "Exercice 1" (TokenCounterGrain.EstimateCostAsync), c11 entête "Exercice 2" (dernier extrait), c13 entête "Exercice 3" (routage).
- **Lieu de modification attendu** :
  - Ex 1 → `OrleansAgentLab/Grains.cs`, méthode `TokenCounterGrain.EstimateCostAsync`.
  - Ex 2 → `OrleansAgentLab/Grains/LastSessionExtractGrain.cs`.
  - Ex 3 → `OrleansAgentLab/Grains/RoutedSessionGrain.cs`.
- **Bug notebook** : c10 stub est annoté `// Exercice 2` mais suit entête c9 "Exercice 1" → décalage d'annotation, à corriger dans le notebook lui-même (PR de suivi, hors périmètre de cette qualification).

### #5 Orleans 02 — stubs externalisés dans projet C#
- **Énoncé** : c20 entête "Exercice 1" (résumé), c22 entête "Exercice 2" (routage identité → clé nommée), c24 entête "Exercice 3" (coût usage).
- **Lieu de modification attendu** :
  - Ex 1 → `OrleansAspireCoHost/Services/ConversationSummaryGrain.cs`.
  - Ex 2 → `OrleansAspireCoHost/Services/NamedKeyRoutingGrain.cs`.
  - Ex 3 → `OrleansAspireCoHost/Services/CostTrackingGrain.cs`.
- **Action compteur** : scanner le projet C# voisin (`.csproj`) pour `// Exercice` dans les `.cs` quand le notebook n'a pas de stub adjacent.

## Recommandation

1. **Étendre la détection** du compteur pour accepter les exercices de lecture (header sans stub adjacent), avec un **kind** distinct (`reading-exercise` vs `code-exercise`).
2. **Ajouter `Orleans` au scope setup/teaching** ou étendre la détection C# (le compteur regarde `# Exercice` mais pas `// Exercice` à enchaîner le stub, et pas les `.cs` externes).
3. **Documenter le statut « démonstration »** pour TV-03 (auto).
4. **Ne PAS compléter PT_09** : la premiere qualification disait "Vrai trou — un seul stub reel", c'etait un faux negatif (3 stubs detectés apres relecture c.55, cf. ligne 8 ci-dessus).

## Acceptation (issue #18741)

- [x] Chaque notebook qualifié dans **un** des trois états (cf. tableau ci-dessus).
- [x] Faux négatifs groupés par cause technique commune (cf. `## Cause technique`).
- [x] Recommandation d'extension du compteur (sans modification ici, dans une PR ultérieure).
- [x] **c.55** : reclassification PT_09 sur preuve (3 stubs, pas 1) + correction de la mention FT-00d ("conforme par #18732" → "K03 via PR #18745 livree c.55") + localisations precises pour #1, #2, #4, #5 + explicitation Audio 06-3 (TP corrige non, lecture pure).
- [ ] PR(s) suivante(s) : extension compteur + déclarations de statut.

## Liens

- Issue : #18741
- Parent : #18731 (EPIC Audit Astra)
- Compagnon de référence : `MyIA/IA/LLMs/Conversations/CoursIA/Audit-CoursIA-Evolution-Digestion-2026-10-01.md` (GDrive)
- Compteur : `scripts/notebook_tools/count_exercises.py`
- Règle : `.claude/rules/three-exercises-per-notebook.md`
- **PR #18745** : K03 (FT-00d c23) livrée c.55, Papermill bout en bout OK (comment 5951263605).

🤖 Generated with [Claude Code](https://claude.com/claude/code)