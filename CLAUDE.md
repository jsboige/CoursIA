# CLAUDE.md

Guidance for Claude Code working with the CoursIA repository.

---

## ⚠️ RÈGLE D'OR - Coordination Inter-Machines

**TOUTE coordination entre machines (po-2023, po-2026, etc.) DOIT se faire via RooSync**

### ❌ JAMAIS:
- Commit de rapports de coordination sur GitHub
- Messages via SSH
- Fichiers `*_TEST_REPORT.md`, `*_COORDINATION.md` dans le repo
- Tout fichier de coordination hors RooSync

### ✅ TOUJOURS:
- Thread RooSync pour toute coordination inter-machine
- Les messages RooSync sont persistants et suivis
- GitHub = code uniquement, pas de coordination

**VIOLATION DE CETTE RÈGLE = ERREUR CRITIQUE**

---

## RÈGLE - Traitement des missions dans l'ordre

**Les missions dispatchees par le coordinateur sont traitees dans l'ordre chronologique, sans demander a l'utilisateur de choisir.** Le coordinateur (ai-01) priorise via le dashboard RooSync. L'agent execute dans l'ordre et rapporte les resultats. Pas de AskUserQuestion pour le choix de missions.

---

## RÈGLE - RooSync Dashboard : toujours lire le contenu complet

Le **dashboard RooSync workspace CoursIA** (`roosync_dashboard` type=workspace, workspace=CoursIA) est le canal central de coordination cross-machine. Il contient le status du coordinateur (ai-01), les missions assignees, les resultats backtests, les decisions de consolidation, et l'intercom entre agents.

### Obligations lors d'un tour de coordination :
1. **Lire le contenu complet** du dashboard — l'API retourne parfois un JSON tronque en preview ("Output too large"). Dans ce cas, TOUJOURS utiliser `Read` sur le fichier persiste pour lire l'integralite.
2. **Verifier l'inbox** RooSync pour les messages directs non lus.
3. **Verifier le heartbeat** cluster pour savoir quelles machines sont actives.
4. **Si aucune mission assignee** : envoyer un message RooSync a ai-01 (coordinateur) pour demander des instructions. Ne pas attendre passivement.

### Ne JAMAIS :
- Resumer le dashboard a partir du seul preview tronque
- Omettre la lecture de l'intercom (contient l'historique des decisions)
- Se considerer "disponible" sans prevenir le coordinateur

---

## 🚨 RÈGLE CRITIQUE - Git Force Push INTERDIT

**INCIDENT 2026-03-13** : Force push accidentel sur main a potentiellement écrasé des commits

### ❌ JAMAIS:
- `git push --force` ou `--force-with-lease` sur main
- `git reset --hard` sur main sans validation
- Modifier l'historique public après publication

### ✅ TOUJOURS:
- Pour une PR : créer feature branch FROM main, ne pas reset main
- Utiliser cherry-pick, revert, ou nouveaux commits
- Demander validation explicite du user pour toute opération destructive
- En cas d'urgence extrême : user doit valider AVANT le force push

**Exception** : Uniquement urgence confirmée avec validation préalable du user

**Voir aussi** : `.claude/rules/git-workflow.md` pour les règles git complètes

**VIOLATION DE CETTE RÈGLE = ERREUR CRITIQUE**

---

## 🚨 RÈGLE CRITIQUE - Exigence et esprit critique (2026-04-20)

**INCIDENT 2026-04-20** : Un étudiant a remonté qu'un exercice Sudoku-8 Hidden Pair est confus/redondant avec Naked Pair ; la même session a révélé 20+ cellules de notebooks d'exercices aplaties en une seule ligne illisible, un agent ayant rapporté "DONE" alors que le travail contenait encore 7 cellules brisées.

**Diagnostic user** : "la moitié du dépôt est de la slop complaisante". L'agent review manque de scepticisme, merge des PRs sans lancer les notebooks ni vérifier la cohérence pédagogique, et propage des rapports de succès non vérifiés.

### ❌ INTERDIT : les mensonges de succès

- Rapporter "DONE" / "fixed" / "validated" sans avoir relancé la validation complète APRÈS le fix
- Mark un todo `completed` alors que même une seule itération de test n'a pas été passée
- Approuver une PR parce que "le CI est vert" — CI = syntaxe, pas pédagogie ni conformité
- Fermer une issue sans vérifier que le problème concret qu'elle décrit est résolu sur le code actuel
- Accepter les rapports d'autres agents sans recouper contre les faits (code, diff, exécution)
- Créer des fichiers markdown de "RAPPORT", "AUDIT", "SYNTHESE" comme preuve de travail sans que le code sous-jacent soit validé
- Répéter "propre" / "valide" / "clean" comme incantation sans preuve concrète

### ✅ OBLIGATOIRE : review exigeante d'une PR

Avant de merger une PR (y compris les siennes), VÉRIFIER les 5 points :

1. **Scope réel** : comparer la PR à l'objectif déclaré. La PR fait-elle ce qu'elle dit ? Rien de plus, rien de moins ?
2. **Validation automatisée complète** : script de validation qui CHECK le livrable (pas le code source), relancé APRÈS le dernier commit de la PR
3. **Cohérence pédagogique (notebooks/slides)** :
   - Les exercices sont-ils alignés sur le contenu enseigné au-dessus ?
   - Un exercice redemande-t-il ce qui est déjà résolu plus haut ?
   - Les stubs `TODO` ont-ils un sens (TODO bien placé, commentaires cohérents) ?
   - L'ordre des cellules est-il logique (interprétation APRÈS code) ?
4. **Exécution au moins une fois** :
   - Notebooks : exécuter via Papermill ou ouvrir dans Jupyter et lancer chaque cellule. "Compile OK" n'est PAS suffisant.
   - Slides : lancer Slidev et vérifier chaque slide avec `?clicks=99`.
5. **Regression check** : le fix a-t-il cassé autre chose ? (grep des symboles touchés dans le reste du dépôt)

Si un seul de ces 5 points n'est pas vérifié personnellement : **ne pas merger**. Demander le complément au user/auteur.

### ✅ OBLIGATOIRE : attitude sceptique envers soi-même

- Après un fix, RELANCER la validation complète. Ne jamais faire confiance à une correction "at sight"
- Lister les cas limites que la correction pourrait avoir manqués. Les tester.
- Un fix sur N fichiers nécessite N validations, pas 1
- Quand le user signale un problème pédagogique (redondance, incohérence, bug dans un exercice) : ne pas tenter de le justifier, investiguer et confirmer/infirmer factuellement
- Les retours étudiants sont des bugs à traiter, pas des "feedbacks à noter pour plus tard"
- Un bug préexistant dans un notebook d'enseignement est un bug à fixer (règle 2026-04-20)

### ✅ OBLIGATOIRE : honnêteté du rapport

- Si un fix a corrigé 5/7 cellules : rapporter "5/7 corrigées, 2 restantes identifiées mais non traitées", PAS "DONE"
- Mentionner explicitement les cas non testés, non validés, non vérifiés
- Si le user exprime de la déception ou parle de "honte" : reconnaître précisément ce qui a été raté, ne pas minimiser ni déborder en justifications
- Pas d'euphémismes : "bug" > "léger oubli", "cassé" > "perfectible"

**VIOLATION = le dépôt se remplit de slop et le cours part en vrille. Impact pédagogique réel.**

**Voir aussi** : `~/.claude/projects/d--CoursIA/memory/feedback_postmortem_epita_slides_20260408.md`, `feedback_exigence_application_20260408.md`, `feedback_no_preexisting_excuse.md`

---

## 🚨 RÈGLE CRITIQUE - Anti-régression : ne jamais effacer du travail existant sous prétexte de "fix" (2026-04-24)

**INCIDENT 2026-04-24** : Un commit prétendument "Mathlib compilation fixes" (`47975400`, merge PR #524) a remplacé **9 preuves structurelles fonctionnelles** d'Arrow.lean (`refl`/`total`/`trans` pour `maketop`/`makebot`/`makeabove`) par des `sorry`, et supprimé 3 proof sketches Geanakoplos 2005. -163 lignes nettes sur un port Lean qui avait coûté **une semaine de travail** en janvier 2026 (commit `1ce6a047`, port de [asouther4/lean-social-choice](https://github.com/asouther4/lean-social-choice)).

**Diagnostic user** : "Ou est-ce que c'est passé ? Encore remplacé par de l'AI slop ?" L'agent a confondu "faire passer la compilation" avec "supprimer ce qui ne compile pas". Pattern récurrent identifié : remplacer une preuve/implémentation par `sorry` / `pass` / `NotImplementedError` pour obtenir un état "qui compile" au lieu de **diagnostiquer pourquoi ça ne compilait plus**.

### ❌ INTERDIT : les régressions disguisées

- **Remplacer une preuve/implémentation fonctionnelle existante par `sorry`/`pass`/`NotImplementedError`/`return None`/stub vide** sans preuve explicite que la version précédente était cassée **et** que le fix tactique est hors de portée
- Commits "compilation fix" / "test fix" / "lint fix" / "Mathlib fix" / "typing fix" avec **deletions > insertions** sur du code métier — red flag systématique, investiguer avant tout autre geste
- Supprimer des commentaires pédagogiques (proof sketches, docstrings, notes d'implémentation) "pour simplifier" sans accord explicite
- Justifier la suppression par "le code ne compilait pas / ne passait pas les tests" sans citer l'erreur précise rencontrée
- Traiter les fichiers de vérification formelle (Lean, Coq, Agda, Z3) comme du code ordinaire : y introduire un `sorry` = **injection d'axiome** = perte de confiance totale dans le théorème
- Prétendre qu'un `rename` massif rend nécessaire de re-prouver tout : un rename (`P → prof`) se fait tactiquement sans toucher aux preuves

### ✅ OBLIGATOIRE : protocole de préservation

Avant tout commit qui supprime des lignes de code/preuve non-triviales :

1. **Diagnostic explicite** : citer l'erreur précise que la version précédente produisait (erreur compilateur exact, test échoué nommé, output comparaison). "Ça ne compilait pas" n'est **pas** un diagnostic.
2. **Minimiser la suppression** : essayer d'adapter (tactique alternative, hypothèse ajoutée, rename localisé) avant de supprimer. `split_ifs <;>` cassé ? Essayer `split_ifs with h1 h2; · ...; · ...`. `Typeclass not found` ? Ajouter l'instance au lieu de supprimer la preuve.
3. **Prouver l'équivalence** : si on remplace une preuve A par une preuve B, la signature doit être identique. Si on supprime une fonction, prouver qu'elle n'est plus appelée.
4. **PR dédiée** : tout commit qui introduit `sorry`/`pass`/`NotImplementedError` **à la place de code existant** doit être dans une PR **explicitement labellisée `debt`/`regression-accepted`** avec sign-off utilisateur. Jamais dans une PR "fix" anodine.
5. **Diff check avant push** : relire `git diff` ligne par ligne sur chaque suppression et justifier. `git diff --stat` doit être cohérent avec l'intention.

### ✅ OBLIGATOIRE : review spécifique anti-régression

Lors de la review d'une PR prétendant "fix compilation" / "simplification" :

- **Comparer avec l'historique** : `git log --all -- <file>` pour voir les versions antérieures. Si le commit initial contient plus de code que la PR, poser la question.
- **Checker les patterns red-flag** : `sorry`, `pass  # TODO`, `raise NotImplementedError`, `return None  # placeholder`, cellules `# Solution` remplacées par stubs
- **Fichiers Lean/Coq** : `grep -c sorry <file>` avant/après. Toute augmentation = PR à contester sauf justification explicite
- **Ne jamais auto-merger un commit "fix compilation"** avec deletions > insertions sur fichier Lean/formel/cœur métier

### ✅ OBLIGATOIRE : mémoire du patrimoine

- Le dépôt contient du travail accumulé sur des mois (port Lean social_choice = 1 semaine, notebooks enseignement = itérations multiples avec étudiants). **Tout contenu non-trivial mérite d'être traité comme patrimoine** avant d'être "simplifié".
- Quand un commentaire dit "Port of X" ou "Original: <url>", c'est un signal qu'il y a un travail à préserver. Lire la source avant de toucher.
- Quand un commit ancien ajoute du contenu avec `git log --grep` cherchant des mots-clés du sujet, comprendre son intention avant de supprimer.

**Voir `.claude/rules/anti-regression.md` pour les critères de détection détaillés (patterns red-flag, workflow de review, audit rogue commits).**

**VIOLATION = perte silencieuse de travail antérieur. Le patrimoine pédagogique du cours se dissout en faux "fix".**

---

## Regles Agents (Roo Code / machines distantes)

Les agents Roo sur les machines po-2023, po-2024, po-2025, po-2026 travaillent sur ce depot via RooSync. Ces regles sont **OBLIGATOIRES** pour tout agent.

### Git : PRs obligatoires

- **JAMAIS** de push direct sur `main`. Creer une feature branch, pousser, creer une PR
- Nommage branche : `feature/<sujet>` ou `fix/<sujet>`
- Un seul sujet par PR (pas de mega-PR multi-issues)
- Le coordinateur (ai-01) review et merge. Les agents ne mergent pas eux-memes

### Qualite : code avant documentation

- **Priorite** : code fonctionnel > tests/validation > documentation
- Ne pas generer de markdown (README, MAPPING, RAPPORT) sans code fonctionnel associe
- Ne pas creer de fichiers de planification (EXTEND_*.md, PROCEDURE_*.md) dans le repo — utiliser RooSync
- Les rapports d'audit, inventaires, et status vont sur le **dashboard RooSync**, pas dans le repo

### Review PR : validation explicite des objectifs

Toute PR doit faire l'objet d'une **review complete** avant merge :

1. **Relire l'issue ou le contexte d'origine** : identifier les objectifs precis (layout, positionnement, contenu, format)
2. **Valider chaque objectif explicitement** : verifier dans le code ET visuellement que chaque exigence est satisfaite
3. **Verification visuelle obligatoire pour les slides** :
   - Lancer le serveur Slidev et verifier CHAQUE slide modifie (pas un echantillon)
   - Verifier avec `?clicks=99` pour voir le contenu complet revele
   - Verifier l'absence d'overflow (contenu coupe en bas)
   - Verifier les layouts d'images (overlay uniquement, jamais colonne droite)
4. **Verification visuelle obligatoire pour les notebooks** : executer ou au moins valider la structure
5. **Ne jamais merger une PR sur la seule base du CI green** : CI valide la syntaxe, pas le rendu visuel ni la conformite aux specifications

**Slides : images en overlay uniquement**
- Les images de fond doivent utiliser `layout: image-overlay` avec le texte par-dessus, jamais en colonne droite
- Cette regle a ete specifiee dans l'issue #221 et confirmee 5+ fois dans les discussions
- Verifier que chaque image est bien positionnee sur le bon slide

**VIOLATION = PR a rejeter, meme si le code compile**

### Pas de duplication

- Avant de creer un fichier (README, docs, shared library), verifier qu'il n'existe pas deja
- Utiliser `grep` et `find` pour chercher les doublons
- Si un fichier similaire existe, le mettre a jour plutot qu'en creer un nouveau

### Enrichissement notebooks : regles strictes

- Chaque cellule de transition doit avoir du **contenu pedagogique specifique** (pas de "Suite du traitement" generique)
- Les cellules d'interpretation doivent etre placees **apres** la cellule de code qu'elles interpretent
- Ne pas enrichir le meme notebook dans deux sessions paralleles (risque de doublons)
- Verifier l'absence de doublons avec `git diff` avant de committer

### Emojis interdits

Regle code-style.md : **Pas d'emojis** dans le code, les noms de variables, les fichiers generes, ni les messages de commit. Utiliser des mots.

---

## QuantConnect (QC) - Regles specifiques

### Backtests obligatoires

Toute modification d'une strategie QC (main.py, parametres, periodes) **DOIT** etre validee par un backtest :
1. `create_compile` pour verifier la compilation
2. `create_backtest` pour lancer le backtest
3. `read_backtest` pour recuperer les metriques (Sharpe, CAGR, MaxDD)
4. Reporter les resultats dans le message de commit ET sur RooSync

**Changer une date ou un parametre sans backtest = travail invalide.**

### QC Cloud API - Acces via MCP Docker (OBLIGATOIRE)

**Methode d'acces** : Utiliser le MCP Docker `quantconnect/mcp-server` configure dans `.mcp.json` a la racine du projet.
- **NE PAS** utiliser de scripts Python avec l'API REST directe (provoque du rate-limiting et des erreurs d'auth)
- Le MCP gere l'authentification et le rate-limiting automatiquement
- Fichier de config : `.mcp.json` (deja dans `.gitignore`, JAMAIS committer)

**Configuration** (`.mcp.json`) :
```json
{
  "mcpServers": {
    "quantconnect": {
      "command": "docker",
      "args": ["run", "--rm", "-i", "-e", "QUANTCONNECT_USER_ID", "-e", "QUANTCONNECT_API_TOKEN", "-e", "QUANTCONNECT_ORGANIZATION_ID", "quantconnect/mcp-server"],
      "env": {
        "QUANTCONNECT_USER_ID": "<voir dashboard RooSync>",
        "QUANTCONNECT_API_TOKEN": "<voir dashboard RooSync>",
        "QUANTCONNECT_ORGANIZATION_ID": "<voir dashboard RooSync>"
      }
    }
  }
}
```

**Rate limiting strict** : MAX 10 appels/minute entre TOUS les agents. Avant de lancer un backtest, poster sur le dashboard. Un seul agent a la fois sur l'API QC.

**Pour retrouver les tokens** :
- Dashboard workspace CoursIA : section status
- Messages RooSync : tag `quantconnect` ou `TOKEN`
- En cas de token invalide : demander au coordinateur (ai-01) via RooSync

### Structure QC dans le depot

```
MyIA.AI.Notebooks/QuantConnect/
  Python/           # 27 notebooks progressifs (QC-Py-01 a QC-Py-27)
  projects/          # ~50 strategies avec main.py + research.ipynb
  shared/            # Librairie utilitaire (backtestlib, indicators, plotting)
  ESGF-2026/         # Cours ESGF : exercices, templates, lean-workspace
  docs/              # Documentation technique (pas de coordination)
```

### Livre de reference

*Hands-On AI Trading* de Jared Broad — https://www.hands-on-ai-trading.com/
Repo exemples : https://github.com/QuantConnect/HandsOnAITradingBook
Issues associees : #107 (mapping), #143 (implementation ML)

---

## Project Overview

CoursIA is an educational AI course platform:
- **Jupyter notebooks** for AI learning (C# with .NET Interactive and Python)
- **Docker infrastructure** for GenAI services (ComfyUI + Qwen image editing)
- **GradeBookApp** for student evaluation with collegial grading

Repository: https://github.com/jsboige/CoursIA

## Common Commands

### Environment Setup

```bash
# Python
python -m venv venv && venv\Scripts\activate
pip install -r MyIA.AI.Notebooks/GenAI/requirements.txt

# C# (.NET 9.0)
dotnet restore MyIA.CoursIA.sln
```

### Docker/ComfyUI Services

```bash
python scripts/genai-stack/genai.py docker status    # Statut des services
python scripts/genai-stack/genai.py docker start all # Demarrer tous les services
python scripts/genai-stack/genai.py docker stop all  # Arreter tous les services
```

### Validation & Testing

**IMPORTANT: Always use existing scripts for notebook validation/execution. Never write ad-hoc execution scripts.**

```bash
# === Notebook Tools (multi-family, production CLI) ===
python scripts/notebook_tools/notebook_tools.py validate [target]         # Structure validation
python scripts/notebook_tools/notebook_tools.py execute [target]          # Execute via Papermill
python scripts/notebook_tools/notebook_tools.py execute [target] --cell-by-cell  # Cell-by-cell (.NET/Lean)
python scripts/notebook_tools/notebook_tools.py analyze [path]            # Analyze structure
python scripts/notebook_tools/notebook_tools.py skeleton [path]           # Generate skeleton

# === SmartContracts-specific validator ===
python scripts/smartcontracts/validate_sc_notebooks.py                    # Full SC validation
python scripts/smartcontracts/validate_sc_notebooks.py --quick            # Structure only
python scripts/smartcontracts/validate_sc_notebooks.py --execute --anvil  # Execute with anvil

# === GenAI stack ===
python scripts/genai-stack/genai.py validate --full       # Validation complete ComfyUI
python scripts/genai-stack/genai.py validate --notebooks   # Validation syntaxe notebooks
python scripts/genai-stack/genai.py notebooks              # Validation Papermill notebooks
python scripts/genai-stack/genai.py gpu                    # Verification VRAM
```

**Kernel auto-detection**: `notebook_tools.py` reads kernel name from notebook metadata and uses it automatically. Custom kernels (smartcontracts, lean4-wsl) are supported with extended startup timeouts.

GitHub Actions validates notebooks on PR (`.github/workflows/notebook-validation.yml`)

### Claude Code Skills (slash commands)

```
/verify-notebooks [target] [--quick] [--fix]      # Verify and test notebooks
/enrich-notebooks [target] [--execute] [--strict]  # Add pedagogical content
/cleanup-notebooks [target] [--dry-run]             # Clean markdown structure
/build-notebook <action> <path> [--quality=90]      # Create/improve/fix notebooks
/execute-notebook <path> [--batch] [--save]         # Execute via MCP
/validate-genai [target] [--local]                  # Validate GenAI stack
```

### GradeBookApp

```bash
python GradeBookApp/gradebook.py               # Python grading pipeline
python GradeBookApp/run_epf_mis_2026.py         # EPF MIS multi-epreuves
```

## ECE Student Repos

ECE students submit work in a **separate GitHub org**, NOT in CoursIA.

**Org**: `jsboigeECE` on GitHub
**Repos pattern**: `2026-ECE-Ing4-Fin-IA-Projet{1,2,3}-Gr{01,02,03}`

| Repo | Description |
| ------ | ------------- |
| `2026-ECE-Ing4-Fin-IA-Projet1-Gr01` | Projet 1 - Groupe 01 |
| `2026-ECE-Ing4-Fin-IA-Projet1-Gr02` | Projet 1 - Groupe 02 |
| `2026-ECE-Ing4-Fin-IA-Projet1-Gr03` | Projet 1 - Groupe 03 |
| `2026-ECE-Ing4-Fin-IA-Projet2-Gr01` | Projet 2 - Groupe 01 |
| `2026-ECE-Ing4-Fin-IA-Projet2-Gr02` | Projet 2 - Groupe 02 |
| `2026-ECE-Ing4-Fin-IA-Projet2-Gr03` | Projet 2 - Groupe 03 |

**For any ECE student grading or rattrapage investigation**: search `jsboigeECE/` repos, NOT CoursIA.

```bash
# List student PRs
gh pr list --repo jsboigeECE/2026-ECE-Ing4-Fin-IA-Projet2-Gr02 --state all --limit 30

# View a specific PR
gh pr view 12 --repo jsboigeECE/2026-ECE-Ing4-Fin-IA-Projet2-Gr02
```

**Grading compilation**: `G:/Mon Drive/MyIA/Formation/ECE/2026/Notes_Finales_ECE_2026_Compilation.xlsx`

## Architecture

```
MyIA.AI.Notebooks/           # Jupyter notebooks by topic
├── GenAI/                   # Image, Audio, Video generation, LLMs (Python)
│   ├── Image/               # Image generation (19 notebooks)
│   ├── Audio/               # Speech, Voice & Music (16 notebooks)
│   ├── Video/               # Video generation & comprehension (16 notebooks)
│   └── Texte/               # Text generation (10 notebooks)
├── ML/                      # ML.NET tutorials (.NET C#)
├── Sudoku/                  # Constraint solving (.NET C#)
├── Search/                  # Optimization (Mixed Python/C#)
├── SymbolicAI/              # RDF, Z3, Tweety, Lean (Mixed)
├── Probas/                  # Infer.NET probabilistic programming (.NET C#)
├── GameTheory/              # OpenSpiel (Python WSL)
├── IIT/                     # PyPhi (Python)
└── Config/                  # API settings (settings.json)

scripts/
├── notebook_helpers.py      # Notebook manipulation (NotebookHelper, CellIterator)
├── notebook_tools.py        # CLI: validate, skeleton, analyze, execute
├── extract_notebook_skeleton.py  # README generation
└── genai-stack/             # GenAI validation scripts

.claude/
├── agents/                  # 10 specialized sub-agents (auto-discovered)
├── skills/                  # 9 skills: 6 user-invocable + 3 reference
└── rules/                   # 5 modular rules (notebook, git, style, genai, wsl)

GradeBookApp/                # Student grading system
docker-configurations/       # ComfyUI + Qwen Docker services
notebook-infrastructure/     # Papermill automation & MCP maintenance
```

## Key Technologies

- **AI/ML**: OpenAI API, Anthropic Claude, Qwen 2.5-VL, Hugging Face, Semantic Kernel
- **Notebooks**: Python 3.10+, .NET 9.0 Interactive, Papermill, MCP Jupyter
- **Docker**: ComfyUI GPU services (RTX 3090, 24GB VRAM)
- **GenAI Models**: DALL-E 3, GPT-5, Qwen Image Edit, Lumina/Z-Image

---

## GenAI Services - ComfyUI Image Generation

### Services disponibles

| Service | Modele | VRAM | Description |
|---------|--------|------|-------------|
| **Qwen Image Edit** | qwen_image_edit_2509 | ~29GB | Edition d'images avec prompts multimodaux |
| **Z-Image/Lumina** | Lumina-Next-SFT | ~10GB | Generation text-to-image haute qualite |

### Architecture Qwen (Phase 29)

Workflow ComfyUI pour Qwen Image Edit 2509 :

```
VAELoader (qwen_image_vae.safetensors, 16 channels)
    |
CLIPLoader (qwen_2.5_vl_7b_fp8_scaled.safetensors, type: sd3)
    |
UNETLoader (qwen_image_edit_2509_fp8_e4m3fn.safetensors)
    |
ModelSamplingAuraFlow (shift=3.0)
    |
CFGNorm (strength=1.0)
    |
TextEncodeQwenImageEdit (clip, prompt, vae)
    |
ConditioningZeroOut (negative)
    |
EmptySD3LatentImage (16 channels)
    |
KSampler (scheduler=beta, cfg=1.0, sampler=euler)
    |
VAEDecode
```

**Points critiques** :
- VAE 16 canaux (pas SDXL standard)
- `scheduler=beta` obligatoire
- `cfg=1.0` (pas de CFG classique, utilise CFGNorm)
- `ModelSamplingAuraFlow` avec shift=3.0

### Architecture Z-Image/Lumina

Workflow ComfyUI simplifie avec LuminaDiffusersNode :

```
LuminaDiffusersNode (Alpha-VLLM/Lumina-Next-SFT-diffusers)
    |
VAELoader (sdxl_vae.safetensors)
    |
VAEDecode
    |
SaveImage
```

**Parametres LuminaDiffusersNode** :
- `model_path`: "Alpha-VLLM/Lumina-Next-SFT-diffusers"
- `num_inference_steps`: 20-40
- `guidance_scale`: 3.0-5.0
- `scaling_watershed`: 0.3
- `proportional_attn`: true
- `max_sequence_length`: 256

**Note technique (Janvier 2025)** : Le node utilise `LuminaPipeline` (diffusers 0.34+), ancien nom `LuminaText2ImgPipeline` obsolete.

### Approches abandonnees

| Approche | Raison abandon |
|----------|----------------|
| Z-Image GGUF | Incompatibilite dimensionnelle (2560 vs 2304) entre RecurrentGemma et Gemma-2 |
| Qwen GGUF | Non teste, prefer les poids fp8 pour qualite |

### Scripts de gestion GenAI (scripts/genai-stack/)

**IMPORTANT pour agents** : Utiliser le CLI unifie `genai.py` au lieu de demarrer des kernels MCP directement.

```bash
# CLI unifie - aide
python scripts/genai-stack/genai.py --help

# Gestion services Docker
python scripts/genai-stack/genai.py docker status          # Statut services
python scripts/genai-stack/genai.py docker start all       # Demarrer tous les services
python scripts/genai-stack/genai.py docker test --remote   # Tester endpoints (local + remote)

# Validation stack ComfyUI
python scripts/genai-stack/genai.py validate --full        # Validation complete
python scripts/genai-stack/genai.py validate --nunchaku    # Test Nunchaku INT4 Lightning

# Validation notebooks
python scripts/genai-stack/genai.py validate --notebooks   # Syntaxe notebooks GenAI
python scripts/genai-stack/genai.py notebooks              # Execution Papermill

# GPU et modeles
python scripts/genai-stack/genai.py gpu                    # Verification VRAM
python scripts/genai-stack/genai.py models list-nodes      # Custom nodes ComfyUI
python scripts/genai-stack/genai.py models list-checkpoints # Checkpoints disponibles

# Authentification
python scripts/genai-stack/genai.py auth audit             # Audit securite tokens
python scripts/genai-stack/genai.py auth sync              # Synchroniser tokens
```

### Mapping notebooks GenAI Image → services

| Notebooks | Service | Prerequis |
|-----------|---------|-----------|
| 01-1, 01-3 | OpenAI API (cloud) | OPENAI_API_KEY |
| 01-4, 02-3 | SD Forge | Service local ou myia.io |
| 01-5, 02-1 | ComfyUI Qwen | COMFYUI_AUTH_TOKEN, ~29GB VRAM |
| 02-4 | Z-Image/vLLM | ~10GB VRAM |
| 03-* | Multi-modeles | Tous les services |
| 04-* | Applications | Variable |

### Mapping notebooks Audio → services

| Notebooks | Service | Prerequis |
|-----------|---------|-----------|
| Audio/01-1, 01-2 | OpenAI API (TTS/STT) | OPENAI_API_KEY |
| Audio/01-3 | Local (librosa, pydub) | Aucun |
| Audio/01-4 | Whisper local | GPU ~10 GB |
| Audio/01-5 | Kokoro TTS | GPU ~2 GB |
| Audio/02-1 | Chatterbox TTS | GPU ~8 GB |
| Audio/02-2 | XTTS v2 | GPU ~6 GB |
| Audio/02-3 | MusicGen | GPU ~10 GB |
| Audio/02-4 | Demucs v4 | GPU ~4 GB |
| Audio/03-* | Multi-modeles | Mixed |
| Audio/04-* | Applications | Mixed |

### Mapping notebooks Video → services

| Notebooks | Service | Prerequis |
|-----------|---------|-----------|
| Video/01-1 | Local (moviepy, FFmpeg) | FFmpeg installe |
| Video/01-2 | OpenAI GPT-5 | OPENAI_API_KEY |
| Video/01-3 | Qwen2.5-VL local | GPU ~18 GB |
| Video/01-4 | Real-ESRGAN/RIFE | GPU ~4 GB |
| Video/01-5 | AnimateDiff | GPU ~12 GB |
| Video/02-1 | HunyuanVideo | GPU ~18 GB |
| Video/02-2 | LTX-Video | GPU ~8 GB |
| Video/02-3 | Wan 2.1/2.2 | GPU ~10 GB |
| Video/02-4 | SVD | GPU ~10 GB |
| Video/03-3 | ComfyUI Video | Docker, nodes video |
| Video/04-3 | Sora 2 API | OPENAI_API_KEY |

### Configuration .env GenAI

Fichier : `MyIA.AI.Notebooks/GenAI/.env`

```bash
# Mode local (Docker) vs remote (myia.io)
LOCAL_MODE=false

# ComfyUI
COMFYUI_API_URL=https://qwen-image-edit.myia.io
COMFYUI_AUTH_TOKEN=<bearer_token_bcrypt>

# OpenAI via OpenRouter
OPENAI_API_KEY=sk-or-v1-...
OPENAI_BASE_URL=https://openrouter.ai/api/v1

# Mode batch pour execution automatisee
BATCH_MODE=false
```

## Configuration

- **API keys**: `MyIA.AI.Notebooks/GenAI/.env` (template: `.env.example`)
- **C# settings**: `MyIA.AI.Notebooks/Config/settings.json`
- **Docker**: `docker-configurations/services/comfyui-qwen/.env`

## Claude Code Extension Points

### Agents (`.claude/agents/`)

Agents are auto-discovered by Claude Code. Each has YAML frontmatter with model, tools, memory, and skills configuration. Key agents:

| Agent | Model | Purpose |
|-------|-------|---------|
| notebook-iterative-builder | inherit | Orchestrate build/improve/fix cycles |
| notebook-executor | sonnet | Execute notebooks via MCP |
| notebook-validator | sonnet | Validate all quality aspects |
| notebook-enricher | sonnet | Add pedagogical content |
| notebook-cleaner | sonnet | Fix markdown structure |
| notebook-designer | inherit | Create new notebooks |
| notebook-cell-iterator | sonnet | Fix specific cells iteratively |
| readme-updater | haiku | Update README files |
| readme-hierarchy-auditor | haiku | Audit README hierarchy |

### Skills (`.claude/skills/`)

| Skill | Type | Description |
|-------|------|-------------|
| notebook-helpers | Reference (auto) | Script reference for notebook manipulation |
| mcp-jupyter | Reference (auto) | MCP Jupyter tools and patterns |
| notebook-patterns | Reference (auto) | Enrichment patterns (GameTheory model) |
| verify-notebooks | User (`/command`) | Verify and test notebooks |
| enrich-notebooks | User (`/command`) | Enrich with pedagogical content |
| cleanup-notebooks | User (`/command`) | Clean markdown structure |
| build-notebook | User (`/command`) | Create/improve/fix notebooks |
| execute-notebook | User (`/command`) | Execute via MCP |
| validate-genai | User (`/command`) | Validate GenAI stack |

### Rules (`.claude/rules/`)

| Rule | Scope | Content |
|------|-------|---------|
| notebook-conventions | `*.ipynb` files | Manipulation, structure, execution rules |
| git-workflow | All files | Branch naming, commit messages, safety |
| code-style | All files | PEP 8, .NET, no emojis, naming |
| genai-config | `GenAI/**/*` | Services, env, scripts, architecture |
| wsl-kernels | `GameTheory/**`, `Lean/**` | WSL kernel issues and workarounds |

### Model Selection Strategy

When delegating to sub-agents, use intelligent model selection:
- **haiku**: Quick tasks (README updates, structure scans, simple validation)
- **sonnet**: Standard tasks (enrichment, execution, cleanup, validation)
- **inherit/opus**: Complex tasks (design, orchestration, debugging)

### Proactive Behaviors

- After completing notebook work, **update agent memory** with lessons learned
- After enrichment, **verify cell placement** with git diff
- Before executing GenAI notebooks, **validate the stack** with `/validate-genai`
- When encountering repeated errors, **record the pattern** in memory for future reference
- When working with notebooks, **use the helper scripts** (not ad-hoc Python)

## Language

Primary documentation language: French. Code comments: French or English.
