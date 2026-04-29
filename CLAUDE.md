# CLAUDE.md

Guidance pour Claude Code travaillant avec le repository CoursIA.

**Documentation deportee :**
- [docs/common-commands.md](docs/common-commands.md) - Setup environnement, validation notebooks, slash commands
- [docs/genai-services.md](docs/genai-services.md) - Architectures Qwen/Lumina, scripts genai-stack, mappings notebooks
- [docs/claude-code-config.md](docs/claude-code-config.md) - Agents, skills, rules, model selection
- [docs/quantconnect.md](docs/quantconnect.md) - Backtests, MCP Docker, structure, livre reference
- [docs/ece-grading.md](docs/ece-grading.md) - ECE student repos, autres ecoles
- [.claude/rules/](.claude/rules/) - Regles modulaires auto-loaded (notebook, git, code-style, anti-regression, genai, wsl)

---

## REGLES CRITIQUES

### Coordination inter-machines = RooSync uniquement

Les machines po-2023, po-2024, po-2025, po-2026 coordonnent via RooSync.

- **JAMAIS** : commit de rapports de coordination, fichiers `*_TEST_REPORT.md`/`*_COORDINATION.md` dans le repo, messages SSH
- **TOUJOURS** : dashboard workspace CoursIA + messages RooSync. GitHub = code uniquement.

Lors d'un tour de coordination :
1. **Lire le contenu complet** du dashboard (utiliser `Read` sur le fichier persiste si la sortie est tronquee)
2. **Verifier l'inbox** RooSync pour les messages directs non lus
3. **Verifier le heartbeat** cluster pour savoir quelles machines sont actives
4. **Si aucune mission assignee** : envoyer un message RooSync a ai-01 pour demander des instructions, ne pas attendre passivement

### Git : pas de force push, PRs obligatoires

- **JAMAIS** `git push --force` / `--force-with-lease` sur main, **JAMAIS** `git reset --hard` sur main sans validation user
- **JAMAIS** push direct sur `main`. Creer une feature branch, pousser, creer une PR
- Nommage branche : `feature/<sujet>` ou `fix/<sujet>`, un seul sujet par PR
- Le coordinateur (ai-01) review et merge. Les agents ne mergent pas eux-memes
- En cas d'urgence extreme : validation explicite user AVANT toute operation destructive

Incident 2026-03-13 : force push accidentel sur main a potentiellement ecrase des commits. Cf [.claude/rules/git-workflow.md](.claude/rules/git-workflow.md).

### Reviews PR exigeantes (5 points obligatoires)

Avant de merger une PR (y compris les siennes), verifier :

1. **Scope reel** : la PR fait ce qu'elle dit, rien de plus, rien de moins
2. **Validation automatisee complete** : script de validation **du livrable** (pas du code source) relance APRES le dernier commit
3. **Coherence pedagogique** (notebooks/slides) : exercices alignes au contenu enseigne, pas de redondance, stubs `TODO` coherents, ordre cellules logique
4. **Execution au moins une fois** : Papermill ou Jupyter pour notebooks (CI = syntaxe, pas pedagogie). Slidev `?clicks=99` pour slides
5. **Regression check** : grep des symboles touches dans le reste du depot

Si un seul point n'est pas verifie : **ne pas merger**.

**INTERDIT : les mensonges de succes.** Pas de "DONE"/"fixed"/"validated" sans validation post-fix. Pas de fichiers markdown de "RAPPORT"/"AUDIT" comme preuve sans code valide. Pas d'incantations "propre"/"clean" sans preuve. Si un fix a corrige 5/7 cellules : rapporter "5/7, 2 restantes", pas "DONE".

Incidents references : 2026-04-08 (slides EPITA "PROPRE" mais inutilisables), 2026-04-20 (Sudoku-8 + 27 cellules cassees rapportees DONE).

### Anti-regression : ne pas effacer le travail existant

S'applique au **code de production** (preuves Lean/Coq, fonctions metier, tests, librairies).

**INTERDIT** :
- Remplacer une preuve formelle ou implementation existante par `sorry`/stub vide sans diagnostic explicite
- Commits "fix compilation"/"lint fix"/"Mathlib fix" avec **deletions > insertions** sur code metier
- Supprimer des commentaires pedagogiques (proof sketches, docstrings) "pour simplifier"
- Justifier la suppression par "ca compilait pas" sans citer l'erreur precise
- Cellule `# Solution` (exemple resolu pedagogique) remplacee par stub

**Protocole avant suppression** :
1. Diagnostic explicite (citer erreur compilateur exacte, test echoue nomme)
2. Minimiser la suppression : essayer 3 adaptations tactiques avant de supprimer
3. PR dediee labellisee `debt`/`regression-accepted` avec sign-off user pour toute regression
4. `git diff --stat` coherent avec l'intention

**Detection patterns red-flag** : `grep -c sorry` avant/apres sur fichiers Lean/Coq, suppressions de corps de fonction metier appelee, cellules `# Solution` -> stubs.

Incident 2026-04-24 : commit "Mathlib compilation fixes" (#524) a remplace 9 preuves d'Arrow.lean par `sorry`, perte d'une semaine de port Lean. Cf [.claude/rules/anti-regression.md](.claude/rules/anti-regression.md).

### Notebooks : pas d'erreur volontaire (regle user 2026-04-26)

**INTERDIT partout dans un notebook pedagogique** : `raise NotImplementedError`, `assert False`, `1/0`, ou toute erreur intentionnelle. Que ce soit top-level, methode, fonction utilitaire.

Raisons : les scripts de validation trackent les cellules en erreur comme bugs ; Papermill plante sur la suite du notebook ; les agents tentent de "resoudre" pour faire passer.

**Patterns corrects pour cellule d'exercice** :

| Cas | Pattern correct |
|-----|-----------------|
| Cellule top-level a completer | `print("Exercice a completer")` ou `pass` |
| Methode classe a implementer | `def foo(self): pass  # TODO etudiant : <description>` |
| Fonction utilitaire stub | `def helper(...): return None  # TODO etudiant` |
| Bloc avec valeur attendue | `result = None  # TODO etudiant : remplacer par compute_thing()` |

Conserver **TOUS** les commentaires `# TODO`, `# Indice`, `# Etape N`. Le notebook entier doit s'executer de bout en bout sans erreur, meme exercices non completes.

**Pour la review** : remplacer un `raise NotImplementedError` legacy par `pass`/`print`/`return None` est **conforme** a cette regle, pas une regression.

### Notebooks committes AVEC leurs sorties (regle user 2026-04-26)

Les outputs font partie du livrable pedagogique (affichables sur GitHub, reproductibles).

- **JAMAIS** commit avec `execution_count: null` partout ou `outputs: []` vidés sans re-execution
- **JAMAIS** "clean outputs avant commit" comme etape de routine (sauf donnees sensibles)
- Toute modification de cellule code (source, deps, parametres) implique **re-execution complete** avant commit
- Format attendu : `execution_count: <int>` + `outputs: [...]` coherents pour chaque cellule code executable
- Notebook non-executable en local (kernel manquant, GPU requis) : documenter pourquoi (markdown), executer ailleurs et committer avec outputs

Exception : modifications uniquement dans cellules markdown -> outputs des cellules code restent valides.

### Scope strict des re-executions Papermill

Un agent ne commit QUE les notebooks qu'il a effectivement modifies (source code, paths, imports, cellules markdown). Les re-executions Papermill de notebooks dont **aucune cellule source n'a change** ne doivent **pas etre stagees**.

Procedure avant commit :

```bash
git diff --name-only -- '*.ipynb'
# Pour chaque .ipynb, verifier qu'au moins une ligne "source" a change
for nb in $(git diff --name-only -- '*.ipynb'); do
  source_changes=$(git diff "$nb" | grep -cE '^\+\s*"source"')
  if [ "$source_changes" -eq 0 ]; then
    echo "WARN: $nb a uniquement des changements d'outputs -> NE PAS COMMIT"
    git restore --staged "$nb" 2>/dev/null
    git checkout "$nb"
  fi
done
git add MyIA.AI.Notebooks/<famille>/<notebook-modifie>.ipynb  # explicite, jamais `git add -A`
```

Pour audit/inventaire : Papermill dans `/tmp/audit_<famille>_$(date +%s)/`, rapport sur dashboard, pas de fichier dans le repo.

Incidents 2026-04-25 : 2 collisions PR par re-executions paralleles (#540 vs #541, #541 vs #542).

### Code style

- **Pas d'emojis** dans le code, noms de variables, fichiers generes, messages de commit
- Python : PEP 8, type hints, Python 3.10+
- C# : .NET 9.0, .NET Interactive pour notebooks, Microsoft.SemanticKernel
- Notebooks : documentation primaire en francais, code en francais ou anglais

---

## REGLES AGENTS (Roo Code distants)

### Qualite : code avant documentation

- **Priorite** : code fonctionnel > tests/validation > documentation
- Pas de markdown (README, MAPPING, RAPPORT) sans code fonctionnel associe
- Pas de fichiers de planification (EXTEND_*.md, PROCEDURE_*.md) dans le repo - utiliser RooSync
- Les rapports d'audit, inventaires, status vont sur le **dashboard RooSync**, pas dans le repo

### Slides : images en overlay uniquement

- Layout `image-overlay` avec texte par-dessus, jamais en colonne droite (regle issue #221, confirmee 5+ fois)
- Verification visuelle obligatoire : Slidev sur CHAQUE slide modifie (pas un echantillon), `?clicks=99`, absence d'overflow

### Pas de duplication

Avant de creer un fichier (README, docs, shared library), verifier qu'il n'existe pas deja. Si fichier similaire existe, le mettre a jour plutot qu'en creer un nouveau.

### Enrichissement notebooks

- Cellules de transition : contenu pedagogique specifique (pas de "Suite du traitement" generique)
- Cellules d'interpretation : APRES la cellule de code interpretee
- Pas d'enrichissement parallele du meme notebook dans deux sessions (risque doublons)

---

## QuantConnect (resume)

- **Backtest obligatoire** apres toute modification (`create_compile` -> `create_backtest` -> `read_backtest`). Reporter Sharpe/CAGR/MaxDD dans commit + RooSync. Cf [docs/quantconnect.md](docs/quantconnect.md).
- **Acces API uniquement via MCP Docker** `quantconnect/mcp-server` (config `.mcp.json`, jamais committer). Pas de scripts REST directs.
- **Rate limiting** : MAX 10 appels/min entre TOUS les agents. Annoncer sur dashboard avant backtest.
- **Livre reference** : *Hands-On AI Trading* (Jared Broad), https://www.hands-on-ai-trading.com/

---

## Project Overview

CoursIA = plateforme educative AI :
- **Jupyter notebooks** (C# .NET Interactive + Python) pour apprentissage AI
- **Docker** infrastructure pour services GenAI (ComfyUI + Qwen)
- **GradeBookApp** evaluation etudiants

Repository : https://github.com/jsboige/CoursIA

### Architecture

```
MyIA.AI.Notebooks/           # Jupyter notebooks par theme
- GenAI/Image, Audio, Video, Texte   (Python)
- ML/                                 (.NET C#)
- Sudoku/, Search/, SymbolicAI/      (Mixed)
- Probas/, GameTheory/, IIT/         (Mixed)
- QuantConnect/                       (Python, voir docs/quantconnect.md)
- Config/settings.json                (API settings)

scripts/
- notebook_helpers.py, notebook_tools.py  (CLI)
- genai-stack/                            (GenAI validation, voir docs/)

.claude/
- agents/, skills/, rules/                (voir docs/claude-code-config.md)

GradeBookApp/                # Grading system (voir docs/ece-grading.md)
docker-configurations/        # ComfyUI + Qwen Docker (voir docs/genai-services.md)
notebook-infrastructure/      # Papermill + MCP maintenance
docs/                         # Documentation deportee de ce CLAUDE.md
```

### Key Technologies

- **AI/ML** : OpenAI API, Anthropic Claude, Qwen 2.5-VL, Hugging Face, Semantic Kernel
- **Notebooks** : Python 3.10+, .NET 9.0 Interactive, Papermill, MCP Jupyter
- **Docker** : ComfyUI GPU services (RTX 3090, 24GB VRAM)
- **GenAI Models** : DALL-E 3, GPT-5, Qwen Image Edit, Lumina/Z-Image

---

## Language

Documentation primaire : francais. Commentaires code : francais ou anglais.
