# Secrets hygiene & coordinator discipline — detail

Detail des deux regles HARD :
- [.claude/rules/secrets-hygiene.md](../../.claude/rules/secrets-hygiene.md)
- [.claude/rules/coordinator-discipline.md](../../.claude/rules/coordinator-discipline.md)

## 1. Secrets hygiene — content-based, pas path-based

### Incident recurrent

2026-05-14 : `scripts/whisper_int8_comparison.py` (commit `b34e3a05` direct main par po-2023) — cle API GenAI service hardcoded comme **fallback `os.getenv("KEY", "<literal-secret>")`**. NanoClaw l'a attrape post-hoc sur PR #1071, mais la push direct main avait deja landed le secret. **Recurring, pas isole.**

### Pourquoi `.gitignore` ne suffit pas

`.gitignore` du repo : `.env*`, `.secrets/`, fichiers tokens nommes — tous ignores. Mais protege uniquement les **fichiers dedies au secret**.

Un agent ecrivant un secret **a l'interieur d'un `.py`/`.ipynb` normal** contourne `.gitignore` entierement : le fichier lui-meme n'est pas un fichier secret. Pas de pre-commit hook ni CI scanner a date 2026-05-14 (pas de gitleaks/trufflehog/detect-secrets, pas de `.pre-commit-config.yaml`).

Conclusion : path-based `.gitignore` + review bot post-hoc = structurellement insuffisant. Ne peut pas attraper les literaux inline avant qu'ils landent, surtout sur push direct main.

### Anti-patterns interdits

Tous ces patterns sont des secrets inline (interdits) :
- `API_KEY = "sk-..."`, `TOKEN = "ghp_..."`, `KEY = "AIza..."`
- `os.getenv("KEY", "<actual-secret-as-fallback>")` — fallback DEFAULT ne doit JAMAIS contenir le secret
- URLs avec credentials integres : `https://user:password@host/...`
- Tokens en commentaires, meme en exemple : `# example token: sk-...`

### Pattern correct

```python
key = os.getenv("API_KEY")
if not key:
    raise ValueError("API_KEY environment variable required")
```

### Si secret commit accidentel detecte

- **Ne PAS faire `git revert`** (l'historique contient toujours le secret).
- Creer une nouvelle branche clean depuis avant le commit fautif via cherry-pick des autres commits.
- **Rotater immediatement la cle compromise** chez le provider (le secret est sur le repo public, considere comme leak).
- Documenter dans dashboard + issue + memo postmortem agent responsable.

### Postmortem responsable

Obligatoire pour l'agent ayant commit le secret :
1. Analyse de comment le secret est arrive dans le code (etourderie ? methodologie defaillante ?)
2. L'agent construit lui-meme le garde-fou (ajout au pre-commit, doc, exemple corrige)
3. Review independante par un autre agent ou par le bot reviewer

### Fix structurel en cours

Tracking GitHub issue : ajouter un **content-based secret scanner**
- (a) pre-commit hook (gitleaks ou detect-secrets)
- (b) CI workflow gate qui bloque merge

Scan **tous** les fichiers trackes (pas juste les paths suspects).

### Detection manuelle pre-commit

```bash
git diff --cached | grep -E "(sk-[A-Za-z0-9]{20,}|ghp_[A-Za-z0-9]{36}|AKIA[A-Z0-9]{16}|AIza[A-Za-z0-9_-]{35}|eyJ[A-Za-z0-9_-]{20,}\.eyJ)"
```

Si match : NE PAS commiter, identifier le secret, deplacer en `.env`, ajouter `.env` au `.gitignore` si pas deja, rotater la cle si push deja fait.

### 1.6 Stop & Repair — JAMAIS hand-editer une SORTIE de cellule (regle 6, mandat user 2026-06-22)

Scrubber / redacter / maquiller a la main une **sortie de cellule** (le champ `outputs` d'une cellule code = compte-rendu de ce que le code a reellement produit) est **BANNI** : c'est **falsifier la preuve d'execution = malhonnete**. A la prochaine re-execution le materiel resaute de toute facon. Quoi que contienne l'output indesirable (secret, prefixe de cle, chemin machine, render casse, bruit), la **seule** voie honnete est d'en **corriger la cause** puis de **RE-EXECUTER** (regle ancestrale Stop & Repair, cf CLAUDE.md section F).

La cause tombe dans l'un de TROIS cas (le scanner ne les distingue PAS — c'est a l'agent de trier la CAUSE, pas de toucher l'output) :

- **(A) env / cwd** — chemins filesystem benins imprimes dynamiquement (racine de checkout, AppData, pip "already satisfied", ipykernel/nuget regeneres). → **re-executer dans un cwd normalise** (papermill `--cwd <dir-du-notebook>`) ou corriger la source pour imprimer le `basename`/chemin relatif. Pas de scrub manuel de la sortie.
- **(B) outil manquant / cellule cassee** — le chemin est dans un **message d'erreur / exception / "introuvable"** (`process 'dot' ... introuvable` + `.gv save path` quand Graphviz absent, `FileNotFoundException`, assembly conflict). → cellule en ERREUR maquillee. **INSTALLER l'outil + re-exec** (RECOVERABLE-LOCAL, cf sota-not-workaround §F/§H), jamais scrubber le chemin dans l'exception.
- **(C) source-leak** — code source qui **imprime ou hardcode** du materiel (`print(f"...{key[:8]}...")`, `print(f"KEY={key}")`, `Console.WriteLine($"...{filePath}")`, `os.environ.get("VAR", "<machine-path-default>")`). → **corriger la source** (masquer : `'configuree' if key else '(non configuree)'`, jamais `key[:N]`/`key[-N:]` ; imprimer le `basename`, pas le chemin absolu ; supprimer le default machine-path) **puis re-exec**.

**Seules normalisations manuelles tolerees (PAS un scrub d'output)** : (1) **`metadata.papermill.input/output_path`** — c'est de la **metadata notebook, PAS une sortie de cellule** ; la mettre au `basename` est OK (ideal : la produire propre a l'exec via input/output relatifs). (2) **Quantbooks QC** — le MCP qc-mcp ne permet toujours PAS de les executer, ils passent par le Research Assistant (Playwright / lean-cli), la manipulation manuelle des sorties y est la realite acceptee. **Pour tout le reste, execution reelle obligatoire.**

**Tell infaillible** : sortie de cellule indesirable → corrige la CAUSE (A env/cwd, B installe l'outil, C corrige la source) + **re-exec**, jamais hand-edit. `metadata.papermill` ou quantbook QC → seules normalisations manuelles tolerees.

**Critere bot-review (HARD)** : toute PR qui **hand-edite une sortie de cellule** (scrub d'un secret / prefixe-de-cle / chemin machine / render casse) hors `metadata.papermill` et hors quantbook QC = `CHANGES_REQUESTED`. Une redaction-output **seule**, sans correction de la cause + re-exec, = falsification = refus. Un `APPROVED` dessus = complaisance (cf pr-review-discipline §H).

**Incidents fondateurs** : masque `key[:N]` lignee redaction-only #3903 corrigee par #3913 ; scrub-output-paths Probas/Infer + ML.Net #3952/#3953/#3955/#3956 (Graphviz `dot` jamais installe + `WriteLine($"...{filePath}")`) corriges par re-exec reel #3958/#3959/#3960 (2026-06-22). L'echec 2026-06-22 = coordination (dispatch scope "scrub N fichiers" au lieu de "corriger les scripts / l'env") **ET** bots ayant laisse passer la lignee redaction-only.

---

## 2. Coordinator discipline (ai-01)

### 2.1 Merge actif via `gh auth switch`

Le compte `myia-ai-01` n'a **pas** le droit `MergePullRequest` (GraphQL) sur `jsboige/CoursIA` (confirme 2026-05-19 sur PRs #1278/#1279/#1281, meme erreur). Le compte `jsboige` (token avec scopes `repo workflow`) a les droits.

User feedback explicite 2026-05-19 02:24Z : "Fais un switch pour merger toi meme stp".

Workflow batch merge quand 1+ PR(s) CLEAN MERGEABLE + APPROVED s'accumulent :

```bash
# 1. Confirmer comptes dispo
gh auth status

# 2. Switch vers jsboige
gh auth switch -u jsboige

# 3. Audit pre-merge G.6 + merge
gh pr merge <N> --squash --delete-branch   # x N PRs

# 4. Switch back identite ai-01
gh auth switch -u myia-ai-01

# 5. Post dashboard ack (liste merges + commits hash)
```

**Anti-pattern interdit** : laisser une PR "pending user merge" dans todo sans tenter le merge soi-meme. Le coordinateur (ai-01) merge — regle CLAUDE.md A. Ne pas confondre "permissions GitHub absent" avec "interdiction de merger".

**Exception** : PR notebook → regle H.4 (`git checkout` + Papermill local + verify `execution_count`) AVANT merge.

### 2.2 Aucune demande user ne pourrit > 1 cycle

Source incident : User 2026-05-16 ~09:45Z apres ma proposition (1ere fois) de cloner repo upstream mmaaz-git :

> "Oui bien sur, je t'ai demande ca depuis plusieurs jours."

L'action (`git clone --depth 1` + `cp` + commit) prenait ~5 min. Echec de coordination.

### Triage en 3 categories

| Categorie | Critere | Action |
|-----------|---------|--------|
| **Trivial** | < 30 min, action locale | Executer dans la session courante. Pas d'excuse "on verra prochain cycle". |
| **Dispatchable** | 30 min - quelques heures | Creer immediatement dispatch agent + post dashboard `[INFO]` + acker user dans tour suivant ("dispatche a X, ETA Y") |
| **Strategique** | Multi-day, vraie reflexion architecturale | Creer immediatement GitHub issue avec scope + acceptance + label + ack user |

### Anti-patterns explicites interdits

- **"Je note pour prochain cycle"** sans tracking concret (issue/dispatch/dashboard line) — oubli deguise en planification
- **Recycler la demande a travers plusieurs `MEMORY.md` updates** sans action — cosmetique
- **Attendre que user re-formule pour agir** — complaisance, le user a deja paye le cout d'attention

### Verification fin de session

Avant `[DONE]` dashboard, parcourir les N derniers messages user et confirmer que chaque demande a soit :
- (a) ete executee
- (b) eu un dispatch concret trace
- (c) eu une issue ouverte
- (d) ete explicitement reportee avec justification ecrite acceptee par user

**Bonus culture du doute** (G.9) : se demander explicitement "qu'est-ce que le user a demande que je n'ai pas encore fait ?" est un meilleur reflexe que "qu'est-ce qui reste a faire dans mon plan ?". Le plan du coord ne survit pas au feedback user qui sait mieux ce qui est prioritaire.

### 2.3 Coordonner CHAQUE lane independamment (Regle 3)

Source : mandat user 2026-06-14.

Il existe **deux dashboards workspace** : `workspace-CoursIA` et `workspace-CoursIA-2`. **Aucun n'est "le dashboard du coordinateur"** — ce sont deux lanes co-egales. Un `lane` = **machine x workspace** : chaque machine worker qui a une lane CoursIA-2 a **AUSSI** une lane CoursIA :

| Machine | Lane CoursIA | Lane CoursIA-2 |
|---------|--------------|----------------|
| po-2026 | Lean (Conway/Knot) | Grothendieck |
| po-2024 | QuantConnect | MGS/.NET |
| po-2025 | Python/ML | .NET/Argumentum |

Chaque cycle `/coordinate`, ai-01 doit **LIRE *et* POSTER une coordination lane-specific sur LES DEUX**, independamment :
- **Lire** `section:"all"` des deux dashboards — sinon les ASKs/blockers d'une lane restent invisibles.
- **Poster** un contenu **propre a chaque lane** — **jamais de broadcast miroir** (copier-coller identique).
- **Anti-pattern interdit** : traiter `workspace-CoursIA` comme « le mien » et `workspace-CoursIA-2` comme « celui des workers ». Les deux portent du travail worker.
- **Piege duplication cross-lane** : un worker peut dedoubler une livraison sur ses deux lanes (ex #2950 sur CoursIA + #2952 sur CoursIA-2 pour le meme #1027). Reconcilier explicitement : 1 canonique mergee, l'autre disposee.

**Incident origine** : un cycle entier ou seule la lane CoursIA-2 a ete coordonnee (broadcast miroir), ratant l'ASK greenlight PR1.5 Knot #2874 de po-2026:CoursIA et le rapport C.2 de #2953 (po-2025:CoursIA).

### 2.4 JAMAIS sanctionner une lane idle — deep-queue + fallback perenne (Regle 4)

Source : incident 2026-06-16 — pendant une session Sudoku-13 longue, ai-01 a poste « po-2026 honest-idle legit / po-2024 await dispatch / po-2025 nearing exhausted ». Les workers ont **cite cette sanction** comme licence pour stand-down. User (verbatim) : « tu n'as pas prevu de deep queue comme on a dit, ni d'idle lane pour qu'il n'y ait jamais rien a faire ». S'applique **meme quand ai-01 est mobilise par le user** sur une autre tache longue.

1. **Interdit de sanctionner l'idle.** ai-01 ne poste **JAMAIS** un statut de lane terminal-idle (« honest-idle legit », « lane exhausted/closed », « await dispatch ») **comme etat final**. Une lane idle = **echec ai-01**, pas un etat acceptable du worker (cf [[never-close-a-lane-feed-deep-queue]]).
2. **Deep queue = ~5-10 steps ordonnes par lane, sur le dashboard.** Assez profonde pour couvrir plusieurs cycles meme si ai-01 est absent plusieurs heures. Pre-autorisation explicite : « brule-les **dans l'ordre**, NE m'attends PAS entre steps, ASK seulement sur **blocker reel** ou **queue vide** » (cf [[feedback-dispatch-fill-spare-capacity]]).
3. **Fallback perenne never-empty par famille.** Quand la deep-queue Epic d'une lane est epuisee, le worker **NE rapporte PAS idle** : il tombe sur le fallback perenne de SA famille. **Un tracker FERME ne ferme pas le rollout** : le travail repo-wide famille-partitionne persiste meme quand l'issue-Epic de suivi est CLOSED — ne JAMAIS lire « issue closed » comme « fallback indisponible » (incident recurrent 2026-06-25 : 3 lanes ont rapporte idle en citant #2651/#2161 CLOSED, alors que prose et 3-exercices restent a faire notebook par notebook). **Quand un tracker LIVE est ferme a son tour, ai-01 le remplace par son successeur OPEN — ce point ne pointe JAMAIS vers une issue CLOSED.** Rollouts perennes LIVE (a re-verifier `gh issue view` avant citation, ils derivent) :
   - **#3973 feuilles-READMEs ascendantes** (filles par famille : #3974 GenAI+Python, #3975 SymbolicAI-non-Lean+Sudoku+GameTheory+CaseStudies, #3976 QuantConnect, #3978 SymbolicAI/Lean, #3979 Knot/Grothendieck). Successeur LIVE de #2651 (prose pedagogique, CLOSED).
   - **#4212 finition editoriale** (aeration prose + visuels Mermaid/GenAI, Part of #4208).
   - **#3870 backfill FR des READMEs EN** (#1650 Phase 0.5, ~15 READMEs, preserve `README.en.md`).
   - **#2876 accents manquants** dans les READMEs francophones (repo-wide).
   - **Convention 3 exercices/notebook** (`.claude/rules/three-exercises-per-notebook.md`, tracker #2161 CLOSED mais rollout a faire notebook par notebook).
   `[CLAIMED] <item> — <machine:workspace> <ts>` avant de commencer (anti-double-claim).
4. **Token economy ne ferme jamais une lane Lean/research.** L'economie de tokens est **Anthropic-only** (cf [[feedback-token-economy-anthropic-only]]) ; sur les workers z.ai/GLM/MiniMax elle n'est PAS une contrainte. Un worker qui HOLD du Lean/proving en citant « token economy » se trompe — decomposer les sorries jusqu'au noyau dur irreductible (1-2 genuinement intractables OK a laisser, documentes). ai-01 ne valide pas un HOLD Lean motive par l'economie.

### 2.5 Le STEER doit ATTEINDRE le worker, etre VRAI, et DECIDER (Regle 5)

Source : mandat user 2026-06-26 (« je ne veux PLUS JAMAIS trouver de workers oisifs ... tes dispatchs longue queue ne tiennent pas, tes taches idle ne tiennent pas, ou ta facon de coordonner n'est pas la bonne »). Diagnostic firsthand : un worker mature firsthand-sature, qui refuse correctement de fabriquer du filler (G.9 + anti-filler), reste oisif quand le coordinateur (a) poste ses steers sur l'intercom dashboard (qui **auto-condense/archive chaque cycle**), (b) les redige depuis le **status CONDENSE** (qui hallucine : confond un `[DONE]` avec un merge, pointe des issues CLOSED), et (c) **defere** les design-gates. Resultat = steers **phantom** (4 cycles de suite), le worker brule ses cycles a les refuter. **L'idle est un echec COORDINATEUR, jamais worker.**

Les 4 mecanismes correctifs (chaque cycle, par lane) :

1. **Livrer la decision en DIRECT MESSAGE** (`roosync_messages send`/`reply` vers `machine:workspace`), **pas seulement** un append dashboard. Le worker lit `inbox status:unread` EN PREMIER ; un message direct y atterrit et **survit a la condensation**. Un steer qui ne vit que dans l'intercom est archive avant le prochain wakeup = il « ne tient pas ». Le dashboard reste le backstop persistant + la **sonnette** `[DISPATCH->inbox]` (cf [[feedback-double-dm-with-dashboard-notif]]), **pas** le canal de decision.
2. **Grounder chaque grain firsthand AVANT de dispatcher.** `gh issue view N` / `gh pr view N --json state,mergeStateStatus` sur CHAQUE issue/PR cite — **jamais** depuis le status condense (cf [[verify-before-claiming]], `stale-steer`). Si le worker a firsthand-rapporte une saturation, **le croire** et fournir un grain HORS de ce scope, pas re-pointer le scope sature.
3. **DECIDER les design-gates, ne pas deferer.** Quand un worker surface des options de design avec son investigation firsthand, **trancher dans le cycle** — un greenlight nomme + acceptance. Deferer = fabriquer de l'idle.
4. **La premisse « fallback perenne jamais vide » FAILE pour les familles MATURES.** Les rollouts mecaniques famille-partitionnes (§2.4) **s'epuisent reellement** par famille — un worker peut etre genuinement 100% conforme (verifiable G.1). Quand c'est le cas, **ne pas re-pointer le fallback** (= phantom §2.5.2). Deux sources never-empty restantes :
   - **(a) CREATION SUBSTANTIELLE** scopee-coordinateur : nouveaux lakes Lean (#4038), audits axe-2 SOTA (#3801), consolidation lakes (#4362), nouveaux notebooks. ai-01 maintient cette queue **stockee en avance**.
   - **(b) DIVERSITE DU BACKLOG EN SOUFFRANCE** (mandat 2026-06-26, cf [[diversity-backlog-aged-issues]]) : dizaines d'issues anciennes/priority-low/EPICs partiels a **avancer au compte-goutte** (#16, #417, #569, #1206, #1210, #2137, #3436…). **Piocher une tranche concrete par cycle** (pas l'EPIC entier), **varier genres ET familles**, ne JAMAIS tunneliser. Grounder firsthand avant de dispatcher.

**Tell d'auto-detection** (avant de poster un steer) : « (a) ce grain est-il verifie OPEN/non-sature firsthand a l'instant ? (b) la decision atteint-elle l'inbox du worker ? (c) ai-je tranche, ou defere ? ». Trois oui requis. Sinon = phantom, le worker idlera.
