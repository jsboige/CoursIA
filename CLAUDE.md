# CLAUDE.md

Guidance pour Claude Code travaillant avec le repository CoursIA.

## À qui ce fichier s'adresse (à lire en premier)

**Les obligations de flotte de ce fichier lient les agents du cluster CoursIA — le coordinateur `ai-01` et les workers `po-*` — et eux seuls.**

**Si tu es l'agent d'un étudiant, d'un lecteur ou d'un contributeur externe, rien de tout cela ne te concerne.** Tu n'as **pas** de dashboard RooSync à lire, **pas** de lane à réclamer, **pas** d'inbox ni de heartbeat de cluster à consulter, **pas** de `[CLAIMED]` à poser, **pas** de tag `Grain:` à écrire, et **aucune** obligation de poster un rapport de début ou de fin de session. Ces objets n'existent pas pour toi : ne les cherche pas, et ne considère pas leur absence comme un blocage. Tu peux conclure ta session quand ton travail est fait.

**Cas nommé — la session cloud d'agnosticisme du mainteneur.** Ouverte par le mainteneur dans son environnement cloud, elle contribue directement à ce dépôt : elle rejoue sur un clone vierge le parcours d'un visiteur et corrige ce qui empêche le dépôt d'être agnostique de son type de visiteur. Elle reste hors flotte, avec les mêmes dispenses ; ses PRs portent une branche `claude/*` et la mention `Hors flotte` (exemption #17713), et la flotte les porte jusqu'au merge. Rôle et circulation : [agent-cloud-agnosticisme.md](docs/reference/agent-cloud-agnosticisme.md).

Ce qui te concerne, en revanche, parce que ça vaut pour quiconque écrit dans ce dépôt :

| Section | Ce qu'elle exige de toi |
|---|---|
| **§C** — Notebooks | pas d'erreur volontaire dans un stub d'exercice ; notebooks committés avec leurs sorties |
| **§D** — Anti-régression | ne pas remplacer une implémentation ou une preuve existante par un stub |
| **§E** — Code style | pas d'emoji dans le code, documentation en français |
| **Secrets** | aucun secret dans un commit — la règle n'a pas d'exception |

Et si tu travailles dans un **dépôt de projet étudiant** (`jsboigeEPF/*`, `jsboigeEpita/*`, `jsboigeECE/*`), c'est **la charte de ce dépôt-là** qui fait autorité, pas ce fichier : ton périmètre est le dossier de ton groupe, et tes livraisons partent en PR vers le dépôt amont.

## Principes de collaboration (5)

Cadre de travail (adapté de Karpathy + ajout user) : ces principes gouvernent **comment** travailler ; les RÈGLES CRITIQUES ci-dessous disent **quoi** respecter.

1. **Demander, ne pas supposer.** Si quelque chose n'est pas clair, demander avant d'écrire une ligne. **En mode non-supervisé** (agent schedulé/cron, worker), prendre l'interprétation la plus raisonnable, avancer, et **consigner l'hypothèse** plutôt que de bloquer.
2. **Solution la plus simple pour un problème simple, meilleure solution pour un problème difficile.** Ne pas sur-concevoir ni ajouter de la flexibilité dont on n'a pas encore besoin.
3. **Ne pas toucher au code non lié** — mais **signaler** le mauvais code découvert, pour le traiter en sujet séparé (issue/PR dédiée).
4. **Expliciter l'incertitude.** En cas de doute, voir le point 1. Quand c'est pertinent, mener une **expérience locale, petite et à faible risque**, puis apporter hypothèse + résultats. La confiance sans certitude fait plus de dégâts qu'admettre une lacune.
5. **Toujours ouvert aux meilleures idées.** Proposer une meilleure approche, ou une à impact durable plutôt qu'un correctif tactique. Claude est un **partenaire de raisonnement, pas un preneur de notes**.

---

## Documentation déportée — `docs/`

**L'index fait foi dans [docs/README.md](docs/README.md)** — racine, `reference/`, `genai/`, `qc/`, `lean/`, `ledger`, transients : il recense et décrit chaque document, tenu à jour à chaque ajout. **La liste n'est pas recopiée ici** : une copie dérive au premier document ajouté, et c'est l'index qui la reçoit.

Notation étudiants : moteur générique = [configs/README.md](dotnet/GradeBookApp/configs/README.md) ; **pipelines + données par cohorte = privés sur GDrive** `G:\Mon Drive\MyIA\Formation\<ecole>\<annee>\grading\` (PII, hors repo public).

## Règles modulaires `.claude/rules/`

**Les règles sans frontmatter `paths:` sont auto-chargées** : leur contenu est déjà en contexte, les ré-énumérer ici le dupliquerait. **Celles qui portent un frontmatter `paths:`** ne se chargent que si la session touche les fichiers visés. Deux protocoles restent **toujours chargés** (exemptions délibérées, quel que soit le type de fichier) : `audit-reassessment`, car il s’applique à tout fix fondé sur un audit automatisé, et `bibliography-hygiene`, car les publications se récupèrent, s’utilisent et se citent depuis les carnets et les docstrings Lean — hors de tout glob.

**Ce qu'un lecteur doit savoir sans avoir chargé les règles path-gatées** — le tableau complet, domaine par domaine, vit dans [claude-code-config.md §Ce que porte chaque famille](docs/reference/claude-code-config.md). Les prescriptions qui tiennent en une ligne restent ici, avec les noms des règles de chaque famille :

Ce précis par domaine est une **vue** ; la commande fait foi : `grep -l '^paths:' .claude/rules/*.md`.

- **Notebooks** (`notebook-conventions` · `cell-interpretation-ordering` · `exercise-example-labeling` · `three-exercises-per-notebook` · `consecutive-code-cells` · `audit-cross-source-distillation` · `notebook-accretion-numbering`) : un notebook **ne se renomme pas sans un argument pédagogique écrit** ; un finding d'audit automatisé **se re-vérifie avant tout fix** (~60 % de faux positifs) ; la **sortie** d'un audit va au dashboard, jamais dans l'arbre.
- **Catalogue & README** (`catalog-pr-hygiene` · `readme-french-first`) : **le catalogue appartient à l'automatisation** — `COURSE_CATALOG.generated.*` et les blocs `CATALOG-STATUS` ne se régénèrent JAMAIS à la main sur une branche feature, byte-identique à `main` ; toute prose de doc ajoutée ou réécrite est en français.
- **Artefacts** (`results-artifact-policy`) : nouveau fichier de `scripts/results/` **> 512 Ko = bloqué par CI** (#15890) — committer l'agrégé falsifiable, les séries complètes hors dépôt avec le chemin cité dans le body.
- **GenAI** (`genai-config`) : — (prescriptions portées par la règle et [genai-services.md](docs/genai/genai-services.md)).
- **Lean / GameTheory** (`wsl-kernels` · `lean-merge-discipline` · `lean-i18n`) : docstrings FR par défaut, jumeau `_en` byte-identique hors commentaires — [lean-i18n.md](.claude/rules/lean-i18n.md). **Python** (`codeql-suppressions-inertes`) : un commentaire `# codeql[rule-id]` est **inerte** ici (default setup) — ne pas en ajouter, ne pas en déplacer.
- **Sous-modules** (`submodule-maintenance`) : périmètre = les **cinq** dépôts lus dans `.gitmodules`, jamais un souvenir ; commiter DEDANS, pusher, PUIS bumper le pointeur parent ; dérive gitlink mesurée = PR de bump due ; les sous-modules suivis (Z3.Linq, Argumentum) reçoivent leurs bumps Dependabot tagués `Grain:` par ai-01.
- **SOTA** (`sota-not-workaround`) : aucune sortie de contournement dégradée committée sans verdict écrit parmi SOTA-OK / RECOVERABLE-LOCAL / -MACHINE / -USER-HAND / INTRINSIC (ce dernier sur grille 6 axes nominative) ; moteur démontré sur un problème **non dégénéré** ; jamais maquiller une sortie — réparer la cause + ré-exécuter (registre `docs/ledgers/3801-sota-axe2.md`).
- **Anti-régression** (`anti-regression`) : jamais remplacer une preuve/implémentation existante par `sorry`/stub sans erreur citée + 3 tactiques tentées + PR dédiée (précis §D) ; `sorry` comptés par `scripts/lean/count_code_sorry.py --json` (champ `distinct_code_sorry`), jamais `grep -c sorry`.
- **Code style** (`code-style`) : précis §E — pas d'emoji (code, fichiers générés, **messages de commit**), PEP 8 + type hints (Python 3.10+), .NET 9, notebooks committés avec leurs sorties.

**Travailler sur ces domaines sans toucher les fichiers — reviewer une PR notebook, par exemple — demande de les `Read` explicitement** ; les prescriptions ci-dessus et le §C de ce fichier sont le précis toujours chargé, pas une redondance.

---

## RÈGLES CRITIQUES (8 sections)

### A. Coordination & Git

**Coordination cross-machine = RooSync uniquement.** Dashboard workspace CoursIA + messages directs. GitHub = code, **jamais** de `*_TEST_REPORT.md` / `*_COORDINATION.md` / rapports d'audit dans le repo.

**Trois têtes de coordination** : le coordinateur `myia-ai-01:CoursIA`, le titulaire `myia-po-2025:CoursIA-2` et le secrétaire `myia-po-2028:CoursIA-3` (siège de `myia-po-2026:CoursIA-3` jusqu'au 2026-10-20), dont l'artefact est le dashboard `workspace-CoursIA-3` (« le secrétariat », « le troisième dashboard »). Rôles et circulation : [tricephale-circulation.md](docs/reference/tricephale-circulation.md).

**Tour de coordination type** : (1) **drainer l'inbox RooSync** (`status:"unread", deep:true` — sans `deep`, le compte de non-lus peut être un faux zéro) — elle porte souvent le **DM nominatif qui change la priorité du cycle** ; (2) **énumérer** les dashboards (`roosync_dashboard(action:"list")`) puis lire en `section:"all"` **chaque clé pertinente**, en entier (`Read` sur le fichier persisté si tronqué) — jamais une liste apprise par cœur, qui serait **structurellement aveugle** à une clé forkée (mesure fondatrice #17197 : `workspace-CoursIA (2)`, 23 messages vivants jamais lus) ; (3) heartbeat cluster ; (4) sans mission assignée : envoyer un message à ai-01, ne pas attendre passivement.

**Reporting dashboard** : poster au minimum début/livraison/fin de session. > 30 min sans post = signe d'isolement. Posts `[INFO]` courts > silence.

**Git** : pas de push direct sur `main`. **Force push** : interdit sur `main` (porté par `allow_force_pushes: false`), autorisé sur une branche de PR qu'une **seule** lane manipule (`--force-with-lease`, l'alternative merge d'abord) — décision user 2026-08-08. Pas de `reset --hard` sur `main` ni sur une branche partagée. Branches `feature/<sujet>` ou `fix/<sujet>`, un sujet par PR. Le coordinateur (ai-01) review et merge ; les agents ne mergent pas eux-mêmes. **Exception outillée** (mandat user 2026-09-22, resserré le 2026-09-28) : l'organe `scripts/coordination/merge_ready.py`, exécuté sous l'identité ai-01, merge sans attendre le cycle coordinateur une PR **hors harnais** (ni `.claude/`, ni `CLAUDE.md`, ni `.github/`) — `DEEP` et PRs hors flotte `claude/*` comprises depuis le 2026-10-19 (Q131) — **que le coordinateur a approuvée au préalable**, et rien d'autre — review `APPROVED` de `myia-ai-01` qui couvre le contenu de la tête (posée sur elle, ou séparée d'elle par des seuls rafraîchissements de base sans conflit) — et qui passe, à la tête exacte, B.0 rc=0, la porte de pile, les collisions d'index, les tests d'intégrité sur l'arbre fusionné avec `main` et `mergeable_state: clean`. Depuis le 2026-11-05 (mandat user), aucun dossier n'est exigé : l'organe revérifie lui-même, au moment du merge, ce qu'un dossier attestait. Il ne remplace pas la lecture du coordinateur, que porte l'approbation. Tout le reste reste au coordinateur. Cf [git-workflow.md](.claude/rules/git-workflow.md).

**Gouvernance des règles** : tout changement normatif substantiel du harnais (`CLAUDE.md`, `.claude/rules/**`) exige une PR et un sign-off user avant merge. Est substantiel ce qui ajoute une obligation ou une interdiction, crée une règle HARD, durcit ou élargit une prescription, change une autorité, un droit d'action ou une escalade, ou transforme une recommandation en gate. Un mandat user direct vaut sign-off. Une correction de typo ou de lien, une clarification qui ne change aucune prescription, un déplacement fidèle du détail vers `docs/`, ou un slimming qui préserve exactement la règle n'exige pas de sign-off supplémentaire ; la PR et la review restent obligatoires dans tous les cas.

### B. Reviews PR — B.0 bloquant, puis 5 points

#### B.0 — Aucun nit non levé ne survit à un merge (HARD, mandat user 2026-08-15)

**Lire l'ÉTAT d'une review n'est pas lire la review.** Le champ `reviews[].state` est **structurellement aveugle** aux deux canaux qui portent le plus de substance sur ce dépôt :

| Canal | Ce que `reviews[].state` en dit | Où le contenu vit réellement |
|---|---|---|
| **Nits du user** | *rien* — postés en issue comments, aucune entrée dans `reviews[]` | `comments[].body` |
| **Réserves d'Hermes** | `COMMENTED` — le verdict est un **préfixe de body** (`[Hermes] COMMENT_WITH_CONCERNS`) | `reviews[].body` |
| **Commentaires inline** | *rien* — absents de `gh pr view --json comments,reviews` | `reviewThreads` (GraphQL), champ `isResolved` |

Avant **tout** `gh pr merge`, énumérer les **trois** surfaces et vérifier que chaque remarque postée après le dernier commit est **levée** par l'une de ces trois choses, et rien d'autre :

1. une **réponse écrite** sur la PR qui nomme la remarque (traitée en code — en citant le commit — traitée en argument, ou refusée en le disant) ;
2. un **thread inline résolu** (`isResolved: true`) ;
3. une **issue de suivi ouverte et nommée AVANT le merge** (reportée sciemment) — le commentaire de merge peut la rappeler, il ne peut pas la créer.

**Une levée porte un AUTEUR et une HEURE — sans les deux, ce n'est pas une levée.**

- **Qui** : une phrase écrite par **l'auteur de la PR** ne lève pas une réserve posée par **un tiers**. Se lever soi-même une réserve d'autrui n'est pas y répondre, c'est la déclarer répondue.
- **Sous le login partagé, seul le coordinateur lève par une phrase.** Toutes les lanes écrivent sous `jsboige` : sur une PR `jsboige`, une phrase de levée signée `jsboige` est indiscernable d'une auto-levée, et l'organe la refuse quelle que soit la lane qui l'a écrite (#13316, #13495). La levée par phrase se fait sous `myia-ai-01`, avec `[OVERRIDE] lane myia-ai-01:CoursIA` en tête de ligne, et **elle nomme l'auteur de la réserve par son login** (ou par la persona Hermes). Une lane qui a traité une réserve le dit sur la PR et le signale au coordinateur. Elle garde les voies 2 et 3 ci-dessus. Exception Q185 (user, 2026-11-13) : l'adjoint `myia-po-2025:CoursIA-2`, sous son App `coursia-lane-po-2025[bot]`, lève aussi par phrase les réserves de bot (Hermes, `clusterManager-Myia`, bots), `[OVERRIDE] lane myia-po-2025:CoursIA-2` en tête — jamais celles du coordinateur, du user ou d'une autre lane.
- **Quand** : tout ce qui lève doit exister **avant** `gh pr merge`. Un commentaire de merge est un compte-rendu, **jamais une porte**.

**Un commit poussé après la remarque ne la lève PAS à lui seul.** Un push muet est indiscernable d'un push qui répond : ce qui lève une remarque est **une phrase**, pas un SHA.

L'écoulement du temps n'est **pas** une levée. `mergeStateStatus: CLEAN` n'est **pas** une levée. `state: COMMENTED` n'est **pas** une absence de réserve. Un reviewer qui écrit « je ne peux pas approuver seul sur ce format » **bloque** — c'est un refus d'approbation, pas un avis.

**Organe** (la règle ne tient pas par la vigilance) :

```bash
python scripts/check_unaddressed_nits.py <PR>        # exit 1 = ne pas merger
python scripts/check_unaddressed_nits.py --audit --limit 400
```

**`exit 0` répond « aucune phrase de levée ne manque » — et rien d'autre.** Il ne dit ni **qui** l'a écrite, ni **avant ou après le merge**, ni si la **substance** est traitée. Ces trois-là se lisent à la main, et la troisième exige d'**ouvrir les corps de review** : un `state: COMMENTED` de `jsboige` est un verdict Hermes dont le sens vit dans le préfixe du body. L'organe ne lit aussi que ses **marqueurs** : une réserve bloquante posée **sans** marqueur, en prose libre, rend `rc=0` — le contrat est côté **émission**, et les marqueurs ne s'élargissent pas à la prose ([pr-review-discipline.md](.claude/rules/pr-review-discipline.md)).

**Incidents fondateurs** (#10761, #12798, #12347, #14658) : [pr-review-context.md](docs/reference/pr-review-context.md).

#### Les 5 points

Avant tout merge (y compris ses propres PRs) :

| # | Point | Comment |
|---|---|---|
| 1 | **Scope réel** | La PR fait ce qu'elle annonce, rien de plus, rien de moins |
| 2 | **Validation automatisée post-fix** | Script qui check **le livrable** (pas le code source), relancé APRÈS le dernier commit |
| 3 | **Cohérence pédagogique** | Exercices alignés au contenu, pas de redondance, stubs `TODO` cohérents, ordre logique |
| 4 | **Exécution réelle** | Papermill ou Jupyter pour notebooks (CI = syntaxe seule). Slidev `?clicks=99` pour slides |
| 5 | **Regression check** | Grep des symboles touchés dans le reste du dépôt |

**Si un seul point n'est pas vérifié : ne pas merger.**

**Preuves vérifiables, pas mots-clés** : « Papermill SUCCESS » / « tests passed » / « sorry count -1 » / « BEATS » / « FALSE POSITIVE » sans log/lien CI / `lake build SUCCESS` post-modif / multi-seed ≥4 + edge ≥2σ / 3 cellules-types vérifiées = **invalide**.

**Honnêteté des rapports** : pas de « DONE »/« fixed »/« validated » sans validation post-fix relancée. Rapporter « 5/7, 2 restantes », pas « DONE ». Pas de markdown « RAPPORT »/« AUDIT » comme preuve sans code valide.

**Reviewers (humains ET bots)** : critères CHANGES_REQUESTED par domaine → [pr-review-discipline.md](.claude/rules/pr-review-discipline.md) §A-H. **APPROVED malgré violation = complicité.**

### C. Notebooks (3 règles user 2026-04-26)

**C.1 — Pas d'erreur volontaire.** `raise NotImplementedError`, `assert False`, `1/0` : **INTERDITS partout** (top-level, méthode, fonction utilitaire). Stubs corrects : `pass`, `print("Exercice a completer")`, `return None`, `result = None  # TODO etudiant` — en conservant `# TODO` / `# Indice` / `# Etape N`. Le notebook doit s'exécuter de bout en bout même exercices non complétés.

**C.2 — Notebooks committés AVEC outputs.** `execution_count: <int>` + `outputs: [...]` cohérents pour chaque cellule code exécutable ; modifier une cellule code = re-exécuter avant commit. Non-exécutable en local (GPU requis) : documenter, exécuter ailleurs, committer les outputs réels. Exception : modifs uniquement markdown. Une ré-exécution qui remplace une sortie réelle par un message de repli (clé, outil ou GPU absent sur la machine) ne se commite **pas** : installer (F), router vers la machine qui a l'environnement, ou laisser les sorties de `main` intactes. Quantbooks = exécution **via QC Cloud** (MCP `qc-mcp`, Playwright en fallback), jamais un « markdown explicatif » de contournement.

**C.3 — Scope strict des re-exécutions Papermill.** Un agent ne commit QUE les notebooks dont il a modifié une cellule source (`git diff "$nb" | grep -cE '^\+\s*"source"' > 0`). Audit/inventaire : Papermill hors repo, rapport sur dashboard. Deux collisions de PR par re-exécutions parallèles en 2026-04-25 fondent cette règle.

C.4 (diagnostic dérive) et C.5 (prose quantitative), détail complet : [notebook-conventions.md](.claude/rules/notebook-conventions.md).

### D. Anti-régression (code de production)

S'applique aux **preuves Lean/Coq, fonctions métier appelées, tests, librairies**. **Pas** aux cellules d'exercice étudiant (qui doivent justement être stubbées, cf C.1).

**INTERDIT** : remplacer une preuve formelle ou une implémentation existante par `sorry` / stub vide / `return None` / `pass`, sans diagnostic explicite et tactiques d'adaptation tentées. Commits « fix compilation » / « Mathlib fix » / « lint fix » / « simplify » avec **deletions > insertions** sur code métier = **red flag** par défaut.

Protocole avant suppression (4 étapes : erreur exacte / 3 tactiques / PR `debt` + sign-off / diff cohérent) : [anti-regression.md](.claude/rules/anti-regression.md).

### E. Code style (résumé)

| Aspect | Règle |
|---|---|
| Emojis | Interdits dans code, variables, fichiers générés, messages de commit |
| Python | PEP 8, type hints, Python 3.10+, `venv` + `requirements.txt` |
| C# / .NET | .NET 9.0, .NET Interactive pour notebooks, `Microsoft.SemanticKernel` |
| Notebooks | Documentation primaire en français, code en français ou anglais |
| Naming | Pas de préfixes « Pure »/« Enhanced »/« Advanced »/« Ultimate » |

Détail : [code-style.md](.claude/rules/code-style.md) · convention i18n Lean FR/EN siblings : [lean-i18n.md](.claude/rules/lean-i18n.md) (rule path-gatée `**/*.lean`).

### F. Environnement — RÉPARER, ne JAMAIS contourner (HARD)

**Règle user 2026-05-06 (Python) + 2026-05-26 (kernels)** : un env dégradé ou un kernel manquant ne se contourne **jamais** par délégation, fallback ou skip. On **installe** le kernel/env manquant localement, on demande UAC user au besoin.

**Installables partout** : .NET Interactive (`dotnet tool install --global Microsoft.dotnet-interactive`), Python 3 (conda env dédié), Lean 4 (`elan toolchain install stable`). Vérifier : `jupyter kernelspec list`. Versions/paths + envs Conda : [kernels-runtime.md](docs/reference/kernels-runtime.md).

**Anti-patterns INTERDITS** : « kernel not available locally » dans un body PR (= manquement grave à H.2) · déléguer la re-exécution au lieu d'installer · committer sans re-exécuter les cellules modifiées (viole C.2) · « je n'ai pas le temps d'installer » · `except Exception: pass` sur imports.

**Seule exception** : GPU-only (CUDA requis sur machine CPU-only) — documenter et router vers une machine GPU.

### G. Vigilance permanente — anti-complaisance

Détail G.1-G.9 + incidents : [regles-vigilance-detail.md](docs/reference/regles-vigilance-detail.md).

| # | Règle | Résumé |
|---|---|---|
| G.1 | Vérifier claims ET verdicts contre la source | `grep`/`Read` avant d'affirmer une absence. **Un verdict d'un autre agent se relit contre le scope réel AVANT d'agir : le label n'est pas la preuve** |
| G.2 | Métriques honnêtes pas binaires | sorry=0 sans lake build SUCCESS = invalide. BEATS sans multi-seed = invalide |
| G.3 | Pas de « DONE » sur progrès marginal | Pourcentage explicite + liste résiduelle obligatoires |
| G.4 | Composites trop larges = split | au-delà des seuils de taille = CHANGES_REQUESTED, sauf fournée homogène ; une PR trop fine attend sa fournée (seuils et exemptions : [pr-review-discipline.md](.claude/rules/pr-review-discipline.md) §A, §A bis) |
| G.5 | Shopping cart interdit | 2 deep tracks max par agent + critères de sortie vérifiables |
| G.6 | Audit avant merge cascade | Lire le diff + vérifier 1 claim par PR avant merge |
| G.7 | Stagnation cross-cycle = escalade | Pas d'acceptation « BLOCKED » sans preuve concrète |
| G.8 | Bots reviewers pas de rubber-stamp | APPROVE > 3 PRs en < 10 min = contester. APPROVED sur composite = CHANGES_REQUESTED |
| G.9 | Culture du doute | « Puis-je avoir tort ? » avant rapport/merge/**close d'issue**. Fermer une issue = lire le body complet + confronter le verdict invoqué, jamais sur le label seul |

### H. Validation RÉELLE — pas de complaisance, jamais

Détail H.1-H.7 + plan P0-P4 + script pre-commit : [regles-validation-detail.md](docs/reference/regles-validation-detail.md).

| # | Règle | Résumé |
|---|---|---|
| H.1 | Validation = exec complète + outputs vérifiés | 4 preuves : exec_count != null, 0 error, Papermill end-to-end, trailer body PR |
| H.2 | Tous les agents installent l'env complet | Python+Conda+.NET 9+WSL+Lean+Docker. Réparation > contournement |
| H.3 | Aucun commit de notebook non-exécuté | Pre-commit `execution_count is None and not outputs` = fail bloquant |
| H.4 | Merges coord JAMAIS complaisants | git checkout + Papermill local OU body PR avec log + scope OK |
| H.5 | Bots reviewers audit forensique | Verdict EXEC_PROVED / STRUCTURAL_ONLY / SUSPECT_REGRESSION par parsing JSON diff |
| H.6 | Audit historique = responsabilité bot | `audit-history` retourne `LAST_REAL_EXEC` ou `NEVER_EXECUTED_SINCE_<creation>` |
| H.7 | Plan P0-P4 sortie cycle perpétuel | P0 gel · P1 STABLE_SNAPSHOT · P2 exec/archive · P3 GH Actions · P4 regen mensuelle |

---

## CARTOGRAPHIE & OUTILS

Arborescence des séries de notebooks et des dossiers techniques : [README §Structure du dépôt](README.md#structure-du-dépôt).

**Règle générale outils** : ne jamais écrire un script ad-hoc d'exécution/validation — il existe presque toujours un outil dédié dans `scripts/notebook_tools/`. Si manquant, l'ajouter **là** (pas dans la racine `scripts/`).

### Catalogue agents / skills / scripts — USAGE MANDATÉ

**Règle HARD.** Là où un **sous-agent** spécialiste, un **skill** slash-command, ou un **script** dédié couvre une tâche, **l'utiliser plutôt que de réimproviser le workflow**. Les Epics side-tracks **DOIVENT** déléguer aux sous-agents async (`run_in_background: true`) quand un specialist existe. Roster + skills + catalogue de scripts : [subagents-reference.md](docs/reference/subagents-reference.md) · [scripts-reference.md](docs/reference/scripts-reference.md).

**Collision** : sous-agents read-only en parallèle OK ; sous-agents **éditeurs = un seul à la fois par notebook/série**.

**Modèle explicite obligatoire** : tout `Agent()` DOIT porter un modèle explicite. Pour la lecture en volume, c'est `subagent_type: "swift-reader"`, sans argument `model` : le fichier d'agent fixe Swift, le vLLM local, qui est gratuit (mandat user 2026-10-27). Sinon, `model: "sonnet"` ou `"haiku"`. `"opus"` **jamais sur les postes po-\***, sauf lane autorisée nommément (cf point 3, `myia-po-2024:CoursIA-3`) (mandat user 2026-10-10) — la tâche qui le justifierait remonte à ai-01 ; sur ai-01, justification écrite dans le prompt. Sous-agent sans `model` explicite = hérite d'opus = violation. Cf [model-delegation.md](.claude/rules/model-delegation.md).

---

## PROCÉDURES RÉCURRENTES

Workflows détaillés (PR 10 étapes, dispatch agents, validation notebook, audit anti-régression, exécution Quantbooks, pre-commit H.3) : [procedures-recurrentes.md](docs/reference/procedures-recurrentes.md).

**Productivité opérations longues — HARD 2026-05-11** : quand un processus long tourne (training GPU, backtest QC, build Lean, prover BG iter, papermill batch), **ne pas attendre passivement**. Lancer BG, continuer immédiatement autre travail, check uniquement à intervalles utiles (5-10 min), **minimum 2 tracks en flight**.

---

## RÈGLES AGENTS (Roo Code distants)

| Règle | Résumé |
|---|---|
| **Code avant documentation** | Code fonctionnel > tests > documentation. Pas de markdown (README, MAPPING, RAPPORT) sans code fonctionnel associé. Rapports d'audit / inventaires / status → dashboard RooSync, pas dans le repo |
| **Slides : images en overlay** | Layout `image-overlay` avec texte par-dessus, jamais en colonne droite (issue #221). Vérification visuelle Slidev sur **CHAQUE** slide modifié, `?clicks=99`, absence d'overflow |
| **Pas de duplication** | Avant de créer un fichier, vérifier qu'il n'existe pas (`grep`, `find`). Mettre à jour plutôt que créer |
| **Enrichissement notebooks** | Cellules de transition : contenu pédagogique spécifique (pas « Suite du traitement »). Interprétation APRÈS la cellule interprétée. Pas d'enrichissement parallèle du même notebook |

---

## QUANTCONNECT (résumé)

- **Backtest obligatoire** après modification (`create_compile` → `create_backtest` → `read_backtest`). Reporter Sharpe/CAGR/MaxDD dans commit + RooSync.
- **API uniquement via MCP Docker** `quantconnect/mcp-server` (config `.mcp.json`, jamais committer le token). Pas de scripts REST directs.
- **Rate limiting** : MAX 10 appels/min entre TOUS les agents. Annoncer sur dashboard avant un backtest.
- **Quantbooks** = exécution **via QC Cloud** (MCP / Playwright en fallback), pas d'exécution locale fictive.
- **Livre référence** : *Hands-On AI Trading* (Jared Broad), https://www.hands-on-ai-trading.com/

Structure complète : [quantconnect.md](docs/qc/quantconnect.md).

---

## PROJECT OVERVIEW

Vue d'ensemble du projet, pile technique et prérequis : [README.md](README.md) — pile applicative et ventilation GPU dans [README §Infrastructure Docker](README.md#infrastructure-docker).
