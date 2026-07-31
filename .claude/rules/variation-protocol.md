# Protocole de variation — anti-monoculture, tag déclaré + merge-gate coordinateur

S'applique à **tous les workers** (`po-*`) **et au coordinateur `ai-01`**. Source : mandat user 2026-07-21 (« Tu constateras que la monoculture de PRs facile est toujours bien là, il faut que tu steere mieux, c'est peut-être le moment d'imposer un protocole de variation »).

**Ce fichier n'est PAS une redite de [proactive-coordination.md](proactive-coordination.md) R6/R7.** Les *concepts* (tiers DEEP/MED/LIGHT, cap 1 LIGHT/lane/jour, rotation genres, never-idle outcome-test) y sont déjà posés — et pourtant la monoculture persiste, parce qu'ils étaient **auto-évalués, invisibles, et non-gatés au merge**. Ce protocole ajoute la **mécanique d'enforcement manquante** : un **tag déclaré auditable**, un **merge-gate coordinateur**, et une **obligation de provisionnement** qui lie `ai-01`. C'est la couche qui fait *mordre* R6/R7, pas un contrepoids.

## 1. Le tag de grain — déclaré, objectif, non-gamable (HARD)

Tout `[CLAIMED]` (dashboard) **et** tout body de PR portent en **première ligne** :

```
Grain: <TIER>/<GENRE> — lane <machine:workspace> — prev: <TIER>/<GENRE> #<PR>
```

Ex. `Grain: DEEP/lean — lane myia-po-2026:CoursIA — prev: LIGHT/guard #8954`.

**Champ `prev:` — genre + numéro de PR (la forme que la flotte écrit réellement).** `prev:` documente le grain précédent de la lane pour l'adjacence G-VAR-3 (`<TIER>/<GENRE>`) **et** le lie à une PR vérifiable (`#<PR>`). Le numéro de PR est **plus vérifiable** qu'un genre auto-déclaré seul : un `prev: MED/lean` nu est re-dérivable de mémoire (donc contestable), tandis qu'un `prev: MED/lean #8954` pointe vers une PR réelle dont on peut relire le diff. Mesuré sur la flotte (55 PR taguées post-ratification 2026-07-21) : **100 %** portent déjà le numéro de PR (`prev: MED/tooling #8975`, `prev: MED/lean (#8954 …)`) — la spec précédente `prev: <TIER>/<GENRE>` (sans numéro) n'était respectée par personne. Le genre reste **obligatoire** (c'est la clé d'adjacence G-VAR-3) ; le numéro est obligatoire aussi. Le checker `variation-tag-guard.yml` ne valide pas le champ `prev:` (il valide `TIER` + `GENRE` + `lane`), donc cette forme n'ajoute ni ne retire aucun gate — c'est une **doc de spec** qui aligne la règle sur la pratique réelle plutôt que d'imposer du churn.

### TIER — test objectif, PAS auto-évaluation de valeur

Le TIER se décide par un **test mécanique**, pour couper le gaming (« mon tranche-de-guards est de la *substance* ») :

| TIER | Test décisif (litmus) | Exemples |
|------|----------------------|----------|
| **DEEP** | `main` contient-il désormais un **résultat/capacité qui n'existait pas**, dont la production a demandé du **raisonnement de domaine** ? | sorry Lean retiré + `lake build SUCCESS` · training/backtest avec verdict multi-seed · nouveau notebook pédagogique exécuté (≥3 exos, outputs réels) · moteur SOTA nouvellement branché (verdict SOTA-OK) · module de recherche avec résultat falsifiable |
| **MED** | Étend de la substance existante **avec ré-exécution/vérification**, et **change quelque chose** (pas « 0 trouvé ») | enrichissement pédagogique + ré-exec · audit borné dont le finding **change une décision** · exercice ajouté + exécuté · refactor avec tests qui passent · audit README fichier-entier corrigeant un drift **structurel** réel |
| **LIGHT** | **« Pourrais-je en générer une douzaine d'autres à la chaîne en scannant l'instance suivante ? »** → si oui : LIGHT, quel que soit le nom qu'on lui donne | guard-tranche · portability/path-fix · doc-resync (+1/−1 caption/count) · ledger append · fix accent/leak/FP · propagation de marqueur |

Le litmus LIGHT (« générable en série par scan ») est le **cœur anti-gaming** : guards, resyncs, ledger-entries, accents passent TOUS ce test → tous LIGHT, peu importe l'étiquette que le worker leur colle.

### GENRE — étiquette de rotation

`lean` · `qc` · `training` · `genai` · `notebook-python` · `notebook-dotnet` · `docs` · `guard` · `refactor` · `ledger` · `readme` · `test`. Sert la règle anti-consécutif (§2, G-VAR-3).

**Le GENRE est le TYPE DE TRAVAIL, jamais la famille où vivent les fichiers.** C'est la seconde voie de contournement, et elle est plus discrète que la sur-cotation de tier : un même rollout scan-générable change d'étiquette à chaque tranche selon le répertoire qu'il traverse, et G-VAR-3 ne voit jamais deux fois le même genre. Une passe de stamping `metadata.cost` est du `ledger` — qu'elle traverse `GenAI/`, `Search/` ou `Probas/`. La tagger `genai` parce que les notebooks sont dans `GenAI/`, puis `data` parce que les suivants sont dans `Search/`, fait passer une vague unique pour de la variété.

Test : **si le prochain grain de ce rollout tombait dans une autre famille, changerais-je le GENRE ?** Si oui, le genre choisi décrit le répertoire, pas le travail — reprendre le genre du travail.

> Incident fondateur (2026-07-28, rollout `metadata.cost` #8056) : quatre tranches d'un seul rollout scan-générable ont porté **trois étiquettes différentes** — #8732 `DEEP/genai`, #8735 `MED/genai`, #8699 `MED/data`, #8697 antérieure. Aucune n'a déclenché G-VAR-2 ni G-VAR-3, alors que les quatre sont LIGHT par le litmus (« j'en génère une douzaine en scannant la série suivante » — c'est littéralement ce que fait « tranche 2 »). Le coordinateur en a mergé plusieurs sans auditer le tag : la responsabilité est partagée, et le merge-gate §3 lit désormais le genre contre le **type de travail**, pas contre le chemin des fichiers.

## 2. Les trois gates durs

- **G-VAR-1 — Plat principal DEEP ou MED.** La PR-plancher du cycle (le `≥1 PR/wakeup` de [proactive-coordination.md](proactive-coordination.md) R1) **DOIT** être DEEP ou MED. **Une LIGHT ne satisfait JAMAIS le plancher.** Le pool global (`gh issue list --state open`, ~65 issues) porte toujours du DEEP/MED à tous les niveaux → le plancher-substance est toujours atteignable ; la monoculture vient du choix du plus facile *disponible*, pas d'une absence de substance.
- **G-VAR-2 — Cap LIGHT = 1/lane/jour, agrégé.** Au plus **une** LIGHT par lane par jour, **toutes catégories LIGHT confondues**. C'est ce qui ferme le gaming « guard + resync + ledger = 3 familles différentes » : ce sont 3 LIGHT → **une seule** compte, les autres attendent demain ou cèdent la place à du DEEP/MED.
- **G-VAR-3 — Pas deux fois le même GENRE **LIGHT** consécutif ; DEEP/MED same-genre seulement si substance genuinement distincte.** Le ban **absolu** vise les **genres LIGHT** : `guard`→`guard`, `ledger`→`ledger`, `docs`→`docs`, `readme`→`readme`, `test`→`test` = **bloqué** dès 2 (la vague se forme dès 2 — durcit le « après 3 grains similaires » de R6, trop laxiste). Pour un genre **DEEP ou MED dans le domaine-cœur d'une lane spécialiste** (`lean` pour po-2026, `qc` pour po-2024, `training`/`genai` selon la lane), **deux grains same-genre consécutifs sont autorisés SI chacun est une substance genuinement distincte** — théorème / module / résultat différent, produit par du raisonnement de domaine neuf, **pas** une variante scan-générée. Un spécialiste Lean qui enchaîne deux preuves DEEP **distinctes** (ex. #7649 puis #2159 Grothendieck) n'est **PAS** la monoculture visée. Le tell décisif reste le litmus LIGHT : « pourrais-je générer le suivant en scannant l'instance d'à-côté ? » — **oui** → c'est la vague, bloqué **même sous une étiquette DEEP** ; **non**, il a fallu du raisonnement de domaine neuf → OK.

## 3. Merge-gate coordinateur (ai-01) — les dents (HARD)

Le protocole ne mord que si `ai-01` **cesse de merger passivement la monoculture**. À chaque passe de merge, pour chaque PR, `ai-01` **lit le tag** et croise avec les grains récents de la lane :

- **PR LIGHT d'une lane ayant déjà mergé une LIGHT aujourd'hui** (G-VAR-2 violé) → **HOLD** : commenter « variation-protocol G-VAR-2 : LIGHT-du-jour déjà consommée sur cette lane ; apporte un DEEP/MED ou attends demain », **ne pas merger**.
- **2ᵉ même-GENRE consécutif** (G-VAR-3 violé) → **HOLD** *seulement si c'est un genre LIGHT (`guard`/`ledger`/`docs`/`readme`/`test`) OU un DEEP/MED non-distinct (variante scan-générée)* : « variation-protocol G-VAR-3 : `<genre>`→`<genre>` ; change de genre ». Ne pas merger. Un 2ᵉ DEEP/MED **genuinement distinct** dans le domaine-cœur de la lane (ex. Lean spécialiste, preuve différente) **passe** — ne pas HOLD une preuve dure au motif du seul label de genre.
- **Plancher tenu par une LIGHT** (G-VAR-1 violé) → steer vers un grain DEEP/MED du pool, nommé.
- **Tag mal dérivé** — tier sur-coté au regard du litmus (scan-générable étiqueté DEEP/MED), ou genre pris sur la famille plutôt que sur le type de travail → `ai-01` **re-qualifie le tag lui-même** avant d'appliquer les gates, puis traite la PR selon le tag corrigé. **Le tag déclaré n'est pas auto-exécutoire** : il rend le grain auditable, il ne le définit pas. Merger sans lire le tag, c'est laisser le protocole s'auto-certifier — et c'est ainsi que le rollout #8056 a traversé quatre tranches sans jamais déclencher un gate.
- **Tag incomplet — `lane` absente** → **HOLD jusqu'à ce que la lane soit déclarée**. G-VAR-2 est un cap **par lane et par jour** : un grain qui ne dit pas de quelle lane il vient est **structurellement incomptable**, et le cap devient inapplicable sans que personne n'ait à le contourner. Le champ `lane` de §1 n'est donc pas de la décoration de reporting, c'est la clé d'agrégation du gate. (Constaté sur #8697 et #8699, deux tranches du même rollout, toutes deux sans lane.)

Le HOLD **ne sanctionne jamais la lane en idle** (cf [coordinator-discipline.md](coordinator-discipline.md) R4) : il est **toujours accompagné d'un grain DEEP/MED nommé** du pool global, poussé en **double canal** (DM inbox + `[DISPATCH→inbox]` dashboard). HOLD sans grain de remplacement = échec coordinateur, pas enforcement.

**Exception plancher** : ne jamais bloquer l'**unique** PR qui garde une lane hors-idle *si* le pool était réellement vide — mais le pool n'est jamais vide (§2 G-VAR-1), donc en pratique on **redirige**, on ne bloque pas à sec.

## 4. Obligation de provisionnement — ce qui lie ai-01 (HARD)

La cause racine de la monoculture est **autant** un défaut de provisionnement coordinateur qu'un réflexe de facilité worker : quand `ai-01` ne stocke pas de substance, le worker tombe sur les veines faciles générables-à-la-demande. Donc **chaque cycle `/coordinate`**, `ai-01` :

1. **Provisionne ≥1 grain DEEP/MED par lane** (la « loterie substance », cf [[feedback-substance-lottery-provisioning]]), **groundé firsthand** (`gh issue view`), varié en genre d'une lane à l'autre — pour que le plat principal soit disponible **sans** self-serve de veine facile.
2. **Varie la loterie d'un cycle à l'autre** : ne pas re-provisionner le même genre à la même lane deux cycles de suite (le coordinateur applique G-VAR-3 à son propre dispatch).

Sous-provisionner puis merger la monoculture qui en résulte = **le** manquement que ce protocole corrige. « Steere mieux » = provisionne + gate, pas « constate la vague au merge ».

## 5. Auto-détection (worker et coordinateur)

Avant de claim / de merger, une question : **« ce grain est-il générable-en-série (LIGHT) ET (déjà une LIGHT-jour OU même-genre-que-le-précédent) ? »** — si oui, c'est la monoculture : le worker pioche un DEEP/MED du pool à la place ; le coordinateur HOLD+redirige. Le tag rend la réponse visible en un coup d'œil.

## Voir aussi

- [proactive-coordination.md](proactive-coordination.md) — R1 (≥1 PR/wakeup plancher), R5 (pool global cross-lane), R6 (variété/rotation), R7 (never-idle outcome-test, tiers DEEP/MED/LIGHT). **Ce protocole opérationnalise R6/R7.**
- [coordinator-discipline.md](coordinator-discipline.md) — R4 (jamais sanctionner l'idle : HOLD toujours + grain de remplacement), R5 (steer qui ATTEINT/VRAI/DÉCIDE).
- `~/.claude/projects/d--CoursIA/memory/feedback-substance-lottery-provisioning.md` — loterie substance ungated (obligation §4).
- `~/.claude/projects/d--CoursIA/memory/feedback-vary-backlog-not-accent-day.md` — jamais une journée d'un seul registre.
