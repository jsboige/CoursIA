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

**Forme canonique vs substance (le guard est agnostique à la ponctuation).** La ligne ci-dessus est la **forme canonique** (`—` em-dash, libellés minuscules). Le guard d'enforcement ([`variation-tag-guard.yml`](../../.github/workflows/variation-tag-guard.yml)) matche par **mot-clé** (`Grain:`, `lane`) en casse insensible, après neutralisation de la décoration markdown (`tr -d '*\`'`) — il ne voit **ni** le séparateur (`—` / `·` / virgule) **ni** la casse des libellés (`Lane:` / backticks passent). Ce que G-VAR-2/G-VAR-3 et le coordinateur vérifient est la **substance** (TIER par le litmus, GENRE dans l'énumération §1, `lane` présente) — pas la ponctuation. Un tag existant en variante de présentation n'est **pas** une non-conformité à reformatter : ne pas forcer du churn cosmétique sur un tag valide. (See #8934 tranche (C).)

### TIER — test objectif, PAS auto-évaluation de valeur

Le TIER se décide par un **test mécanique**, pour couper le gaming (« mon tranche-de-guards est de la *substance* ») :

| TIER | Test décisif (litmus) | Exemples |
|------|----------------------|----------|
| **DEEP** | `main` contient-il désormais un **résultat/capacité qui n'existait pas**, dont la production a demandé du **raisonnement de domaine** ? | sorry Lean retiré + `lake build SUCCESS` · training/backtest avec verdict multi-seed · nouveau notebook pédagogique exécuté (≥3 exos, outputs réels) · moteur SOTA nouvellement branché (verdict SOTA-OK) · module de recherche avec résultat falsifiable |
| **MED** | Étend de la substance existante **avec ré-exécution/vérification**, et **change quelque chose** (pas « 0 trouvé ») | enrichissement pédagogique + ré-exec · audit borné dont le finding **change une décision** · exercice ajouté + exécuté · refactor avec tests qui passent · audit README fichier-entier corrigeant un drift **structurel** réel |
| **LIGHT** | **« Pourrais-je en générer une douzaine d'autres à la chaîne en scannant l'instance suivante ? »** → si oui : LIGHT, quel que soit le nom qu'on lui donne | guard-tranche · portability/path-fix · doc-resync (+1/−1 caption/count) · ledger append · fix accent/leak/FP · propagation de marqueur |

Le litmus LIGHT (« générable en série par scan ») est le **cœur anti-gaming** : guards, resyncs, ledger-entries, accents passent TOUS ce test → tous LIGHT, peu importe l'étiquette que le worker leur colle.

### GENRE — étiquette de rotation

`lean` · `qc` · `training` · `genai` · `notebook-python` · `notebook-dotnet` · `docs` · `guard` · `refactor` · `ledger` · `readme` · `test` · `tooling` · `research-code`. Sert la règle anti-consécutif (§2, G-VAR-3).

**L'énumération est CLOSE.** Un genre écrit hors de cette liste n'est pas un quinzième genre : c'est un **alias** que le merge-gate normalise (table ci-dessous) avant d'appliquer les gates. La fermeture n'est pas de la bureaucratie de vocabulaire — c'est ce qui rend G-VAR-3 applicable. L'adjacence compare des genres ; si le vocabulaire est ouvert, deux grains du même travail sous deux étiquettes différentes ne sont **jamais** vus comme consécutifs, et le ban LIGHT devient inatteignable par simple choix de mot.

**Le GENRE est le TYPE DE TRAVAIL, jamais la famille où vivent les fichiers.** C'est la seconde voie de contournement, et elle est plus discrète que la sur-cotation de tier : un même rollout scan-générable change d'étiquette à chaque tranche selon le répertoire qu'il traverse, et G-VAR-3 ne voit jamais deux fois le même genre. Une passe de stamping `metadata.cost` est du `ledger` — qu'elle traverse `GenAI/`, `Search/` ou `Probas/`. La tagger `genai` parce que les notebooks sont dans `GenAI/`, puis `data` parce que les suivants sont dans `Search/`, fait passer une vague unique pour de la variété.

Test : **si le prochain grain de ce rollout tombait dans une autre famille, changerais-je le GENRE ?** Si oui, le genre choisi décrit le répertoire, pas le travail — reprendre le genre du travail.

**La seconde forme du même contournement : le genre composé `<famille>-<genre>`.** Le paragraphe ci-dessus interdit de *choisir* le genre d'après le répertoire ; la pratique a trouvé le chemin voisin, qui est d'**agrafer** le répertoire au genre. `lean-ci`, `lean-tooling`, `cjk-ci`, `audit-tooling` : chacun est un genre privé, valable pour une seule famille, donc invisible à l'adjacence. Une lane qui fait quatre fois le même type de travail dans quatre familles affiche quatre genres différents et ne déclenche jamais G-VAR-3. **Un genre composé se réduit toujours à sa tête** : `<famille>-<genre>` → `<genre>`. La famille se lit déjà dans les chemins du diff ; elle n'a rien à faire dans l'étiquette de rotation.

**Table de normalisation** (mesurée sur les 55 PR taguées mergées depuis la ratification du 2026-07-21 — 18, soit **33 %**, portaient un genre hors liste) :

| Écrit | Occurrences | Canonique | Motif |
|---|---|---|---|
| `lean-ci` | 4 | `guard` ou `tooling` (cf. discriminant) | composé `<famille>-<genre>` |
| `test-coverage` | 3 | `test` | synonyme — garder les deux rend le ban `test` inatteignable |
| `refs` | 2 | `docs` | l'hygiène de liens/références est du travail de documentation |
| `lean-tooling` | 1 | `tooling` | composé |
| `cjk-ci` | 1 | `guard` ou `tooling` | composé |
| `audit-tooling` | 1 | `tooling` | composé |
| `documentation` | 1 | `docs` | synonyme |
| `data` | 1 | `ledger` | déjà tranché par l'incident fondateur §1 |
| `Lean` | 1 | `lean` | les genres sont en minuscules |

Deux entrées sont au contraire de **vraies lacunes**, et rejoignent l'énumération plutôt que d'être repliées : **`tooling`** (5 usages — script ou helper qui n'est pas une porte ; ni `guard`, ni `refactor` qui restructure de l'existant) et **`research-code`** (module de recherche/bibliothèque produisant un résultat falsifiable — `notebook-python` est faux dès que le livrable n'est pas un notebook).

**`guard` vs `tooling` — le discriminant est « est-ce que ça peut rougir ».** Un livrable qui ajoute ou corrige un **check susceptible de passer au rouge** est `guard`. Un livrable qui ajoute ou corrige un **script, un helper, un convertisseur** sans statut d'échec propre est `tooling`. C'est ce qui tranche `lean-ci` au cas par cas plutôt qu'en bloc : le job CI qui fait échouer un lake est `guard` ; le wrapper qui l'appelle plus commodément est `tooling`.

**Une entrée rejoint la liste des genres LIGHT de G-VAR-3 sur mesure, jamais sur intuition.** Cette liste (`guard` · `ledger` · `docs` · `readme` · `test`) porte le ban absolu des deux-consécutifs ; l'y ajouter à l'aveugle bloquerait du travail substantiel. Critère : **un genre y entre dès qu'il a accumulé ≥ 2 grains LIGHT mergés**. Au 2026-07-30, `tooling` est à 5 grains MED sur 5 et `research-code` à 1 DEEP sur 1 — aucun des deux ne qualifie ; ils y entreront d'eux-mêmes si la mesure change.

**Un alias n'est pas une violation.** Le worker qui écrit `documentation` ou `lean-ci` n'est ni HOLD ni repris : le coordinateur normalise silencieusement et applique les gates au genre canonique — l'adjacence de `LIGHT/refs` se calcule contre `docs`. Ce qui compte est que deux grains du même travail soient **comptés comme le même genre**, pas que le worker ait mémorisé la liste.

> Incident fondateur (2026-07-28, rollout `metadata.cost` #8056) : quatre tranches d'un seul rollout scan-générable ont porté **trois étiquettes différentes** — #8732 `DEEP/genai`, #8735 `MED/genai`, #8699 `MED/data`, #8697 antérieure. Aucune n'a déclenché G-VAR-2 ni G-VAR-3, alors que les quatre sont LIGHT par le litmus (« j'en génère une douzaine en scannant la série suivante » — c'est littéralement ce que fait « tranche 2 »). Le coordinateur en a mergé plusieurs sans auditer le tag : la responsabilité est partagée, et le merge-gate §3 lit désormais le genre contre le **type de travail**, pas contre le chemin des fichiers.

## 2. Les trois gates durs

- **G-VAR-1 — Plat principal DEEP ou MED.** La PR-plancher du cycle (le `≥1 PR/wakeup` de [proactive-coordination.md](proactive-coordination.md) R1) **DOIT** être DEEP ou MED. **Une LIGHT ne satisfait JAMAIS le plancher.** Le pool global (`gh issue list --state open`, ~65 issues) porte toujours du DEEP/MED à tous les niveaux → le plancher-substance est toujours atteignable ; la monoculture vient du choix du plus facile *disponible*, pas d'une absence de substance.
- **G-VAR-2 — Budget LIGHT proportionnel : 1 LIGHT par tranche de 3 grains mergés, plancher 1/jour.** Le budget d'une lane pour la journée est `max(1, grains_mergés_du_jour // 3)`, **toutes catégories LIGHT confondues** (`guard` + `resync` + `ledger` restent 3 LIGHT, pas 3 familles — le gaming par renommage de genre reste fermé). Une lane qui merge 1 à 5 grains garde donc **exactement l'ancien plafond d'une LIGHT** ; à 6 grains elle en a deux, à 19 elle en a six. Au-delà du budget : la LIGHT attend demain ou cède la place à du DEEP/MED.

  > **Pourquoi un ratio et plus un plafond absolu (2026-07-31, sign-off user).** Le cap `1/lane/jour` traitait identiquement une lane à 1 PR et une lane à 19 merges dont 13 DEEP : le second cas est l'exact opposé de la monoculture, et se voyait sanctionné pareil. Un plafond insensible au débit ne mesure pas la monoculture, il **plafonne le débit**. Pire, il **fabrique** le travail en double qu'il prétend économiser : #8961 (doc du piège d'ordre `strip`→`--update`) a été tenue une journée au titre de G-VAR-2 ; pendant ce hold la doc n'a pas atteint `main`, et **deux autres sessions ont réécrit la même chose** (#8983, #8996, fermées comme doublons) — ~98 lignes rédigées trois fois. Le ratio garde l'intention (une lane ne peut pas être *majoritairement* LIGHT) en la rendant proportionnelle à ce qui est réellement produit. Organe : [`scripts/variation_light_cap.py`](../../scripts/variation_light_cap.py) (le budget est calculé, pas déclaré).
- **G-VAR-3 — Pas deux fois le même GENRE **LIGHT** consécutif ; DEEP/MED same-genre seulement si substance genuinement distincte.** Le ban **absolu** vise les **genres LIGHT** : `guard`→`guard`, `ledger`→`ledger`, `docs`→`docs`, `readme`→`readme`, `test`→`test` = **bloqué** dès 2 (la vague se forme dès 2 — durcit le « après 3 grains similaires » de R6, trop laxiste). Pour un genre **DEEP ou MED dans le domaine-cœur d'une lane spécialiste** (`lean` pour po-2026, `qc` pour po-2024, `training`/`genai` selon la lane), **deux grains same-genre consécutifs sont autorisés SI chacun est une substance genuinement distincte** — théorème / module / résultat différent, produit par du raisonnement de domaine neuf, **pas** une variante scan-générée. Un spécialiste Lean qui enchaîne deux preuves DEEP **distinctes** (ex. #7649 puis #2159 Grothendieck) n'est **PAS** la monoculture visée. Le tell décisif reste le litmus LIGHT : « pourrais-je générer le suivant en scannant l'instance d'à-côté ? » — **oui** → c'est la vague, bloqué **même sous une étiquette DEEP** ; **non**, il a fallu du raisonnement de domaine neuf → OK.

## 3. Merge-gate coordinateur (ai-01) — les dents (HARD)

Le protocole ne mord que si `ai-01` **cesse de merger passivement la monoculture**. À chaque passe de merge, pour chaque PR, `ai-01` **lit le tag** et croise avec les grains récents de la lane :

- **PR LIGHT d'une lane ayant épuisé son budget du jour** (G-VAR-2 violé) → **HOLD** : commenter « variation-protocol G-VAR-2 : budget LIGHT épuisé sur cette lane (`N` LIGHT pour `M` grains mergés) ; apporte un DEEP/MED ou attends demain », **ne pas merger**. Le budget se **calcule** (`max(1, M // 3)`), il ne s'estime pas : `python scripts/variation_light_cap.py --replay <merged.json>` le fait, et c'est cette sortie qu'on cite dans le HOLD. **Ne jamais tenir une LIGHT plus d'une journée** : un hold prolongé sur une doc ou un guard fait réécrire le même travail par une autre lane (#8961 → #8983/#8996). Passé 24 h, soit on merge, soit on ferme en nommant le remplaçant.
- **2ᵉ même-GENRE consécutif** (G-VAR-3 violé) → **HOLD** *seulement si c'est un genre LIGHT (`guard`/`ledger`/`docs`/`readme`/`test`) OU un DEEP/MED non-distinct (variante scan-générée)* : « variation-protocol G-VAR-3 : `<genre>`→`<genre>` ; change de genre ». Ne pas merger. Un 2ᵉ DEEP/MED **genuinement distinct** dans le domaine-cœur de la lane (ex. Lean spécialiste, preuve différente) **passe** — ne pas HOLD une preuve dure au motif du seul label de genre.
- **Plancher tenu par une LIGHT** (G-VAR-1 violé) → steer vers un grain DEEP/MED du pool, nommé.
- **Tag mal dérivé** — tier sur-coté au regard du litmus (scan-générable étiqueté DEEP/MED), genre pris sur la famille plutôt que sur le type de travail, ou genre hors énumération (alias, composé `<famille>-<genre>` : **normaliser via la table §1** avant de comparer) → `ai-01` **re-qualifie le tag lui-même** avant d'appliquer les gates, puis traite la PR selon le tag corrigé. **Le tag déclaré n'est pas auto-exécutoire** : il rend le grain auditable, il ne le définit pas. Merger sans lire le tag, c'est laisser le protocole s'auto-certifier — et c'est ainsi que le rollout #8056 a traversé quatre tranches sans jamais déclencher un gate.
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
