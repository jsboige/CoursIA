# Protocole de variation — anti-monoculture, tag déclaré + merge-gate coordinateur

S'applique à **tous les workers** (`po-*`) **et au coordinateur `ai-01`**. Source : mandat user 2026-07-21 (« la monoculture de PRs facile est toujours bien là, il faut que tu steere mieux, c'est peut-être le moment d'imposer un protocole de variation »).

Les *concepts* (tiers DEEP/MED/LIGHT, rotation des genres, never-idle) sont déjà dans [proactive-coordination.md](proactive-coordination.md) R6/R7 — et la monoculture a persisté, parce qu'ils étaient **auto-évalués, invisibles, non-gatés au merge**. Ce fichier ajoute la mécanique manquante : un **tag auditable**, un **merge-gate**, une **obligation de provisionnement**. C'est ce qui fait mordre R6/R7.

**Détail (justifications mesurées, incidents fondateurs, verbatims)** : [docs/reference/variation-protocol-detail.md](../../docs/reference/variation-protocol-detail.md).

## 1. Le tag de grain (HARD)

Tout `[CLAIMED]` **et** tout body de PR portent en **première ligne** :

```
Grain: <TIER>/<GENRE> — lane <machine:workspace> — prev: <TIER>/<GENRE> #<PR>
```

Ex. `Grain: DEEP/lean — lane myia-po-2026:CoursIA — prev: LIGHT/guard #8954`.

`prev:` documente le grain précédent de la lane (adjacence G-VAR-3) **et** le lie à une PR relisable — le genre est la clé d'adjacence, le numéro rend la déclaration vérifiable ; les deux sont obligatoires.

Le guard ([`variation-tag-guard.yml`](../../.github/workflows/variation-tag-guard.yml)) matche par **mot-clé** (`Grain:`, `lane`), casse insensible, décoration markdown neutralisée : ni le séparateur ni la casse ne comptent. Ce qui est vérifié est la **substance** (TIER par le litmus, GENRE dans l'énumération, `lane` présente). **Ne pas forcer de churn cosmétique** sur un tag valide en substance.

### TIER — test objectif, pas auto-évaluation

| TIER | Litmus décisif | Exemples |
|---|---|---|
| **DEEP** | `main` contient-il désormais un **résultat/capacité qui n'existait pas**, dont la production a demandé du **raisonnement de domaine** ? | sorry Lean retiré + `lake build SUCCESS` · backtest/training avec verdict multi-seed · nouveau notebook exécuté (≥3 exos, outputs réels) · moteur SOTA branché (verdict SOTA-OK) · module de recherche à résultat falsifiable |
| **MED** | Étend de la substance existante **avec ré-exécution/vérification**, et **change quelque chose** (pas « 0 trouvé ») | enrichissement + ré-exec · audit borné dont le finding **change une décision** · exercice ajouté + exécuté · refactor avec tests verts · audit README fichier-entier corrigeant un drift structurel |
| **LIGHT** | **« Pourrais-je en générer une douzaine en scannant l'instance suivante ? »** → si oui : LIGHT, quel que soit le label | guard-tranche · path-fix · doc-resync · ledger append · accent/leak/FP · propagation de marqueur |

Le litmus LIGHT est le **cœur anti-gaming** : guards, resyncs, ledger-entries, accents le passent tous.

### GENRE — énumération CLOSE

`lean` · `qc` · `training` · `genai` · `notebook-python` · `notebook-dotnet` · `notebook-lean` · `slides` · `docs` · `guard` · `refactor` · `ledger` · `readme` · `test` · `tooling` · `research-code`.

**L'énumération se partitionne en deux, et la frontière porte G-VAR-1 :**

| Classe | Genres | Ce qu'un grain y produit |
|---|---|---|
| **CONTENU** | `lean` · `qc` · `training` · `genai` · `notebook-python` · `notebook-dotnet` · `notebook-lean` · `slides` · `research-code` | une capacité, une preuve, un résultat, du matériel pédagogique — ce que le dépôt existe pour offrir |
| **META** | `guard` · `tooling` · `ledger` · `docs` · `readme` · `test` · `refactor` | l'outillage, les garde-fous et la prose *autour* du contenu — nécessaire, jamais suffisant |

Un genre META n'est pas inférieur — un guard qui rougit au bon moment vaut mieux qu'un notebook de plus — mais une flotte qui ne produit que du META construit un atelier sans rien y fabriquer.

**`slides` reste CONTENU quand le grain écrit ou enrichit le contenu du deck** (12 slides de cours neuves = CONTENU, pas `docs`) ; un grain slides qui fait autre chose garde son genre de type de travail — `guard` pour un gate CI de build Slidev, `refactor` pour un script, `tooling` pour un convertisseur.

Un genre hors liste est un **alias** que le merge-gate normalise : pas une violation, le worker n'est ni repris ni HOLD. La fermeture protège G-VAR-3, qu'un vocabulaire ouvert rendrait inatteignable par simple choix de mot.

**Le GENRE est le TYPE DE TRAVAIL, jamais la famille où vivent les fichiers.** Test : *si le prochain grain de ce rollout tombait dans une autre famille, changerais-je le GENRE ?* Si oui, le genre décrit le répertoire — reprendre celui du travail. Le composé `<famille>-<genre>` (`lean-ci`, `cjk-ci`, `audit-tooling`) **se réduit toujours à sa tête** ; les synonymes (`test-coverage` → `test`, `documentation` → `docs`, `data` → `ledger`, `slidev` → `slides`) se normalisent. Table d'alias complète : [détail §Alias](../../docs/reference/variation-protocol-detail.md).

**`guard` vs `tooling` — le discriminant est « est-ce que ça peut rougir ».** Un check susceptible de passer au rouge est `guard` ; un script/helper/convertisseur sans statut d'échec propre est `tooling`.

**Entrer dans la liste LIGHT de G-VAR-3 se mesure, jamais s'intuitionne** : un genre y entre dès **≥ 2 grains LIGHT mergés**.

### Grain REPAIR — hérite du genre de la PR qu'il répare

Un grain dont le livrable principal est **réparer une PR pré-existante** (la débloquer après un PR-gate rouge, lever une review REQUEST_CHANGES, fixer un ratchet Papermill, etc.) **hérite du genre de la PR qu'il répare** :

- Réparer une PR `notebook-python` (ex : #12141 tranche E #12128) → tag `MED/notebook-python` → genre **CONTENU** → tient le plancher G-VAR-1.
- Réparer une PR `lean` (ex : #12252 Lean-21b companion) → tag `MED/notebook-lean` → genre **CONTENU** → tient le plancher.
- Réparer une PR `guard` (ex : #11997 fix #11732 abort --update) → tag `MED/guard` → genre **META** → ne tient **pas** le plancher, comme toute PR META.

Le raisonnement : G-VAR-1 demande « qu'est-ce qui atteint `main` quand ce travail aboutit ? » — la réponse regarde ce qui **arrive sur `main`**, pas ce que le REPAIR a fait. Quand une PR de notebook passe au vert et merge, ce qui arrive sur `main` est un notebook. Le REPAIR est de la fabrication qui sortait de l'entrepôt, pas de l'outillage.

**Cas négatif explicite** : un REPAIR d'une PR **META** reste **META**. Une lane qui ne réparerait que ses propres PR de tooling/docs ne tiendrait toujours pas G-VAR-1. L'échappatoire se ferme d'elle-même.

**Forme du tag** : le REPAIR déclare directement le genre hérité, sans annotation spéciale. Le fait que ce soit un REPAIR se lit dans le titre (préfixe `fix(`) et le diff (`<fichiers de la PR originale> + ajustements`). Une annotation `MED/notebook-python (repair de #11722)` ajoute du bruit sans information : le tag existe pour répondre « quel genre de substance ce grain met-il sur `main` », et la réponse est la même dans les deux cas.

**Tier du REPAIR** : trancher par le litmus habituel. Un REPAIR qui demande une **ré-exécution complète + diagnostic de ratchet** est `MED` (ré-exécution + change quelque chose). Un REPAIR d'**une ligne de body** reste `LIGHT` et consomme le budget G-VAR-2 — `variation-protocol.md` ne crée pas d'exception.

**Sources de l'arbitrage** : ticket #11815 (escalade formelle po-2023 après 3 cycles G-VAR-1 non-tenu sur REPAIR de notebooks, voir DM `msg-20260819T163135-h66acw` et arbitrage `msg-20260819T171752-4jd3od`). La présente clause en codifie la lecture **au cas** en forme **durable**, sous sign-off user (CLAUDE.md §A).

## 2. Les trois gates durs

- **G-VAR-1 — Plat principal DEEP ou MED, dans un genre de CONTENU.** La PR-plancher du cycle (R1 de proactive-coordination) **DOIT** être DEEP ou MED **et** porter un genre de la classe CONTENU. **Une LIGHT ne satisfait JAMAIS le plancher ; un genre META non plus, quel que soit son tier.** Le pool global porte toujours du DEEP/MED de contenu : la monoculture vient du choix du plus facile *disponible*, pas d'une absence de substance.

  **Pourquoi la clause de genre existe** : le tier seul laissait une porte que la flotte a prise sans jamais mentir — un `tooling`/`guard` qui attrape un vrai défaut « change quelque chose », donc **MED** est défendable, donc le plancher paraît tenu, et **zéro contenu livré** (mesuré sur six semaines, aucun gate n'a rougi : [chiffres](../../docs/reference/variation-protocol-detail.md)). Un cycle dont le plat principal est META **n'a pas de plancher tenu**, même avec dix PR livrées. Le remède n'est pas de bannir le META (bienvenu au-delà du plancher, sous budget G-VAR-2 pour ses composantes LIGHT) mais d'exiger qu'**au moins un** grain de contenu porte le cycle.

  **La sécheresse se mesure — [`scripts/pick_idle_grain.py`](../../scripts/pick_idle_grain.py) — elle ne s'auto-évalue pas (#13086).** G-VAR-1 est resté prose auto-déclarée pendant que G-VAR-2 avait son organe, et c'est ce déséquilibre qui l'a rendu inapplicable : `variation_light_cap.py` n'émet que des signaux de comptabilité LIGHT, si bien qu'une lane alternant `guard` → `tooling` → `docs` → `test` ne déclenche **jamais** `GENRE-RUN` tout en produisant zéro contenu indéfiniment. Le picker compte désormais les **merges consécutifs sans genre CONTENU** de la lane et, au seuil (3 par défaut, calibré pour ne pas pouvoir se déclencher sur la lane la plus saine de la flotte), **restreint le tirage aux genres CONTENU** au lieu de se contenter de les pondérer. Ce n'est pas un refus : la lane reçoit un grain, et ce grain tient le plancher — mandat user #13086, « tu prends un deep grain ». L'échappatoire `--ignore-drought` existe pour la lane dont la capability exclut le contenu (GPU-only, vision-only) et **se justifie par écrit**, jamais en silence.
- **G-VAR-2 — Budget LIGHT proportionnel : `max(1, grains_mergés_du_jour // 3)`**, par lane et par jour, **toutes catégories LIGHT confondues**. Une lane à 1-5 grains garde l'ancien plafond d'une LIGHT ; à 6 elle en a deux, à 19 elle en a six. Au-delà : la LIGHT attend demain ou cède la place à du DEEP/MED. Le budget se **calcule** — [`scripts/variation_light_cap.py`](../../scripts/variation_light_cap.py) — il ne se déclare pas.

  **Note d'arbitrage (#11154) — `DEFECT-ALIVE` et dette #11044.** Arbitré (option 1) : les PRs `DEFECT-ALIVE` (dette de review #11044) **consomment le budget LIGHT**, avec exception écrite + mesure de la dette résiduelle citée à chaque merge au cap — justification chiffrée dans [#11154](https://github.com/jsboige/CoursIA/issues/11154). Réouverture : si la dette remonte, c'est le compte qui redécide.
- **G-VAR-3 — Pas deux fois le même GENRE LIGHT consécutif.** Ban **absolu** sur les genres LIGHT (`guard` · `ledger` · `docs` · `readme` · `test`) : bloqué dès 2. Pour un genre **DEEP ou MED dans le domaine-cœur d'une lane spécialiste**, deux consécutifs sont autorisés **si chacun est une substance genuinement distincte** — théorème/module/résultat différent, produit par du raisonnement neuf. Un spécialiste Lean qui enchaîne deux preuves DEEP distinctes n'est **pas** la monoculture visée. Tell décisif : le litmus LIGHT — générable en scannant l'instance d'à-côté → bloqué **même sous une étiquette DEEP**.

## 3. Merge-gate coordinateur (ai-01) — les dents (HARD)

Le protocole ne mord que si `ai-01` cesse de merger passivement. À chaque passe, pour chaque PR, **lire le tag** et croiser avec les grains récents de la lane :

| Constat | Action |
|---|---|
| LIGHT d'une lane à budget épuisé (G-VAR-2) | **HOLD** : citer la sortie de `variation_light_cap.py` (`N` LIGHT pour `M` grains), pas une estimation |
| 2ᵉ même-GENRE consécutif (G-VAR-3) | **HOLD** *si* genre LIGHT **ou** DEEP/MED non-distinct. Un 2ᵉ DEEP/MED genuinement distinct **passe** |
| Plancher tenu par une LIGHT (G-VAR-1) | steer vers un grain DEEP/MED de **contenu** du pool, **nommé** |
| Plancher tenu par un genre **META**, même tagué DEEP/MED (G-VAR-1) | le cycle n'a pas de plancher : merger la PR si elle est bonne, **et** nommer dans le même geste le grain de contenu qui portera le cycle suivant. Ne **pas** HOLD une PR META saine — la sanction porterait sur le mauvais objet ; c'est le **provisionnement** qui a manqué (obligation §4) |
| Tag mal dérivé (tier sur-coté, genre pris sur la famille, alias/composé) | **re-qualifier le tag soi-même**, puis traiter selon le tag corrigé |
| `lane` absente | **HOLD** jusqu'à déclaration — un grain sans lane est **structurellement incomptable**, et le cap devient inapplicable sans que personne ne le contourne |

**Le tag déclaré n'est pas auto-exécutoire** : il rend le grain auditable, il ne le définit pas. Merger sans lire le tag laisse le protocole s'auto-certifier.

**Ne jamais tenir une LIGHT plus d'une journée** : un hold prolongé fait réécrire le même travail par une autre lane. Passé 24 h : merger, ou fermer **en nommant le remplaçant**.

Le HOLD **ne sanctionne jamais la lane en idle** ([coordinator-discipline.md](coordinator-discipline.md) R4) : il est **toujours accompagné d'un grain DEEP/MED nommé** du pool, poussé en **double canal** (DM inbox + `[DISPATCH→inbox]` dashboard). HOLD sans remplacement = échec coordinateur.

## 4. Obligation de provisionnement — ce qui lie ai-01 (HARD)

La cause racine est **autant** un défaut de provisionnement qu'un réflexe de facilité worker : sans substance stockée, le worker tombe sur les veines faciles. Chaque cycle `/coordinate`, `ai-01` :

0. **Le tirage est la voie par défaut** (règle 5 de [proactive-coordination.md](proactive-coordination.md), mandat user 2026-08-20) : une lane qui n'a pas reçu de steering **tire** et n'attend rien. Le provisionnement ci-dessous reste dû — il devient l'**exception nommée**, et c'est *parce que* c'est une exception qu'il doit être le plus équilibré possible : un steering qui répète le genre du cycle précédent fait pire que le tirage, puisqu'il **écarte** un mécanisme conçu pour ne pas biaiser.
1. **Provisionne ≥1 grain DEEP/MED de CONTENU par lane**, **groundé firsthand** (`gh issue view`), varié en genre d'une lane à l'autre. Un provisionnement uniquement `guard`/`tooling`/`docs` ne satisfait pas l'obligation — il garantit que toutes les lanes manqueront leur plancher.
   Deux corollaires mesurés : **agréger les GENRES des merges récents** avant de provisionner, pas seulement leurs tiers (« 15 MED sur 21 » avait l'air sain et cachait 15 grains de harnais pour 0 `qc`/`genai`/`notebook`) ; et **un batch-close de famille crée une dette de provisionnement**, à honorer dans le même cycle (précédent ICT).
2. **Varie la loterie** d'un cycle à l'autre — le coordinateur applique G-VAR-3 à son propre dispatch.

Sous-provisionner puis merger la monoculture qui en résulte est **le** manquement que ce protocole corrige.

## 5. Auto-détection

Avant de claim / de merger : **« ce grain est-il générable-en-série (LIGHT) ET (budget épuisé OU même-genre-que-le-précédent) ? »** Si oui, c'est la monoculture — le worker pioche un DEEP/MED, le coordinateur HOLD+redirige.

Et la question que le tier seul ne posait pas, à se poser en fin de cycle : **« qu'est-ce que ce cycle a ajouté au dépôt qu'un lecteur ou un étudiant puisse utiliser ? »** Si la seule réponse honnête est « un détecteur de plus, un guard de plus, une doc de plus », le plancher n'est pas tenu — quel que soit le nombre de PR mergées et quels que soient les tiers déclarés. Côté worker : piocher un grain de contenu. Côté coordinateur : c'est un défaut de provisionnement (§4), pas une faute de lane.

## Voir aussi

- [docs/reference/variation-protocol-detail.md](../../docs/reference/variation-protocol-detail.md) — justifications mesurées, incidents #8056 / #8961, historique des applications
- [proactive-coordination.md](proactive-coordination.md) — R1, R5 (pool global), R6/R7 (variété, never-idle)
- [coordinator-discipline.md](coordinator-discipline.md) — R4 (jamais sanctionner l'idle), R5 (steer qui ATTEINT/VRAI/DÉCIDE)
