# Protocole de variation — anti-monoculture, tag déclaré + merge-gate coordinateur

S'applique à **tous les workers** (`po-*`) **et au coordinateur `ai-01`**. Source : mandat user 2026-07-21. Les concepts (tiers DEEP/MED/LIGHT, rotation des genres, never-idle) vivent dans [proactive-coordination.md](proactive-coordination.md) R6/R7 — la monoculture a persisté parce qu'ils étaient auto-évalués et invisibles ; ce fichier ajoute la mécanique qui les fait mordre : **tag auditable**, **merge-gate**, **obligation de provisionnement**.

**Détail (justifications mesurées, incidents fondateurs, verbatims)** : [docs/reference/variation-protocol-detail.md](../../docs/reference/variation-protocol-detail.md).

## 1. Le tag de grain (HARD)

Tout `[CLAIMED]` **et** tout body de PR portent en **première ligne** :

```
Grain: <TIER>/<GENRE> — lane <machine:workspace> — prev: <TIER>/<GENRE> #<PR>
```

Ex. `Grain: DEEP/lean — lane myia-po-2026:CoursIA — prev: LIGHT/guard #8954`.

`prev:` documente le grain précédent de la lane (adjacence G-VAR-3) et le lie à une PR relisable — le numéro rend la déclaration vérifiable ; les deux sont obligatoires. **Le genre déclaré dans `prev:` n'est PAS la clé d'adjacence** : l'organe [`scripts/ci/variation_adjacency_guard.py`](../../scripts/ci/variation_adjacency_guard.py) lit la **séquence mergée** de la lane et rend le genre déclaré dans un champ séparé (`declared_prev_genre`) ; le `prev:` n'est source de vérité qu'en repli. Ne pas dériver l'adjacence à la main depuis les `prev:` déclarés — deux HOLD faux en ont résulté le 2026-09-11. Mécanisme : [détail §2.1](../../docs/reference/variation-protocol-detail.md).

Le guard ([`variation-tag-guard.yml`](../../.github/workflows/variation-tag-guard.yml)) matche par **mot-clé** (`Grain:`, `lane`), casse insensible, décoration markdown neutralisée : la **substance** seule est vérifiée (TIER par le litmus, GENRE dans l'énumération, `lane` présente). Pas de churn cosmétique sur un tag valide en substance.

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

Un genre META n'est pas inférieur — un guard qui rougit au bon moment vaut mieux qu'un notebook de plus — mais une flotte qui ne produit que du META construit un atelier sans rien y fabriquer (mesure fondatrice : [détail §11](../../docs/reference/variation-protocol-detail.md)).

**`slides` reste CONTENU** quand le grain écrit ou enrichit le contenu du deck (12 slides de cours neuves = CONTENU, pas `docs`) ; un grain slides qui fait autre chose garde son genre de type de travail — `guard` pour un gate CI de build Slidev, `refactor` pour un script, `tooling` pour un convertisseur.

Un genre hors liste est un **alias** que le merge-gate normalise : pas une violation, le worker n'est ni repris ni HOLD. **Le GENRE est le TYPE DE TRAVAIL, jamais la famille où vivent les fichiers** (test : *si le prochain grain tombait dans une autre famille, changerais-je le GENRE ?*) : le composé `<famille>-<genre>` (`lean-ci`, `cjk-ci`, `audit-tooling`) **se réduit toujours à sa tête** ; les synonymes (`test-coverage` → `test`, `documentation` → `docs`, `data` → `ledger`, `slidev` → `slides`) se normalisent. Table complète : [détail §Alias](../../docs/reference/variation-protocol-detail.md).

**`guard` vs `tooling` — le discriminant est « est-ce que ça peut rougir ».** Un check susceptible de passer au rouge est `guard` ; un script/helper/convertisseur sans statut d'échec propre est `tooling`.

**Entrer dans la liste LIGHT de G-VAR-3 se mesure, jamais s'intuitionne** : un genre y entre dès **≥ 2 grains LIGHT mergés**.

### Grain REPAIR — hérite du genre de la PR qu'il répare

| PR réparée | Tag REPAIR | Genre | Plancher G-VAR-1 |
|---|---|---|---|
| `notebook-python` (ex #12141) | `MED/notebook-python` | **CONTENU** | grain de contenu **au-delà** du plancher |
| `lean` (ex #12252) | `MED/notebook-lean` | **CONTENU** | grain de contenu **au-delà** du plancher |
| `guard` (ex #11997) | `MED/guard` | **META** | ne tient **pas** le plancher, comme toute PR META |

Le raisonnement : G-VAR-1 demande « qu'est-ce qui atteint `main` quand ce travail aboutit ? » — la réponse regarde ce qui **arrive sur `main`**, pas ce que le REPAIR a fait. **Cas négatif explicite** : un REPAIR d'une PR META reste META — une lane qui ne réparerait que ses PRs de tooling/docs ne tiendrait toujours pas G-VAR-1. **Forme** : le genre hérité est déclaré directement, sans annotation spéciale (le REPAIR se lit dans le titre `fix(` et le diff) ; une annotation ajoute du bruit sans information. **Tier** : litmus habituel — un REPAIR à ré-exécution complète + diagnostic de ratchet est `MED` ; un REPAIR d'une ligne de body reste `LIGHT` et consomme le budget G-VAR-2 (pas d'exception). Raisonnement complet et arbitrage #11815 : [détail §13](../../docs/reference/variation-protocol-detail.md).

## 2. Les trois gates durs

- **G-VAR-1 — Plat principal DEEP, dans un genre de CONTENU.** La PR-plancher du cycle (R1 de proactive-coordination) **DOIT** être DEEP **et** porter un genre de la classe CONTENU. **Une LIGHT ne satisfait JAMAIS le plancher ; un genre META non plus, quel que soit son tier ; un MED non plus.** Le MED et le META restent **bienvenus au-delà** du plancher (sous budget G-VAR-2 pour leurs composantes LIGHT) : ce qui est exigé, c'est qu'**au moins un** grain DEEP de contenu porte le cycle. Le pool global porte toujours du DEEP de contenu : la monoculture vient du choix du plus facile *disponible*, pas d'une absence de substance.

  **Durcissement #15793 (2026-09-12)** : le plancher passe de « DEEP **ou MED** » à **DEEP** — mesure motrice (15 % de DEEP sur 7 j, META devant CONTENU sur 48 h) et contre-poids anti-inflation (`TIER-INFLATION` + re-qualification par le merge-gate, §3) : [détail §12](../../docs/reference/variation-protocol-detail.md). Le litmus DEEP reste objectif. Le durcissement se paie en **lecture de tags par ai-01**, jamais en confiance.

  **La sécheresse se mesure — [`scripts/pick_idle_grain.py`](../../scripts/pick_idle_grain.py) — elle ne s'auto-évalue pas (#13086).** Le picker compte les **merges consécutifs sans genre CONTENU** de la lane et, au seuil (3 par défaut), **restreint le tirage aux genres CONTENU** : la lane reçoit un grain, et ce grain tient le plancher. L'échappatoire `--ignore-drought` (capability GPU-only/vision-only) **se justifie par écrit** ; une capability **se mesure sur les lanes sœurs du même modèle**, elle ne se déclare pas — tant qu'une lane sœur livre du contenu, « ma capability exclut le contenu » est réfuté.

- **G-VAR-2 — Budget LIGHT proportionnel : `max(1, grains_mergés_du_jour // 3)`**, par lane et par jour, **toutes catégories LIGHT confondues**. Une lane à 1-5 grains garde le plafond d'une LIGHT ; à 6 elle en a deux, à 19 elle en a six. Au-delà : la LIGHT attend demain ou cède la place à du DEEP/MED. Le budget se **calcule** — [`scripts/variation_light_cap.py`](../../scripts/variation_light_cap.py) — il ne se déclare pas.

  Note d'arbitrage (#11154) : les PRs `DEFECT-ALIVE` (dette #11044) **consomment le budget LIGHT**, avec exception écrite + mesure de la dette résiduelle à chaque merge au cap.

- **G-VAR-3 — Pas deux fois le même GENRE LIGHT consécutif.** Sur les genres LIGHT (`guard` · `ledger` · `docs` · `readme` · `test`) : bloqué dès 2 grains consécutifs de même genre, **sauf** exception mécanique. Les genres de CONTENU ne relèvent pas de G-VAR-3 — un spécialiste Lean qui enchaîne deux preuves DEEP distinctes n'est **pas** la monoculture visée.

  **Exception MED/DEEP mesurable (#14357)** : deux grains consécutifs d'un même genre LIGHT sont autorisés **ssi** (i) le **second** est MED ou DEEP et (ii) les deux PRs ne partagent **aucun fichier**. Le critère est mécanique — rendu par l'organe (`variation_light_cap.py`, clé `exempt_runs`) et consommé par le gate (`variation_adjacency_guard.py`, verdict `exempted`), jamais jugé à la main ; un run de ≥3 ne s'exempte que si **chaque paire adjacente** satisfait (i) et (ii) ; ce que l'organe ne peut pas lire ne s'exempte pas — fail-CLOSED. Tell décisif : le litmus LIGHT — générable en scannant l'instance d'à-côté → bloqué **même sous une étiquette DEEP**.

## 3. Merge-gate coordinateur (ai-01) — les dents (HARD)

Le protocole ne mord que si `ai-01` cesse de merger passivement. À chaque passe, pour chaque PR, **lire le tag** et croiser avec les grains récents de la lane :

| Constat | Action |
|---|---|
| LIGHT d'une lane à budget épuisé (G-VAR-2) | **HOLD** : citer la sortie de `variation_light_cap.py` (`N` LIGHT pour `M` grains), pas une estimation |
| 2ᵉ même-GENRE consécutif (G-VAR-3) | **HOLD**, sauf exception mécanique #14357 rendue par l'organe (`exempt_runs`) |
| Plancher tenu par une LIGHT (G-VAR-1) | steer vers un grain **DEEP de contenu** du pool, **nommé** |
| Plancher tenu par un **MED** ou un genre **META**, même tagué DEEP (G-VAR-1) | le cycle n'a pas de plancher : merger la PR si elle est bonne, **et** nommer dans le même geste le grain DEEP de contenu qui portera le cycle suivant. Ne **pas** HOLD une PR META saine — c'est le **provisionnement** qui a manqué (§4) |
| Tag mal dérivé (tier sur-coté, genre pris sur la famille, alias/composé) | **re-qualifier le tag soi-même**, puis traiter selon le tag corrigé |
| `lane` absente | **HOLD** jusqu'à déclaration — un grain sans lane est **structurellement incomptable** |

**Le tag déclaré n'est pas auto-exécutoire** : il rend le grain auditable, il ne le définit pas. Merger sans lire le tag laisse le protocole s'auto-certifier.

**Ne jamais tenir une LIGHT plus d'une journée** : un hold prolongé fait réécrire le même travail par une autre lane. Passé 24 h : merger, ou fermer **en nommant le remplaçant**.

Le HOLD est **attaché à la candidate**, jamais à la cadence de sa lane. Il ne sanctionne jamais l'idle ([coordinator-discipline.md](coordinator-discipline.md) R0/R4) et ne bloque jamais un nouveau grain **DEEP de contenu** : toujours accompagné d'un grain nommé du pool, en **double canal** (DM inbox + `[DISPATCH→inbox]` dashboard). HOLD sans remplacement, ou HOLD pour réduire les dispatchs, = échec coordinateur.

## 4. Obligation de provisionnement — ce qui lie ai-01 (HARD)

La cause racine est **autant** un défaut de provisionnement qu'un réflexe de facilité worker. Chaque cycle `/coordinate`, `ai-01` :

0. **Le tirage est la voie par défaut** (règle 5 de [proactive-coordination.md](proactive-coordination.md)) : une lane sans steering **tire** et n'attend rien. Le provisionnement reste dû comme **exception nommée** — et doit être le plus équilibré possible : un steering qui répète le genre du cycle précédent fait pire que le tirage.
1. **Provisionne ≥1 grain DEEP de CONTENU par lane**, **groundé firsthand** (`gh issue view`), varié en genre d'une lane à l'autre. Un provisionnement `MED`, ou uniquement `guard`/`tooling`/`docs`, ne satisfait pas l'obligation. Corollaires mesurés (agréger les **GENRES** des merges récents, pas seulement leurs tiers ; un batch-close de famille crée une dette de provisionnement) : [détail §9](../../docs/reference/variation-protocol-detail.md).
2. **Varie la loterie** — le coordinateur applique G-VAR-3 à son propre dispatch.
3. **Dissocie admission et production** : les candidates en HOLD, `DWELL`, review ou attente de merge ne diminuent jamais le provisionnement. La queue d'admission se résorbe par une piste de digestion parallèle ; elle n'applique aucune backpressure globale aux producteurs.

Sous-provisionner puis merger la monoculture qui en résulte est **le** manquement que ce protocole corrige. Ralentir la production pour accommoder la digestion en est un autre.

## 5. Auto-détection

Avant de claim / de merger : **« ce grain est-il générable-en-série (LIGHT) ET (budget épuisé OU même-genre-que-le-précédent) ? »** Si oui, c'est la monoculture — le worker pioche un **DEEP de contenu**, le coordinateur HOLD+redirige.

Et la question que le tier seul ne posait pas, en fin de cycle : **« qu'est-ce que ce cycle a ajouté au dépôt qu'un lecteur ou un étudiant puisse utiliser ? »** Si la seule réponse honnête est « un détecteur de plus, un guard de plus, une doc de plus », le plancher n'est pas tenu — quel que soit le nombre de PR mergées. Côté worker : piocher un grain de contenu. Côté coordinateur : c'est un défaut de provisionnement (§4), pas une faute de lane.

## Voir aussi

- [docs/reference/variation-protocol-detail.md](../../docs/reference/variation-protocol-detail.md) — justifications mesurées, incidents #8056 / #8961, historique des applications
- [proactive-coordination.md](proactive-coordination.md) — R1, R5 (pool global), R6/R7 (variété, never-idle)
- [coordinator-discipline.md](coordinator-discipline.md) — R4 (jamais sanctionner l'idle), R5 (steer qui ATTEINT/VRAI/DÉCIDE)
