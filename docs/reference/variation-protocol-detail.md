# Protocole de variation — détail, justifications mesurées, incidents fondateurs

Détail déporté de [`.claude/rules/variation-protocol.md`](../../.claude/rules/variation-protocol.md) (harness-hygiene : la règle reste succincte et auto-chargée, le détail vit ici et se lit à la demande).

---

## 1. Pourquoi un tag déclaré plutôt qu'une simple exhortation

Verbatim du mandat user 2026-07-21 : « la monoculture de PRs facile est toujours bien là, il faut que tu steere mieux, c'est peut-être le moment d'imposer un protocole de variation ».

Les concepts de variation (tiers, rotation, never-idle) existaient déjà dans [`proactive-coordination.md`](../../.claude/rules/proactive-coordination.md) R6/R7 depuis 2026-07-06. La monoculture a persisté quinze jours de plus. Diagnostic du mandat : les concepts étaient **auto-évalués** (le worker décide seul si son grain est « de la substance »), **invisibles** (rien dans la PR ne dit à quel tier elle prétend), et **non-gatés** (le coordinateur mergeait sans lire).

C'est l'application directe de la leçon `rule-needs-an-organ-not-more-vigilance` : une règle dont le seul mécanisme d'application est la vigilance sera violée. Le tag est l'organe — il rend le grain **auditable en un coup d'œil**, ce qui est la précondition du merge-gate.

## 2. Champ `prev:` — pourquoi le numéro de PR est obligatoire

Mesuré sur les **55 PR taguées** mergées depuis la ratification du 2026-07-21 : **100 %** portent le numéro de PR (`prev: MED/tooling #8975`, `prev: MED/lean (#8954 …)`). La spec initiale demandait `prev: <TIER>/<GENRE>` sans numéro — forme que **personne** n'écrivait.

La raison est bonne, pas paresseuse : un `prev: MED/lean` nu est re-dérivable de mémoire, donc contestable ; un `prev: MED/lean #8954` pointe vers une PR dont on peut relire le diff. La spec a été alignée sur la pratique (2026-07-30) plutôt que d'imposer du churn.

### 2.1 Le `prev:` déclaré n'est PAS la clé d'adjacence — l'organe lit la séquence mergée (#15589)

Jusqu'au 2026-09-11, la règle disait : « **le genre est la clé d'adjacence** ». C'était faux, et faux **depuis #12095**. Le mécanisme réel, lu dans le code de [`scripts/ci/variation_adjacency_guard.py`](../../scripts/ci/variation_adjacency_guard.py) :

| | source du prédécesseur | champ rendu |
|---|---|---|
| **cas normal** | la **séquence mergée** de la lane (option `--merged-prs-file`) | `prev_genre`, `prev_pr`, `prev_source: "merged-sequence"` |
| **repli** (premier grain, ou échec de fetch — jamais un crash) | le `prev:` **déclaré** | `prev_source: "declared"` |

Le `prev:` déclaré garde une valeur **documentaire** (il dit ce que l'auteur croyait) et il est exposé dans un champ **séparé**, `declared_prev_genre`, précisément pour que le gate ne s'y fie pas. La raison est mesurée : **le `prev:` est figé à l'ouverture de la PR**, donc une lane qui merge des grains pendant que sa PR est ouverte rend le champ périmé. #11963 a mesuré `prev: MED/guard #11841` — exact à la rédaction, suivi de **quatre** grains mergés ; le vrai prédécesseur était `notebook-python`. L'adjacence est une propriété de **ce que la lane a réellement mergé**, pas de ce qu'elle a déclaré.

**Ce que ça coûte quand on lit la règle à la lettre.** Le 2026-09-11, au merge-gate, le coordinateur a dérivé l'adjacence à la main depuis les `prev:` déclarés et posé **deux HOLD motivés G-VAR-3** sur #15551 (`prev: LIGHT/readme #15550`) et #15552 (`prev: LIGHT/readme #15551`) — une chaîne de trois `LIGHT/readme` déclarés, qualifiée d'« inexemptable par construction ». L'organe, interrogé ensuite, rend l'inverse sur les deux : `adjacent: false`, `prev_genre: "guard"`, `prev_pr: 15569`, `prev_source: "merged-sequence"`. Le prédécesseur réel était #15569 (`MED/guard`), mergé à 11:34:51Z, qui s'interpose dans la séquence et **rompt** l'adjacence. Deux rétractations ont dû être postées (`issuecomment-5633877872`, `issuecomment-5633878069`). Le défaut n'est donc pas réservé aux workers : il a fait écrire un motif faux au coordinateur, dans le geste même que la règle existe pour outiller.

**Conséquence opérationnelle, à ne pas inverser** : un `prev:` qui pointe une PR **encore ouverte n'est pas un défaut**, et ne doit pas être signalé. La piste « vérifier que le `prev:` référence une PR mergée » a été **implémentée, mesurée, puis retirée** le 2026-09-08 : invariant `PREV-ABANDONED`, [`validate_prev_targets`](../../scripts/ci/variation_prev_guard.py) — le gate ne rougit désormais que sur une PR **fermée sans merge** (lignée abandonnée), jamais sur une PR en vol. Mesure : **cinq** PRs ouvertes bloquées (#15156, #15190, #15207, #15209, #15210) citant **quatre** prédécesseurs distincts (#15129, #15175, #15199, #15203) — **les quatre OPEN, pas un seul abandonné**. Flaguer `OPEN` punissait exactement le comportement que le **R1 d'alors** de [`proactive-coordination.md`](../../.claude/rules/proactive-coordination.md) *imposait* (« 1 PR entre 2 wakeups = PLANCHER, jamais plafond » — R1 porte depuis #15793 un plancher pluriel, la conclusion du 2026-09-08 est inchangée). Seule la relecture trompeuse est un défaut — et elle est traitée par la prose ci-dessus, pas par un gate.

**Hors périmètre** : le vocabulaire de genre fail-OPEN de `canonicalize_genre` est un autre défaut, suivi par **#13475**.

## 3. Forme canonique vs substance — le guard est agnostique à la ponctuation

Le guard [`variation-tag-guard.yml`](../../.github/workflows/variation-tag-guard.yml) matche par mot-clé (`Grain:`, `lane`) en casse insensible, après `tr -d '*\`'` pour neutraliser la décoration markdown. Il ne voit **ni** le séparateur (`—` / `·` / virgule) **ni** la casse des libellés (`Lane:` et les backticks passent).

Conséquence opérationnelle : un tag existant en variante de présentation n'est **pas** une non-conformité à reformatter. Ne pas forcer de churn cosmétique sur un tag valide en substance (tranché par #8934 tranche (C)).

## 4. G-VAR-2 — pourquoi un ratio et non plus un plafond absolu

**Sign-off user 2026-07-31.** Le cap initial `1 LIGHT/lane/jour` traitait identiquement une lane à 1 PR et une lane à 19 merges dont 13 DEEP. Le second cas est l'exact opposé de la monoculture, et se voyait sanctionné pareil : un plafond insensible au débit ne mesure pas la monoculture, il **plafonne le débit**.

Pire, il **fabriquait** le travail en double qu'il prétendait économiser. Incident : **#8961** (documentation du piège d'ordre `strip`→`--update`) tenue une journée au titre de G-VAR-2. Pendant ce hold la doc n'a pas atteint `main`, et **deux autres sessions ont réécrit la même chose** — **#8983** et **#8996**, toutes deux fermées comme doublons. ~98 lignes rédigées **trois fois**.

Le ratio `max(1, grains_mergés // 3)` garde l'intention (une lane ne peut pas être *majoritairement* LIGHT) en la rendant proportionnelle à la production réelle. D'où aussi la règle des 24 h au merge-gate : passé une journée, on merge ou on ferme **en nommant le remplaçant** — jamais un hold qui dort.

Organe : [`scripts/variation_light_cap.py`](../../scripts/variation_light_cap.py) — le budget est **calculé** (`--replay <merged.json>`), et c'est cette sortie qu'on cite dans un HOLD, jamais une estimation à l'œil.

**Arbitrage #11154 — `DEFECT-ALIVE` et dette #11044** (option 1) : les PRs `DEFECT-ALIVE` (dette de review #11044) **consomment le budget LIGHT**, avec exception écrite + mesure de la dette résiduelle citée à chaque merge au cap — justification chiffrée dans [#11154](https://github.com/jsboige/CoursIA/issues/11154). Réouverture : si la dette remonte, c'est le compte qui redécide.

### 4.1 Vue agrégée cross-lane (per-lane, 7j)

`scripts/variation_light_cap.py` répond à « *combien de LIGHT cette lane peut-elle encore merger aujourd'hui ?* » — utile au merge-gate, aveugle au cluster. La **vue d'ensemble** (où le provisionnement manque, quelles lanes en monoculture, combien de PRs sans tag) est dans [`scripts/coordination_budget.py`](../../scripts/coordination_budget.py) — sorti par #9868, vérifié sur main par #9859. Deux modes :

- `--days N` (défaut 7) : live via `gh pr list --state merged --search "merged:>=YYYY-MM-DD" --json number,title,body,mergedAt,labels`.
- `--replay <file>` : offline (test, audit historique post-mortem).
- `--json` : sortie machine-readable (CI, post-traitement).
- `--known-lanes a,b,c` : signale les lanes connues **idle** (sans la liste canonique, le script ne sait pas).

Le script **réutilise** `parse_grain_tag` (parsing tolerant casse/décoration, voir #9485) et `effective_tier` + `light_budget` + `label_names` (voir #8970 / #8964) — pas de duplication, les bugs historiques (divergence guard/organ, requalification invisible) sont hérités gratuits. Les nombres sont **calculés**, jamais déclarés, et un tag malformé (genre `WTF/bogus`, casse mixte `gRaIn: deEp/LeAn`) **ne crashe pas** — il est signalé en anomalie avec sa PR. Le tableau par lane (DEEP / MED / LIGHT / budget / consommé / genres) est suivi d'un bloc d'anomalies : 32 sans tag, 8 sans lane, monoculture smells G-VAR-3 par lane.

Sortie réelle (live, 7j, après #9734 merge) — capturée par ce PR :

```
| Lane | DEEP | MED | LIGHT | total | budget | consumed | genres |
|------|-----:|----:|------:|------:|-------:|---------:|--------|
| myia-po-2024:CoursIA-2 | 5 | 39 | 6 | 57 | 19 | 6 | ... |
| myia-po-2023:CoursIA-2 | 2 | 27 | 6 | 35 | 11 | 6 | ... |
| myia-po-2025:CoursIA | 15 | 17 | 2 | 34 | 11 | 2 | ... |
| myia-po-2023:CoursIA | 3 | 11 | 13 | 30 | 10 | 13  (+3 over) | ... |
| myia-po-2025:CoursIA-2 | 8 | 19 | 0 | 27 | 9 | 0 | ... |
| myia-ai-01:CoursIA | 9 | 11 | 6 | 26 | 8 | 6 | ... |
| myia-po-2024:CoursIA | 11 | 12 | 1 | 24 | 8 | 1 | ... |
| myia-po-2026:CoursIA | 3 | 15 | 1 | 19 | 6 | 1 | ... |
| myia-po-2026:CoursIA-2 | 1 | 3 | 0 | 4 | 1 | 0 | ... |
| myia-ai-01:LivresAgit | 0 | 2 | 0 | 2 | 1 | 0 | ... |
| myia-po-2026:CoursIA. | 0 | 2 | 0 | 2 | 1 | 0 | ... |
```

300 PRs mergés, 40 unattributed (32 sans tag + 8 sans lane). Le tag typo `myia-po-2026:CoursIA.` (point final) — le script le sépare en lane fantôme, signal de **qualité des tags** au-delà du compteur.

**Pourquoi c'est utile au-delà de la conformité** : une lane à 4 LIGHT / 0 DEEP dit « *coordinateur qui n'a pas stocké de substance pour cette lane* » (variation-protocol §4 obligation de provisionnement), pas « worker paresseux ». Le compteur rend ce diagnostic **lisible** au lieu de dépendre de la mémoire du coordinateur. C'est aussi ce qui permet la §4 règle « passer 24 h ou nommer le remplaçant » — un hold prolongé se voit en agrégat avant de devenir un doublon.

## 5. Incident fondateur du GENRE — rollout `metadata.cost` #8056 (2026-07-28)

Quatre tranches d'un **seul** rollout scan-générable ont porté **trois étiquettes différentes** :

| PR | Tag déclaré | Réalité |
|---|---|---|
| #8732 | `DEEP/genai` | LIGHT (stamping en série) |
| #8735 | `MED/genai` | LIGHT |
| #8699 | `MED/data` | LIGHT, genre hors énumération |
| #8697 | (antérieure, `lane` absente) | LIGHT, incomptable |

Aucune n'a déclenché G-VAR-2 ni G-VAR-3, alors que les quatre sont LIGHT par le litmus — « j'en génère une douzaine en scannant la série suivante » est *littéralement* ce que fait une tranche 2.

Deux mécaniques de contournement en sont sorties, toutes deux fermées dans la règle :

1. **Le genre pris sur la famille** — un même rollout change d'étiquette selon le répertoire traversé (`genai` dans `GenAI/`, `data` dans `Search/`), et l'adjacence ne voit jamais deux fois le même genre. Test correctif : *si le prochain grain tombait dans une autre famille, changerais-je le GENRE ?*
2. **Le genre composé `<famille>-<genre>`** — variante plus discrète : au lieu de *choisir* le genre d'après le répertoire, on l'y **agrafe** (`lean-ci`, `lean-tooling`, `cjk-ci`, `audit-tooling`). Chacun est un genre privé valable pour une seule famille, donc invisible à l'adjacence : une lane faisant quatre fois le même travail dans quatre familles affiche quatre genres et ne déclenche jamais G-VAR-3.

Le coordinateur en a mergé plusieurs **sans auditer le tag** : la responsabilité est partagée, d'où la clause §3 « le tag déclaré n'est pas auto-exécutoire » et l'obligation de re-qualifier.

## 6. Normalisation des genres — la mesure derrière la table

Sur les mêmes 55 PR taguées, **18 (33 %)** portaient un genre hors énumération. La table de normalisation de la règle en est la synthèse ; les comptes bruts :

| Écrit | Occurrences |
|---|---|
| `lean-ci` | 4 |
| `test-coverage` | 3 |
| `refs` | 2 |
| `lean-tooling`, `cjk-ci`, `audit-tooling`, `documentation`, `data`, `Lean` | 1 chacun |

Deux entrées étaient au contraire de **vraies lacunes** de l'énumération, et l'ont donc rejointe plutôt que d'être repliées :

- **`tooling`** (5 usages) — script ou helper qui n'est **pas** une porte : ni `guard` (rien ne peut rougir), ni `refactor` (ne restructure pas de l'existant).
- **`research-code`** — module/bibliothèque de recherche produisant un résultat falsifiable ; `notebook-python` est faux dès que le livrable n'est pas un notebook.

**Critère d'entrée dans la liste LIGHT de G-VAR-3** (celle qui porte le ban des deux-consécutifs, sauf exception mécanique #14357) : un genre y entre dès **≥ 2 grains LIGHT mergés**, jamais sur intuition — l'y ajouter à l'aveugle bloquerait du travail substantiel. Au 2026-07-30, `tooling` était à **5 MED sur 5** et `research-code` à **1 DEEP sur 1** : aucun ne qualifiait. Ils y entreront d'eux-mêmes si la mesure change.

**Un alias n'est pas une violation.** Le worker qui écrit `documentation` ou `lean-ci` n'est ni HOLD ni repris : le coordinateur normalise silencieusement et applique les gates au genre canonique (l'adjacence de `LIGHT/refs` se calcule contre `docs`). Ce qui compte est que deux grains du même travail soient **comptés comme le même genre**, pas que le worker ait mémorisé la liste.

## 7. G-VAR-3 — pourquoi le ban absolu ne vise que les genres LIGHT

Le ban « pas deux fois le même genre » appliqué uniformément aurait bloqué un spécialiste Lean enchaînant deux preuves DEEP **distinctes** (ex. #7649 puis #2159 Grothendieck) — l'exact opposé de la monoculture visée, et une sanction du travail le plus difficile du dépôt.

D'où la ligne de partage : ban sur les genres LIGHT (`guard` · `ledger` · `docs` · `readme` · `test`), où la vague se forme dès 2 (ce qui durcit le « après 3 grains similaires » de R6, trop laxiste) ; **exception mécanique #14357** — deux consécutifs d'un même genre LIGHT passent **si et seulement si** le second grain est MED/DEEP **et** les deux PRs ne partagent **aucun fichier** (intersection vide, calculée par `variation_light_cap.py`, clé `exempt_runs`, **et consommée par le gate bloquant G-VAR-3** `variation_adjacency_guard.py`, verdict `exempted`, fail-CLOSED quand les `files` sont illisibles — le gate lit les `files` via `gh pr view --json files`, il ne décide pas d'une exemption sur la seule étiquette de tier déclarée).

L'ancienne formulation — « tolérance » sur DEEP/MED dans le domaine-cœur « à condition que chaque grain soit une substance genuinement distincte » — était un jugement humain sans organe, et vivait en conflit direct avec le ban absolu sur les cinq genres LIGHT : un grain `MED/guard` tombait sous les deux clauses, et l'organe ne suivait que le ban (#14357, mesure po-2026 du 2026-09-02 : le couple #13869 → #14330, deux fixes de guards sur fichiers disjoints, bloqué puis overridé à la main par le coordinateur — un aller-retour par occurrence). L'intersection vide des fichiers est le **proxy observable** de la « substance distincte » : deux grains qui ne touchent aucune même partie de l'arbre ne sont pas la vague scannée-générée que G-VAR-3 vise.

Le litmus LIGHT reste l'arbitre dans les deux sens : générable en scannant l'instance d'à-côté → bloqué **même sous une étiquette DEEP** (l'exception exige la disjointure de fichiers, pas un tag de tier).

## 8. Champ `lane` — pourquoi son absence est un HOLD dur

G-VAR-2 est un cap **par lane et par jour**. Un grain qui ne déclare pas sa lane est **structurellement incomptable** : le cap devient inapplicable sans que personne n'ait eu à le contourner. Le champ `lane` n'est donc pas de la décoration de reporting, c'est la **clé d'agrégation du gate**. Constaté sur #8697 et #8699 — deux tranches du même rollout, toutes deux sans lane.

## 9. Obligation de provisionnement — la moitié coordinateur du problème

Le mandat 2026-07-21 dit « steere **mieux** », pas « constate la vague au merge ». La cause racine est **autant** un défaut de provisionnement qu'un réflexe de facilité worker : quand `ai-01` ne stocke pas de substance, le worker tombe mécaniquement sur les veines faciles générables-à-la-demande.

Détail du mécanisme (loterie substance, variation du dispatch d'un cycle à l'autre) : mémoire locale `feedback-substance-lottery-provisioning.md`. Le principe qui lie le coordinateur : **sous-provisionner puis merger la monoculture qui en résulte est le manquement que ce protocole corrige.**

Deux corollaires mesurés de l'obligation « ≥1 grain DEEP de CONTENU par lane » :

1. **Agréger les GENRES des merges récents avant de provisionner, pas seulement leurs tiers.** « 15 MED sur 21 » avait l'air sain et cachait 15 grains de harnais pour 0 `qc`/`genai`/`notebook` — le tier alone répète exactement l'échappatoire que la clause CONTENU/META a fermée (§11).
2. **Un batch-close de famille crée une dette de provisionnement**, à honorer dans le même cycle (précédent ICT) : vider d'un coup la file d'une famille laisse les lanes qui la servaient sans grain, et le premier réflexe disponible est la veine facile.

## 10. Alias — table de normalisation du GENRE

Le GENRE est le **type de travail**, jamais la famille où vivent les fichiers. Le merge-gate normalise avant d'appliquer les gates ; le worker n'est ni repris ni HOLD pour un alias.

| Écrit | Canonique | Motif |
|---|---|---|
| `lean-ci`, `lean-tooling`, `cjk-ci`, `audit-tooling` | `guard` ou `tooling` (cf. discriminant « est-ce que ça peut rougir ») | composé `<famille>-<genre>` : il se réduit toujours à sa tête, la famille se lit déjà dans les chemins du diff |
| `test-coverage` | `test` | synonyme — sinon le ban `test` de G-VAR-3 est inatteignable |
| `refs`, `documentation` | `docs` | synonyme |
| `data` | `ledger` | tranché par l'incident #8056 |
| `content` | `docs` ou `notebook-python` selon le travail réel | genre **hors énumération** — six grains consécutifs de `po-2023:CoursIA` l'ont porté (#10745, #10742, #10733, #10727, #10712, #10711), rendant l'adjacence G-VAR-3 inatteignable : un genre hors liste ne collisionne avec rien |
| `slidev` | `slides` | outil → type de travail — `slides` est CONTENU quand le grain écrit/enrichit le contenu du deck, sinon le grain garde son genre de type de travail (`guard`/`refactor`/`tooling`) |
| `Lean` | `lean` | genres en minuscules |

**Entrer dans la liste LIGHT de G-VAR-3 se mesure, jamais s'intuitionne** : un genre y entre dès **≥ 2 grains LIGHT mergés**. Au 2026-07-30, `tooling` était à 5 MED sur 5 et `research-code` à 1 DEEP sur 1 — aucun ne qualifiait.

## 11. Chiffres de la clause CONTENU/META (mesure 2026-08-10)

Justification complète de la clause de genre de G-VAR-1. Mesuré sur six semaines de commits, à volume de PR quasi constant (**S29 = 994**, **S32 = 917** PR mergées) :

| Indicateur | S29 | S32 |
|---|---|---|
| part `scripts/` dans les commits | 3 % | **45 %** |
| part code-de-série (hors notebooks) | 51 % | **18 %** |
| préfixe `fix` | 29 % | **44 %** |
| préfixe `feat` | 26 % | **15 %** |

Aucun gate n'avait rougi pendant cette dérive, et aucune lane n'avait menti : un grain `tooling`/`guard` qui attrape un vrai défaut « change quelque chose », donc **MED** est défendable, donc le plancher paraît tenu. L'échappatoire était dans la **spécification**, pas dans la discipline des lanes — d'où la clause de genre plutôt qu'un re-steer.

## 12. Durcissement du plancher (#15793, 2026-09-12) et organe de sécheresse (#13086)

### 12.1 La mesure motrice du durcissement

Le plancher passe de « DEEP **ou MED** » à **DEEP**. Mesure déposée datée dans [`proactive-coordination-detail.md`](proactive-coordination-detail.md), section Plancher durci : **15 % de DEEP sur 7 j**, le **META passant devant le CONTENU sur 48 h**, avec un contraste fort par lane — les lanes saines prouvent que le plancher DEEP est tenable, donc que les autres n'ont pas d'alibi de capacité.

### 12.2 Le contre-poids anti-inflation

Exiger un DEEP crée une incitation à **sur-coter le tier**. Ce qui la couvre est **déjà en place et n'a pas été inventé pour le durcissement** : le signal bot `TIER-INFLATION`, et le merge-gate qui **re-qualifie lui-même un tag mal dérivé** (règle §3, ligne « Tag mal dérivé »). Le litmus DEEP reste objectif — *`main` contient-il désormais un résultat ou une capacité qui n'existait pas, dont la production a demandé du raisonnement de domaine ?* Le durcissement se paie en **lecture de tags par ai-01**, jamais en confiance.

### 12.3 Pourquoi la sécheresse a eu besoin d'un organe (#13086)

G-VAR-1 est resté **prose auto-déclarée** pendant que G-VAR-2 avait son organe, et c'est ce déséquilibre qui l'a rendu inapplicable : `variation_light_cap.py` n'émet que des signaux de comptabilité LIGHT, si bien qu'une lane alternant `guard` → `tooling` → `docs` → `test` ne déclenche **jamais** `GENRE-RUN` tout en produisant zéro contenu indéfiniment.

Le picker ([`scripts/pick_idle_grain.py`](../../scripts/pick_idle_grain.py)) compte désormais les **merges consécutifs sans genre CONTENU** de la lane et, au seuil (3 par défaut, calibré pour ne pas pouvoir se déclencher sur la lane la plus saine de la flotte), **restreint le tirage aux genres CONTENU** au lieu de se contenter de les pondérer. Ce n'est pas un refus : la lane reçoit un grain, et ce grain tient le plancher — mandat user #13086, « tu prends un deep grain ». L'échappatoire `--ignore-drought` existe pour la lane dont la capability exclut le contenu (GPU-only, vision-only) et **se justifie par écrit**, jamais en silence. Une capability **se mesure sur les lanes sœurs du même modèle**, elle ne se déclare pas : tant qu'une lane sœur livre du contenu, « ma capability exclut le contenu » est réfuté, et la sécheresse invoquée est un frein, pas un mur.

## 13. Grain REPAIR — raisonnement complet et arbitrage #11815

L'héritage du genre se déduit de la question même de G-VAR-1 : « qu'est-ce qui atteint `main` quand ce travail aboutit ? » — la réponse regarde ce qui **arrive sur `main`**, pas ce que le REPAIR a fait. Quand une PR de notebook passe au vert et merge, ce qui arrive sur `main` est un notebook. Le REPAIR est de la fabrication qui sortait de l'entrepôt, pas de l'outillage.

**Cas négatif explicite** : un REPAIR d'une PR **META** reste **META**. Une lane qui ne réparerait que ses propres PRs de tooling/docs ne tiendrait toujours pas G-VAR-1 — l'échappatoire se ferme d'elle-même, sans clause spéciale.

**Forme du tag** : le REPAIR déclare directement le genre hérité, sans annotation spéciale. Le fait que ce soit un REPAIR se lit dans le titre (préfixe `fix(`) et le diff (`<fichiers de la PR originale> + ajustements`). Une annotation `MED/notebook-python (repair de #11722)` ajoute du bruit sans information : le tag existe pour répondre « quel genre de substance ce grain met-il sur `main` », et la réponse est la même dans les deux cas.

**Tier du REPAIR** : litmus habituel. Un REPAIR qui demande une **ré-exécution complète + diagnostic de ratchet** est `MED` ; un REPAIR d'**une ligne de body** reste `LIGHT` et consomme le budget G-VAR-2 — pas d'exception. Depuis le durcissement #15793 (§12), un REPAIR `MED` ne tient plus le plancher G-VAR-1 : le tableau du rule dit « grain de contenu **au-delà** du plancher ».

**Sources de l'arbitrage** : ticket [#11815](https://github.com/jsboige/CoursIA/issues/11815) (escalade formelle po-2023 après 3 cycles G-VAR-1 non-tenu sur REPAIR de notebooks ; DM `msg-20260819T163135-h66acw`, arbitrage `msg-20260819T171752-4jd3od`). La clause en codifie la lecture **au cas** en forme **durable**, sous sign-off user (CLAUDE.md §A).

## Voir aussi

- [`.claude/rules/variation-protocol.md`](../../.claude/rules/variation-protocol.md) — la règle (tag, 3 gates, merge-gate, provisionnement)
- [`.claude/rules/proactive-coordination.md`](../../.claude/rules/proactive-coordination.md) — R1, R5, R6/R7
- [`.claude/rules/coordinator-discipline.md`](../../.claude/rules/coordinator-discipline.md) — R4 (jamais sanctionner l'idle), R5 (steer qui ATTEINT/VRAI/DÉCIDE)
- [`docs/reference/proactive-coordination-detail.md`](proactive-coordination-detail.md) — backlog, sources, anti-patterns
