# Protocole de variation — détail, justifications mesurées, incidents fondateurs

Détail déporté de [`.claude/rules/variation-protocol.md`](../../.claude/rules/variation-protocol.md) (harness-hygiene : la règle reste succincte et auto-chargée, le détail vit ici et se lit à la demande).

---

## 1. Pourquoi un tag déclaré plutôt qu'une simple exhortation

Les concepts de variation (tiers, rotation, never-idle) existaient déjà dans [`proactive-coordination.md`](../../.claude/rules/proactive-coordination.md) R6/R7 depuis 2026-07-06. La monoculture a persisté quinze jours de plus. Diagnostic du mandat 2026-07-21 : les concepts étaient **auto-évalués** (le worker décide seul si son grain est « de la substance »), **invisibles** (rien dans la PR ne dit à quel tier elle prétend), et **non-gatés** (le coordinateur mergeait sans lire).

C'est l'application directe de la leçon `rule-needs-an-organ-not-more-vigilance` : une règle dont le seul mécanisme d'application est la vigilance sera violée. Le tag est l'organe — il rend le grain **auditable en un coup d'œil**, ce qui est la précondition du merge-gate.

## 2. Champ `prev:` — pourquoi le numéro de PR est obligatoire

Mesuré sur les **55 PR taguées** mergées depuis la ratification du 2026-07-21 : **100 %** portent le numéro de PR (`prev: MED/tooling #8975`, `prev: MED/lean (#8954 …)`). La spec initiale demandait `prev: <TIER>/<GENRE>` sans numéro — forme que **personne** n'écrivait.

La raison est bonne, pas paresseuse : un `prev: MED/lean` nu est re-dérivable de mémoire, donc contestable ; un `prev: MED/lean #8954` pointe vers une PR dont on peut relire le diff. La spec a été alignée sur la pratique (2026-07-30) plutôt que d'imposer du churn.

## 3. Forme canonique vs substance — le guard est agnostique à la ponctuation

Le guard [`variation-tag-guard.yml`](../../.github/workflows/variation-tag-guard.yml) matche par mot-clé (`Grain:`, `lane`) en casse insensible, après `tr -d '*\`'` pour neutraliser la décoration markdown. Il ne voit **ni** le séparateur (`—` / `·` / virgule) **ni** la casse des libellés (`Lane:` et les backticks passent).

Conséquence opérationnelle : un tag existant en variante de présentation n'est **pas** une non-conformité à reformatter. Ne pas forcer de churn cosmétique sur un tag valide en substance (tranché par #8934 tranche (C)).

## 4. G-VAR-2 — pourquoi un ratio et non plus un plafond absolu

**Sign-off user 2026-07-31.** Le cap initial `1 LIGHT/lane/jour` traitait identiquement une lane à 1 PR et une lane à 19 merges dont 13 DEEP. Le second cas est l'exact opposé de la monoculture, et se voyait sanctionné pareil : un plafond insensible au débit ne mesure pas la monoculture, il **plafonne le débit**.

Pire, il **fabriquait** le travail en double qu'il prétendait économiser. Incident : **#8961** (documentation du piège d'ordre `strip`→`--update`) tenue une journée au titre de G-VAR-2. Pendant ce hold la doc n'a pas atteint `main`, et **deux autres sessions ont réécrit la même chose** — **#8983** et **#8996**, toutes deux fermées comme doublons. ~98 lignes rédigées **trois fois**.

Le ratio `max(1, grains_mergés // 3)` garde l'intention (une lane ne peut pas être *majoritairement* LIGHT) en la rendant proportionnelle à la production réelle. D'où aussi la règle des 24 h au merge-gate : passé une journée, on merge ou on ferme **en nommant le remplaçant** — jamais un hold qui dort.

Organe : [`scripts/variation_light_cap.py`](../../scripts/variation_light_cap.py) — le budget est **calculé** (`--replay <merged.json>`), et c'est cette sortie qu'on cite dans un HOLD, jamais une estimation à l'œil.

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

**Critère d'entrée dans la liste LIGHT de G-VAR-3** (celle qui porte le ban absolu des deux-consécutifs) : un genre y entre dès **≥ 2 grains LIGHT mergés**, jamais sur intuition — l'y ajouter à l'aveugle bloquerait du travail substantiel. Au 2026-07-30, `tooling` était à **5 MED sur 5** et `research-code` à **1 DEEP sur 1** : aucun ne qualifiait. Ils y entreront d'eux-mêmes si la mesure change.

**Un alias n'est pas une violation.** Le worker qui écrit `documentation` ou `lean-ci` n'est ni HOLD ni repris : le coordinateur normalise silencieusement et applique les gates au genre canonique (l'adjacence de `LIGHT/refs` se calcule contre `docs`). Ce qui compte est que deux grains du même travail soient **comptés comme le même genre**, pas que le worker ait mémorisé la liste.

## 7. G-VAR-3 — pourquoi le ban absolu ne vise que les genres LIGHT

Le ban « pas deux fois le même genre » appliqué uniformément aurait bloqué un spécialiste Lean enchaînant deux preuves DEEP **distinctes** (ex. #7649 puis #2159 Grothendieck) — l'exact opposé de la monoculture visée, et une sanction du travail le plus difficile du dépôt.

D'où la ligne de partage : ban **absolu** sur les genres LIGHT (`guard` · `ledger` · `docs` · `readme` · `test`), où la vague se forme dès 2 (ce qui durcit le « après 3 grains similaires » de R6, trop laxiste) ; **tolérance** sur DEEP/MED dans le domaine-cœur d'une lane spécialiste, à condition que chaque grain soit une substance genuinement distincte.

Le litmus LIGHT reste l'arbitre dans les deux sens : générable en scannant l'instance d'à-côté → bloqué **même sous une étiquette DEEP**.

## 8. Champ `lane` — pourquoi son absence est un HOLD dur

G-VAR-2 est un cap **par lane et par jour**. Un grain qui ne déclare pas sa lane est **structurellement incomptable** : le cap devient inapplicable sans que personne n'ait eu à le contourner. Le champ `lane` n'est donc pas de la décoration de reporting, c'est la **clé d'agrégation du gate**. Constaté sur #8697 et #8699 — deux tranches du même rollout, toutes deux sans lane.

## 9. Obligation de provisionnement — la moitié coordinateur du problème

Le mandat 2026-07-21 dit « steere **mieux** », pas « constate la vague au merge ». La cause racine est **autant** un défaut de provisionnement qu'un réflexe de facilité worker : quand `ai-01` ne stocke pas de substance, le worker tombe mécaniquement sur les veines faciles générables-à-la-demande.

Détail du mécanisme (loterie substance, variation du dispatch d'un cycle à l'autre) : mémoire locale `feedback-substance-lottery-provisioning.md`. Le principe qui lie le coordinateur : **sous-provisionner puis merger la monoculture qui en résulte est le manquement que ce protocole corrige.**

## 10. Alias — table de normalisation du GENRE

Le GENRE est le **type de travail**, jamais la famille où vivent les fichiers. Le merge-gate normalise avant d'appliquer les gates ; le worker n'est ni repris ni HOLD pour un alias.

| Écrit | Canonique | Motif |
|---|---|---|
| `lean-ci`, `lean-tooling`, `cjk-ci`, `audit-tooling` | `guard` ou `tooling` (cf. discriminant « est-ce que ça peut rougir ») | composé `<famille>-<genre>` : il se réduit toujours à sa tête, la famille se lit déjà dans les chemins du diff |
| `test-coverage` | `test` | synonyme — sinon le ban `test` de G-VAR-3 est inatteignable |
| `refs`, `documentation` | `docs` | synonyme |
| `data` | `ledger` | tranché par l'incident #8056 |
| `content` | `docs` ou `notebook-python` selon le travail réel | genre **hors énumération** — six grains consécutifs de `po-2023:CoursIA` l'ont porté (#10745, #10742, #10733, #10727, #10712, #10711), rendant l'adjacence G-VAR-3 inatteignable : un genre hors liste ne collisionne avec rien |
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

## Voir aussi

- [`.claude/rules/variation-protocol.md`](../../.claude/rules/variation-protocol.md) — la règle (tag, 3 gates, merge-gate, provisionnement)
- [`.claude/rules/proactive-coordination.md`](../../.claude/rules/proactive-coordination.md) — R1, R5, R6/R7
- [`.claude/rules/coordinator-discipline.md`](../../.claude/rules/coordinator-discipline.md) — R4 (jamais sanctionner l'idle), R5 (steer qui ATTEINT/VRAI/DÉCIDE)
- [`docs/reference/proactive-coordination-detail.md`](proactive-coordination-detail.md) — backlog, sources, anti-patterns
