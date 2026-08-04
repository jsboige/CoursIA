# Protocole de variation — détail, incidents fondateurs, mesures

Détail déporté de [`.claude/rules/variation-protocol.md`](../../.claude/rules/variation-protocol.md), qui reste le texte normatif. Ce fichier porte ce qui **justifie** les gates : les incidents qui les ont créés, les mesures qui ont tranché leurs seuils, et les tables de référence trop volumineuses pour le harnais auto-chargé.

Motif du déport : le fichier de règle est passé de **7 644 o (2026-07-21, création) à 19 057 o (2026-07-31)** en dix jours, par sept commits dont cinq sont des `docs(variation-protocol)` de clarification. Il pesait à lui seul ~8,4k tokens dans le contexte de chaque session, soit la quasi-totalité de l'écart mesuré entre le harnais de `ai-01` et celui des workers. La règle contre la monoculture était devenue une veine à PR faciles.

---

## 1. Champ `prev:` — pourquoi le numéro de PR est obligatoire

`prev: <TIER>/<GENRE> #<PR>` documente le grain précédent de la lane pour l'adjacence G-VAR-3, **et** le lie à une PR vérifiable.

Le numéro est **plus vérifiable** que le genre seul : un `prev: MED/lean` nu est re-dérivable de mémoire (donc contestable), tandis qu'un `prev: MED/lean #8954` pointe vers une PR réelle dont on peut relire le diff.

**Mesure (2026-07-31, 55 PR taguées depuis la ratification du 2026-07-21)** : **100 %** portaient déjà le numéro de PR. La spec d'origine (`prev: <TIER>/<GENRE>`, sans numéro) n'était respectée par personne — la règle a été alignée sur la pratique plutôt que d'imposer du churn de reformatage.

Le checker [`variation-tag-guard.yml`](../../.github/workflows/variation-tag-guard.yml) ne valide **pas** le champ `prev:` (il valide `TIER` + `GENRE` + `lane`). Cette forme n'ajoute donc ni ne retire aucun gate.

## 2. Le guard est agnostique à la ponctuation

La forme canonique du tag utilise `—` (em-dash) et des libellés minuscules. Le guard matche par **mot-clé** (`Grain:`, `lane`) en casse insensible, après neutralisation de la décoration markdown (`tr -d '*\``). Il ne voit **ni** le séparateur (`—` / `·` / virgule) **ni** la casse (`Lane:` et les backticks passent).

Conséquence : un tag en variante de présentation n'est **pas** une non-conformité à reformatter. Ce que le coordinateur vérifie est la **substance** (TIER par le litmus, GENRE dans l'énumération, `lane` présente), jamais la ponctuation. Ne pas forcer de churn cosmétique sur un tag valide. (See #8934 tranche (C).)

## 3. GENRE — table de normalisation des alias

**Mesure (2026-07-31, 55 PR taguées)** : 18, soit **33 %**, portaient un genre hors énumération.

| Écrit | Occ. | Canonique | Motif |
|---|---|---|---|
| `lean-ci` | 4 | `guard` ou `tooling` (cf. §4) | composé `<famille>-<genre>` |
| `test-coverage` | 3 | `test` | synonyme — garder les deux rend le ban `test` inatteignable |
| `refs` | 2 | `docs` | l'hygiène de liens/références est du travail de documentation |
| `lean-tooling` | 1 | `tooling` | composé |
| `cjk-ci` | 1 | `guard` ou `tooling` | composé |
| `audit-tooling` | 1 | `tooling` | composé |
| `documentation` | 1 | `docs` | synonyme |
| `data` | 1 | `ledger` | tranché par l'incident §5 |
| `Lean` | 1 | `lean` | les genres sont en minuscules |

Deux entrées étaient au contraire de **vraies lacunes** et ont rejoint l'énumération : **`tooling`** (script ou helper qui n'est pas une porte — ni `guard`, ni `refactor` qui restructure de l'existant) et **`research-code`** (module de recherche produisant un résultat falsifiable — `notebook-python` est faux dès que le livrable n'est pas un notebook).

**Un alias n'est pas une violation.** Le worker qui écrit `documentation` ou `lean-ci` n'est ni HOLD ni repris : le coordinateur normalise silencieusement et applique les gates au genre canonique. Ce qui compte est que deux grains du même travail soient **comptés comme le même genre**, pas que le worker ait mémorisé la liste.

## 4. `guard` vs `tooling` — le discriminant est « est-ce que ça peut rougir »

Un livrable qui ajoute ou corrige un **check susceptible de passer au rouge** est `guard`. Un livrable qui ajoute ou corrige un **script, un helper, un convertisseur** sans statut d'échec propre est `tooling`. C'est ce qui tranche `lean-ci` au cas par cas plutôt qu'en bloc : le job CI qui fait échouer un lake est `guard` ; le wrapper qui l'appelle plus commodément est `tooling`.

**Admission dans la liste des genres LIGHT de G-VAR-3 — sur mesure, jamais sur intuition.** Cette liste (`guard` · `ledger` · `docs` · `readme` · `test`) porte le ban absolu des deux-consécutifs ; l'y ajouter à l'aveugle bloquerait du travail substantiel. Critère : **un genre y entre dès qu'il a accumulé ≥ 2 grains LIGHT mergés**. Au 2026-07-30, `tooling` était à 5 grains MED sur 5 et `research-code` à 1 DEEP sur 1 — aucun ne qualifiait.

## 5. Incident fondateur — le rollout `metadata.cost` (#8056, 2026-07-28)

Quatre tranches d'un **seul** rollout scan-générable ont porté **trois étiquettes différentes** : #8732 `DEEP/genai`, #8735 `MED/genai`, #8699 `MED/data`, #8697 (antérieure, sans lane).

Aucune n'a déclenché G-VAR-2 ni G-VAR-3, alors que les quatre sont LIGHT par le litmus — « j'en génère une douzaine en scannant la série suivante » est littéralement ce que fait une « tranche 2 ». Le genre avait été choisi d'après le **répertoire traversé** (`GenAI/` → `genai`, `Search/` → `data`), pas d'après le type de travail.

Le coordinateur en a mergé plusieurs sans auditer le tag. Responsabilité partagée : c'est de là que vient la clause « le tag déclaré n'est pas auto-exécutoire » du merge-gate.

Deux tranches (#8697, #8699) n'avaient **pas de champ `lane`** — G-VAR-2 étant un cap par lane et par jour, un grain sans lane est structurellement incomptable. D'où le HOLD sur tag incomplet.

## 6. G-VAR-2 — pourquoi un ratio et plus un plafond absolu (2026-07-31, sign-off user)

Le cap `1 LIGHT/lane/jour` traitait identiquement une lane à 1 PR et une lane à 19 merges dont 13 DEEP. Le second cas est l'**exact opposé** de la monoculture, et se voyait sanctionné pareil. Un plafond insensible au débit ne mesure pas la monoculture : il plafonne le débit.

Pire, il **fabriquait** le travail en double qu'il prétendait économiser. #8961 (documentation du piège d'ordre `strip` → `--update`) a été tenue une journée au titre de G-VAR-2 ; pendant ce hold la doc n'a pas atteint `main`, et **deux autres sessions ont réécrit la même chose** — #8983 et #8996, fermées comme doublons. ~98 lignes rédigées trois fois.

D'où les deux clauses actuelles : le budget est **proportionnel** (`max(1, merges_du_jour // 3)`), et un HOLD sur LIGHT **ne dépasse jamais 24 h**. Passé ce délai, soit on merge, soit on ferme en nommant le remplaçant.

Le budget se **calcule**, il ne s'estime pas : [`scripts/variation_light_cap.py`](../../scripts/variation_light_cap.py) `--replay <merged.json>`. C'est cette sortie qu'on cite dans un HOLD.

## 7. G-VAR-3 — pourquoi le ban absolu ne vise que les genres LIGHT

Un spécialiste Lean qui enchaîne deux preuves DEEP **distinctes** (ex. #7649 puis #2159 Grothendieck) n'est pas la monoculture visée : chacune a demandé du raisonnement de domaine neuf. Scoper le ban aux seuls genres LIGHT (#7657) évite de bloquer le travail dur au motif du seul label.

Le tell décisif reste le litmus : « pourrais-je générer le suivant en scannant l'instance d'à-côté ? » — **oui** → c'est la vague, bloqué **même sous une étiquette DEEP** ; **non** → OK.

---

## Voir aussi

- [`.claude/rules/variation-protocol.md`](../../.claude/rules/variation-protocol.md) — le texte normatif
- [`.claude/rules/proactive-coordination.md`](../../.claude/rules/proactive-coordination.md) — R6/R7, que ce protocole opérationnalise
- [`.claude/rules/harness-hygiene.md`](../../.claude/rules/harness-hygiene.md) — les 3 tiers d'information qui motivent ce déport
