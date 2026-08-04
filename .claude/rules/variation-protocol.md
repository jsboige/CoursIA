# Protocole de variation — anti-monoculture, tag déclaré + merge-gate coordinateur

S'applique à **tous les workers** (`po-*`) **et au coordinateur `ai-01`**. Source : mandat user 2026-07-21 (« la monoculture de PRs facile est toujours bien là, il faut que tu steere mieux, c'est peut-être le moment d'imposer un protocole de variation »).

Les *concepts* (tiers DEEP/MED/LIGHT, budget LIGHT, rotation des genres) sont déjà posés en R6/R7 de [proactive-coordination.md](proactive-coordination.md) — et pourtant la monoculture persistait, parce qu'ils étaient auto-évalués, invisibles et non-gatés au merge. Ce fichier ajoute la **mécanique d'enforcement** : tag déclaré auditable, merge-gate coordinateur, obligation de provisionnement.

**Incidents fondateurs, tables de normalisation, mesures et justifications de seuils** : [docs/reference/variation-protocol-detail.md](../../docs/reference/variation-protocol-detail.md).

## 1. Le tag de grain (HARD)

Tout `[CLAIMED]` (dashboard) **et** tout body de PR portent en **première ligne** :

```
Grain: <TIER>/<GENRE> — lane <machine:workspace> — prev: <TIER>/<GENRE> #<PR>
```

Ex. `Grain: DEEP/lean — lane myia-po-2026:CoursIA — prev: LIGHT/guard #8954`.

Le numéro de PR de `prev:` est **obligatoire** : il rend le grain précédent vérifiable au lieu d'auto-déclaré. Le guard [`variation-tag-guard.yml`](../../.github/workflows/variation-tag-guard.yml) est **agnostique à la ponctuation et à la casse** — il vérifie la présence de `TIER`, `GENRE`, `lane`, pas le séparateur. **Ne jamais reformatter un tag valide** ([détail §1-2](../../docs/reference/variation-protocol-detail.md)).

### TIER — test objectif, PAS auto-évaluation de valeur

| TIER | Test décisif (litmus) | Exemples |
|------|----------------------|----------|
| **DEEP** | `main` contient-il désormais un **résultat/capacité qui n'existait pas**, dont la production a demandé du **raisonnement de domaine** ? | sorry Lean retiré + `lake build SUCCESS` · training/backtest avec verdict multi-seed · nouveau notebook pédagogique exécuté (≥3 exos, outputs réels) · moteur SOTA nouvellement branché · module de recherche avec résultat falsifiable |
| **MED** | Étend de la substance existante **avec ré-exécution/vérification**, et **change quelque chose** (pas « 0 trouvé ») | enrichissement + ré-exec · audit borné dont le finding **change une décision** · exercice ajouté + exécuté · refactor avec tests qui passent · audit README corrigeant un drift structurel réel |
| **LIGHT** | **« Pourrais-je en générer une douzaine d'autres à la chaîne en scannant l'instance suivante ? »** → si oui : LIGHT, quel que soit le nom qu'on lui donne | guard-tranche · portability/path-fix · doc-resync · ledger append · fix accent/leak/FP · propagation de marqueur |

Le litmus LIGHT est le **cœur anti-gaming** : guards, resyncs, ledger-entries, accents passent TOUS ce test → tous LIGHT, peu importe l'étiquette collée.

### GENRE — étiquette de rotation

`lean` · `qc` · `training` · `genai` · `notebook-python` · `notebook-dotnet` · `docs` · `guard` · `refactor` · `ledger` · `readme` · `test` · `tooling` · `research-code`

**L'énumération est CLOSE**, parce que l'adjacence G-VAR-3 compare des genres : si le vocabulaire est ouvert, deux grains du même travail sous deux étiquettes ne sont jamais vus comme consécutifs, et le ban devient inatteignable par simple choix de mot. Un genre hors liste est un **alias** que le coordinateur normalise silencieusement — ce n'est pas une violation, et le worker n'est pas repris ([table de normalisation](../../docs/reference/variation-protocol-detail.md#3-genre--table-de-normalisation-des-alias)).

Deux voies de contournement, toutes deux fermées :

- **Le GENRE est le TYPE DE TRAVAIL, jamais la famille où vivent les fichiers.** Une passe de stamping `metadata.cost` est du `ledger`, qu'elle traverse `GenAI/`, `Search/` ou `Probas/`. Test : *si le prochain grain de ce rollout tombait dans une autre famille, changerais-je le GENRE ?* Si oui, le genre décrit le répertoire — reprendre celui du travail.
- **Un genre composé se réduit toujours à sa tête** : `<famille>-<genre>` → `<genre>` (`lean-ci` → `guard` ou `tooling`, `audit-tooling` → `tooling`). La famille se lit déjà dans les chemins du diff. Discriminant `guard` vs `tooling` : **est-ce que ça peut rougir ?** Un check qui peut échouer est `guard` ; un script ou helper sans statut d'échec propre est `tooling`.

## 2. Les trois gates durs

- **G-VAR-1 — Plat principal DEEP ou MED.** La PR-plancher du cycle (`≥1 PR/wakeup`, R1) **DOIT** être DEEP ou MED. **Une LIGHT ne satisfait JAMAIS le plancher.** Le pool global porte toujours du DEEP/MED : la monoculture vient du choix du plus facile *disponible*, pas d'une absence de substance.
- **G-VAR-2 — Budget LIGHT proportionnel : `max(1, merges_du_jour // 3)` par lane**, toutes catégories LIGHT confondues (`guard` + `resync` + `ledger` = 3 LIGHT, pas 3 familles). Une lane à 1-5 merges garde exactement l'ancien plafond d'une LIGHT ; à 19 merges elle en a six. Au-delà : la LIGHT attend demain ou cède la place. Le budget se **calcule**, il ne s'estime pas : [`scripts/variation_light_cap.py`](../../scripts/variation_light_cap.py) `--replay`.
- **G-VAR-3 — Pas deux fois le même GENRE LIGHT consécutif.** Ban **absolu** dès 2 sur `guard` · `ledger` · `docs` · `readme` · `test` (la vague se forme dès 2). Pour un genre **DEEP ou MED dans le domaine-cœur d'une lane spécialiste**, deux consécutifs sont autorisés **si chacun est une substance genuinement distincte** — théorème/module/résultat différent produit par du raisonnement neuf, pas une variante scan-générée. Tell décisif : le litmus LIGHT. « Oui, je peux générer le suivant par scan » → c'est la vague, bloqué **même sous une étiquette DEEP**.

## 3. Merge-gate coordinateur (ai-01) — les dents (HARD)

Le protocole ne mord que si `ai-01` **cesse de merger passivement la monoculture**. À chaque passe de merge, `ai-01` **lit le tag** et le croise avec les grains récents de la lane :

| Violation | Action |
|---|---|
| **G-VAR-2** — budget LIGHT épuisé | **HOLD** en citant la sortie de `variation_light_cap.py` (`N` LIGHT pour `M` merges). **Jamais plus de 24 h** : au-delà, merger ou fermer en nommant le remplaçant — un hold prolongé fait réécrire le même travail par une autre lane (#8961 → #8983/#8996). |
| **G-VAR-3** — 2ᵉ même-genre consécutif | **HOLD** *seulement* si genre LIGHT, ou DEEP/MED non-distinct (variante scan-générée). Un 2ᵉ DEEP/MED genuinement distinct **passe** — ne pas HOLD une preuve dure au motif du seul label. |
| **G-VAR-1** — plancher tenu par une LIGHT | steer vers un grain DEEP/MED du pool, **nommé**. |
| **Tag mal dérivé** — tier sur-coté, genre pris sur la famille, alias/composé | `ai-01` **re-qualifie le tag lui-même**, puis traite la PR selon le tag corrigé. Le tag déclaré **n'est pas auto-exécutoire** : il rend le grain auditable, il ne le définit pas. Merger sans lire le tag laisse le protocole s'auto-certifier. |
| **`lane` absente** | **HOLD** jusqu'à déclaration. G-VAR-2 est un cap *par lane et par jour* : un grain sans lane est structurellement incomptable. |

Le HOLD **ne sanctionne jamais la lane en idle** (cf [coordinator-discipline.md](coordinator-discipline.md) R4) : il est **toujours accompagné d'un grain DEEP/MED nommé** du pool, poussé en **double canal** (DM inbox + `[DISPATCH→inbox]` dashboard). HOLD sans grain de remplacement = échec coordinateur, pas enforcement.

## 4. Obligation de provisionnement — ce qui lie ai-01 (HARD)

La cause racine est **autant** un défaut de provisionnement coordinateur qu'un réflexe de facilité worker : quand `ai-01` ne stocke pas de substance, le worker tombe sur les veines faciles. Donc **chaque cycle `/coordinate`** :

1. **Provisionner ≥1 grain DEEP/MED par lane** (« loterie substance », cf [[feedback-substance-lottery-provisioning]]), **groundé firsthand** (`gh issue view`), varié d'une lane à l'autre.
2. **Varier la loterie d'un cycle à l'autre** — `ai-01` applique G-VAR-3 à son propre dispatch.

Sous-provisionner puis merger la monoculture qui en résulte = **le** manquement que ce protocole corrige. « Steere mieux » = provisionne + gate, pas « constate la vague au merge ».

## 5. Auto-détection (worker et coordinateur)

Avant de claim / de merger : **« ce grain est-il générable-en-série (LIGHT) ET (budget LIGHT épuisé OU même-genre-que-le-précédent) ? »** Si oui, c'est la monoculture : le worker pioche un DEEP/MED du pool ; le coordinateur HOLD + redirige.

## Voir aussi

- [docs/reference/variation-protocol-detail.md](../../docs/reference/variation-protocol-detail.md) — incidents, tables, mesures, justifications de seuils
- [proactive-coordination.md](proactive-coordination.md) — R1 (plancher), R5 (pool global cross-lane), R6/R7 (variété, never-idle). **Ce protocole les opérationnalise.**
- [coordinator-discipline.md](coordinator-discipline.md) — R4 (jamais sanctionner l'idle), R5 (steer qui ATTEINT/VRAI/DÉCIDE)
- [harness-hygiene.md](harness-hygiene.md) — les 3 tiers qui motivent le déport du détail
