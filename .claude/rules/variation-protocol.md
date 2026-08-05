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

`lean` · `qc` · `training` · `genai` · `notebook-python` · `notebook-dotnet` · `docs` · `guard` · `refactor` · `ledger` · `readme` · `test` · `tooling` · `research-code`.

Un genre hors liste est un **alias** que le merge-gate normalise avant d'appliquer les gates — pas une violation, le worker n'est ni repris ni HOLD. La fermeture n'est pas du vocabulaire : l'adjacence compare des genres, et un vocabulaire ouvert rend G-VAR-3 inatteignable par simple choix de mot.

**Le GENRE est le TYPE DE TRAVAIL, jamais la famille où vivent les fichiers.** Test : *si le prochain grain de ce rollout tombait dans une autre famille, changerais-je le GENRE ?* Si oui, le genre décrit le répertoire — reprendre celui du travail. Même chose pour le composé `<famille>-<genre>` (`lean-ci`, `cjk-ci`, `audit-tooling`) : **il se réduit toujours à sa tête**, la famille se lit déjà dans les chemins du diff.

| Écrit | Canonique | Motif |
|---|---|---|
| `lean-ci`, `lean-tooling`, `cjk-ci`, `audit-tooling` | `guard` ou `tooling` (cf. discriminant) | composé `<famille>-<genre>` |
| `test-coverage` | `test` | synonyme — sinon le ban `test` est inatteignable |
| `refs`, `documentation` | `docs` | synonyme |
| `data` | `ledger` | tranché par l'incident #8056 |
| `Lean` | `lean` | genres en minuscules |

**`guard` vs `tooling` — le discriminant est « est-ce que ça peut rougir ».** Un check susceptible de passer au rouge est `guard` ; un script/helper/convertisseur sans statut d'échec propre est `tooling`.

**Entrer dans la liste LIGHT de G-VAR-3 se mesure, jamais s'intuitionne** : un genre y entre dès **≥ 2 grains LIGHT mergés**. Au 2026-07-30, `tooling` est à 5 MED sur 5 et `research-code` à 1 DEEP sur 1 — aucun ne qualifie.

## 2. Les trois gates durs

- **G-VAR-1 — Plat principal DEEP ou MED.** La PR-plancher du cycle (R1 de proactive-coordination) **DOIT** être DEEP ou MED. **Une LIGHT ne satisfait JAMAIS le plancher.** Le pool global porte toujours du DEEP/MED : la monoculture vient du choix du plus facile *disponible*, pas d'une absence de substance.
- **G-VAR-2 — Budget LIGHT proportionnel : `max(1, grains_mergés_du_jour // 3)`**, par lane et par jour, **toutes catégories LIGHT confondues**. Une lane à 1-5 grains garde l'ancien plafond d'une LIGHT ; à 6 elle en a deux, à 19 elle en a six. Au-delà : la LIGHT attend demain ou cède la place à du DEEP/MED. Le budget se **calcule** — [`scripts/variation_light_cap.py`](../../scripts/variation_light_cap.py) — il ne se déclare pas.
- **G-VAR-3 — Pas deux fois le même GENRE LIGHT consécutif.** Ban **absolu** sur les genres LIGHT (`guard` · `ledger` · `docs` · `readme` · `test`) : bloqué dès 2. Pour un genre **DEEP ou MED dans le domaine-cœur d'une lane spécialiste**, deux consécutifs sont autorisés **si chacun est une substance genuinement distincte** — théorème/module/résultat différent, produit par du raisonnement neuf. Un spécialiste Lean qui enchaîne deux preuves DEEP distinctes n'est **pas** la monoculture visée. Tell décisif : le litmus LIGHT — générable en scannant l'instance d'à-côté → bloqué **même sous une étiquette DEEP**.

## 3. Merge-gate coordinateur (ai-01) — les dents (HARD)

Le protocole ne mord que si `ai-01` cesse de merger passivement. À chaque passe, pour chaque PR, **lire le tag** et croiser avec les grains récents de la lane :

| Constat | Action |
|---|---|
| LIGHT d'une lane à budget épuisé (G-VAR-2) | **HOLD** : citer la sortie de `variation_light_cap.py` (`N` LIGHT pour `M` grains), pas une estimation |
| 2ᵉ même-GENRE consécutif (G-VAR-3) | **HOLD** *si* genre LIGHT **ou** DEEP/MED non-distinct. Un 2ᵉ DEEP/MED genuinement distinct **passe** |
| Plancher tenu par une LIGHT (G-VAR-1) | steer vers un grain DEEP/MED du pool, **nommé** |
| Tag mal dérivé (tier sur-coté, genre pris sur la famille, alias/composé) | **re-qualifier le tag soi-même**, puis traiter selon le tag corrigé |
| `lane` absente | **HOLD** jusqu'à déclaration — un grain sans lane est **structurellement incomptable**, et le cap devient inapplicable sans que personne ne le contourne |

**Le tag déclaré n'est pas auto-exécutoire** : il rend le grain auditable, il ne le définit pas. Merger sans lire le tag laisse le protocole s'auto-certifier.

**Ne jamais tenir une LIGHT plus d'une journée** : un hold prolongé fait réécrire le même travail par une autre lane. Passé 24 h : merger, ou fermer **en nommant le remplaçant**.

Le HOLD **ne sanctionne jamais la lane en idle** ([coordinator-discipline.md](coordinator-discipline.md) R4) : il est **toujours accompagné d'un grain DEEP/MED nommé** du pool, poussé en **double canal** (DM inbox + `[DISPATCH→inbox]` dashboard). HOLD sans remplacement = échec coordinateur.

## 4. Obligation de provisionnement — ce qui lie ai-01 (HARD)

La cause racine est **autant** un défaut de provisionnement qu'un réflexe de facilité worker : sans substance stockée, le worker tombe sur les veines faciles. Chaque cycle `/coordinate`, `ai-01` :

1. **Provisionne ≥1 grain DEEP/MED par lane**, **groundé firsthand** (`gh issue view`), varié en genre d'une lane à l'autre.
2. **Varie la loterie** d'un cycle à l'autre — le coordinateur applique G-VAR-3 à son propre dispatch.

Sous-provisionner puis merger la monoculture qui en résulte est **le** manquement que ce protocole corrige.

## 5. Auto-détection

Avant de claim / de merger : **« ce grain est-il générable-en-série (LIGHT) ET (budget épuisé OU même-genre-que-le-précédent) ? »** Si oui, c'est la monoculture — le worker pioche un DEEP/MED, le coordinateur HOLD+redirige.

## Voir aussi

- [docs/reference/variation-protocol-detail.md](../../docs/reference/variation-protocol-detail.md) — justifications mesurées, incidents #8056 / #8961, historique des applications
- [proactive-coordination.md](proactive-coordination.md) — R1, R5 (pool global), R6/R7 (variété, never-idle)
- [coordinator-discipline.md](coordinator-discipline.md) — R4 (jamais sanctionner l'idle), R5 (steer qui ATTEINT/VRAI/DÉCIDE)
