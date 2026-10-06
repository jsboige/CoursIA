# Renum 04-Vision (4.2c-k) → 4.4/4.5/4.6 — plan détaillé (2026-10-06)

**Issue parente :** #19386 · **Précédent :** #19366 (gate de séquencement)
**Mesure :** 2026-10-06T05:23Z (cat. `git ls-tree origin/main`, `gh pr view 19366 --json files`)

## Contexte et mandat

La série `ML/DataScienceWithAgents/04-Vision` porte un carnet de plus que la mesure précédente (l'adversarial camouflage 4.2k arrive via PR #19366). Le tronc 4.2 abrite une famille détection qui dépasse la lettre `k` — soit largement la norme `notebook-accretion-numbering.md` §4 (plafond `e-f` par branche). Cette famille est la **quatrième violatrice** mesurée (après ICT-15, Lean-16, GameTheory-03).

**Mandat user** (concern jsboige 2026-10-05T21:36:47Z sur #19366) : « la numérotation de la série Vision devient presque risible. On ne peut pas garder moins de numéros que d'accrétions d'un seul numéro. Il faut proposer une nouvelle numérotation, et combler d'éventuels angles morts. »

## Catalogue state mesuré au 2026-10-06T05:23Z

`git ls-tree origin/main --name-only -r MyIA.AI.Notebooks/ML/DataScienceWithAgents/04-Vision/` :

| Fichier | Présence main | Touché par #19366 |
|---|---|---|
| `4.1-Conv-NumPy-Torch-Allclose.ipynb` | oui | non |
| `4.2-ConvNet-Profonde-Residuelles.ipynb` | oui | non |
| `4.2b-Lean-GradientFlow-Vanishing.ipynb` | oui (INCHANGÉ) | non |
| `4.2c-Detection-Anchor-From-Scratch.ipynb` | oui | non |
| `4.2d-Detection-AnchorFree-From-Scratch.ipynb` | oui | non |
| `4.2e-Detection-FocalLoss-From-Scratch.ipynb` | oui | non |
| `4.2f-Detection-SOTA-Torchvision.ipynb` | oui | non |
| `4.2g-Detection-SOTA-Ultralytics.ipynb` | oui | non |
| `4.2h-YOLOv5-Bench-Ultralytics.ipynb` | oui | non |
| `4.2i-Detection-Ultralytics-Difficult-Scenes.ipynb` | oui | non |
| `4.2j-Detection-SOTA-LibreYOLO.ipynb` | oui | **oui (modifié)** |
| `4.2k-Detection-Adversarial-Camouflage.ipynb` | **non (PR #19366)** | **oui (ajouté)** |
| `4.3-TransferLearning-ResNet.ipynb` | oui | non |
| `README.md` | oui | oui (modifié) |

`gh pr view 19366 --json files` : 4.2j (modifié) + 4.2k (ajouté) + README + `_quarto.yml`.

## Plan de renum — Option A (recommandée par l'issue #19386)

**3 nouveaux troncs**, chaque branche retombe sous la norme `e-f` :

| Tronc cible | Contenu | Mapping (actuel → cible) |
|---|---|---|
| **4.4 — Détection from scratch** | la trilogie pédagogique anchor / anchor-free / focal | `4.2c` → `4.4` · `4.2d` → `4.4b` · `4.2e` → `4.4c` |
| **4.5 — Détection SOTA** | les wrappers et leurs benches | `4.2f` → `4.5` · `4.2g` → `4.5b` · `4.2h` → `4.5c` · `4.2j` → `4.5d` |
| **4.6 — Robustesse de la détection** | scènes hostiles et adversarial | `4.2i` → `4.6` · `4.2k` → `4.6b` |

**Inchangés** : `4.1` (conv from scratch), `4.2` + `4.2b` (profondeur / résiduelles + companion Lean — l'accrétion `b` approfondit bien 4.2 lui-même), `4.3` (transfer learning).

**Speed-run canonique** après renum : 4.1 → 4.2 → 4.3 → 4.4 → 4.5 → 4.6. La détection entre dans le parcours principal, ce qui reflète son poids réel dans la série (la majorité de l'effectif).

**Option B écartée** (issue §4) : fusionner les benches en carnets plus lourds préserverait les numéros mais perdrait la structure de chunks de l'EPIC #16057 et l'exécution bornée (< 10 min/carnet) qui conditionne la CI golden-set. Coût pédagogique > bénéfice de rangement.

## Tranche split (gating par #19366)

Le mandat de l'issue #19386 demande « une seule PR `renum(...)` content-free (`git mv` uniquement, aucun changement de contenu) ». Le gating par #19366 (qui touche 4.2j et ajoute 4.2k) impose **deux tranches** :

### Tranche A — la volée libre, les carnets qui ne touchent pas la PR #19366

| Source (sur main) | Cible |
|---|---|
| `4.2c-Detection-Anchor-From-Scratch.ipynb` | `4.4-Detection-Anchor-From-Scratch.ipynb` |
| `4.2d-Detection-AnchorFree-From-Scratch.ipynb` | `4.4b-Detection-AnchorFree-From-Scratch.ipynb` |
| `4.2e-Detection-FocalLoss-From-Scratch.ipynb` | `4.4c-Detection-FocalLoss-From-Scratch.ipynb` |
| `4.2f-Detection-SOTA-Torchvision.ipynb` | `4.5-Detection-SOTA-Torchvision.ipynb` |
| `4.2g-Detection-SOTA-Ultralytics.ipynb` | `4.5b-Detection-SOTA-Ultralytics.ipynb` |
| `4.2h-YOLOv5-Bench-Ultralytics.ipynb` | `4.5c-YOLOv5-Bench-Ultralytics.ipynb` |
| `4.2i-Detection-Ultralytics-Difficult-Scenes.ipynb` | `4.6-Detection-Ultralytics-Difficult-Scenes.ipynb` |

**+ README.md** : mise à jour des liens internes 4.2c-i vers 4.4/4.4b/4.4c/4.5/4.5b/4.5c/4.6.

### Tranche B — la volée gated, dépendante du merge de #19366

| Source (sur main post-#19366) | Cible |
|---|---|
| `4.2j-Detection-SOTA-LibreYOLO.ipynb` | `4.5d-Detection-SOTA-LibreYOLO.ipynb` |
| `4.2k-Detection-Adversarial-Camouflage.ipynb` | `4.6b-Detection-Adversarial-Camouflage.ipynb` |

**Gate** : `#19366` doit être **MERGED** (pas juste MERGEABLE) avant l'ouverture de la Tranche B. État au 2026-10-06T05:23Z : `mergeStateStatus: CLEAN`, `mergeable: MERGEABLE`, tête `3d74915d9ddb630d31d73026053c78d4306312cd`, labels `consecutive-code-cells` + `paragraph-length`. Aucun `CHANGES_REQUESTED` visible sur la PR.

## Sweep des 6 surfaces §6 (notebook-accretion-numbering)

Une fois la Tranche A livrée (et la Tranche B après merge), les surfaces §6 de `notebook-accretion-numbering.md` doivent être patchées pour que la renum soit complète :

| # | Surface | Outil de vérif | Cible |
|---|---|---|---|
| 1 | **Navlinks READMEs** (catalogue, famille, série) | `check-docs-links.py` | `**/04-Vision/README.md` + catalogue `MyIA.AI.Notebooks/ML/DataScienceWithAgents/README.md` |
| 2 | **Docs links** (autres .md pointant vers les anciens chemins) | `check-docs-links.py` | grep récursif `4\.2[chij].*\.ipynb` |
| 3 | **Accents / encoding** (Tell c.1057-N1 symétrie FR/EN obligatoire) | `check_markdown_claims_output.py` (classe accents) | aucun chemin corrompu par renommage |
| 4 | **Render README** (visualisation par sk-agent) | `sk-agent` (vision indirecte) | cohérence visuelle des blocs de code vers les nouveaux chemins |
| 5 | **Accord libellé/cible** (#14625) | `check-docs-links.py --label-target` | les liens textuels disent bien « détection anchor / SOTA / robustesse » selon le tronc |
| 6 | **Catalogue étudiant** `jsboigeEPF/2026-MSMIN5IN52-GenAI` | `grep -rn '4\.2[chij]'` (sur la copie locale GDrive) | anciens chemins non cassés, ou note d'accompagnement pour les étudiants |

**Sub-tâches** : (1) un script `scripts/ci/check_vision_renum_sweep.py` qui parcourt les 6 surfaces et sort un verdict `[OK]` ou `[FAIL] <surface>` ; (2) intégration au gate `pr-renum-vision-sweep.yml` ad hoc (le temps de la transition).

## PRs à ouvrir

| PR | Tranche | Tête | Branche | Pré-gate | Post-gate |
|---|---|---|---|---|---|
| **#prep** (cette PR) | n/a | ce doc | `feature/19386-renum-vision-prep` | n/a | doc + claim |
| **#tranche-a** | A (volée libre) | `git mv` + README.md | `renum/19386-vision-44-45-46-tranche-a` | sweep §6 sur les cibles de la Tranche A | après merge de #tranche-a |
| **#tranche-b** | B (volée gated) | `git mv` | `renum/19386-vision-45d-46b-tranche-b` | **merge de #19366** | après merge de #tranche-b |

**Ordre obligatoire** : `git mv` **avant** tout edit de README / sweep — sinon les chemins cibles n'existent pas et les outils cassent.

**Convention `renum(...)`** : `git mv` content-free (règle §5.1 de accretion-numbering), pas d'édition de cellule, pas de `pre-commit` qui touche le contenu. Le sweep des 6 surfaces est sur la **PR tranche** (pas sur ce doc).

## Risques et mitigations

| Risque | Mitigation |
|---|---|
| Squash-merge de #19366 efface l'ascendance de 4.2j/k → ne pas rebase après le merge | `git fetch` + check sur `origin/main` avant `git mv` 4.2j/k |
| Différends catalogue si une autre lane ajoute un 4.2l entre temps | claim explicite + sweep `gh issue list` au moment d'ouvrir la PR tranche |
| Liens brisés dans docs externes (catalogue étudiant GDrive) | sweep surface #6 + note dans le body de la PR tranche |
| `_quarto.yml` mis à jour par #19366 (touché) | attendre merge #19366 pour la Tranche B (4.2kのみ) — la Tranche A n'affecte pas `_quarto.yml` |
| Ratchet exec-sequence #11577 sur les cellules exécutées | les fichiers renommés gardent leur `execution_count` ; pas de re-exec nécessaire si le contenu est intact |

## Péremption

Ce plan est **valide tant que la topologie catalogue n'a pas changé** (pas d'ajout d'un 4.2l, pas de renum alternatif) — mesure 2026-10-06T05:23Z. Un diff `origin/main` sur le dossier Vision à chaque PR tranche confirmera la cohérence.

## Issue parente : #19386 · #15652 (renum policy)
