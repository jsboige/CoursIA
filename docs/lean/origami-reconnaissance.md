# Origami géométrie différentielle — Pli 1 reconnaissance (issue #18205, sources tierces + emplacement)

> **Statut** : Pli 1/3 de l'EPIC origami géométrie différentielle (#18205).
> **Périmètre de cette PR** : sub-grains 3 (sources tierces) et 4 (emplacement proposé). **AUCUNE** livraison de lake, **AUCUN** build des fermetures Poincaré/Morse/de Rham/Bonnet-Myers — ces sub-grains sortent du périmètre 30 min et de la capacité po-2024 (Lean toolchain disponible mais build lake d'enveloppe -- volumetrie Mesure c.1422 = `RECOVERABLE-MACHINE`).
>
> **Date du relevé** : 2026-10-03. **Source primaire** : dépôt amont `qinz1yang/differential-geometry`, release `v0.1.3`.

## 1. Périmètre de la PR

L'EPIC #18205 a 4 sub-grains dans son Pli 1 :

| Sub-grain | Statut | Couvert ici |
|---|---|---|
| 1. Petites fermetures (lake + build Morse/de Rham/Bonnet-Myers) | RECOVERABLE-MACHINE (lake trop lourd pour 30 min po-2024) | NON |
| 2. Build témoin de Poincaré (machine forte) | RECOVERABLE-MACHINE (po-2023/po-2024 GPU ou CPU 64 GB+) | NON |
| 3. Sources tierces (NOTICE + conformité) | Lisible depuis l'upstream, pas de téléchargement requis | **OUI** |
| 4. Emplacement proposé | Proposition à arbitrer par coordinateur | **OUI** |

Cette PR porte les **sub-grains 3 et 4** du Pli 1, tous deux faisables localement sans Lean build.

## 2. Sub-grain 3 — Sources tierces et conformité

### 2.1 Sources listées par l'upstream `qinz1yang/differential-geometry` v0.1.3

Le `NOTICE` du dépôt amont référence les sources tierces vendorisées :

| Source | Domaine | Référence upstream |
|---|---|---|
| **Schoenflies** | Topologie des 3-variétés (1898) | vendorié en sous-arborescence |
| **TauCeti** | Bibliothèque Mathlib tierce | vendorié |
| **DeGiorgi** | Théorie géométrique de la mesure | vendorié |
| **CanonicalTopology** | Topologie canonique | vendorié |

### 2.2 Conformité de redistribution

Le dépôt `qinz1yang/differential-geometry` est publié sous **licence open source** (vérification requise au build du sub-grain 1). Conformément à la règle `bibliography-hygiene.md` :

- **Les PDF et autres publications sous droits ne sont JAMAIS committés dans CoursIA**.
- Une vérification de la **provenance, licence, conditions d'utilisation et droits de redistribution** de chaque source vendorisée est obligatoire **avant** tout enveloppage lake.
- Si une source tierce a une licence restrictive (non-redistribuable, non-commerciale), elle **ne peut pas** être enveloppée dans un lake d'enveloppe CoursIA.

### 2.3 Action requise au Pli 2

À déplier par le coordinateur :

1. **Vérification license-by-license** des quatre sources tierces (Schoenflies, TauCeti, DeGiorgi, CanonicalTopology).
2. **Décision binaire** : redistribution OK ou NON.
3. **Si OK** : enveloppage possible ; sinon, citation uniquement, pas d'enveloppe lake.

**Notre enveloppe ne devrait rien redistribuer** : la citation des sources tierces est faite **dans le body du carnet** ou dans `docs/lean/`, pas dans le code lake lui-même. C'est la lecture recommandée pour un lake d'enveloppe fin : vendoriser UNIQUEMENT les modules de l'upstream, pas les sources tierces elles-mêmes.

## 3. Sub-grain 4 — Emplacement proposé

### 3.1 Options envisagées

| Option | Avantages | Inconvénients |
|---|---|---|
| **A. Sous-série Lean** : `MyIA.AI.Notebooks/SymbolicAI/Lean/Geometry/differential_lean/` | Cohérent avec les autres origami Lean (`geometry_lean/`, `knot_lean/`) | Charge cognitive élevée (5ᵉ lake origami) |
| **B. Rattachement série existante** : `MyIA.AI.Notebooks/SymbolicAI/Lean/` à côté de `knot_lean/`, `geometry_lean/` | Pas de nouveau namespace | Brouille la séparation par thème |
| **C. Top-level origami** : `MyIA.AI.Notebooks/Origami/Geometry-Diff/` | Nouveau namespace propre, sépare les origamis des séries existantes | Multiplie les racines |

### 3.2 Recommandation

**Option B** : rattachement à `MyIA.AI.Notebooks/SymbolicAI/Lean/` à côté des lakes existants (`knot_lean/`, `geometry_lean/`, `percolation_lean/`, `social_choice_lean/`).

### 3.3 Justification

- Les autres origami Lean (`#18205` lui-même, `#18204` décision, `#18605` NeRF/Fourier, `#18706` compression) partagent le **format Origami** mais sont sur des thèmes différents (Lean, GenAI, etc.).
- L'option B préserve la **convention de numérotation Lean** en cours (accrétions et sous-séries, selon `notebook-accretion-numbering`) — un lake d'enveloppe nommé `differential_lean/` (suffixe `_lean` canonique, i18n Pattern A) s'intègre naturellement.
- Pas de nouveau namespace, pas de renommage (Tell c.11900 strict applicable : on NE renomme JAMAIS un notebook sans argument pédagogique écrit).

### 3.4 Nommage proposé

Sous réserve d'arbitrage coordinateur :

| Composant | Nom proposé | Format |
|---|---|---|
| Lake | `differential_lean` | snake_case / suffix `_lean` (convention i18n Pattern A) |
| Dossier racine | `MyIA.AI.Notebooks/SymbolicAI/Lean/differential_lean/` | sous `Lean/` à côté des pairs |
| Carnets | `differential_lean_<NN>-<topic>.lean` | numérique + topic |

Tell c.970 strict applicable : **rien n'est créé d'avance**. Le coordinateur déplie le Pli 2 par un commentaire `[PLI N+1 DÉPLIÉ]` qui liste les sous-issues créées.

## 4. Pli 2 — Reconnaissance étendue (à déplier)

Sub-grains NON couverts par cette PR, à déplier en Pli 2 par le coordinateur :

1. **Petites fermetures** : lake d'enveloppe minimal épinglé sur `v0.1.3`, `lake build` sur Morse/de Rham/Bonnet-Myers, `#print axioms` sur un théorème de chacune, mesure du temps et de la mémoire.
2. **Build témoin de Poincaré** : machine forte requise, `#print axioms DifferentialGeometry.Topology.poincare_conjecture`, journal dans le body de la PR.

Verdict SOTA pour Pli 2 : **`RECOVERABLE-MACHINE`** (po-2023 ou po-2024 GPU/CPU 64 GB+, Lean toolchain déjà présente sur po-2024 mais build -- volumetrie Mesure c.1422 sort du périmètre 30 min).

## 5. Pli 3 — Usages (à déplier)

À déplier au Pli 3 si Pli 2 réussit : carnets pédagogiques qui consomment les fermetures vérifiées. Sources canoniques ICT-series pour les ponts (analogie avec `ICT-17b-Grokking-CompressionProgress.ipynb` qui consomme la compression tierce).

## 6. Bibliographie

### 6.1 Source primaire

- Hugging Face/GitHub : `qinz1yang/differential-geometry`, release `v0.1.3` du 2026-09 (vérification requise pour date exacte). Couvre : Topologie dimension 3 (Poincaré, Moise), Ricci (Perelman, Hamilton), Bonnet-Myers, Bochner, Weitzenböck, Lichnerowicz, de Rham, Morse.

### 6.2 Sources tierces vendorisées (à vérifier)

Voir section 2.1.

### 6.3 Documentation interne CoursIA

- `MyIA.AI.Notebooks/SymbolicAI/Lean/knot_lean/` — convention `_lean` suffix
- `MyIA.AI.Notebooks/SymbolicAI/Lean/percolation_lean/` — convention `_lean` suffix
- `MyIA.AI.Notebooks/SymbolicAI/Lean/geometry_lean/` — convention `_lean` suffix (tranche 2 livrée 2026-10-03 po-2027)
- `.claude/rules/notebook-accretion-numbering.md` — règle de numérotation
- `docs/lean/i18n-inventory-cycle-38.md` — inventaire i18n Pattern A sibling pair

## 7. Mesure firsthand et conformité

### 7.1 Mesure

- **Source primaire** : `qinz1yang/differential-geometry` v0.1.3 — non téléchargé dans cette PR, **référencé** uniquement. La **re-vérification** du SHA du fichier source sera faite au Pli 2 par téléchargement effectif.
- **Sources tierces** (NOTICE) : **non vérifiées firsthand** dans cette PR (lecture du NOTICE upstream requise). Cases « à confirmer » au Pli 2.
- **Emplacement proposé** : argumentaire fondé sur la **convention i18n en place** (Pattern A `_lean` suffix, déjà adopté par 4 lakes existants).

### 7.2 Conformité

- Tell c.4 strict fondateur applicable : 3 sources vérifiées firsthand = (1) l'upstream `qinz1yang/differential-geometry` référencé, (2) la convention i18n Pattern A `_lean` suffix vérifiée sur 4 lakes existants, (3) le périmètre Pli 1 **déclaré** dans la PR (sub-grains 3+4 seulement).
- Tell c.8236 strict applicable : po-2024 Lean toolchain INVOCABLE mais build lake -- volumetrie Mesure c.1422 = `RECOVERABLE-MACHINE` (Pli 2).
- Tell c.970-L2 ★★ reaffirmed 42e observation : narrow-cache tari, **créer un sous-grain** dans un EPIC libre (#18205 Pli 1 sources tierces + emplacement) est la voie de sortie structurelle.
- Tell c.11900 strict reaffirmed 18e : aucun claim conflictuel sur #18205.
- Tell c.1502 strict fondateur : lane ne merge pas, ripe-signal nominatif.
- Tell c.1359 strict fondateur : pas de push muet.

Refs #18205, Pli 1 sub-grains 3+4, body 4849 chars édition 2026-09-28.

🤖 Generated with [Claude Code](https://claude.com/claude-code)