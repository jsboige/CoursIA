# Origami géométrie différentielle — Pli 1 reconnaissance (issue #18205, sources tierces + emplacement)

> **Statut** : Pli 1/3 de l'EPIC origami géométrie différentielle (#18205).
> **Périmètre de cette PR** : sub-grains 3 (sources tierces) et 4 (emplacement proposé). **Aucune** modification du lake d'enveloppe — il est **déjà versionné sur `main`** (`MyIA.AI.Notebooks/SymbolicAI/Lean/differential_lean/lakefile.lean`) et cette PR ne fait que documenter son état — et **aucun** build des fermetures Poincaré/Morse/de Rham/Bonnet-Myers : ces sub-grains sortent du périmètre 30 min et de la capacité po-2024 (Lean toolchain disponible mais build lake d'enveloppe -- volumetrie Mesure c.1422 = `RECOVERABLE-MACHINE`).
>
> **Date du relevé** : 2026-10-03. **Source primaire** : dépôt amont `qinz1yang/differential-geometry`, release `v0.1.3`.
>
> **Mise à jour du 2026-10-22** (lane `myia-po-2024:CoursIA-2`, dispatch de l'adjoint `myia-po-2025:CoursIA-2`) : le **sub-grain 3 (sources tierces)** est désormais **mesuré firsthand** — `NOTICE`, `LICENSE` et les fichiers de provenance de chaque répertoire vendorisé ont été lus **au pin `7a48598d`**, avec les SHA de blob cités. Les sections 2.1 à 2.3 sont mises à jour ; **le relevé du 2026-10-03 est conservé** en tête de chaque section (il reste l'état de la rédaction). Le sub-grain 4 (emplacement) et le Pli 2 (builds) sont **inchangés**.

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

> **Relève du 2026-10-03** (conservé) — le `NOTICE` du dépôt amont référence les sources tierces vendorisées :
>
> | Source | Domaine | Référence upstream |
> |---|---|---|
> | **Schoenflies** | Topologie des 3-variétés (1898) | vendorié en sous-arborescence |
> | **TauCeti** | Bibliothèque Mathlib tierce | vendorié |
> | **DeGiorgi** | Théorie géométrique de la mesure | vendorié |
> | **CanonicalTopology** | Topologie canonique | vendorié |

#### 2.1 bis — Mesure firsthand du 2026-10-22 (pin `7a48598d`)

Lecture directe de l'amont, sans téléchargement du dépôt (2,2 Go) : `NOTICE`, `LICENSE`, `DifferentialGeometry/External/README.md` et les fichiers de provenance de chaque répertoire vendorisé, au commit `7a48598d` de la release `v0.1.3`. Les SHA sont les **SHA de blob git** (API `contents`), donc vérifiables par `git cat-file`.

**Présence** : `DifferentialGeometry/External/` contient **six** arbres vendorisés et un répertoire de provenance — `Schoenflies/`, `TauCeti/`, `DeGiorgi/`, `CanonicalTopology/`, `ClassificationOfSurfaces/`, `RiemannMapping/`, plus `CanonicalTopologyProvenance/`. Le relevé du 2026-10-03 en citait **quatre** : `ClassificationOfSurfaces/` et `RiemannMapping/` n'y étaient pas.

| Répertoire vendorisé | Provenance déclarée (amont + révision) | Droits déclarés | Preuve (fichier : SHA de blob) |
|---|---|---|---|
| `External/Schoenflies/` | `alonamaloh/schoenflies-lean` @ `05a43d29cde026618777db3d4e4316204ccca237` (README externe) — Álvaro Begué | **Apache-2.0** | `Schoenflies/LICENSE` `8dada3edaf50dbc082c9a125058f25def75e625a` (11 357 o) · `MODIFICATIONS.md` `a2a1faebed339c1ab744348d3c5b6bdfb10f74dc` (7 692 o) · `SOURCE_MAP_arc_05a43d2.json` `d5bec6fc…` · `UPSTREAM_README.md` `718b3dc5…` · `formalization.yaml` `ac1dfe8c…` |
| `External/TauCeti/` | `TauCetiProject/TauCeti` @ `3358033ba2fd35f321356dceaf2372a0fd6c0bfd` (NOTICE racine) — Joseph Tooby-Smith et les contributeurs Tau Ceti | **Apache-2.0** | `TauCeti/LICENSE` `8dada3ed…` (identique au blob `8dada3ed…`) · `MODIFICATIONS.md` `d3c47d64bd35e07d80de00488cebe035ea0ddcfb` · `SOURCE_MAP.json` `832177f6212640e79c0b9e2abad90a64deb23fb5` · `DECLARATION_MAP.json` `12cd4097…` |
| `External/DeGiorgi/` | `scottnarmstrong/DeGiorgi` @ `4c1b307` (README externe) — Scott Armstrong, Julia Kempe (arXiv:2604.05984) | **Apache-2.0** | `DeGiorgi/LICENSE` `ae20225f2f5481948aa4caaf4f69773b5408ebba` (11 361 o : texte Apache 2.0 **avec** la ligne « Copyright 2026 Scott Armstrong and Julia Kempe ») · `CITATION.cff` `3266139ff4d60b152f5fb6cec65e9886e532f772` · `MODIFICATIONS.md` `31b41a9188d85d51fc59dc7df1ebf41bed16d43c` (24 307 o) · `README.md` `a6dc155754c4050578a80aaff0954a697b86a5c0` |
| `External/CanonicalTopology/` | `canonical-topology/Poincare` (Ayush Khaitan et ses contributeurs) ; **partie dérivée** `plby/HopfProblem`, `Solution.lean` @ `9ac8a456b526527837d7082ff775213ca8bc9809`, **lignes 62156–62228** (NOTICE racine) | **Apache-2.0** | `CanonicalTopology/LICENSE` `261eeb9e9f8b2b4b0d119366dda99c6fd7d35c64` (blob identique au `LICENSE` racine) · `MODIFICATIONS.md` `4ce2b04f095b77cacf7e0d5487561828b2ffa40a` (8 762 o) · `SOURCE_MAP.json` `dd089fee49c260109e317195566be037a5df0ffd` (192 998 o) |
| `External/ClassificationOfSurfaces/` | `mccorvie/classification-of-surfaces` @ `e3c7230fe78d7b056a415d9ecae6f77887046b32` (README externe) — contributeurs, Steven Sivek, Kai Lam | **Apache-2.0** | `LICENSE` `8dada3ed…` · `MODIFICATIONS.md` `92aff40570d9686af3bad38f8b4d2c2c857ee912` (15 008 o) · `PROVENANCE.json` `5676f8bf462da64594ddc78ca361b925f76298f5` · `VENDOR.md` `fbec51029a3321ff0fbb0dcb3772e20f33c564e1` (108 355 o) + les fichiers de provenance (patches, cartes de sélection, collisions) |
| `External/RiemannMapping/` | `urkud/mathlib4` @ `d43061d911b1aeae0788591da437a3b115098962` (PR `leanprover-community/mathlib4#33505`, Yury Kudryashov) | **Apache-2.0** | `UPSTREAM.json` `04454df1319fad1fb41e27a59883cdeac13eaf68` (**SHA-256 par fichier**) · `LICENSE` `8dada3ed…` · `MODIFICATIONS.md` `4276ae56d1bee3fda7aee9e60a6187681febf941` · `SNAPSHOTS.json` `9a352393…` · `EXTREMAL-PROVENANCE.json` `69305ffc…` · `HURWITZ-PROVENANCE.json` `80aa8dac…` |

**Deux écarts d'attribution, à signaler à l'amont** (ils ne bloquent pas l'enveloppe, mais ils sont des faits mesurés) :

1. **`DeGiorgi/` n'est pas dans le `NOTICE` racine** : sa provenance n'est déclarée que dans `DifferentialGeometry/External/README.md`. **Fait observé** : l'attribution de `DeGiorgi/` figure dans un fichier annexe, et n'apparaît pas dans le `NOTICE` racine. **Ce que ce fait ne prouve pas** : la présence d'une mention de provenance dans un `README`/`UPSTREAM` ne vaut pas, à elle seule, preuve que les conditions applicables de l'Apache-2.0 sont satisfaites (§4(d) : conservation de la `LICENSE`/`NOTICE`, mention des modifications) — cette vérification reste **à faire au cas par cas**, et aucune conclusion de conformité globale n'est tirée ici.
2. **`RiemannMapping/` n'est dans ni le `NOTICE` racine ni le `External/README.md`** : son attribution ne vit que dans son propre `UPSTREAM.json` (avec SHA-256 par fichier). La provenance est traçable et vérifiable ; l'omission au niveau racine est un défaut d'annonce, à signaler en upstream.

### 2.2 Conformité de redistribution

> **Relève du 2026-10-03** (conservé) — le dépôt `qinz1yang/differential-geometry` est publié sous **licence open source** (vérification requise au build du sub-grain 1). Conformément à la règle `bibliography-hygiene.md` :
>
> - **Les PDF et autres publications sous droits ne sont JAMAIS committés dans CoursIA**.
> - Une vérification de la **provenance, licence, conditions d'utilisation et droits de redistribution** de chaque source vendorisée est obligatoire **avant** tout enveloppage lake.
> - Si une source tierce a une licence restrictive (non-redistribuable, non-commerciale), elle **ne peut pas** être enveloppée dans un lake d'enveloppe CoursIA.

**Mesure du 2026-10-22** : le `LICENSE` racine est le texte **Apache License 2.0** intégral (11 357 o, blob `261eeb9e9f8b2b4b0d119366dda99c6fd7d35c64`), et la GitHub API renvoie la SPDX `Apache-2.0` pour le dépôt. Le `NOTICE` racine (1 791 o, blob `264ca83de5638b06033196bbb8b2da4cca7aba1c`) est présent. **Les six arbres vendorisés sont sous Apache-2.0**, chacun avec son `LICENSE` (blob `8dada3ed…` pour quatre d'entre eux, `261eeb9e…` pour CanonicalTopology, `ae20225f…` pour DeGiorgi) et son `MODIFICATIONS.md`.

**Faits mesurés** : les six sources sont sous **Apache-2.0** — aucune n'est sous licence restrictive (non-redistribuable ou non commerciale) ; aucun PDF n'est concerné, les sources vendorisées sont du **code Lean**, pas des publications. **Permission, sous conditions** : Apache-2.0 **autorise** la redistribution, à condition de conserver `LICENSE` et `NOTICE` et de signaler les modifications (§4). **Vérification des conditions applicables** : ce document mesure les licences et les fichiers de provenance ; il ne conclut **pas** à la conformité de l'amont, et la satisfaction effective des conditions de redistribution reste à vérifier par l'entité qui redistribue.

### 2.3 Verdict mesuré (2026-10-22)

> **Ce qui était demandé** (relève du 2026-10-03, conservé) :
>
> 1. **Vérification license-by-license** des quatre sources tierces (Schoenflies, TauCeti, DeGiorgi, CanonicalTopology).
> 2. **Décision binaire** : redistribution OK ou NON.
> 3. **Si OK** : enveloppage possible ; sinon, citation uniquement, pas d'enveloppe lake.
>
> **Notre enveloppe ne devrait rien redistribuer** : la citation des sources tierces est faite **dans le body du carnet** ou dans `docs/lean/`, pas dans le code lake lui-même. C'est la lecture recommandée pour un lake d'enveloppe fin : vendoriser UNIQUEMENT les modules de l'upstream, pas les sources tierces elles-mêmes.

**Réponse mesurée** :

1. **License-by-license : fait** — tableau 2.1 bis (six arbres, pas quatre : `ClassificationOfSurfaces/` et `RiemannMapping/` étaient absents du relevé du 2026-10-03). Chaque ligne porte sa provenance (amont + révision), ses droits et le SHA de blob de ses fichiers de licence et de modification.
2. **Décision binaire : redistribution possible SOUS CONDITIONS.** Aucune source restrictive : la licence est Apache-2.0 pour les six sources, qui autorise la redistribution **sous condition** de conservation des `LICENSE`/`NOTICE` et de mention des modifications. Cette décision porte sur la **licence** ; elle ne vaut pas conclusion de conformité de l'amont.
3. **Conséquence pour nous : l'enveloppe lake existe déjà sur `main`**, et **notre dépôt ne redistribue rien**. Le lake d'enveloppe versionné (`MyIA.AI.Notebooks/SymbolicAI/Lean/differential_lean/lakefile.lean`) déclare déjà l'amont en `require DifferentialGeometry from git … @ "v0.1.3"` — tag `v0.1.3`, commit `7a48598d` — et son en-tête pose les mêmes invariants : « Aucune source de l'amont n'est recopiée, aucun fork n'est fait : la surface est une dépendance ». **Cette PR ne modifie pas ce lake** (périmètre : sub-grains 3 et 4 — mesure des licences et proposition d'emplacement) ; elle en **documente** l'état. Les sources tierces et leurs licences restent **chez l'amont** et sont téléchargées par le gestionnaire de dépendances, pas recopiées dans CoursIA. La citation se fait dans le body des carnets et dans `docs/lean/`, comme le voulait le relevé initial.

**Ce qui reste à faire, et par qui** : signaler à l'amont les deux écarts d'attribution du § 2.1 bis (DeGiorgi et RiemannMapping absents du `NOTICE` racine) — sous la forme d'une **issue proposée**, sans PR à leur place sans invitation (règle du Pli 1 : « aucune PR chez eux sans y être invités »). Le **Pli 2** (builds) n'est pas ouvert par ce document : il reste un dépli du coordinateur.

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
- Pas de nouveau namespace, pas de renommage (applicable, [notebook-accretion-numbering.md](../../.claude/rules/notebook-accretion-numbering.md) : on NE renomme JAMAIS un notebook sans argument pédagogique écrit).

### 3.4 Nommage proposé

Sous réserve d'arbitrage coordinateur :

| Composant | Nom proposé | Format |
|---|---|---|
| Lake | `differential_lean` | snake_case / suffix `_lean` (convention i18n Pattern A) |
| Dossier racine | `MyIA.AI.Notebooks/SymbolicAI/Lean/differential_lean/` | sous `Lean/` à côté des pairs |
| Carnets | `differential_lean_<NN>-<topic>.lean` | numérique + topic |

**Rien n'est créé d'avance**. Le coordinateur déplie le Pli 2 par un commentaire `[PLI N+1 DÉPLIÉ]` qui liste les sous-issues créées.

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

### 6.2 Sources tierces vendorisées (mesurées le 2026-10-22)

Voir section 2.1 bis (six arbres, provenance + droits + SHA de blob). En amont, toutes en **Apache-2.0**.

### 6.3 Documentation interne CoursIA

- `MyIA.AI.Notebooks/SymbolicAI/Lean/knot_lean/` — convention `_lean` suffix
- `MyIA.AI.Notebooks/SymbolicAI/Lean/percolation_lean/` — convention `_lean` suffix
- `MyIA.AI.Notebooks/SymbolicAI/Lean/geometry_lean/` — convention `_lean` suffix (tranche 2 livrée 2026-10-03 po-2027)
- `.claude/rules/notebook-accretion-numbering.md` — règle de numérotation
- `docs/transients/2026-07-04-lean-i18n-inventory-cycle-38.md` — inventaire i18n Pattern A sibling pair (lane transiente, tranche 3b #14623)

## 7. Mesure firsthand et conformité

### 7.1 Mesure

- **Source primaire** : `qinz1yang/differential-geometry` v0.1.3 — **pin `7a48598d` lu firsthand le 2026-10-22** pour les fichiers de licence et de provenance (`NOTICE` blob `264ca83de5638b06033196bbb8b2da4cca7aba1c`, 1 791 o ; `LICENSE` blob `261eeb9e9f8b2b4b0d119366dda99c6fd7d35c64`, 11 357 o ; `External/README.md`). Le dépôt complet n'est **pas** téléchargé (2,2 Go) ; le reste (sources Lean) sera mesuré au Pli 2 par téléchargement effectif, si le coordinateur déplie ce pli.
- **Sources tierces** (NOTICE) : **vérifiées firsthand le 2026-10-22** — six arbres vendorisés, tous **Apache-2.0**, avec provenance et SHA de blob dans le tableau 2.1 bis. Deux écarts d'attribution relevés (DeGiorgi et RiemannMapping absents du `NOTICE` racine) : à signaler en upstream ; ils ne bloquent pas la décision de licence (redistribution possible sous conditions), et aucune conclusion de conformité de l'amont n'est tirée.
- **Emplacement proposé** : argumentaire fondé sur la **convention i18n en place** (Pattern A `_lean` suffix, déjà adopté par 4 lakes existants).

### 7.2 Conformité

- Applicable ([verify-before-claiming.md](../../.claude/rules/verify-before-claiming.md)) : sources vérifiées firsthand = (1) l'upstream `qinz1yang/differential-geometry` au pin `7a48598d` — `NOTICE`, `LICENSE`, `External/README.md` et les fichiers de provenance des six répertoires vendorisés lus et cités par SHA de blob, (2) la convention i18n Pattern A `_lean` suffix vérifiée sur 4 lakes existants, (3) le périmètre Pli 1 **déclaré** dans la PR (sub-grains 3+4 seulement). Les **sources Lean** de l'amont ne sont pas téléchargées : elles ne sont pas mesurées par ce document.
- Applicable ([sota-not-workaround.md](../../.claude/rules/sota-not-workaround.md)) : po-2024 Lean toolchain INVOCABLE mais build lake -- volumetrie Mesure c.1422 = `RECOVERABLE-MACHINE` (Pli 2).
- Observation ([proactive-coordination.md](../../.claude/rules/proactive-coordination.md), urne umbrella) : narrow-cache tari, **créer un sous-grain** dans un EPIC libre (#18205 Pli 1 sources tierces + emplacement) est la voie de sortie structurelle.
- Applicable ([lane-claim-protocol.md](../../.claude/rules/lane-claim-protocol.md)) : aucun claim conflictuel sur #18205.
- Rappel ([CLAUDE.md](../../CLAUDE.md) §A) : lane ne merge pas, ripe-signal nominatif.
- Rappel ([CLAUDE.md](../../CLAUDE.md) §B.0) : pas de push muet.

Refs #18205, Pli 1 sub-grains 3+4, body 4849 chars édition 2026-09-28.

🤖 Generated with [Claude Code](https://claude.com/claude-code)