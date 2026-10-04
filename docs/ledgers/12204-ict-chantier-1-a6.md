# Chantier 1 — tranche A6 : statuation des opérations 11-13 (promotions TABLE) et de la file d'attente

**EPIC** : [#12204](https://github.com/jsboige/CoursIA/issues/12204) · **lane** `myia-po-2024:CoursIA` · **date de mesure** 2026-09-27 · **base** `1e19752a233`
**Tranches sœurs** : [A2](12204-ict-chantier-1-a2.md) (opération 1) · [A3](12204-ict-chantier-1-a3.md) (opérations 3, 9) · [A4](12204-ict-chantier-1-a4.md) (opération 4) · [audit froid](12204-ict-chantier-1-audit-froid.md) (les 14 opérations, trois axes)

## Ce que cette tranche fait, et ce qu'elle ne fait pas

L'audit froid laissait les opérations **11, 12, 13** « en construction », chacune avec sa seconde attestation **livrée mais non comptée** — la convention posée pour l'opération 7 (reprise telle quelle ici) : *une attestation ne compte qu'une fois son artefact mergé sur `main`*. Cette tranche vérifie **mécaniquement** que la condition est à présent remplie pour les trois, et opère les promotions que l'audit froid renvoyait « à statuer ». Elle ne re-décide ni les provenances (toutes `FIRSTHAND` déjà), ni les témoins (forms fixées par l'audit froid) — elle **active des promotions déjà conditionnées**.

Elle statue aussi sur la **file d'attente** : `point fixe` est **promue TABLE** sur second usage mesuré (correctif post-publication, cf. dernière section) ; deux homonymes sont écartés avec preuve.

## Promotions — les trois secondes attestations comptées

Constitution des trois : artefacts présents sur `origin/main` (base `1e19752a233`), état mécanique mesuré par lecture du JSON des carnets (comptes de cellules, `execution_count`, erreurs).

### Opération 11 — Descendre sous budget → TABLE

| Attestation | Témoin | État mesuré sur main |
|---|---|---|
| `mimo_lean/Descent.lean` (thèse op 11 explicite, sorry-free — A6/c.1208) | le budget atteint, ou le blocage | préexistante, comptée |
| `Search/Part1-Foundations/Search-11d-Descente-Sous-Budget.ipynb` (#16392) | décroissance stricte + barrière + non-blocage hors cible | **toutes les cellules code exécutées, 0 erreur** — mesuré ce cycle |

Deux substrats indépendants (Lean-formel + empirique-notebook). Promotion **TABLE**.

### Opération 12 — Composer des regards → TABLE

| Attestation | Témoin | État mesuré sur main |
|---|---|---|
| GT-21 #12259 (jeux 2×2, merged) | la paire de lectures incompatibles exhibée | préexistante, comptée |
| `Search/Part1-Foundations/Search-12a-Composer-Regards.ipynb` (#16426) | gridworld pondéré, play/coplay | **toutes les cellules code exécutées, 0 erreur** — mesuré ce cycle |

Deux attestations directes sur substrats indépendants, witness form connu (§5 du carnet). Promotion **TABLE**.

### Opération 13 — Traverser un mur → TABLE

| Attestation | Témoin | État mesuré sur main |
|---|---|---|
| GT-24 #12364 (MERGED) | chambre → mur → chambre voisine, six swaps générateurs | préexistante, comptée |
| `Search/Part1-Foundations/Search-13a-Traverser-Murs-Certifies.ipynb` (#16438) | chemin minimal certifié, épaisseur m_path / largeur m + test négatif morphisme/percement | **toutes les cellules code exécutées, 0 erreur** — mesuré ce cycle |

Promotion **TABLE**.

## File d'attente — statuation

### `point fixe` → TABLE (second usage mesuré)

L'entrée disait « Knaster-Tarski dans `argumentation_lean` — très solide, à promouvoir **dès le second usage** ». Le second usage est **mesuré ce cycle** :

| Attestation | Substrat | Témoin |
|---|---|---|
| `argumentation_lean` (`Extensions.lean:44` — opérateur caractéristique de Dung via Knaster-Tarski, propriétés dans `Grounded.lean`) | **Lean-formel** | la preuve (lfp atteint, théorème) |
| `Tweety/Tweety-07a-Extended-Frameworks-CSharp.ipynb` **cellule 5, exécutée** (`execution_count: 2`, sortie réelle) | **.NET 9 empirique** | `ADF.Grounded()` from-scratch : itération depuis tout-U jusqu'au fixed-point, **témoin imprimé** (interprétation grounded `a=t, c=t, b=f`, extension `{a, c}`) + re-dérivation « c=T → b=not c=F → a=not b=T → {a,c} » ; la ligne 647 documente le **least fixed-point de la fonction caractéristique** `F(S) = {x : validDefeats(x) ⊆ OUT(S)}` pour la section SetAF/EAF |

**Indépendance** : substrats distincts (lake Lean vs carnet .NET), opérateurs distincts (fonction caractéristique de Dung vs conditions d'acceptation 3-valuées ADF — le carnet présente lui-même l'ADF comme **généralisation** du cadre de Dung, §3.3 : ce n'est pas une re-dérivation du théorème du lake). Corroboré par le jumeau Python (`Tweety-07a-…-Python.ipynb`, dont la conclusion revendique la parité d'algorithme « Kleene 3-valued + grounded fixed-point » entre les deux jumeaux).

**Réserve documentée** : les deux attestations vivent dans la famille Tweety/ (lake vs carnets). Le §4 de l'EPIC fait de la table un objet vivant — rétrogradation possible si cette lecture de l'indépendance est contestée.

### Homonymes écartés, avec preuve

- `formal_logic_lean/FormalLogic/FolBridge.lean:124` — lu firsthand : **sémantique de Tarski** (théorème `models_iff_eval` : satisfaction d'une phrase par restriction de structure ↔ évaluation `Eval`, preuve `rw [models_iff]`), pas un point fixe de Knaster-Tarski d'un opérateur monotone.
- `GameTheory/GameTheory-22-Ensembles-Limites-Poincare-Bendixson.ipynb` — « point fixe » au **sens des systèmes dynamiques** (équilibre d'un flot, Poincaré-Bendixson), sans structure de treillis ni monotonie : autre opération.

### Autres entrées, inchangées

**`institutionnaliser`** (DAO seulement), **`inhiber`** (pas de banc), **`réviser une croyance`** (Tweety non branché) : aucune seconde attestation repérée ce cycle.

## État de la table après cette tranche

**TABLE** : opérations numérotées **1, 4, 7, 8, 9, 10, 11, 12, 13, 14** (10) + **`point fixe`** (promue ce cycle).
**FILE D'ATTENTE** : opérations **2, 5, 6** (attendent leurs secondes attestations — via la distillation Sandholm, chantier 5) + `institutionnaliser`, `inhiber`, `réviser une croyance`.

## Correctif post-publication (même cycle, ~20:10Z)

La première version de ce ledger écartait `point fixe` (« seul candidat repéré : FolBridge »). Ce verdict reposait sur le grep `knaster|tarski` seul ; le second grep (motifs `least fixed point` / `point_fixe`), lancé en tâche de fond **avant** la livraison, n'a atterri qu'après — révélant `Tweety-07a` (vraie seconde attestation, ci-dessus) et `GameTheory-22` (homonyme, ci-dessus). Leçon consignée : ne pas statuer sur un grep dont le jumeau est encore en vol. La promotion est le correctif ; le témoin et la réserve sont documentés ci-dessus pour arbitrage en review.
