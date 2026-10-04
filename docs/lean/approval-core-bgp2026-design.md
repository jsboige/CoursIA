# Cadrage — Core d'approbation (Becker-Greger-Peters 2026)

**Statut :** document de design, précède la livraison `.lean` (Tranches 1-3 de #17988).
**Issue :** #17988.
**Lane :** myia-po-2024:CoursIA-2.

## 1. Contexte et motivation

L'issue #17988 demande de formaliser, dans le sous-projet Lake
`social_choice_lean_peters/`, la **preuve que le core d'approbation est non-vide**
pour toute élection de comité par approbation et tout profil de ballots.

Le résultat principal est dû à **Becker, Greger et Peters (2026)**, arXiv
`2609.11912`. Dominik Peters — auteur de `SocialChoiceLean` — est co-auteur
du papier, ce qui rend la cohérence interne particulièrement naturelle : le
résultat viendrait s'inscrire au-dessus de son propre dépôt upstream comme
extension au-dessus de `SocialChoice.*`.

L'option A du périmètre — un carnet Jupyter `07-Committees-Core.ipynb` (PR
`#16896`) — est déjà livrée. L'option B (cette PR) complète le volet
formel et ferme `#16848` une fois Tranche 3 livrée.

## 2. État amont mesuré (2026-09-26, revisité c.1486)

| Vérification | Résultat | Source |
|---|---|---|
| Dernier commit upstream `DominikPeters/SocialChoiceLean` | `94a4c650b6` (2026-07-21) | `gh api repos/DominikPeters/SocialChoiceLean/commits` |
| Présence d'une formalisation « approval core » en amont | absente | `grep -rli 'approval'` sur le dépôt local `_peters/` ne renvoie aucun fichier (limite `SocialChoice/Committees/Approval/` non versionné localement) |
| Type d'attache au dépôt CoursIA | **dossier versionné ordinaire** (PAS un submodule git) | `git ls-files MyIA.AI.Notebooks/GameTheory/social_choice_lean_peters/` ne renvoie que des fichiers plats ; `.gitmodules` ne contient pas ce chemin |
| Sous-projet Lake | `package «social_choice_peters»` ; `lean_lib PetersTour` avec globs `PetersTour, PetersTour_en` (i18n #4980) | `lakefile.lean` |

Le corps de l'issue #17988 dit « submodule épinglé `94a4c650` » — c'est un
raccourci : le submodule upstream est consommé via `require SocialChoiceLean
from git` dans le `lakefile.lean`, **pas** via `.gitmodules` du dépôt
principal. Conséquence pratique : la frontière de modification est le
dossier `_peters/` lui-même, pas une étape de bump de submodule.

## 3. Architecture cible (siblings i18n #4980)

Trois tranches, chacune livrée en PR séparée et mergeable indépendamment.

### Tranche 1 — Socle de définitions

Deux fichiers siblings, dans `social_choice_lean_peters/Committees/Approval/` :

- `Defs.lean` (FR) — namespace `ApprovalDefs`
- `Defs_en.lean` (EN) — namespace `ApprovalDefs_en`

Contenu (les définitions exactes seront affinées dans la PR de Tranche 1) :

```lean
structure ApprovalBallot (A : Type) [Fintype A] where
  approved : Finset A           -- sous-ensemble des candidats approuvés

structure ApprovalProfile (V A : Type) [Fintype V] [Fintype A] where
  ballots : V → ApprovalBallot A
  committeeSize : ℕ

def Committee (A : Type) [Fintype A] (k : ℕ) : Type :=
  { S : Finset A // S.card = k }

def Happiness {V A : Type} [instV : Fintype V] [instA : Fintype A]
    (P : ApprovalProfile V A) (S : Committee A P.committeeSize)
    (v : V) : ℕ :=
  (P.ballots v).approved ∩ S.val |>.card

structure PaymentFunction (V : Type) [Fintype V] where
  payments : V → ℚ
  zero_sum : (∑ v, payments v) = 0

def HarmonicEntropy {V A : Type} [instV : Fintype V] [instA : Fintype A]
    (P : ApprovalProfile V A) (S : Committee A P.committeeSize)
    (p : PaymentFunction V) : ℝ :=
  let weights := fun v : V => (1 : ℝ) / (1 + p.payments v)
  -- ∑_v weights v · log (1 + Happiness(P, S, v)) à formaliser avec Mathlib
  sorry  -- Tranche 1 marque la forme ; Tranche 3 la précise
```

`lake build` doit compiler les **deux** siblings en `lake build
ApprovalDefs ApprovalDefs_en`. Le glob dans `lakefile.lean` est mis à
jour :

```lean
lean_lib «PetersTour» where
  globs := #[`PetersTour, `PetersTour_en, `ApprovalDefs, `ApprovalDefs_en]
```

Drift FR/EN : zéro sur les définitions ; seuls les docstrings `/-- ... --/`
et commentaires `-- ...` diffèrent (convention i18n Pattern A, validé par
`scripts/lean/check_i18n_siblings.py` — 1/1 byte-identical sauf docstrings).

### Tranche 2 — Définition du core et lemmes d'identité

Un fichier `Core.lean` + `Core_en.lean`. La définition du core
**standard** en committee voting (cf. Peters, Equality of
opportunity, handbook 2024, et reprise dans le papier BGP 2026) ne
fait **pas** intervenir de paiements dans la condition de blocage :
la définition est :

> Un comité `S` est dans le **core** ssi il n'existe **aucune coalition
> non vide** `T ⊆ V` et aucun comité `S' ≠ S` de même taille tel que
> **chaque membre** de `T` préfère **strictement** `S'` à `S`.

Les paiements dans la **preuve** de BGP 2026 sont une composante de
**l'objectif** (`HarmonicEntropy`), pas de la définition du core.
L'algorithme de la preuve optimise l'objectif sur (comité, paiements) ;
tout optimum local est dans le core. C'est précisément ce que l'abstract
du papier (#2609.11912) formule :

> *« All local optima of this objective function lie in the core, which
> implies that a core committee can be found in polynomial time. »*

```lean
def InCore {V A : Type} [Fintype V] [Fintype A]
    (P : ApprovalProfile V A) (S : Committee A P.committeeSize) : Prop :=
  ∀ (T : Finset V), T.Nonempty →
    ¬ ∃ S' : Committee A P.committeeSize, S' ≠ S ∧
        ∀ v ∈ T, Happiness P S' v > Happiness P S v
```

Trois corrections par rapport au sketch initial (revue NanoClaw
c.1487) :
1. **`T.Nonempty`** ajouté — sans cette contrainte, le core serait
   `False` pour tout `S` (cohérence de la coalition vide = triviale).
2. **Pas de paiements dans la condition** — la structure
   `PaymentFunction` reste définie en Tranche 1 pour la **preuve**, pas
   pour la **définition** du core.
3. **Strict amélioration uniquement** — pas de clause « ou égal ET
   payé > 0 », qui sort du core standard.

Lemme d'identité :

```lean
lemma core_empty_iff_no_improvement (P : ApprovalProfile V A) :
    (∃ S, InCore P S) ↔
    ¬ ∃ (T : Finset V), T.Nonempty ∧
        ∃ S' : Committee A P.committeeSize, S' ≠ S ∧
        ∀ v ∈ T, Happiness P S' v > Happiness P S v
```

Le `strict_better` non-défini du sketch initial est remplacé par
`Happiness P S' v > Happiness P S v` directement — plus lisible, et la
preuve complète ne fait pas intervenir la notion de « strict mieux
ou payé » puisque le core n'utilise pas les paiements (réserve 2 et 3
NanoClaw c.1487 résolues).

### Tranche 3 — Énoncé BGP 2026 et ébauche de preuve constructive

Théorème principal :

```lean
theorem becker_greger_peters_2026 (P : ApprovalProfile V A) :
    ∃ S : Committee A P.committeeSize, InCore P S := by
  -- algorithme : la règle de vote BGP optimise HarmonicEntropy sur
  -- l'espace Comité × Paiement (les paiements sont dans l'OBJECTIF,
  -- pas dans la définition du core -- correction de la Tranche 2).
  -- Existence d'un optimum local garantie par Fintype sur l'espace
  -- Comité × Paiement, et l'abstract BGP garantit que tout optimum
  -- local est dans le core.
  sorry
```

Statut `sorry` à surveiller :
- **Si Mathlib 4 v4.32.0** fournit les outils nécessaires (Fintype.card,
  existence de max sur Finset, HarmonicNumber), la preuve est rédigée
  complètement et le `sorry` est retiré avant le merge.
- **Si une étape manque** (par exemple un lemme sur l'entropie harmonique),
  la sortie de `count_code_sorry.py --lake social_choice_peters` signale
  et le scénario INTRINSIC est documenté explicitement dans le body
  (cf. `anti-regression.md` règle HARD).

## 4. Conventions de la base Peters (à respecter)

- Le code suit le style des fichiers PetersTour.lean / PetersTour_en.lean
  (cf. entête `namespace PetersTour open SocialChoice`).
- Imports minimaux depuis `DominikPeters/SocialChoiceLean` : `Profile`,
  `Fintype`, structures de base uniquement. Pas de réimplémentation d'un
  type déjà présent en amont.
- Préfère `abbrev` aux `def` quand l'égalité définitionnelle compte.
- Pas de `Mathlib.Tactic` ad-hoc sans justification — rester sur
  `omega`, `decide`, `fin_cases`, `exact`, `apply`.

## 5. Critères d'admission d'une tranche

Pour qu'une tranche soit mergeable (au-delà de la [checklist PR Discipline
de coursIA-2](../../CLAUDE.md#b-reviews-pr--b0-bloquant-puis-5-points)) :

1. **Sortie SOTA sans workaround dégradé** : `lake build` réel sur la tête,
   pas une citation. (cf. `sota-not-workaround.md` Prong A.)
2. **Convention i18n vérifiée** : `scripts/lean/check_i18n_siblings.py
   Defs.lean Defs_en.lean` rend `1/1 byte-identical 0 drift 0 orphan`
   (cf. `code-style.md` §Lean i18n).
3. **Pas de `sorry` injustifié** : à Tranche 3, `count_code_sorry.py
   --lake social_choice_peters` ne montre aucun sorry hors baseline,
   OU chaque sorry est explicitement déclaré INTRINSIC avec justification
   (cf. `anti-regression.md`).
4. **Pas de cellule d'exercice non-stubbée** : ne s'applique pas ici (code
   de production, pas notebook), mais la règle `no NotImplementedError` est
   l'image-miroir : pas de demi-implémentation masquée.
5. **Diagnostic dérive C.4** : non applicable (pas un notebook). Mais le
   body de PR documente l'environnement d'exécution : Lean 4 v4.32.0,
   Mathlib `@ 520045ab14e26149ee970e2e617ca04b09bde5d6`, OS de test.

## 6. Risques identifiés et mitigations

| Risque | Mitigation |
|---|---|
| `lake build` échoue sur un lemme trivial, itérations multiples | limiter la portée Tranche 1 à des définitions sans lemmes intermédiaires non triviaux |
| Le submodule upstream `DominikPeters/SocialChoiceLean` avance entre les tranches et casse une signature | bumper re-vérifié à chaque cycle (`git ls-remote` + `lake build` à blanc) avant push |
| Souris `sorry` framework dans le Peters project (cf. incident fondateur 2026-04-24 Arrow.lean) | pas de `sorry` non documenté ; `count_code_sorry.py` à chaque merge |
| Coord cross-lane collision sur `lakefile.lean` (le fichier est partagé Peters ↔ Approval) | annoncer en dashboard `[INFO] lake-edit #17988` à chaque modif, vérifier `git log -- lakefile.lean` 48 h avant |
| Patch race sur `.github/workflows/lean-peters.yml` si ajout d'un workflow dédié | ne pas créer de workflow dédié tant que `.github/workflows/lean-peters.yml` n'existe pas ; sinon le créer dans la même PR que Tranche 1 |

## 7. Plan d'exécution

- **c.1486** (ce cycle) — PR de **ce document de design** (Tranche 0).
- **c.1487** — Tranche 1 livraison : les siblings `Defs.lean` + `Defs_en.lean`,
  bump `lakefile.lean`, vérif `lake build` (WSL po-2024 si dispo, sinon
  escalade ai-01 pour exécution machine-capable Mathlib).
- **c.1490+** — Tranche 2 (Core.lean + lemmes), après stabilisation
  Tranche 1 mergée.
- **c.1500+** — Tranche 3 (théorème BGP 2026), après Tranche 2.

## 7bis. Réponses aux réserves de la revue cid 5327843625

Cette section documente où les **trois réserves structurelles** de la revue
NanoClaw `clusterManager-Myia` cid `5327843625` (soumis 2026-09-26T22:48:52Z)
sont tranchées dans ce document.

**Réserve 1 — Coalition vide dans `InCore`.** Le sketch initial
omettait la contrainte `T.Nonempty` dans la quantification universelle,
ce qui rendait la définition trivialement `False`. La correction est
portée par le code Lean de la section §3 Tranche 2 :

```lean
def InCore {V A : Type} [Fintype V] [Fintype A]
    (P : ApprovalProfile V A) (S : Committee A P.committeeSize) : Prop :=
  ∀ (T : Finset V), T.Nonempty →    -- ← contrainte ajoutée
    ¬ ∃ S' : Committee A P.committeeSize, S' ≠ S ∧
        ∀ v ∈ T, Happiness P S' v > Happiness P S v
```

**Réserve 2 — Portée du `zero_sum`.** La `PaymentFunction` est conservée
en Tranche 1 uniquement comme **composante de l'objectif** (pour
`HarmonicEntropy`), pas comme **condition de blocage** du core. Le core
standard (définition Peters, handbook 2024, reprise BGP 2026) ne fait pas
intervenir de paiements. La structure `PaymentFunction` (avec son champ
`zero_sum : (∑ v, payments v) = 0`) est définie sur **V entier**, et
l'optimisation `HarmonicEntropy` prend en entrée un couple
`(comité, paiement)` dont le second est libre à somme nulle globale. La
définition du core reste la définition **sans paiements** — voir §3
Tranche 2.

**Réserve 3 — Paiements dans la définition du core vs dans la preuve.**
La définition du core retenue est la définition **standard** :

> *Un comité S est dans le core ssi il n'existe aucune coalition non vide
> T ⊆ V et aucun comité S' ≠ S de même taille tel que chaque membre de T
> préfère strictement S' à S.*

Les paiements sont une composante de **l'objectif de la preuve**
(`HarmonicEntropy`), pas de la définition. La preuve BGP 2026 montre que
tout optimum local de cet objectif (sur l'espace Comité × Paiement)
appartient au core. C'est précisément la formulation de l'abstract
arXiv `2609.11912` :

> *« All local optima of this objective function lie in the core, which
> implies that a core committee can be found in polynomial time. »*

La variante « strict mieux ou égal ET payé > 0 » du sketch initial a été
**élidée** — voir §3 Tranche 2.

**Statut des trois corrections :** appliquées dans la version courante
(`1f903a859f` et suivants) du document, avant la rédaction de toute
ligne de `Core.lean` en Tranche 2.

## 8. Liens

- Issue : https://github.com/jsboige/CoursIA/issues/17988
- Claim : cid `5850363535` (c.1485)
- Plan détaillé : commentaire cid `5850370980` sur l'issue
- PR #16896 — carnet option A livré (volet Jupyter)
- Issue #16848 — fermeture candidate après Tranche 3
- Convention i18n : [code-style.md §Lean i18n](../../.claude/rules/code-style.md#lean-i18n),
  [docs/lean/i18n-sibling-patterns.md](i18n-sibling-patterns.md)
- Anti-régression Lean : [anti-regression.md](../../.claude/rules/anti-regression.md)
- Petersen Tour existant : `social_choice_lean_peters/PetersTour.lean` + `_en.lean`
- Submodule upstream : `DominikPeters/SocialChoiceLean` rev `94a4c650b6`
