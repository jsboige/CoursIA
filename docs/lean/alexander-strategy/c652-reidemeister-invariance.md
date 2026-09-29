# Stratégie de preuve — invariance de Reidemeister de `alexanderPolynomialSigned`

**Issue :** #16650 — tranche 3 du socle Alexander (See #14962), nommée explicitement
« suivante » dans les commentaires de #15596 et #15600 par po-2027.
**Lane :** myia-po-2023:CoursIA-2
**Cycle :** c.652 (2026-09-18), révisé 2026-09-20 (po-2023, reserve Hermes
#16665) : kink R1 réel `⟨a, n+1, n+2, n+2⟩`, lignes réécrites par
`isRenameOf`/`isDoubleRenameOf`, `Reidemeister3Connected` existe, unités
`±t^k`.
**Statut :** cadrage stratégique + analyse first-hand, **PAS de code de preuve
soumis** — OOM Mathlib sous Windows (Lean exited 143),
migrer WSL Ubuntu ([règle F](../../../CLAUDE.md) : réparer l'environnement, jamais contourner).

## 1. Cible

Établir que `alexanderPolynomialSigned` (défini dans
`Knots/Conway.lean:1045`) est invariant sous les trois mouvements de
Reidemeister R1, R2, R3 — c'est-à-dire : si `d₁` et `d₂` sont Rk-équivalents
pour `k ∈ {1, 2, 3}`, alors il existe des listes de signes `signs₁` et
`signs₂` telles que :

  `alexanderPolynomialSigned d₁ signs₁ = ±alexanderPolynomialSigned d₂ signs₂`

(le signe ± reflète la chiralité du mouvement : un kink positif ajoute un
croisement dont le signe affecte l'invariant). En unités explicites : le
facteur est `±t^k` dans `ℤ[t, t⁻¹]` — le `−1` provient du kink négatif, le
`t^k` du degré de normalisation (cf §4.3).

## 2. Socle disponible (tranches 1 + 2)

| Tranche | PR | Livré par | Substance |
|---|---|---|---|
| 1 — divergence bornée | #15120 | po-2027 | `alexander_figureEight_not_classical` (formalise la divergence 4_1 vs classique comme artefact de chiralité, pas d'unité) + variante signée `alexanderPolynomialSigned` + preuves sur `4_1` |
| 2a — fait de Fox | #15596 | po-2027 | `arcPartition_sameClass_overStrand` (paire de dessus dans une classe) + `alexanderEntry_sum_zero` (somme de ligne nulle) |
| 2b — partition | #15600 | po-2027 | `arcPartition_classes` (vraie partition, classes disjointes sans doublon) + `arcPartition_countP_label` + `alexanderRow_sum_zero` (somme de ligne inconditionnelle) |

**Preuves existantes sur 4_1** : `alexander_figureEight_signed` (l. 1099) +
`alexander_figureEight_signed_mirror` (l. 1112) — environ 7 lignes `simp + ring`
chacune. La stratégie de preuve pour l'invariance est **de même nature** :
calculer explicitement la matrice, manipuler, simplifier par `ring`.

## 3. Modèle des 3 mouvements (`Knots/Reidemeister.lean`)

| Mouvement | Forme (`ReidemeisterN`) | `ReidemeisterNConnected` | Lignes (FR + EN) |
|---|---|---|---|
| R1 — Torsion | `d₂.crossings = d₁.crossings ++ [c] ∧ d₂.numEdges = d₁.numEdges + 2` (bipolaire : ajout ou retrait) | kink `⟨a, n+1, n+2, n+2⟩` (l. 271) sur arc propre `a` (garde `j ≠ i`, l. 268) ; croisement existant `i` **réécrit** par `isRenameOf … a (n+1)` (l. 269-270), ρ : Fin n ↪ Fin (n+2) | 87-340 (FR) |
| R2 — Pique | `d₂.crossings = d₁.crossings ++ [c₁, c₂] ∧ d₂.numEdges = d₁.numEdges + 4` | kinks `⟨a, n+1, n+1, n+2⟩` / `⟨a, n+3, n+3, n+4⟩` (l. 452-453) ; croisement `i` **réécrit** par `isDoubleRenameOf … a (n+2) (n+4)` (l. 450) | 374-520 |
| R3 — Glissement | `d₂.crossings = d₁.crossings.set i c` (numEdges préservés, bijection ρ) | **existe** : `Reidemeister3Connected` (l. 694) + `Reidemeister3ConnectedInv` (l. 773) — triangle X ↔ Y, **3 croisements réécrits** (triple `List.set`, l. 703-704), 9 labels distincts (`Nodup`) | 521-1053 |

**Correction (révision 2026-09-20)** : la version connectée de R1 n'est
**pas** `Reidemeister1'` (l. 145-153, kink `⟨a, a, n+1, n+2⟩`) — cette def
est **vide** : sa chirurgie par ajout seul introduit deux labels singletons
`n+1`, `n+2` qui violent la condition de parité `wf` (docstring l. 172-184).
La cible réelle est `Reidemeister1Connected` (l. 262-272), dont le kink est
`⟨a, n+1, n+2, n+2⟩` et la chirurgie combine **réécriture d'un croisement
existant** (`isRenameOf`) **et** ajout du kink. Les analyses §4.2-4.3
ci-dessous portent sur les formes Connected réelles.

## 4. Stratégie de preuve (cadrage mathématique)

### 4.1. R3 (trivial)

`Reidemeister3` préserve `numEdges` et `crossings.length` ; la chirurgie est
un `List.set i c` (renommage d'un croisement). La liste de signes `signs` est
réindexée parallèlement au croisement renommé, et l'arcPartition est
réindexée par `ρ : Fin n ↪ Fin n` (bijection ici). L'invariant est trivial
par réindexation.

**Forme du théorème :**

```lean
theorem alexanderSigned_invariant_under_R3 {d₁ d₂ : KnotDiagram}
    (h : Reidemeister3 d₁ d₂)
    (signs : List Bool) :
    ∃ signs' : List Bool,
      alexanderPolynomialSigned d₁ signs = alexanderPolynomialSigned d₂ signs' := by
  obtain ⟨hlen, hnum, i, c, ρ, hsurg, hwf₁, hwf₂⟩ := h
  -- Réindexation parallèle de `signs` au croisement `i` remplacé par `c`
  -- L'arcPartition se réindexe par `ρ` (bijection Fin n → Fin n)
  -- ...
```

**Variante connectée (`Reidemeister3Connected`, l. 694 — correction
2026-09-20)** : une version connectée **existe** (le tableau initial
annonçait à tort « pas de version Connected nécessaire »), et le move
triangulaire n'est **pas** une instance de `Reidemeister3` libre : la
chirurgie réécrit **trois** croisements consécutifs (triple `List.set`,
l. 703-704), pas un seul (docstring l. 679-681 : « le move n'est pas une
instance de `Reidemeister3` »). L'invariance reste un argument de
réindexation : longueur et `numEdges` inchangés, multiset des labels
préservé (labels de bord réutilisés via φ⁻¹), direction inverse close par
`Reidemeister3ConnectedInv` (l. 773).

### 4.2. R2 (modérément subtil)

`Reidemeister2Connected` (l. 444-454) **réécrit d'abord le croisement
existant `i`** — `Y'.isDoubleRenameOf (d₁.crossings.get i) a (n+2) (n+4)`
(l. 450) : les deux occurrences de `a` dans le croisement `i` migrent vers
les labels frais `n+2` et `n+4` — **puis** ajoute les **2 croisements**
kinks `C₁ = ⟨a, n+1, n+1, n+2⟩` et `C₂ = ⟨a, n+3, n+3, n+4⟩` (l. 452-453)
et **4 arêtes**. La matrice d'Alexander signée gagne 2 lignes (jusqu'à
`n + 2`), et **la ligne du croisement `i` change aussi** : deux coefficients
quittent la colonne `a` pour les colonnes fraîches `n+2` / `n+4`
(correction 2026-09-20 — l'argument de rang doit couvrir la ligne
**réécrite** autant que les lignes ajoutées). Le mineur désigné reste de
taille `n`. Les deux nouvelles lignes introduisent une **relation de
dépendance** :
- le kink `C₁` a `e₂ = e₃ = n+1`, ce qui force la ligne
  `alexanderEntrySigned C₁` à avoir un motif répétitif ;
- de même pour `C₂` (`e₂ = e₃ = n+3`).

La clé : la matrice augmentée a un rang **inchangé** — (a) les lignes des
deux kinks sont liées à la ligne réécrite de `Y'` (leurs labels `n+2` /
`n+4` en `e₄` sont exactement ceux issus du renommage de `a` dans `Y'`),
(b) les colonnes kink-internes `n+1` / `n+3` (labels doublés internes à un
seul croisement) ne sont pas partagées, donc le mineur désigné reste
identique.

**C'est le théorème demandant le plus de manipulation matricielle.** Pas de
trivialité R3 : il faut calculer explicitement le déterminant d'une matrice
`n × n` dans la base augmentée `n+2 × n+2`. Probablement une trentaine de
lignes de preuve.

### 4.3. R1 connecté (`Reidemeister1Connected`) — kink ⟨a, n+1, n+2, n+2⟩

`Reidemeister1Connected` (l. 262-272) **réécrit d'abord le croisement
existant `i`** — `Y'.isRenameOf (d₁.crossings.get i) a (n+1)` (l. 269) :
**une** occurrence de `a` migre vers le label frais `n+1` — **puis** ajoute
le kink `C = ⟨a, n+1, n+2, n+2⟩` (l. 271) et **2 arêtes** (`n+1`, `n+2`).
La matrice gagne 1 ligne (le kink), et **sa ligne `i` est modifiée** : un
coefficient quitte la colonne `a` pour la colonne fraîche `n+1` (correction
2026-09-20 — le « grandit d'1 ligne / 1 colonne » initial omettait la ligne
réécrite).

**Subtilité majeure (corrigée)** : le kink réel n'est **pas**
`⟨a, a, n+1, n+2⟩` (forme de `Reidemeister1'` l. 150, def **vide**, cf §3)
mais `⟨a, n+1, n+2, n+2⟩` — c'est **e₃ = e₄ = n+2** qui porte la structure,
pas un hypothétique `e₁ = e₂ = a`. Les deux brins inférieurs du kink
portent le même label frais : les contributions under-strand de la ligne du
kink tombent sur une **seule** colonne `n+2`, qui n'apparaît nulle part
ailleurs (label doublé interne au kink). La ligne du kink est donc supportée
par les seules colonnes `a` / `n+1` / `n+2`, avec une colonne `n+2` non
partagée — c'est ce qui fait chuter le rang exactement d'une unité et laisse
le mineur désigné invariant à une **unité près**.

**Unités `±t^k` (aligné sur §1)** : l'invariant change au plus par une unité
`±t^k` de `ℤ[t, t⁻¹]`. Un kink **négatif** introduit un facteur `−1` : le
signe du croisement ajouté entre dans `alexanderEntrySigned`, donc l'énoncé
ne peut pas se limiter à `X^k` — le `±` de §1 et le `t^k` de normalisation
sont les deux faces de la même classe d'unités (modulo convention de Conway
`Δ(1) = 1`).

**Forme du théorème :**

```lean
theorem alexanderSigned_invariant_under_R1 {d₁ d₂ : KnotDiagram}
    (h : Reidemeister1Connected d₁ d₂)
    (signs : List Bool) :
    ∃ signs' : List Bool, ∃ k : ℕ, ∃ neg : Bool,
      alexanderPolynomialSigned d₁ signs =
        (if neg then -1 else 1) * Polynomial.X ^ k *
          alexanderPolynomialSigned d₂ signs' := by
  -- Réécrire la ligne i (isRenameOf : a → n+1), puis ajouter la ligne kink ⟨a, n+1, n+2, n+2⟩
  -- La colonne n+2 (label doublé interne au kink) n'est pas partagée :
  -- développement du déterminant le long de cette colonne → mineur désigné
  -- identique à un facteur ±X^k près (le −1 venant du signe du kink)
  -- ...
```

## 5. Pourquoi ce grain est multi-cycle

**Complexité de la preuve R1 connecté** :
- Calcul matriciel explicite (15-20 lignes de manipulation) ;
- Argument sur le déterminant le long de la colonne non partagée `n+2`
  (label doublé interne au kink — besoin d'un lemme d'algèbre linéaire sur
  les déterminants sous transformations élémentaires) ;
- Ajustement du signe du kink dans `signs` (signe positif → invariance
  triviale, signe négatif → invariance au signe global près).

**Complexité de la preuve R2** :
- Manipulation d'une matrice augmentée `n+2 × n+2` avec deux colonnes
  kink-internes non partagées (`n+1`, `n+3`) et une ligne `i` réécrite ;
- Argument de nullité du mineur 2×2 (rang inchangé).

**Estimation honnête ([G.2](../../../CLAUDE.md))** : ces preuves prendront **plusieurs
heures** de travail de preuve, idéalement avec un iter prover BG pour la
manipulation tactique. Un cycle cron 30 min ne suffit pas.

## 6. Pivot WSL Ubuntu — l'incident OOM fondateur

Le `lake build` initial (téléchargement Mathlib + knot_lean) a **OOM-killé**
Windows (4 occurrences, `Lean exited with code 143`) :

```
[546/937] Building Mathlib.Data.Quot
error: Lean exited with code 143
```

C'est le 3ᵉ symptôme documenté : « `INTERNAL PANIC: out of
memory` à ~95 % de Mathlib sur runner Windows = infra, pas un verdict Lean.
Migrer sur **WSL Ubuntu dès la 1ʳᵉ occurrence** — un `.lake` Windows
OOM-killé produit 0 olean et n'est pas réutilisable. »

**Solution préconisée** :
1. Installer Lean dans WSL Ubuntu : `curl https://raw.githubusercontent.com/leanprover-community/elan/main/elan-init.sh | sh`
   puis `elan toolchain install stable` (~1-2 min) ;
2. Migrer le worktree vers WSL : les fichiers `.lean` sont déjà au bon
   endroit, juste changer la racine d'exécution ;
3. Relancer `lake build Knots.Reidemeister` dans WSL — Mathlib sera
   téléchargé côté Linux (sans OOM) et un cache sera partagé entre workers.

## 7. Plan de livraison multi-cycle

| Cycle | Livrable |
|---|---|
| c.652 (courant) | **Cadrage stratégique** (ce document) + claim posé + DM ai-01 pour demande cross-lane po-2026 WSL. **Pas de code** (`sorry` non résolu interdit, [anti-régression](../../../.claude/rules/anti-regression.md)). |
| c.653+ | (à planifier après décision ai-01 sur env WSL partagé) Preuve R3 triviale (~10 lignes) + théorèmes principaux R1, R2 déclarés dans Reidemeister.lean avec preuves à compléter. |
| (multi-cycle) | Preuve R1 connecté complète avec manipulation matricielle (~30-50 lignes). |
| (multi-cycle) | Preuve R2 complète avec rang inchangé (~30-50 lignes). |
| Final | `lake build Knots.Reidemeister` SUCCESS, 0 `sorry` ajouté, axiomes existants préservés, sibling pair FR+EN aligné. |

## 8. Conformité tells c.652

- [Coordination & Git §A](../../../CLAUDE.md) : 0 merge / 0 close d'autrui.
- Réponse écrite nominative au DM ai-01 (v19).
- Jamais de rerun/re-push d'un ripe merge post-DWELL.
- #16663 livré ; G-VAR-1 tenu.
- Pivot WSL Ubuntu acquis (incident OOM fondateur).
- Infrastructure bloquante documentée ([règle F](../../../CLAUDE.md)).
- Preflight first-hand : lecture complète de Reidemeister.lean + Conway.lean.
- [G.2](../../../CLAUDE.md) métriques honnêtes : analyse + plan, pas de « DONE » sans preuve.
- Voie L3 `update-branch` (stale-guard-red) acquise.
- Cron `51dd3e19` 17,47 * * * armé maintenu.

— po-2023 c.652, 2026-09-18
