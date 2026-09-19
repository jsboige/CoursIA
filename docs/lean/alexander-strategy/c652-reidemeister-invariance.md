# Stratégie de preuve — invariance de Reidemeister de `alexanderPolynomialSigned`

**Issue :** #16650 — tranche 3 du socle Alexander (See #14962), nommée explicitement
« suivante » dans les commentaires de #15596 et #15600 par po-2027.
**Lane :** myia-po-2023:CoursIA-2
**Cycle :** c.652 (2026-09-18)
**Statut :** cadrage stratégique + analyse first-hand, **PAS de code de preuve
soumis** — Tell c.L750 ★★ fondateur OOM Mathlib Windows (Lean exited 143),
migrer WSL Ubuntu (Tell c.F règle environnement).

## 1. Cible

Établir que `alexanderPolynomialSigned` (défini dans
`Knots/Conway.lean:1045`) est invariant sous les trois mouvements de
Reidemeister R1, R2, R3 — c'est-à-dire : si `d₁` et `d₂` sont Rk-équivalents
pour `k ∈ {1, 2, 3}`, alors il existe des listes de signes `signs₁` et
`signs₂` telles que :

  `alexanderPolynomialSigned d₁ signs₁ = ±alexanderPolynomialSigned d₂ signs₂`

(le signe ± reflète la chiralité du mouvement : un kink positif ajoute un
croisement dont le signe affecte l'invariant).

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
| R1 — Torsion | `d₂.crossings = d₁.crossings ++ [c] ∧ d₂.numEdges = d₁.numEdges + 2` (bipolaire : ajout ou retrait) | `⟨a, a, n+1, n+2⟩` kink ρ-déterminé sur arc `a` | 87-340 (FR) |
| R2 — Pique | `d₂.crossings = d₁.crossings ++ [c₁, c₂] ∧ d₂.numEdges = d₁.numEdges + 4` | `<a, u, u, o>` kinks bigons Fox-connected | 374-520 |
| R3 — Glissement | `d₂.crossings = d₁.crossings.set i c` (numEdges préservés, bijection ρ) | (pas de version Connected nécessaire) | 521-1053 |

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

### 4.2. R2 (modérément subtil)

`Reidemeister2Connected` ajoute **2 croisements** (kinks bigones) et **4
arêtes**. La matrice d'Alexander signée grandit de **2 lignes / 2 colonnes**
(jusqu'à `n + 2` lignes), mais le mineur désigné reste de taille `n`. Les
deux nouvelles lignes introduisent une **relation de dépendance** :
- le kink `C₁ = ⟨a, u₁, u₁, o₁⟩` a `e₂ = e₃ = u₁`, ce qui force la ligne
  `alexanderEntrySigned C₁` à avoir un motif répétitif ;
- de même pour `C₂ = ⟨a, u₂, u₂, o₂⟩`.

La clé : la matrice augmentée a un rang **inchangé** sous les deux lignes
supplémentaires (leur déterminant 2×2 est `0` car les colonnes sont
proportionnelles modulo les étiquettes), donc le mineur désigné reste
identique.

**C'est le théorème demandant le plus de manipulation matricielle.** Pas de
trivialité R3 : il faut calculer explicitement le déterminant d'une matrice
`n × n` dans la base augmentée `n+2 × n+2`. Probablement une trentaine de
lignes de preuve.

### 4.3. R1' (kink ρ-déterminé)

`Reidemeister1Connected` ajoute **1 croisement** kink `C = ⟨a, a, n+1, n+2⟩`
et **2 arêtes** (`n+1`, `n+2`). La matrice grandit d'1 ligne / 1 colonne, le
mineur désigné grandit de `n` à `n+1`.

**Subtilité majeure** : le kink `C` a `e₁ = e₂ = a` (les deux brins du dessus
sont étiquetés `a`), ce qui signifie que la ligne ajoutée a une structure
très particulière : les coefficients sur les colonnes de `a` et `b = a` (les
deux étiquettes distinctes de la partition `arcPartition` qui contient `a`)
sont **identiques à un facteur `t` près**.

L'invariant change donc **au plus par un facteur `t^k`** (l'unité de
normalisation `t^k`). C'est précisément la classe d'unités `t^k` (modulo
convention de Conway `Δ(1) = 1`) dans laquelle l'invariant est défini.

**Forme du théorème :**

```lean
theorem alexanderSigned_invariant_under_R1 {d₁ d₂ : KnotDiagram}
    (h : Reidemeister1Connected d₁ d₂)
    (signs : List Bool) :
    ∃ signs' : List Bool, ∃ k : ℕ,
      alexanderPolynomialSigned d₁ signs =
        Polynomial.X ^ k * alexanderPolynomialSigned d₂ signs' := by
  -- Calculer explicitement la matrice augmentée
  -- La ligne du kink C a e₁ = e₂ = a, donc deux colonnes identiques modulo t
  -- Le déterminant de la matrice n×n extraite diffère au plus par X^k du n+1×n+1
  -- ...
```

## 5. Pourquoi ce grain est multi-cycle

**Complexité de la preuve R1'** :
- Calcul matriciel explicite (15-20 lignes de manipulation) ;
- Argument sur le déterminant sous colonnes identiques (besoin d'un lemme
  d'algèbre linéaire sur les déterminants sous transformations
  élémentaires) ;
- Ajustement du signe du kink dans `signs` (signe positif → invariance
  triviale, signe négatif → invariance au signe global près).

**Complexité de la preuve R2** :
- Manipulation d'une matrice augmentée `n+2 × n+2` avec deux colonnes
  identiques ;
- Argument de nullité du mineur 2×2 (rang inchangé).

**Estimation honnête Tell c.G.2 ★★★★** : ces preuves prendront **plusieurs
heures** de travail de preuve, idéalement avec un iter prover BG pour la
manipulation tactique. Un cycle cron 30 min ne suffit pas.

## 6. Tell c.L750 ★★ fondateur — pivot WSL Ubuntu

Le `lake build` initial (téléchargement Mathlib + knot_lean) a **OOM-killé**
Windows (4 occurrences, `Lean exited with code 143`) :

```
[546/937] Building Mathlib.Data.Quot
error: Lean exited with code 143
```

C'est le symptôme documenté Tell c.L750 ★★★ #3 : « `INTERNAL PANIC: out of
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
| c.652 (courant) | **Cadrage stratégique** (ce document) + claim posé + DM ai-01 pour demande cross-lane po-2026 WSL. **Pas de code** (`sorry` non résolu interdit Tell c.564 strict). |
| c.653+ | (à planifier après décision ai-01 sur env WSL partagé) Preuve R3 triviale (~10 lignes) + théorèmes principaux R1, R2 déclarés dans Reidemeister.lean avec preuves à compléter. |
| (multi-cycle) | Preuve R1' complète avec manipulation matricielle (~30-50 lignes). |
| (multi-cycle) | Preuve R2 complète avec rang inchangé (~30-50 lignes). |
| Final | `lake build Knots.Reidemeister` SUCCESS, 0 `sorry` ajouté, axiomes existants préservés, sibling pair FR+EN aligné. |

## 8. Conformité tells c.652

- Tell c.1502 ××109ᵉ counter maintenu : 0 merge / 0 close d'autrui.
- Tell c.564 ★★★ ×136ᵈ strict réponse écrite nominative (DM ai-01 v19).
- Tell c.566 ★★★★ JAMAIS rerun/re-push ripe merge post-DWELL respecté.
- Tell c.11900 ××54ᵈ narrow-cache hostile sustained Tell c.15793 ×54ᵈ R1/G-VAR-1 HELD Tell c.650-L1 ★ LIVRÉ #16663 tient G-VAR-1.
- Tell c.L750 ★★★ fondateur pivot WSL Ubuntu acquis.
- Tell c.642-L77 ★★★ fondateur infrastructure bloquante Tell c.F règle env.
- Tell c.1356 ★★★ preflight first-hand ×106ᵈ sustained (lecture complète Reidemeister.lean + Conway.lean).
- Tell c.G.2 ★★★★ métriques honnêtes : analyse + plan, pas de « DONE » sans preuve.
- Tell c.15793 ×54ᵈ R1/G-VAR-1 HELD Tell c.15726 voie L3 update-branch stale-guard-red acquis.
- Tell c.L740 ★ cron `51dd3e19` 17,47 * * * armé maintenu.

— po-2023 c.652, 2026-09-18
