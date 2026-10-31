# Origami géométrie différentielle — Pli 2, note de conception du carnet Poincaré

> **Statut** : Pli 2 de l'EPIC origami géométrie différentielle ([#18205](https://github.com/jsboige/CoursIA/issues/18205)), grain [#23499](https://github.com/jsboige/CoursIA/issues/23499). Cette note est la **première marche** du pli : elle est livrée **avant** le carnet, comme le demande le mainteneur ([#18205, commentaire du 2026-10-11](https://github.com/jsboige/CoursIA/issues/18205)).
>
> **Date du relevé** : 2026-10-30. **Source primaire** : dépôt amont `qinz1yang/differential-geometry`, release **`v0.1.3`**, commit `7a48598d35109aa99d1cc678e2724c213cdf4ff3` — le pin déjà déclaré par le lake d'enveloppe. **Licence amont** : Apache-2.0.
>
> **Ce que cette note n'est pas** : elle ne remplace ni le carnet, ni son exécution. Elle fixe ce que le carnet exposera, dans quel ordre, et ce qui reste aux plis suivants. Aucun chiffre de cette note n'est destiné à être recopié dans la prose du carnet : le carnet les **recalcule** (C.5).

## 1. Périmètre du Pli 2

Le Pli 2 livre trois objets, dans cet ordre :

| Marche | Objet | État |
|---|---|---|
| 1 | Cette note de conception | livrée ici |
| 2 | Fichier de visite FR/EN — témoin `#print axioms` des maillons de la chaîne | à suivre dans le même pli |
| 3 | Carnet « La conjecture de Poincaré en Lean » | à suivre dans le même pli |

Le carnet ne rejoue **pas** la preuve : la fermeture amont a coûté 22 909 jobs et 11 253 s en local ([#21916](https://github.com/jsboige/CoursIA/pull/21916)), et les jobs Lean de notre CI meurent vers 30 min ([#18100](https://github.com/jsboige/CoursIA/issues/18100)). Il lit **l'énoncé**, la **dépendance axiomatique** de cet énoncé, et le **graphe d'imports** que la chaîne mobilise.

## 2. Inventaire mesuré

### 2.1 Méthode

Relevé exécuté le 2026-10-30 sur le clone amont au pin `v0.1.3`, **hors du dépôt** (clone superficiel de lecture seule, aucune source amont recopiée dans CoursIA). Un module est identifié par son chemin de fichier ; le graphe est construit en lisant les lignes `import` de chaque `.lean`. La **clôture** d'un module est la fermeture transitive de ses imports **restreinte au paquet `DifferentialGeometry`** — les imports Mathlib sont exclus du décompte de modules et de lignes, comme dans la table du Pli 1.

### 2.2 Le paquet, et la clôture de l'énoncé

| Mesure | Valeur |
|---|---:|
| Modules du paquet `DifferentialGeometry` | **17 555** |
| Lignes du paquet | **4 704 458** |
| Modules dans la clôture de `Topology.ThreeManifold.Poincare` | **14 196** |
| Lignes dans cette clôture | **4 020 908** |
| Part du paquet mobilisée par l'énoncé | **80,9 %** des modules, **85,5 %** des lignes |

L'énoncé de la conjecture de Poincaré mobilise donc, à lui seul, les quatre cinquièmes du paquet.

### 2.3 Composition de la clôture

| Famille | Modules | Lignes |
|---|---:|---:|
| `DifferentialGeometry.Geometry` | 6 050 | 1 847 820 |
| `DifferentialGeometry.Topology` | 4 813 | 888 734 |
| `DifferentialGeometry.Analysis` | 2 809 | 1 087 999 |
| `DifferentialGeometry.External` | 360 | 156 329 |
| `DifferentialGeometry.Tensor` | 107 | 29 072 |
| `DifferentialGeometry.Bundle` | 57 | 10 954 |

### 2.4 Les maillons de la chaîne, mesurés séparément

La chaîne que le carnet suit est **Moise → flot de Ricci avec chirurgie → extinction en temps fini**. Chaque maillon a été mesuré comme une clôture indépendante :

| Maillon | Module de tête | Modules | Lignes | Théorèmes déclarés dans le module |
|---|---|---:|---:|---:|
| Découpage PL (Moise) | `Topology.PiecewiseLinear.Moise352Producer` | 3 507 | 720 934 | 6 |
| Flot de Ricci avec chirurgie | `Geometry.Flow.RicciFlow.Surgery.Skeleton.PoincareEndgame` | 11 348 | 3 521 645 | 15 |
| Extinction en temps fini | `Geometry.Flow.RicciFlow.DimensionThree.PositiveRicci.Extinction` | 2 399 | 1 282 938 | 14 |

### 2.7 La preuve de l'énoncé, lue dans son module

Le module de l'énoncé ne fait pas que déclarer : il **prouve**. Mesure au 2026-10-30 : le module fait 23 lignes, le bloc du théorème en fait 11 énoncé compris, et il en reste **5 après `:= by`**. C'est la meilleure pièce pédagogique du Pli 2, et elle dit que la chaîne n'est pas celle qu'un titre de section laisse croire.

```lean
theorem poincare_conjecture
    (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [T2Space M] [CompactSpace M] [SimplyConnectedSpace M] :
    Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := by
  obtain ⟨C, hC⟩ := PiecewiseLinear.exists_isManifold_three (M := M)
  let := C
  let : IsManifold (𝓡 3) ∞ M := hC
  obtain ⟨f⟩ := PDE.RicciFlow.Surgery.Topology.smoothPoincareConjecture_holds M
  exact ⟨f.toHomeomorph⟩
```

Trois temps, et ils ne sont pas symétriques :

1. **Moise est la porte d'entrée, pas une étape latérale.** La conjecture topologique porte des hypothèses purement topologiques ; le flot de Ricci, lui, exige une structure lisse (`IsManifold (𝓡 3) ∞ M`). `exists_isManifold_three` fabrique cette structure — c'est le seul endroit où l'on passe du monde topologique au monde lisse, et sans lui la machine Ricci n'a rien sur quoi mordre.
2. **Le moteur rend un difféomorphisme, pas un homéomorphisme.** `smoothPoincareConjecture_holds` conclut `Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ …)` — une équivalence **lisse**. C'est un résultat strictement plus fort que la conjecture topologique, et l'amont le prouve de bout en bout depuis la chirurgie.
3. **Le retour au topologique est `toHomeomorph`.** Toute la différence entre les deux énoncés tient dans cette coercition.

Deux conséquences pour la note, que je préfère écrire ici plutôt que de les laisser au carnet :

- l'ordre mathématique réel est **Moise (entrée) → flot de Ricci avec chirurgie → extinction contrôlée → difféomorphisme → homéomorphisme**. Mon premier jet disait « Moise → chirurgie → extinction » sans nommer le raccord ; c'est corrigé aux §3.1 et §4 ;
- `fineCutNeckSupplyStrong` n'est **pas** la tête de la chaîne : c'est un maillon interne, en amont de `uniformDebitSurgeryStepStrong`. Les têtes réelles sont `exists_poincare_controlled_extinction` puis `smoothPoincareConjecture_holds`.

### 2.5 Les trois petites fermetures du Pli 1 — contrôle de la méthode

Le Pli 1 avait mesuré trois clôtures ([`differential_lean/README.md`](../../MyIA.AI.Notebooks/SymbolicAI/Lean/differential_lean/README.md)). Le même calcul les reproduit **exactement**, ce qui vaut contrôle indépendant de la méthode employée ci-dessus :

| Fermeture | Modules (Pli 1) | Modules (relevé 2026-10-30) | Lignes (Pli 1) | Lignes (relevé) |
|---|---:|---:|---:|---:|
| `Tensor/Exterior/Cochain` | 33 | **33** | 13 432 | **13 432** |
| `Topology/Morse/ExtremumChart` | 47 | **47** | 23 522 | **23 522** |
| `Geometry/Comparison/BonnetMyers/Diameter` | 383 | **383** | 181 252 | **181 252** |

### 2.6 Réserve de mesure, écrite pour ne pas la masquer

Le body de [#23499](https://github.com/jsboige/CoursIA/issues/23499) cite **14 197 modules** pour la clôture de l'énoncé. Ce relevé en compte **14 196**. L'écart d'une unité vient très probablement du **module racine** (`DifferentialGeometry`) : l'énoncé ne l'importe pas, et l'inclure dans la clôture est une convention, pas une mesure. Le chiffre publié par le carnet sera celui **de ses propres sorties**, et la convention retenue y sera écrite.

## 3. Inventaire des modules et théorèmes exposés

Le critère de l'EPIC est qu'aucun théorème exposé ne reste sans carnet : chacun est exposé par **ce carnet-ci** ou par un carnet du **Pli 3**. « Exposé » veut dire : nommé, lu, et relié à la phrase mathématique qu'il porte.

### 3.1 Ce que ce carnet expose (Pli 2)

| Théorème (nom qualifié) | Ce qu'il dit, en une phrase | Marche |
|---|---|---|
| `DifferentialGeometry.Topology.poincare_conjecture` | Toute 3-variété fermée, séparée, simplement connexe est homéomorphe à la 3-sphère | 1 |
| `DifferentialGeometry.Topology.PiecewiseLinear.exists_isManifold_three` | Une structure lisse existe sur toute 3-variété topologique — la porte d'entrée de la machine de Ricci | 2 |
| `DifferentialGeometry.Topology.PiecewiseLinear.moise352` | Le résultat de Moise 352 sous-jacent, en forme de fournisseur | 2 |
| `DifferentialGeometry.Topology.PiecewiseLinear.plApproximation_three` | Approximation PL des applications, en dimension 3 | 2 |
| `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.fineCutNeckSupplyStrong` | L'approvisionnement en cols fins que la chirurgie doit couper | 3 |
| `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.uniformDebitSurgeryStepStrong` | Le débit uniforme d'une étape de chirurgie | 3 |
| `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction` | Toute 3-variété fermée orientée simplement connexe admet une extinction contrôlée | 3 |
| `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.smoothPoincareConjecture_holds` | La conjecture de Poincaré **lisse** : difféomorphisme vers la 3-sphère | 3 |
| `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.exists_hamilton_finite_time_flow_on_closed_open` | Le flot de Ricci en courbure de Ricci positive s'éteint en temps fini | 3 |

Les petits modules (`moise352Open`, `plApproximationManifold_three`, `plSmoothingCompact_three`) sont exposés par la même marche que `moise352`, sans énumération séparée : ils forment avec lui une seule phrase (« le découpage PL existe, et il lisse »).

Un fait de lecture qui mérite d'être dit ici : `smoothPoincareConjecture_holds` est **plus fort** que l'énoncé du carnet — il rend un difféomorphisme là où `poincare_conjecture` rend un homéomorphisme. Le carnet le signale, et la marche 3 explique que la coercition `toHomeomorph` est tout ce qui les sépare.

### 3.2 Ce qui reste au Pli 3

| Matière | Module d'entrée repéré | Pourquoi elle n'est pas ici |
|---|---|---|
| Lemme de Morse | `Topology/Morse/ExtremumChart` (clôture 47 / 23 522) | Déjà **témoin** au Pli 1 ; son carnet propre est une marche à part entière (source de la décomposition en anses) |
| Cohomologie de de Rham | `Tensor/Exterior/Cochain` (33 / 13 432) | Déjà témoin au Pli 1 ; mérite son carnet (complexe, tiré en arrière) |
| Bonnet–Myers | `Geometry/Comparison/BonnetMyers/Diameter` (383 / 181 252) | Déjà témoin au Pli 1 ; c'est l'invariant de compacité que la non-collapse utilise |
| Principe du maximum | `Analysis/Parabolic/MaximumPrinciple/…` (83 fichiers du thème) | Le carnet du maximum porte **une famille** entière, pas une marche du carnet Poincaré |
| Monotonie de Perelman | `historyReducedVolumeMonotone` et la famille `…Surgery` | C'est l'outil de non-extinction ; il demande le volume réduit, donc un carnet à lui seul |

### 3.3 Ce qui reste au Pli 4

Résonances avec nos lakes — aucune mesure dans cette note, par construction :

- `knot_lean` — la dimension 3 y est déjà travaillée par les nœuds et les mutants de Conway ;
- `grothendieck_lean` — la topologie des schémas y côtoie déjà des énoncés de dimension ;
- `conway_lean` — les objets discrets qui se comparent à une triangulation.

Ces résonances sont nommées, pas mesurées : les chiffrer ici serait de la prose non falsifiable.

## 4. Ordre des marches

Le carnet suit un ordre qui va de **ce qui se lit** à **ce qui se calcule** :

1. **La lecture de l'énoncé et de ses axiomes.** Chaque hypothèse (`ChartedSpace (EuclideanSpace ℝ (Fin 3))`, `T2Space`, `CompactSpace`, `SimplyConnectedSpace`) est lue comme une définition mathématique, puis confrontée au témoin `#print axioms` du Pli 1 : `[propext, Classical.choice, Quot.sound]`. La marche dit **ce que ce témoin garantit** (l'énoncé ne dépend d'aucun axiome prohibé) et **ce qu'il ne garantit pas** (il ne dit rien de la vérité mathématique de l'énoncé, ni de la taille de la preuve).
2. **Le graphe d'imports comme donnée.** Le carnet charge le graphe, le construit, et l'interroge : taille de la fermeture, modules pivots, plus courts chemins depuis l'énoncé vers les maillons. Le chiffre de référence du §2.2 y est **recalculé**, jamais recopié.
3. **La chaîne, dans le graphe et dans la preuve.** Le carnet part de la preuve lue au §2.7 et suit ses trois temps : Moise qui ouvre la porte lisse, le flot de Ricci avec chirurgie qui rend un difféomorphisme, `toHomeomorph` qui referme. Pour chaque maillon : quels modules le portent, par où l'énoncé l'atteint, et combien de modules chacun ajoute à la fermeture. Le fait que la preuve ne compte que cinq lignes de tactiques est en soi l'objet de la marche : la brièveté de l'énoncé et la taille de sa fermeture mesurent la même chose sous deux angles.

Trois exercices ferment le carnet, sans erreur volontaire (C.1) et mesurant chacun quelque chose de neuf :

- **Exercice 1 — la fermeture d'un autre énoncé.** Recalculer la clôture de Bonnet–Myers et la comparer à celle de Poincaré. La compétence mesurée : la fermeture est une **propriété de l'énoncé**, pas du fichier qui le déclare.
- **Exercice 2 — le pivot dépend de la cible.** Trouver le module de plus fort in-degree pour deux cibles différentes et constater qu'il change. La compétence : un « module central » n'existe pas dans l'absolu.
- **Exercice 3 — le chemin le plus court n'est pas la dépendance.** Entre l'énoncé et un maillon, comparer le plus court chemin d'imports à la chaîne **mathématique** annoncée. La compétence : un graphe d'imports porte la compilation, pas l'argument.

## 5. Numéro de carnet proposé

**`Lean-42`**, dans la série principale.

- Le plus grand numéro attribué à ce jour est **`Lean-41`** (`Lean-41-Capstone-MIMO-Python.ipynb`). La règle d'accrétion ajoute après le dernier, elle ne recycle pas.
- Les numéros absents de la série sont **18, 21, 32 et 35**. Ce ne sont **pas** des numéros libres : des migrations ont déplacé des carnets hors de la série (par exemple `Lean-31` → `ANALYSE-13`, [#22643](https://github.com/jsboige/CoursIA/pull/22643)). Réoccuper un numéro vacant brouillerait la table de correspondance de `docs/reference/rename-ledger.tsv`, qui est la mémoire de ces migrations.
- `Lean-42` est libre des deux côtés : aucun fichier ne le porte sur `main` (`git ls-tree` sur la série, 0 résultat pour `Lean-4[2-9]`), et aucune PR ne le réserve (relevé du 2026-10-30).

**Correction de méthode, écrite ici parce qu'elle informe le lecteur.** Un premier jet de cette note proposait `Lean-38` en affirmant que le plus grand numéro était `Lean-37`. Les deux affirmations étaient fausses : `Lean-38-Capstone-Geometry-Lean-Python.ipynb` existe, et la série va jusqu'à `Lean-41`. Le numéro avait été déduit d'un `ls` partiel et d'un souvenir, pas d'un inventaire. C'est exactement le mode d'erreur que la règle de mesure en continu vise : un numéro se lit dans un relevé complet de la série, jamais dans une liste tronquée.

`Lean-38` porte sur la **géométrie du triangle** (« l'escalier d'entrée : de la figure au noyau ») : le voisinage est thématique mais le sujet est distinct — 3-variétés, flot de Ricci et graphe d'imports d'un paquet de 17 555 modules, contre un triangle et quatre méthodes. `Lean-38` sert en revanche de **gabarit de structure** : même escalier, même place des exercices.

Le titre proposé suit la forme des carnets voisins : `Lean-42-Poincare-Conjecture-Lean.ipynb`.

## 6. Ce que le carnet devra prouver

Repris des critères d'acceptation de [#23499](https://github.com/jsboige/CoursIA/issues/23499), pour que la note et le carnet ne divergent pas :

1. le fichier de visite FR/EN est livré, `lake build` de la cible passe sur la machine témoin, journal cité ; `count_code_sorry.py --json` rend `distinct_code_sorry` inchangé ; `#print axioms` est relu **dans les deux siblings** ;
2. le carnet est exécuté de bout en bout : `execution_count` non nul et sorties réelles partout, aucune erreur (C.2), trois exercices sans erreur volontaire (C.1) ;
3. le graphe est **calculé** par le carnet, pas recopié, et les chiffres de sa prose viennent de ses sorties (C.5) ;
4. les références de la chaîne sont citées depuis des copies archivées dans `G:\Mon Drive\MyIA\IA\Bibliographie IA` (règle `bibliography-hygiene`).

## 7. Voir aussi

- [#18205](https://github.com/jsboige/CoursIA/issues/18205) — EPIC origami géométrie différentielle
- [#23499](https://github.com/jsboige/CoursIA/issues/23499) — grain Pli 2
- [`origami-reconnaissance.md`](origami-reconnaissance.md) — Pli 1, sources tierces et emplacement
- [`origami-pli1-mesures.md`](origami-pli1-mesures.md) — Pli 1, mesures de build
- [`differential_lean/README.md`](../../MyIA.AI.Notebooks/SymbolicAI/Lean/differential_lean/README.md) — le lake d'enveloppe et son témoin
