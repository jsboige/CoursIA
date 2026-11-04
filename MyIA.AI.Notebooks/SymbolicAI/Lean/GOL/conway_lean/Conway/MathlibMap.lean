/-
Copyright (c) 2026 CoursIA. Tous droits réservés.
Publié sous licence Apache 2.0 telle que décrite dans le fichier LICENSE.

## MathlibMap — les mathématiques de Conway dans Mathlib (snapshot pinné)

Ce module satellite cartographie ce que **Mathlib fournit réellement** dans
la version pinnée (`54f98fd6`, 2026-05-15) en lien avec les contributions de
John Horton Conway. Il sert de compagnon à nos propres réimplémentations
dans `Conway/` (Life, Angel, Doomsday, Fractran, LookAndSay, Nim, FWT).

### Note historique — suppression CGT (Mathlib PR #35550, 2026-02-20)

Mathlib contenait **auparavant** des modules étendus de théorie combinatoire
des jeux sous `Mathlib.SetTheory` :

- `Surreal.Basic` / `Surreal.Dyadic` / `Surreal.Multiplication`
- `PGame.Basic` / `PGame.Order` / `PGame.Algebra`
- `Game.Basic` / `Game.Birthday` / `Game.State` / `Game.Short`
- `Game.Impartial` / `Game.Nim` / `Game.Domineering` / `Game.Ordinal`
- `Nimber.Basic` / `Nimber.Field`

Ceux-ci ont été supprimés par la PR #35550 ("remove deprecated material from CGT"),
qui notait que les modules étaient dépréciés depuis 6 mois. À notre version
pinnée (mai 2026), aucun ne survit.

Cela signifie que, pour les domaines les plus étroitement associés au *On Numbers
and Games* de Conway (nombres surréels, jeux partisans, Sprague-Grundy), **notre
projet fournit l'implémentation de référence** (voir `Conway.Nim`,
`Conway.Life`, etc.) plutôt que Mathlib.

Ce module est donc un **document vivant** : il documente les éléments Mathlib
existants pertinents pour les mathématiques de Conway, sans tenter de les
réimplémenter. Pour les domaines oê Mathlib a été purgé, nos propres
implémentations dans `Conway/` prennent le relais.

Voir : `Conway.Nim`, `Conway.Life`, `Conway.LookAndSay`, `Conway.Doomsday`.

EPIC #4980 (i18n Lean convention, ratifiée user 2026-07-04, Option A).
Voir #2159 (EPIC Grothendieck au-delà Phase 1).
-/

import Mathlib.SetTheory.Ordinal.CantorNormalForm
import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.Order.GameAdd

namespace Conway

namespace MathlibMap

/-! ## 1. Arithmétique ordinale — le fondement de ONAG

Les nombres surréels de Conway sont construits sur le concept d'“anniversaires”
(birthdays), indexés par des ordinaux. Le type `Ordinal` et son arithmétique
(addition, multiplication, exponentiation) forment le substrat de la
construction des anniversaires. La forme normale de Cantor (`Ordinal.CNF`)
donne la décomposition en base Ω qui sous-tend la structure combinatoire des
jeux. -/

-- Exponentiation ordinale via l'instance Pow (notation a ^ b).
-- L'addition et la multiplication des nombres surréels de Conway étendent
-- l'arithmétique ordinale au corps surréel complet.
#check @Ordinal.instPow

-- Induction par la forme normale de Cantor : tout ordinal α peut s'écrire
-- de manière unique α = Ω^{β₁} · c_1 + Ω^{β₂} · c_2 + ... + Ω^{β₺} · c_k
-- oê β₁ > β₂ > ... > β₺. Conway a exploité cette
-- structure dans ONAG.
#check @Ordinal.CNF.rec

-- Logarithme ordinal : le plus grand exposant dans l'expansion en base Ω.
-- C'est la première composante de la forme normale de Cantor.
#check @Ordinal.log

/-! ## 2. Groupes de Coxeter — symétrie et réflexion

Conway a apporté des contributions significatives à l'étude des groupes
de Coxeter, notamment dans leur lien avec les empilements de sphères (le
réseau de Leech) et la classification des groupes simples finis. Mathlib
fournit une formalisation complète des systèmes de Coxeter. -/

-- Une matrice de Coxeter : symétrique, avec 1 sur la diagonale et ≠ 0 ailleurs.
-- Conway les a étudiées en lien avec les groupes de réflexion et
-- les symétries du réseau de Leech.
#check @CoxeterMatrix

-- Le groupe de Coxeter associé à une matrice M :
-- présenté par des générateurs s_i avec relations (s_i s_j)^{M_{ij}} = 1.
#check @CoxeterMatrix.Group

-- Un système de Coxeter : un groupe W avec un isomorphisme vers un groupe de Coxeter.
#check @CoxeterSystem

-- La réflexion simple s_i d'un système de Coxeter. Elles génèrent W.
#check @CoxeterSystem.simple

-- Propriété universelle : toute fonction satisfaisant les relations de Coxeter
-- s'étend de manière unique en un morphisme de groupes depuis W.
#check @CoxeterSystem.lift

/-! ## 3. Addition de jeux — le résidu de théorie combinatoire des jeux

La relation `Prod.GameAdd` modélise la relation de sous-jeu : depuis la position
(x, y), on peut se déplacer vers (x', y) oê x' < x, ou vers (x, y') oê y' < y.
C'est exactement la structure de la somme de deux jeux combinatoires.

Alors que la bibliothèque CGT complète de Mathlib (PGame, Surreal, Nim) a
été supprimée par la PR #35550, cette relation abstraite d'addition de
jeux survit comme brique de base pour l'induction bien fondée sur les paires. -/

-- Relation d'addition de jeux sur les paires ordonnées. Modèlise la relation
-- de sous-jeu sur la somme de deux jeux combinatoires, concept central d'ONAG.
#check @Prod.GameAdd

-- Bien-fondé de l'addition de jeux : si les deux relations composantes sont
-- bien fondées, alors Prod.GameAdd l'est aussi. C'est le principe d'induction
-- derrière le théorème de Sprague-Grundy.
#check @WellFounded.prod_gameAdd
end MathlibMap
end Conway
