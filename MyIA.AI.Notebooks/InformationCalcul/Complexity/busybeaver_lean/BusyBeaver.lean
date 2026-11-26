import PA196

/-!
# Temoin consommateur de PA196 (BusyBeaver, jamesyc)

Ce module ne redefinit rien : il importe le paquet amont epingle par le
`lakefile.lean` de ce lake et rejoue l'audit d'axiomes sur les theoremes
centraux. Le contenu mathematique (machine de 196 etats, independance de PA)
reste entierement chez l'amont ; CoursIA n'en consomme que l'enonce prouve.

Le module amont `PA196.Audit` est lui-meme un audit **garde** : chacun de ses
`#print axioms` est precede d'un `#guard_msgs` qui fige l'ensemble d'axiomes
attendu. Un axiome supplementaire, une preuve `sorry` ou un changement de la
confiance `native_decide` font **echouer la compilation** de ce lake. Importer
`PA196` fait donc passer ce garde avant meme les reimpressions ci-dessous.

Reference : <https://github.com/jamesyc/BusyBeaver/tree/main/PA196>,
commit `8419afeb6513c2ec5a14d4cbd0d2ade43d5553b0`, licence MIT.
-/

-- Les temoins ci-dessous sont des `def` a corps constant : le type infere est
-- l'enonce amont, sans le recopier. Le linter defProp les verrait en
-- `theorem` -- c'est delibere : l'organe d'axiomes enumere les `def` comme
-- les `theorem`, et le corps-constant garde chaque temoin synchrone avec
-- l'amont sans duplication d'enonce.
set_option linter.defProp false

namespace BusyBeaver

/-- Temoins consommateurs : chaque corps EST la constante amont, le type
infere est son enonce exact. Les axiomes de chaque temoin sont donc
exactement ceux du theoreme consomme -- c'est ce que l'organe
`axiom_check_step.py` mesure quand il evalue ce lake (mode `*`) : il enumere
ces declarations-ci, dans les sources propres du projet, sans avoir a
resoudre les modules de la dependance (le basename `Independence.lean`
existe aussi chez Mathlib, la resolution par fichier serait ambigue). -/
def witness_machine_nonhalting :=
  PA196.machine_nonhalting

def witness_nonhalting_unprovable :=
  PA196.Arithmetic.nonhalting_unprovable

def witness_halting_unprovable :=
  PA196.Arithmetic.halting_unprovable

def witness_two_sided_independence :=
  PA196.Arithmetic.two_sided_independence

end BusyBeaver

-- Reimpression lisible des quatre enonces, en complement du garde amont :
-- chaque ligne doit rendre un sous-ensemble de `propext`,
-- `Classical.choice`, `Quot.sound` -- ni `sorryAx`, ni `native_decide`.
#print axioms PA196.machine_nonhalting
#print axioms PA196.Arithmetic.nonhalting_unprovable
#print axioms PA196.Arithmetic.halting_unprovable
#print axioms PA196.Arithmetic.two_sided_independence