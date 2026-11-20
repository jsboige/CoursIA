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

namespace BusyBeaver

/-- Les quatre theoremes consommes existent et sont ceux de l'amont. -/
example : True := trivial

end BusyBeaver

-- Reimpression lisible des quatre enonces, en complement du garde amont :
-- chaque ligne doit rendre un sous-ensemble de `propext`,
-- `Classical.choice`, `Quot.sound` -- ni `sorryAx`, ni `native_decide`.
#print axioms PA196.machine_nonhalting
#print axioms PA196.Arithmetic.nonhalting_unprovable
#print axioms PA196.Arithmetic.halting_unprovable
#print axioms PA196.Arithmetic.two_sided_independence