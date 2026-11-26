import Covering

/-!
# Temoin consommateur du paquet `covering` (jamesyc/covering)

Ce module ne redefinit rien : il importe le paquet amont epingle par le
`lakefile.lean` de ce lake et rejoue l'audit d'axiomes sur les deux theoremes
de borne inferieure. Le contenu combinatoire (la structure de blocs, les
comptes d'incidence, la propagation de Schonheim) reste entierement chez
l'amont ; CoursIA n'en consomme que l'enonce prouve.

Reference : <https://github.com/jamesyc/covering>, commit
`e28962cff844f155ca5a5cfb22563083369b490e`, licence Apache-2.0.
-/

-- Les temoins ci-dessous sont des `def` a corps constant : le type infere est
-- l'enonce amont, sans le recopier. Le linter defProp les verrait en
-- `theorem` -- c'est delibere : l'organe d'axiomes enumere les `def` comme
-- les `theorem`, et le corps-constant garde chaque temoin synchrone avec
-- l'amont sans duplication d'enonce.
set_option linter.defProp false

namespace CoveringConsumer

/-- Temoin consommateur : le corps EST la constante amont, le type infere est
son enonce exact (`20 <= 𝒯.card` pour C(24,14,4)). Les axiomes du temoin
sont donc exactement ceux du theoreme consomme -- c'est ce que l'organe
`axiom_check_step.py` mesure quand il evalue ce lake (mode `*`). -/
def witness_covering_24_14_4 :=
  Covering.covering_24_14_4

def witness_covering_25_15_5 :=
  Covering.covering_25_15_5

end CoveringConsumer

-- Reimpression lisible des deux enonces, en complement de l'audit amont :
-- chaque ligne doit rendre un sous-ensemble de `propext`,
-- `Classical.choice`, `Quot.sound` -- ni `sorryAx`, ni `native_decide`.
#print axioms Covering.covering_24_14_4
#print axioms Covering.covering_25_15_5
