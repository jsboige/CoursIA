# busybeaver_lean — consommateur epingle de PA196

Lake Lean 4 qui consomme, **sans fork ni adaptation**, le paquet `PA196` du
depot [jamesyc/BusyBeaver](https://github.com/jamesyc/BusyBeaver) : une machine
de Turing de 196 etats dont l'arret est independant de l'arithmetique de Peano.

| Element | Valeur |
| --- | --- |
| Depot amont | `https://github.com/jamesyc/BusyBeaver.git` |
| Commit epingle | `8419afeb6513c2ec5a14d4cbd0d2ade43d5553b0` |
| Sous-repertoire charge | `PA196/` (syntaxe Lake `from git ... / "PA196"`) |
| Toolchain | `leanprover/lean4:v4.35.0` (celui du paquet amont) |
| Licence amont | MIT |

## Pourquoi un lake separe

`formal_logic_lean`, le lake voisin, est en Lean 4.33.1 : c'est la version de son
manifeste Mathlib et de son fork ModalLogic. PA196 est en 4.35.0, et son
`vendor/Foundation` l'est aussi. Le corpus amont est volumineux ; le
ramener a 4.33.1 pour le seul besoin du lake voisin demanderait de porter tout le
corpus, alors qu'un lake par toolchain est la forme prevue par Lake. Les deux
lakes vivent donc cote a cote, chacun avec sa version : le consommateur epingle
ne depend d'aucune adaptation.

**Exception CI, nommee** (doctrine [`lean-lakes-doctrine.md`](../../../../docs/reference/lean-lakes-doctrine.md)
R2 : « les exceptions sont nommees, jamais tacites »). Ce lake n'a **pas**
d'entree dans `scripts/lean/ci_lakes.json`. Le motif est mesure : un job de la
matrice devrait installer un toolchain hors groupe canonique, telecharger le
cache Mathlib v4.35 puis construire le corpus amont sur un runner a quatre
coeurs — un cout sans rapport avec les autres entrees, pour un contenu dont la
CI ne verifierait que la reussite d'une compilation deja mesuree ici. La
verification du lake est portee par le carnet (`lake build` sous l'organe borne
`lean_exec.py`, audit d'axiomes) et par la CI Lean du depot sur les carnets.
L'entree de matrice reste une ligne a ajouter le jour ou un runner a la hauteur
existe.

## Construire et auditer

```bash
lake update          # resout le pin, installe le toolchain 4.35.0
lake exe cache get   # oleans Mathlib de la revision du paquet amont
lake build
```

`BusyBeaver.lean` importe `PA196` et rejoue l'audit d'axiomes sur les quatre
theoremes centraux (`machine_nonhalting`, `nonhalting_unprovable`,
`halting_unprovable`, `two_sided_independence`). Attendu : un sous-ensemble de
`propext`, `Classical.choice`, `Quot.sound` ; aucun `sorryAx`, aucun
`native_decide`.

L'import n'est pas seulement une commodite : le module amont `PA196.Audit` est un
audit **garde**. Chacun de ses `#print axioms` est precede d'un `#guard_msgs` qui
fige l'ensemble d'axiomes attendu, si bien qu'un axiome supplementaire, une preuve
`sorry` ou un changement de la confiance `native_decide` font **echouer la
compilation** de ce lake. Le garde s'execute donc avant nos propres reimpressions,
et non apres elles.

Le carnet `Complexity-08f-Independance-Arithmetique-BusyBeaver-Lean` (et son jumeau
anglais) montre le build et l'audit depuis Python, puis discute le resultat sans
le re-demontrer.

## Reference

Le papier `PA196` est archive au gisement bibliographique
`G:\Mon Drive\MyIA\IA\Bibliographie IA\BusyBeaver\PA196\paper\pa196.pdf`
(MIT, identite verifiee sur la premiere page). Voir l'issue #27477.
