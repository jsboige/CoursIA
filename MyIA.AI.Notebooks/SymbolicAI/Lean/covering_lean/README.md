# covering_lean — consommateur epingle du paquet `covering`

Lake Lean 4 qui consomme, **sans fork ni adaptation**, le paquet `covering` du
depot [jamesyc/covering](https://github.com/jamesyc/covering) : le certificat
formel de la borne inferieure `C(24,14,4) >= 20` (et de sa consequence
`C(25,15,5) >= 34`).

| Element | Valeur |
| --- | --- |
| Depot amont | `https://github.com/jamesyc/covering.git` |
| Commit epingle | `e28962cff844f155ca5a5cfb22563083369b490e` |
| Sous-repertoire charge | racine du depot (le paquet amont est a la racine) |
| Toolchain | `leanprover/lean4:v4.35.0-rc3` (celui du paquet amont) |
| Licence amont | Apache-2.0 |

## Pourquoi un lake separe

La serie compte trois lakes a trois toolchains : `formal_logic_lean` en 4.33.1
(son manifeste Mathlib), `busybeaver_lean` en v4.35.0 (PA196), et
`covering_lean` en v4.35.0-rc3 (Mathlib y est epingle sur la meme balise que le
paquet amont). Un lake par toolchain est la forme prevue par Lake : ramener le
corpus amont a la version du lake voisin demanderait de le porter entierement.
Les trois lakes vivent cote a cote, sans dependance entre eux.

## Ce que consomme le paquet amont

Le depot amont declare **trois** bibliotheques, qui ne jouent pas le meme role :

| Bibliotheque | Role | Contenu |
| --- | --- | --- |
| `Covering` | la preuve | les modules qui construisent l'argument, jusqu'a `Covering/Main.lean` |
| `Challenge` | l'artefact d'audit | les deux enonces **avec `sorry`** — la question posee, pas la reponse |
| `Solution` | la reponse | les memes enonces, prouves, pour la soumission au registre Palomar |

Le consommateur n'importe que `Covering`. Il ne touche ni `Challenge` (les
`sorry` y sont deliberes : c'est la specification) ni `Solution` (redondant avec
`Covering.Main`).

## Construire et auditer

```bash
lake update          # resout le pin, ecrit lake-manifest.json
lake exe cache get   # oleans Mathlib de la revision epinglee par l'amont
lake build
```

`CoveringConsumer.lean` importe `Covering` et rejoue l'audit d'axiomes sur les
deux theoremes (`Covering.covering_24_14_4`, `Covering.covering_25_15_5`).
Attendu : un sous-ensemble de `propext`, `Classical.choice`, `Quot.sound` ; aucun
`sorryAx`, aucun `native_decide` — et un ensemble **concordant** avec la liste
que l'amont publie lui-meme dans son `comparator.json`.

L'amont publie aussi ses **chiffres** : le tableau des bornes (C(24,14,4) :
19 -> 20, meilleure construction connue 23 ; C(25,15,5) : 32 -> 34, meilleure
construction connue 42) et la propagation par le bornes de Schonheim (25 -> 34,
26 -> 56, 27 -> 89, 28 -> 139). Ces trois dernieres valeurs sont une consequence
arithmetique du theoreme, appliquee par le carnet ; le paquet ne les formalise
pas, et l'amont le dit explicitement.

Le carnet `Lean-43-Borne-Couverture-C24-14-4-Lean` (et son jumeau anglais)
montre le build et l'audit depuis Python, puis discute le resultat sans le
re-demontrer.

## Reference

Le papier *A structural lower bound for C(24,14,4)* est archive au gisement
bibliographique
`G:\Mon Drive\MyIA\IA\Bibliographie IA\Automata\Complexity Theory and Hardness\2026 - Chang - A structural lower bound for C(24,14,4) (github jamesyc-covering, Apache-2.0, Lean formalise).pdf`
(Apache-2.0, identite verifiee sur la premiere page). Site annexe :
<https://jamesyc.com/covering/> — registre Palomar `PALOMAR-2026-10-04-000003`.
Voir l'issue #27477 (jalon 3, Greffe B).
