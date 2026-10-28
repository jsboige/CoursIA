# Versions de bibliotheques chargees par les carnets

Organe : `scripts/notebook_tools/check_lib_versions.py` — manifeste :
`scripts/notebook_tools/lib_versions_manifest.json` — issue : #23073.

## Pourquoi cet organe existe

Mandat du mainteneur (2026-10-28, a propos de #23047) : « Ca meritera un
organe pour stabiliser les versions d'API et de libs, car ce genre de
regressions sont parmis les plus terribles et incidieuses. C'est toute une
serie de notebook qui peut exploser. »

Le cas declencheur tient en une cellule : `SymbolicAI/_archive/Tweety.ipynb`
(celle 6) reecrit

```python
TWEETY_VERSION = "1.28"
BASE_URL = f"https://tweetyproject.org/builds/{TWEETY_VERSION}/"
```

alors que l'organe de serie (`SymbolicAI/Tweety/scripts/download_tweety_tools.py`,
l.54) fixe `TWEETY_VERSION = "1.30"` et telecharge depuis Maven Central
(l.57). Le chemin `tweetyproject.org/builds/<version>/` repond **404** depuis
#12789 — et le carnet archive s'est donc reexecute avec des JARs copies hors
du depot, que personne ne peut rejouer.

Un carnet isole est un incident. Pour une bibliotheque partagee par une
serie, l'enjeu est autre : sans reference commune, chaque re-execution peut
charger une autre version, et la rupture d'API apparait carnet par carnet,
des mois plus tard, parfois en silence.

## Ce que l'organe mesure

Trois classes, sur les **cellules code** des carnets :

| classe | ce qui est releve |
|---|---|
| epinglage NuGet | `#r "nuget: IKVM, 8.15.0"` (la virgule peut suivre sans espace) |
| epinglage pip | `pip install x==1.2.3` |
| version locale | un carnet qui **redeclare** un symbole que l'organe de serie possede (`TWEETY_VERSION = "1.28"`) |
| provisionnement etranger | une URL de telechargement hors de l'organe de serie (ici `tweetyproject.org/builds/`) |

## Les deux modes, et pourquoi ils diffèrent

| mode | commande | ce qu'il dit |
|---|---|---|
| **recensement** | `python scripts/notebook_tools/check_lib_versions.py --census` | l'etat du depot : pour chaque bibliotheque, la version canonique et tous les epinglages rencontres, avec le classement de chaque ecart. **rc 0 toujours** — il decrit, il ne juge aucune PR |
| **garde (delta)** | `python scripts/notebook_tools/check_lib_versions.py --changed origin/main...HEAD` | ce que la PR **introduit** : comparaison des epinglages base -> tete |
| **garde (etat)** | `... --state` ou des chemins explicites | l'etat brut d'un carnet : tout epinglage != canonique |

Le delta n'est pas un detail d'implémentation, c'est la **semantique** de la
garde. Un epinglage deja present et non touche par la PR est une derive
historique : elle se traite par la convergence (l'issue la classe), pas par
un rouge sur une PR qui n'a rien fait de mal. Le provisionnement etranger,
lui, est signale **sur l'etat** : son dommage se produit a l'execution, pas a
l'edition.

## Le manifeste : une source par bibliotheque

Quand un organe de serie fixe deja la version, le manifeste **pointe** vers
lui (`canonical_source: "organ"`) et la valeur est lue a l'execution :

```json
{
  "id": "Tweety",
  "ecosystem": "tweety",
  "canonical_source": "organ",
  "organ_path": "MyIA.AI.Notebooks/SymbolicAI/Tweety/scripts/download_tweety_tools.py",
  "organ_symbol": "TWEETY_VERSION",
  "local_symbol": "TWEETY_VERSION"
}
```

Deux surfaces qui recopient la meme valeur finissent par divergir — c'est
exactement la regression que l'organe doit empecher. Pour NuGet et pip, la
version canonique est portee par le manifeste.

Chaque ecart declare porte une **decision** (`to_converge` ou `justified`)
et son **motif ecrit**. Une divergence `justified` ne dispense pas
d'une entree d'allowlist : l'allowlist est ce qui eteint le constat, pour
les carnets nommes, et elle porte elle aussi un motif.

## Les paquets a versions multiples — classement

Ce tableau declare le **classement** : la version canonique, les ecarts
connus, et la decision. Il ne porte **ni le nombre de carnets concernes, ni
un total de paquets** : ces chiffres sont la sortie de l'organe,

```bash
python scripts/notebook_tools/check_lib_versions.py --census
```

et ils ne sont pas recopies ici. Un compte recopie dans une page de
documentation derive au premier carnet touche, sans que rien ne rougisse —
il se lit comme une mesure alors qu'il n'en est plus une.

| paquet | canonique | ecarts declares | classement |
|---|---|---|---|
| Tweety | organe de serie | 1.28 | a classer |
| IKVM | 8.15.0 | 8.14.0 | justifie — DLL Tweety ombree compilee en 8.14.0 |
| IKVM.Image | 8.15.0 | 8.14.0 | justifie — suit IKVM dans la recette de build |
| pythonnet | 3.1.0 | 3.0.5 | a converger — aucun motif ecrit |
| Google.OrTools | 9.15.6755 | 9.11.4210 | a converger — aucun motif ecrit |
| dotNetRDF | 3.4.1 | 3.2.1, 3.4.0 | a converger — aucun motif ecrit |
| Microsoft.ML | 5.0.0 | 3.0.0 | a converger — aucun motif ecrit |
| SkiaSharp | 3.119.4 | 2.88.3 | a converger — aucun motif ecrit |
| Microsoft.ML.AutoML | 0.23.0 | 0.22.3 | a converger — aucun motif ecrit |
| CsvHelper | 33.0.1 | 27.1.1 | a converger — aucun motif ecrit |

Les deux ecarts IKVM font exception : ils portent un motif ecrit dans le
manifeste (l'artefact ombre charge une DLL compilee en 8.14.0, la monter
sans recompiler serait une regression fonctionnelle) et sont donc
`justified`, pas `to_converge`. Les autres series concernees sont la
SemanticWeb (dotNetRDF), le GameTheory et les Search (OrTools, pythonnet).

Une entree `a classer` signale un epinglage que le manifeste ne classe pas
encore : c'est un etat a traiter, pas une decision.

## Taux de faux positifs — mesure

32 PRs de carnets rejouees sur `main` (commits de premier rang, carnets
modifies, epinglages relus a la base et a la tete) :

| garde | constats produits | faux positifs |
|---|---|---|
| delta (base -> tete) | **0** | 0 |
| etat (comparaison brute) | **1** | 1 |

Le faux positif de la ligne « etat » est mesure : la PR `9364be282` modifie
`CSP-5-Optimization-CSharp.ipynb` sans toucher a son epinglage
`Google.OrTools 9.11.4210` (canonique 9.15.6755). Une garde fondee sur l'etat
l'aurait fait rougir a tort.

C'est la mesure qui fonde le demarrage **en advisory** : le stock porte des
derives connues (IKVM 8.14.0, dotNetRDF 3.2.1, OrTools 9.11.4210, pour ne
citer qu'elles — l'etendue se lit au `--census`, pas ici), et un garde
bloquant rougirait des PR qui ne font que retoucher un de ces carnets. La
promotion en bloquant est une tranche distincte, apres convergence.

## Monter une version d'une bibliotheque en un seul geste

La procedure (issue #23073, point 4) :

1. **Un seul PR par serie.** On ne monte pas une bibliotheque dans six PRs
   repartis : la rupture d'API doit se voir sur toute la serie d'un coup.
2. **Monter le manifeste d'abord**, dans le meme PR que la premiere
   convergence. L'organe lit le manifeste du **tree courant** : un carnet
   qui pinne la nouvelle version et un manifeste monte ne produisent aucun
   constat.
3. **Re-executer les carnets de la serie** (regle C.2 : les sorties sont
   committes). Une version qui casse l'API le montre dans les sorties
   committes ; c'est la que se lisent les incompatibilites.
4. **Ecrire les incompatibilites dans le body de la PR** : cellule, appel,
   erreur. Une version qui casse trois carnets doit le dire en clair, pas
   le laisser deduire d'une sortie rouge.
5. **Ne pas toucher aux carnets hors serie** dans le meme PR : le perimetre
   d'une PR est un sujet (regle du depot). Le reste part sur le tapis.
6. **Si un carnet doit rester sur l'ancienne version** (contrainte reelle,
   dependance a une autre bibliotheque), l'ecart passe par une entree
   d'allowlist **avec son motif** — pas par un silence.

## Limites

- L'organe ne reexecute aucun carnet et ne compare pas deux notebooks.
- Il ne juge pas l'interpreteur : c'est le ressort de `check_kernel_drift.py`.
- Mathlib et les lakes Lean restent a #4362 ; les sorties videes par un
  environnement absent restent a #21424.
- La comparaison de versions est **numerique segment par segment** (comme
  NuGet) : `9.11.4210 < 9.15.6755`, et `0.4.x < 0.23.0` (les versions `0.x`
  ne se comparent pas comme des decimaux).
- Une version pre-publique (`1.0.0-preview`) est **inferieure** a la version
  correspondante sans suffixe.

## Voir aussi

- #23073 — l'issue de cadrage (constat, table de dispersion, criteres).
- #23047 — le cas declencheur (re-execution de l'archive Tweety).
- #12789 — le passage de `builds/` (404) vers Maven Central.
- #19673 — l'alignement IKVM 8.14.0 -> 8.15.0, incomplet sur six carnets.
- [procedures-recurrentes.md](procedures-recurrentes.md) — validation des carnets.
