# Versions de bibliotheques chargees par les carnets

Organe : `scripts/notebook_tools/check_lib_versions.py` — manifeste :
`scripts/notebook_tools/lib_versions_manifest.json` — issue : #23073.

## Pourquoi cet organe existe

Mandat du mainteneur (2026-10-28, a propos de #23047) : « Ca meritera un
organe pour stabiliser les versions d'API et de libs, car ce genre de
regressions sont parmis les plus terribles et incidieuses. C'est toute une
serie de notebook qui peut exploser. »

Le cas declencheur tenait en une cellule : `SymbolicAI/_archive/Tweety.ipynb`
(celle 6) reecrivait

```python
TWEETY_VERSION = "1.28"
BASE_URL = f"https://tweetyproject.org/builds/{TWEETY_VERSION}/"
```

alors que l'organe de serie (`SymbolicAI/Tweety/scripts/download_tweety_tools.py`,
l.54) fixe `TWEETY_VERSION = "1.30"` et telecharge depuis Maven Central
(l.57). Le chemin `tweetyproject.org/builds/<version>/` repond **404** depuis
#12789 — et le carnet archive s'est donc reexecute avec des JARs copies hors
du depot, que personne ne peut rejouer.

> **Le cas corpus a ete repare sur `main`** (#23047, commit `d5e44a0919d6`) :
> le carnet archive est desormais provisionne par l'organe de la serie. L'organe
> et son motif sont **conserves** — ils decrivent la *classe* de defaut
> (reclaration locale d'une version que la serie fixe + provisionnement hors de
> l'organe), pas un carnet particulier. Le controle positif du depot rejoue
> desormais cette classe sur une charge utile synthetique : un controle pose
> sur un corpus converge tomberait au sol sans que l'organe ait change.

Un carnet isole est un incident. Pour une bibliotheque partagee par une
serie, l'enjeu est autre : sans reference commune, chaque re-execution peut
charger une autre version, et la rupture d'API apparait carnet par carnet,
des mois plus tard, parfois en silence.

## Ce que l'organe mesure

Trois classes, sur les **cellules code** des carnets :

| classe | ce qui est releve |
|---|---|
| epinglage NuGet | `#r "nuget: IKVM, 8.15.0"` (la virgule peut suivre sans espace) |
| epinglage pip | une **commande** d'installation : `pip install x==1.2.3` (ou `%pip` / `!pip`). Une version citee dans un commentaire ou dans une chaine n'est pas un epinglage |
| version locale | un carnet qui **redeclare** un symbole que l'organe de serie possede (`TWEETY_VERSION = "1.28"`) |
| provisionnement etranger | une URL de telechargement hors de l'organe de serie (ici `tweetyproject.org/builds/`) |
| epinglage flottant | `#r "nuget: Google.OrTools"` ou `pip install mealpy` — la version n'est pas fixee (cf #23086) |

## Les deux modes, et pourquoi ils diffèrent

| mode | commande | ce qu'il dit |
|---|---|---|
| **recensement** | `python scripts/notebook_tools/check_lib_versions.py --census` | l'etat du depot : pour chaque bibliotheque, la version canonique et tous les epinglages rencontres, avec le classement de chaque ecart. **rc 0 toujours** — il decrit, il ne juge aucune PR |
| **garde (delta)** | `python scripts/notebook_tools/check_lib_versions.py --changed origin/main...HEAD` | ce que la PR **introduit** : comparaison des epinglages base -> tete |
| **garde (etat)** | `... --state` ou des chemins explicites | l'etat brut d'un carnet : tout epinglage != canonique |

Le delta n'est pas un detail d'implementation, c'est la **semantique** de la
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

Chaque ecart declare porte une **decision** et son **motif ecrit**. Le
vocabulaire du classement (celui du recensement) est :

| classement | sens | ce que la lane doit en faire |
|---|---|---|
| `canonique` | la version fixee par le manifeste ou par l'organe de serie | rien : c'est la cible |
| `justified` | l'ecart est **motive** dans le depot (contrainte reelle de la serie) | rien : l'ecart est assume |
| `to_converge` | l'ecart n'a **aucun motif ecrit** dans le depot | converger le carnet vers la canonique |
| `a_classer` | l'ecart est **constate mais pas arbitre** : aucune decision n'est ecrite pour lui | l'arbitrage a lieu ; tant qu'il n'est pas arbitre, l'ecart reste visible |

Une divergence `justified` ne dispense pas d'une entree d'allowlist :
l'allowlist est ce qui eteint le constat, pour les carnets nommes, et elle
porte elle aussi un motif. Une entree d'allowlist **sans motif ecrit** est
refusee au chargement du manifeste : une allowlist sans motif n'est pas une
justification.

Les **decompils ne sont jamais recopies** dans le manifeste ni dans cette
page : le nombre de carnets par version, les epinglages flottants et le
classement de chaque ecart sont produits par le recensement, seul a jour sur
le corpus.

## Le classement du corpus — il se lit dans l'organe, pas dans cette page

```bash
python scripts/notebook_tools/check_lib_versions.py --census
```

Le recensement sort la table de dispersion complete : pour chaque
bibliotheque du manifeste, sa version canonique, chaque version
epinglee rencontree, le nombre de carnets qui la portent, le classement de
l'ecart et son motif. Il sort aussi les **epinglages flottants**, qu'aucune
table recopie ne pourrait dire.

Deux usages :

- **diagnostiquer** une serie avant de la converger (quels carnets portent
  l'ecart, quel est son classement) ;
- **verifier** qu'une convergence a bien ete rendue : la ligne disparait de
  la table, elle ne se recopie pas ailleurs.

Ce qui est ecrit dans le manifeste, en revanche, ce sont les **motifs** :
pourquoi un ecart est justifie, pourquoi un autre doit converger. Un motif
qui contient un decompil (« presente sur N carnets ») est un decompil
copic qui perime au premier ajout de carnet ; il n'a pas sa place la.

Les ecarts **a converger** portent aujourd'hui sur OrTools (11 carnets),
pythonnet (7), CsvHelper, Microsoft.ML et SkiaSharp (un chacun). Les ecarts
**justifies** portent sur IKVM et IKVM.Image (8.14.0, six et cinq carnets :
l'artefact ombre est compile dans cette version). Deux series ont **converge**
et ne declarent plus aucun ecart : la SemanticWeb sur dotNetRDF 3.4.1
(#23083) et AutoML sur 0.23.0 (#23088) — leurs entrees ont ete retirees du
manifeste le jour ou la convergence a atterri, pas avant (une divergence
declaree pour une version absente du corpus est un **fantome**, que
l'organe signale).

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
derives connues (les epinglages ages, les epinglages flottants), et un garde
bloquant rougirait des PR qui ne font que retoucher un de ces carnets. Le
detail des derives se lit dans le recensement ; la promotion en bloquant est
une tranche distincte, apres convergence.

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

## Codes de sortie

| code | sens |
|---|---|
| **0** | aucun constat (ou recensement : il decrit, il ne juge) |
| **1** | constats : la PR introduce un ecart, ou l'etat lu porte un ecart |
| **2** | **incident** : l'organe n'a pas pu conclure |

Le rc 2 est la regle de la famille : un carnet illisible, un manifeste dont
une entree d'allowlist n'a pas de motif, un carnet hors du depot, une base
illisible. Aucun de ces cas ne doit produire un **vert silencieux** : le
silence se lirait comme « les carnets examinés sont alignes » alors que
l'organe n'a rien lu. Un incident n'est pas un verdict de la PR : il ne
bloque rien par lui-meme, il dit que la mesure est a refaire.

## Limites

- L'organe ne reexecute aucun carnet et ne compare pas deux notebooks.
- L'organe ne reconnait un epinglage pip que dans une **commande
  d'installation** (`pip install ...`, `%pip install ...`, `!pip install ...`),
  dans une cellule **code** : une version citee dans un commentaire ou dans
  une chaine n'est pas un epinglage, et une commande ecrite en markdown reste
  hors perimetre. Sur le corpus de reference, mealpy n'est donc **pas epingle
  du tout** : sa seule commande d'installation (`pip install mealpy numpy
  matplotlib`) est ecrite dans une cellule markdown, et les deux occurrences
  de 3.0.2 dans les cellules code sont de la prose (un `print` et un
  commentaire C#). L'entree de manifeste porte donc un **contrat
  d'environnement** (la version que `Config/PythonNetLoader.cs` doit
  exposer), pas une observation du corpus ; le suivi de l'installation est
  dans #23104.
- Une version suivie du point final d'une phrase (`... contre IKVM 8.14.0.`)
  n'est pas reconnue comme une mention : le jeton `8.14.0.` est ecarte pour
  ne pas matcher un prefixe de version. Consequence a reboucler (#23104).
- Les **binaires charges depuis un chemin hors du depot** ne sont pas
  detectes : c'est un ecart de dependance, pas d'epinglage. Le suivi est
  l'issue nommee dans le corps de la PR #23079.
- Les **replis indexes sur une version** (`Skipped ... API change`) sont
  signales par la lecture du carnet, pas par l'organe : le suivi est l'issue
  nommee dans le corps de la PR #23079.
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
