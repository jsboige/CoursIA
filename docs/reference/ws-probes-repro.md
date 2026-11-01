# Reproduction hors carnet des sondes wavelet scattering (WS-00c, WS-03)

**Provenance** : issue #21823, suite de la revue [NanoClaw] du 2026-10-21 sur la PR #21771
(« pas de cache Fashion-MNIST ici ; chiffres cités comme mesure de l'auteur »).

**Objet** : établir si les quatre valeurs citées par la série wavelet scattering sont
reproductibles **hors du carnet**, c'est-à-dire indépendamment de l'ordre d'exécution et
de l'état de cache d'une session notebook.

**Outil** : [`scripts/repro/ws_probes_repro.py`](../../scripts/repro/ws_probes_repro.py) —
autonome, graine fixe, imprime les versions, sort en `1` en cas d'écart.

## Paramètres relevés dans les carnets

| Sonde | Carnet, cellule | Corpus | Prétraitement | Classifieur |
|---|---|---|---|---|
| WS-00c | `WS-00c-Scattering-from-scratch.ipynb`, cellules 20-21 (§6) | Fashion-MNIST **train**, **80 premières** images de chaque classe (`np.where(labs == c)[0][:80]`) | pad 28→32, split 75/25 stratifié | `LogisticRegression(max_iter=3000, C=1.0)`, **sans** `random_state` |
| WS-03 | `WS-03-Synthese-Scattering-vs-ResNet.ipynb`, cellule 8 | Fashion-MNIST **train et test**, 150 / 75 par classe tirées par `default_rng(42)` | 28×28 brut, `StandardScaler` ajusté sur le **train seul** | `LogisticRegression(max_iter=3000, C=1.0, random_state=42)` |

Le test translaté a le même **geste** dans les deux carnets (décalage ±2 px alterné, périodique
aux bords, `np.roll`) mais **pas le même index de parité** — et c'est un finding de série, pas
un détail d'implémentation :

- WS-00c alterne sur la parité **globale** (`for i in te_i`, où `te_i` indexe le corpus entier) ;
- WS-03 alterne sur la parité **locale** (`enumerate(X_te)`, donc `0..n-1`).

Sur un même jeu de test, les images des deux parités ne sont donc pas les mêmes : deux carnets
qui se présentent comme comparables appliquent deux tests translatés différents. Le script
respecte chacune (`probe_ws00c` itère `te_i` ; `alternating_shift` prend la parité locale, pour
WS-03).

## Résultat mesuré

Exécution du 2026-10-24, Python 3.13.3, numpy 2.3.5, **scikit-learn 1.6.1**, graine 42,
corpus `torchvision` (cache `~/.cache/ft00a`).

| Sonde | État | Mesuré | Cité | Écart | Verdict |
|---|---|---:|---:|---:|---|
| WS-00c | test propre | 0.7900 | 0.790 | 0.0000 | **ok** |
| WS-00c | test translaté | 0.4300 | 0.425 | **+0.0050** | écart |
| WS-03 | test propre | 0.7800 | 0.780 | 0.0000 | **ok** |
| WS-03 | test translaté | 0.3107 | 0.311 | −0.0003 | **ok** |

**Verdict global : `MISMATCH`** — trois valeurs sur quatre reproduites à la précision
d'affichage ; la quatrième (WS-00c translaté) s'écarte d'**un item** (`86/200` mesuré vs
`85/200` cités).

## Lecture de l'écart WS-00c : un item sur le test translaté

Le test propre se reproduit **à l'identique** (`0.790 = 158/200`). Le seul écart est le test
translaté : `0.430` mesuré contre `0.425` cités, soit **un item** (`86/200` vs `85/200`).
Un point de test vaut `1/200 = 0.005`, donc l'écart est exactement un item — de même ordre
que la variabilité intrinsèque de la sonde.

Les valeurs citées sont **les sorties committées** du carnet WS-00c, ligne `pixels` de la table
de `WS-00c-Scattering-from-scratch.ipynb` (artefact committé : `pixels | 0.790 | 0.425`) — et non
les lignes `scattering S1` (`0.810 / 0.700`) ni `scattering complet` (`0.825 / 0.765`). La sonde
reproduit le classifieur linéaire sur pixels bruts, donc cette ligne-là.

**Provenance du couple `0.773 / 0.431` cité par une version antérieure de ce script : non
établie.** Deux mesures indépendantes l'écartent de WS-00c :

- il n'apparaît dans **aucun fichier** de la série (`git grep` sur les fichiers de
  `05-Wavelet-Scattering` à `origin/main` : 0 occurrence des deux valeurs) — alors que
  `0.790 / 0.425` y est bien présent, sur la ligne citée ci-dessus ;
- il est **arithmétiquement impossible** sur le corpus de WS-00c : la cellule 20 imprime
  `corpus : 600 train / 200 test`, et aucune accuracy sur 200 items ne peut s'écrire `0.773`
  ni `0.431` (il faudrait un `k` tel que `k/200` s'arrondisse à ces valeurs ; il n'en existe
  pas). Le couple est en revanche compatible avec un test d'environ 750 items — la taille du
  découpage de WS-03 — mais cette compatibilité **n'est pas une provenance** : elle dit
  seulement que ce n'est pas une mesure de WS-00c.

Deux causes candidates pour ce décalage d'un item, aucune prouvée ici :

1. **Fork de source dans la cellule du carnet (cause structurelle).** La cellule 20 essaie
   `torchvision.datasets.FashionMNIST` puis retombe sur `fetch_openml("Fashion-MNIST")`.
   Les deux sources ne rangent pas les images dans le même ordre, et la sonde sélectionne
   les **80 premières** de chaque classe : c'est donc un **sous-ensemble différent** selon
   la branche empruntée. La valeur citée dépend de la machine qui l'a produite, sans que le
   carnet le dise.
   **Non testé ici** : `fetch_openml` est injoignable depuis cette machine
   (`URLError: [WinError 10060]`), donc la branche openml n'a pas pu être exécutée. Le script
   expose `--source openml` pour que le test soit rejouable sur une machine qui atteint OpenML.

2. **Dérive de version de scikit-learn.** La version employée par l'auteur n'est pas
   consignée dans le carnet ; une évolution du comportement de `LogisticRegression`
   (solveur, multimodal) peut déplacer une prédiction. Non testé non plus : il faudrait
   l'empreinte de l'environnement d'origine, que le carnet ne porte pas.

Ce qui est **mesuré** : sur la branche `torchvision` avec scikit-learn 1.6.1, le test propre
est exact et le test translaté s'écarte d'un item.

## Troisième cause, celle-ci mesurée : la tolérance d'arrêt du solveur

Les deux causes ci-dessus sont restées non testées. Une troisième, absente de la liste, est
maintenant **mesurée** : `LogisticRegression` ne s'arrête pas sur un optimum unique mais sur
un **critère de norme de gradient** (`tol`, défaut `1e-4`). L'objectif L2 est strictement
convexe, donc l'optimum est unique — mais deux chemins numériques différents (version de
scikit-learn, chaîne BLAS, ordre de réduction) peuvent s'arrêter à des points **différents**,
et l'écart entre ces points n'est pas de l'ordre du bruit d'arrondi.

L'outil est [`scripts/repro/ws_probes_margin.py`](../../scripts/repro/ws_probes_margin.py).
Il mesure les deux moitiés de cette phrase.

**1. L'amplitude nécessaire pour déplacer un item.** La classe prédite d'un item ne change
que si son écart `score(top1) − score(top2)` traverse zéro ; cet écart est donc la
perturbation **minimale** que le mécanisme doit atteindre pour changer le compte. Ajustement
du carnet au siège `po-2024` (Python 3.13.14, numpy 2.4.2, scikit-learn 1.8.0), test
translaté, 200 items :

| Mesure | Valeur |
|---|---|
| marge minimale du jeu (item 123) | `9.282508e-03` |
| marge la moins chère pour **gagner** un item (item 123, classe réelle = second score) | `9.282508e-03` |
| marge la moins chère pour **perdre** un item (item 178) | `1.240631e-02` |
| items sous `1e-3` | `0` |
| items sous `1e-2` | `1` |
| perturbation requise pour l'écart d'un item observé | `1.240631e-02`, soit `1,2e7` fois le seuil de bruit `1e-9` |

Un désaccord d'un item exige donc de l'ordre de `1e-2`, là où une réduction de somme en
float64 déplace un score de `1e-16` relatif : l'écart entre sièges **n'est pas** un effet
d'ordre de réduction, il faut que le modèle ajusté diffère réellement.

**Le sens de l'écart décide du vivier.** Ce siège mesure `0.4350`, l'autre `0.4300` : nous
sommes **plus haut**, donc réconcilier les deux suppose de **détruire** un item que nous
réussissons — pas d'en gagner un. La marge pertinente est celle des items **perdables**
(`1.240631e-02`), et non la plus petite marge du jeu (`9.282508e-03`, item 123, qui est
*winnable*). Ce sont deux nombres différents, et prendre le premier pour le second sous-estime
la perturbation requise. L'instrument sépare les deux sens pour cette raison.

**2. La tolérance suffit, à elle seule, à produire cet écart.** Même siège, mêmes données,
même graine, même version : seule la tolérance change.

| `tol` | exactitude | itérations | déplacement max des coefficients | items qui changent |
|---|---:|---:|---|---|
| `1e-4` (défaut du carnet) | `0.4350` | 210 | référence | aucun |
| `1e-6` | `0.4300` | 492 | `1.76e-02` | item 181 (**perte**) |
| `1e-8` | `0.4300` | 765 | `1.74e-02` | item 181 (**perte**) |

Trois lectures, dans l'ordre de ce qu'elles changent pour la série :

- Les deux valeurs observées entre sièges (`0.4350` et `0.4300`) sont **reproduites sur un
  seul siège** par un réglage de solveur légitime. Aucune différence de données ni de version
  n'est nécessaire pour les obtenir.
- À `1e-4` l'ajustement s'arrête à 210 itérations ; à `1e-6` il en faut 492 et les
  coefficients se déplacent de `1.76e-02`, du même ordre que la marge à franchir. C'est le
  mécanisme : le critère d'arrêt laisse le modèle à une distance des données qui suffit à
  faire basculer un item.
- L'item qui bascule est **181** (`1.328711e-02`). Ni **123**, la marge minimale du jeu
  (`9.282508e-03`, et de surcroît *winnable*, mauvais sens), ni **178**, le perdable le moins
  cher (`1.240631e-02`). La marge est une **borne** sur la perturbation requise, elle n'est pas
  un **sélecteur** : elle dit ce qu'il faut au minimum pour que *quelque chose* bascule, pas ce
  qui basculera. La perturbation a une direction propre, et c'est elle qui décide. Annoncer
  « c'est l'item le plus proche qui bougera » serait doublement faux — de sens et de sélection —
  et c'est exactement ce que la mesure évite.

Cette lecture **réunit les deux premières causes** au lieu de les opposer. La valeur mesurée
en 1.6.1 (section précédente) est `0.4300` ; l'ajustement 1.8.0 **convergé** rend `0.4300` ;
seul l'ajustement 1.8.0 arrêté au défaut rend `0.4350`. Un changement de version déplace le
chemin des itérées, et le critère d'arrêt transforme ce déplacement en un item d'écart. Épingler
la source et la version, comme le demande la section suivante, **ne suffit donc pas** : la
tolérance doit être fixée elle aussi.

**Ce qui n'est pas établi** : que le siège `po-2025` s'arrête effectivement plus près de
l'optimum. La mesure démontre qu'un tel arrêt **suffit** à produire l'écart, pas qu'il en est
la cause là-bas. Les deux premières causes restent donc ouvertes.

## Ce que WS-03 établit, en revanche

Les deux valeurs de `WS-03` sont reproduites à la troisième décimale **et** la sonde WS-03
est la plus contrainte des deux (corpus disjoint train/test, `StandardScaler` sur le train
seul, `random_state` explicite). Cela confirme que la **recette** de la sonde est saine ;
c'est la variabilité de son **approvisionnement en données** (WS-00c) qui n'est pas figée.

## Conséquence pour la série (hors périmètre de cette PR)

La cellule WS-00c gagnerait à **épingler sa source** au lieu de laisser un `try/except`
choisir implicitement, à consigner la version de scikit-learn à côté des valeurs citées, et à
**fixer la tolérance du solveur** (ou à ajuster jusqu'à convergence) : à données et versions
identiques, le défaut `tol=1e-4` déplace déjà la valeur d'un item. Tant que ce n'est pas fait,
un chiffre de WS-00c est une **mesure d'environnement**, pas une propriété du carnet. Suivi à
ouvrir ; cette PR ne modifie aucun carnet.

## Reproduction

```bash
python scripts/repro/ws_probes_repro.py                     # source torchvision (auto)
python scripts/repro/ws_probes_repro.py --source openml      # branche de repli du carnet
python scripts/repro/ws_probes_repro.py --out rapport.json   # rapport structure
```

Le script sort `0` si les quatre valeurs concordent, `1` sinon.

```bash
python scripts/repro/ws_probes_margin.py                             # structure de marge seule
python scripts/repro/ws_probes_margin.py --observed 0.4300 --strict   # l'ecart d'un item est-il arithmetique ?
python scripts/repro/ws_probes_margin.py --observed 0.4300 --tol 1e-4 --tol 1e-6 --tol 1e-8
python scripts/repro/ws_probes_margin.py --out marges.json
```

`--strict` sort `1` quand la perturbation requise depasse `--noise-bound` : l'ecart observe
n'est alors pas de l'arithmetique. `--tol` rejoue l'ajustement a chaque tolerance et nomme les
items dont la classe predite change.

## Voir aussi

- #21823 — issue de suivi (revue NanoClaw du 2026-10-21)
- #20893 — série wavelet scattering (WS-00a à WS-03)
- #21771 — PR de la correction de prose sur laquelle porte la revue