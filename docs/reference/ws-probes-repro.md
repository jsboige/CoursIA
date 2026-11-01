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

### Contre-mesure du 2026-11-01 : même script, scikit-learn 1.8.0

Exécution du 2026-11-01, Python 3.13.14, numpy 2.4.2, **scikit-learn 1.8.0**, graine 42,
corpus `torchvision`, même cache. **Le script est inchangé** — seule la bibliothèque diffère.

| Sonde | État | 2026-10-24 | 2026-11-01 | Cité | Verdict 11-01 |
|---|---|---:|---:|---:|---|
| WS-00c | test propre | 0.7900 | 0.7900 | 0.790 | **ok** |
| WS-00c | test translaté | 0.4300 | **0.4350** | 0.425 | écart |
| WS-03 | test propre | 0.7800 | 0.7800 | 0.780 | **ok** |
| WS-03 | test translaté | 0.3107 | 0.3107 | 0.311 | **ok** |

Le test **propre** de WS-00c et **les deux** valeurs de WS-03 sont identiques au chiffre près
entre les deux versions. Seul le test **translaté** de WS-00c se déplace : `0.4300 → 0.4350`,
soit **un item de plus**, et **deux items** au-dessus de la valeur citée.

## Lecture de l'écart WS-00c : une dépendance d'environnement, pas un item

Le test propre se reproduit **à l'identique** dans les deux versions (`0.790 = 158/200`).
Le seul écart est le test translaté, et il **grandit avec la version de scikit-learn** :
`0.425` cités, `0.430` sous 1.6.1, `0.435` sous 1.8.0. Un point de test vaut
`1/200 = 0.005` : l'écart vaut donc un item pour 1.6.1 et **deux** pour 1.8.0.

La lecture « l'écart est exactement un item, de même ordre que la variabilité intrinsèque de
la sonde » ne vaut donc que pour la version qui l'a produite. Ce n'est pas de la variabilité
intrinsèque : c'est une **dépendance au couple (source de données, version de la sonde)**,
qui se déplace d'un cran à chaque changement de l'un des deux. Le chiffre d'un carnet qui ne
fixe ni l'un ni l'autre est une mesure d'environnement.

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

Deux causes candidates pour ce décalage, la première restant non testée, la seconde
désormais mesurée :

1. **Fork de source dans la cellule du carnet (cause structurelle).** La cellule 20 essaie
   `torchvision.datasets.FashionMNIST` puis retombe sur `fetch_openml("Fashion-MNIST")`.
   Les deux sources ne rangent pas les images dans le même ordre, et la sonde sélectionne
   les **80 premières** de chaque classe : c'est donc un **sous-ensemble différent** selon
   la branche empruntée. La valeur citée dépend de la machine qui l'a produite, sans que le
   carnet le dise.
   **Non testé ici** : `fetch_openml` est injoignable depuis cette machine
   (`URLError: [WinError 10060]`), donc la branche openml n'a pas pu être exécutée. Le script
   expose `--source openml` pour que le test soit rejouable sur une machine qui atteint OpenML.

2. **Dérive de version de scikit-learn — mesurée le 2026-11-01.** La version employée par
   l'auteur n'est pas consignée dans le carnet ; une évolution du comportement de
   `LogisticRegression` (solveur, multimodal) peut déplacer une prédiction. Le test est
   désormais fait, sans réimplémentation : **le script de ce dépôt, inchangé**, rejoué sous
   `scikit-learn 1.8.0` rend `0.4350` là où `1.6.1` rendait `0.4300` (tableau ci-dessus).
   Le test propre et WS-03 ne bougent pas. La cause est donc **confirmée**, et elle seule
   explique un déplacement d'un item vers le haut ; elle n'explique pas l'écart initial de
   `0.425` cités vers `0.430` mesurés, qui reste attribuable à la cause 1 ou à la version
   employée par l'auteur — laquelle n'est toujours pas connue.

Ce qui est **mesuré** : sur la branche `torchvision`, le test propre est exact et le test
translaté s'écarte de la valeur citée — d'un item sous 1.6.1, de deux sous 1.8.0. Le chiffre
dépend donc de la version de la sonde, et cette dépendance est reproductible.

**Contrôle indépendant du finding de parité (2026-11-01).** Une réimplémentation
indépendante de WS-00c, écrite sans lire cette section, a fait basculer le test translaté sur
la parité **locale** au lieu de la parité **globale** `te_i`, et a obtenu `0.410` au lieu de
`0.430`. C'est exactement le piège décrit plus haut, et il coûte quatre items — soit plus que
l'écart total étudié. Le finding de parité n'est donc pas théorique : il a été vérifié par un
agent qui s'y est fait prendre.

## Ce que WS-03 établit, en revanche

Les deux valeurs de `WS-03` sont reproduites à la troisième décimale **et** la sonde WS-03
est la plus contrainte des deux (corpus disjoint train/test, `StandardScaler` sur le train
seul, `random_state` explicite). Cela confirme que la **recette** de la sonde est saine ;
c'est la variabilité de son **approvisionnement en données** (WS-00c) qui n'est pas figée.

## Conséquence pour la série (hors périmètre de cette PR)

La cellule WS-00c gagnerait à **épingler sa source** au lieu de laisser un `try/except`
choisir implicitement, et à consigner la version de scikit-learn à côté des valeurs citées.
Tant que ce n'est pas fait, un chiffre de WS-00c est une **mesure d'environnement**, pas une
propriété du carnet. Suivi à ouvrir ; cette PR ne modifie aucun carnet.

## Reproduction

```bash
python scripts/repro/ws_probes_repro.py                     # source torchvision (auto)
python scripts/repro/ws_probes_repro.py --source openml      # branche de repli du carnet
python scripts/repro/ws_probes_repro.py --out rapport.json   # rapport structure
```

Le script sort `0` si les quatre valeurs concordent, `1` sinon.

## Voir aussi

- #21823 — issue de suivi (revue NanoClaw du 2026-10-21)
- #20893 — série wavelet scattering (WS-00a à WS-03)
- #21771 — PR de la correction de prose sur laquelle porte la revue