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

### Contre-mesure du 2026-11-01 : même script, environnement différent

Exécution du 2026-11-01 sur ce même siège, Python 3.13.14, numpy 2.4.2, **scikit-learn 1.8.0**,
graine 42, corpus `torchvision`, cache `~/.cache/ft00a`. **Le script est inchangé** — mais
**trois** versions ont bougé depuis le 2026-10-24 (Python `3.13.3 → 3.13.14`,
numpy `2.3.5 → 2.4.2`, scikit-learn `1.6.1 → 1.8.0`). La comparaison ci-dessous porte donc
sur **deux environnements**, pas sur deux versions d'une seule bibliothèque.

| Sonde | État | 2026-10-24 | 2026-11-01 | Cité | Verdict 11-01 |
|---|---|---:|---:|---:|---|
| WS-00c | test propre | 0.7900 | 0.7900 | 0.790 | **ok** |
| WS-00c | test translaté | 0.4300 | **0.4350** | 0.425 | écart |
| WS-03 | test propre | 0.7800 | 0.7800 | 0.780 | **ok** |
| WS-03 | test translaté | 0.3107 | 0.3107 | 0.311 | **ok** |

Le test **propre** de WS-00c et **les deux** valeurs de WS-03 sont identiques au chiffre près
d'un environnement à l'autre. Seul le test **translaté** de WS-00c se déplace : `0.4300 → 0.4350`,
soit **un item de plus**, et **deux items** au-dessus de la valeur citée.

### Troisième point : même version de scikit-learn, deux résultats

Une contre-mesure indépendante (lane `myia-po-2025:CoursIA-2`, 2026-11-01) rejoue **le script
du dépôt, inchangé**, sous **la même version de scikit-learn** que ci-dessus (1.8.0) et le même
Python (3.13.14), sur un autre siège, six exécutions et deux caches distincts :

| Siège | Python | numpy | scikit-learn | WS-00c translaté |
|---|---|---|---:|---:|
| po-2024 (ce siège) | 3.13.14 | 2.4.2 | 1.8.0 | **0.4350** (87/200) |
| po-2025 | 3.13.14 | 2.4.6 | 1.8.0 | **0.4300** (86/200), 6/6 runs |
| po-2024, 2026-10-24 | 3.13.3 | 2.3.5 | 1.6.1 | 0.4300 (86/200) |

La ligne de référence vaut donc `0.4300`, et elle se retrouve **sous deux versions différentes**
de scikit-learn (1.6.1 comme 1.8.0). Sous 1.8.0, deux sièges rendent deux valeurs différentes.
Le déplacement observé le 2026-11-01 sur ce siège n'est donc pas attribuable à `scikit-learn`.

## Lecture de l'écart WS-00c : dépendance d'environnement, cause non établie

Le test propre de WS-00c se reproduit **à l'identique** partout (`0.7900 = 158/200`), ainsi que
les deux valeurs de WS-03. Seul le test translaté de WS-00c varie : `0.4350` et `0.4300` sous
`scikit-learn 1.8.0` selon le siège, `0.4300` sous `1.6.1`. Un point de test vaut `1/200 = 0.005`.

Ce qui **est** établi : la valeur du test translaté de WS-00c n'est pas une propriété du carnet —
elle dépend de l'environnement d'exécution, et le `LogisticRegression` de cette sonde est
instancié **sans `random_state`**.

Ce qui n'est **pas** établi : **lequel** des facteurs est causal. Trois candidats restent en
lice, qu'aucune mesure disponible ne départage :

- la version de `scikit-learn` — **infirmée comme cause unique**, puisqu'à version identique
  (1.8.0) deux sièges divergent ;
- la version de `numpy`, seul facteur visible qui distingue les deux sièges sous 1.8.0
  (`2.4.2 → 0.4350`, `2.4.6 → 0.4300`) ;
- la chaîne BLAS du siège, qui varie avec lui et n'a pas été relevée.

Départager demanderait de rejouer les deux sièges sous un `numpy` épinglé identique — numpy seul
variant, tout le reste tenu — puis, si l'écart subsiste, de comparer les BLAS. **Mesure non faite
à ce jour** ; ce document ne la remplace pas par une attribution.

La lecture « l'écart est de l'ordre d'un ou deux items, comparable à la variabilité intrinsèque de
la sonde » vaut donc pour les environnements qui l'ont produite, pas au-delà. Le chiffre d'un
carnet qui ne fixe ni la source de données, ni les versions, ni le siège est une **mesure
d'environnement**.

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

2. **Dérive de version de scikit-learn — testée le 2026-11-01, non concluante.** La version
   employée par l'auteur n'est pas consignée dans le carnet ; une évolution du comportement de
   `LogisticRegression` (solveur, multimodal) pouvait déplacer une prédiction. Le test est fait,
   sans réimplémentation : **le script de ce dépôt, inchangé**, rejoué sous `scikit-learn 1.8.0`
   rend `0.4350` sur ce siège — mais `0.4300` sur un second siège sous **la même version 1.8.0**
   et le même Python (tableau ci-dessus). Une version qui rend deux valeurs n'explique pas le
   déplacement à elle seule : **la cause reste plausible, elle n'est pas établie.** Le test propre
   et WS-03 ne bougent pas, ni ici ni là-bas.

Ce qui est **mesuré** : sur la branche `torchvision`, le test propre est exact partout et le test
translaté s'écarte de la valeur citée — d'un item sur deux sièges, de deux sur un troisième. Le
chiffre dépend donc de l'**environnement** d'exécution, et cette dépendance est reproductible au
sens où elle se répète run après run sur un siège donné (6/6 sur po-2025, déterministe ici) ;
**quel** facteur de l'environnement la porte n'est pas établi.

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
choisir implicitement, à consigner l'environnement (versions et siège) à côté des valeurs
citées, et à **fixer la tolérance de son solveur**. Tant que ce n'est pas fait, un chiffre de
WS-00c est une **mesure d'environnement**, pas une propriété du carnet : deux sièges sous les
mêmes versions de `scikit-learn` et de Python en rendent deux différentes.

Un `random_state` ne remplacerait pas cette prescription : sous `lbfgs`, le solveur par défaut
de `LogisticRegression`, la graine est **inerte** — mesuré sur scikit-learn 1.8.0, `random_state`
42, 7 et 123 rendent des coefficients identiques au bit près, alors qu'elle les déplace sous
`saga` (`3.45e-04`, contrôle positif). Le levier opérant est la **tolérance** : mesuré sur cette
sonde (#21823), à données, graine et versions identiques, passer de `tol=1e-4` à `1e-6` déplace
les coefficients de `1.76e-02` et un item. Suivi à ouvrir ; cette PR ne modifie aucun carnet.

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