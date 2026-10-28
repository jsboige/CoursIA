# HASHLIFE-SPEEDUP-VERDICT — l'acceleration comme mesure de reductibilite

**Pli 3 de l'Epic Origami (#19742, issue #22227 — grain A).** L'irreductibilite
computationnelle se mesure sur notre propre outillage : HashLife accelere les
motifs dont l'espace de configurations se repete, et n'accelere pas ceux dont il
ne se repete pas. Le rapport d'acceleration est donc un releve empirique de
reductibilite, motif par motif.

## La these, citee a sa source archivee

Wolfram, *Undecidability and Intractability in Theoretical Physics*, Physical
Review Letters **54** (8), 25 fevrier 1985, p. 735 :

> « [...] it can determine the outcome of its own evolution only by explicitly
> following it through: **No shortcut is possible.** Such computational
> irreducibility occurs whenever a physical system can act as a computer. The
> behavior of the system can be found only by **direct simulation or
> observation**: No general predictive procedure is possible. »

Copie archivee : `G:\Mon Drive\MyIA\IA\Bibliographie IA\Automata\1985 - Wolfram -
Undecidability and Intractability in Theoretical Physics (PRL 54, 1985).pdf`,
page 735 (premiere page). Le passage est extrait de cette copie, pas d'un resume.

**Ce que HashLife fait, et ce que le mot « reductible » veut dire ici.**
HashLife ne *predit* rien : il memoise des sous-arbres quaternaires identiques
et saute le recalcul d'un cone causal deja vu. Une acceleration mesure donc la
quantite de **configurations repetees**, pas la possibilite de court-circuiter
la dynamique. Le verdict `REDUCIBLE` qualifie un motif **amortissable par
memoisation** ; il ne dit pas qu'on peut prevoir sa configuration dans 10^9
generations sans calculer les etats intermediaires.

## Methode

- **Organe** : `MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/scripts/hashlife.py`
  (`construct` / `advance`), importe -- jamais reimplemente (regle *organ-first*).
  Le sha256 de l'organe mesure est committe dans le JSON.
- **Ligne de base** : simulation naive par ensemble de cellules, `Theta(G x
  population(G))`.
- **Controle de correction** : a chaque point, la population rendue par les deux
  moteurs doit etre **egale**. Un desaccord invalide la mesure (le script sort en
  code 1). Mesure du run canonique : accord sur **36 points sur 36**.
- **Temoin d'etat final** : la population seule ne prouve rien -- deux ensembles
  de meme cardinal peuvent differer entierement. Chaque point porte donc une
  **empreinte sha256 de l'ensemble final des cellules vivantes**, calculee sur
  les deux voies apres normalisation par translation (l'organe reconstruit son
  quadtree depuis l'origine et `crop` decale le cadre : comparer des coordonnees
  absolues mesurerait le cadrage, pas la dynamique). Un desaccord d'empreinte
  invalide la mesure au meme titre qu'un desaccord de cardinal. Mesure du run
  canonique : accord d'empreinte sur **36 points sur 36**, en plus de l'accord de
  population.
- **Isolation par sous-processus** : l'organe memoise globalement
  (`functools.lru_cache`, maxsize 2**24 sur `join` et `life`). Dans un meme
  processus, un motif rechauffe le cache du suivant. Mesure firsthand du defaut :
  le canon de Gosper rend **0,0265 s a G = 4096**, puis **0,0038 s a G = 16 384**
  -- un motif *plus long* rendu six fois *plus rapide*. Chaque (motif, G,
  repetition) tourne donc dans un interpreteur neuf (`--worker`), et le parent
  agrege la **mediane de 3 repetitions**.
- **Statistique du verdict** : exposant d'echelle `alpha` de la regression
  log-log du temps en fonction de G, separement pour HashLife et pour la ligne
  de base. Chaque `alpha` est publie avec le **R2** de son ajustement, et
  l'**enveloppe** `[min, max]` des `alpha` recalcules repetition par repetition
  -- mesure non parametrique, choisie parce que 3 repetitions ne portent pas une
  estimation de variance.

## Seuils, declares avant la mesure

| Constante | Valeur | Sens |
|---|---:|---|
| `ALPHA_REDUCIBLE_MAX` | 0,5 | en dessous : le temps ne suit pas G |
| `ALPHA_IRREDUCIBLE_MIN` | 0,8 | au dessus : le temps suit G, aucun raccourci |
| `R2_MIN_FOR_LINEARITY` | 0,9 | en dessous : la loi de puissance ne decrit pas la serie |

`REDUCIBLE` si `alpha_hash < 0,5` -- `IRREDUCIBLE` si `alpha_hash >= 0,8` --
`AMBIGUOUS` entre les deux. Les seuils n'ont pas ete ajustes apres lecture des
resultats ; ils sont dans le source, au meme endroit que la classification.

**Robustesse** : un verdict n'est declare robuste que si `R2 >= 0,9` **et** si
l'enveloppe des repetitions tient **entierement** dans la bande de ce verdict.
Un verdict non robuste est publie quand meme, etiquete comme tel -- il n'est
jamais requalifie en silence. Un motif `AMBIGUOUS` dont l'enveloppe reste entre
0,5 et 0,8 est robuste *en tant qu'ambigu* : la bande est tenue.

## Mesure canonique

Commande unique, `hashlife_speedup_results.json` committe :

```bash
python scripts/hashlife/hashlife_speedup.py --repeats 3 \
    --json-out scripts/hashlife/hashlife_speedup_results.json
```

Organe mesure : sha256 `233303a1354a1d27...`, Python 3.13.7 (commits dans le JSON).

## Resultat — un spectre, pas une dichotomie

| Motif | Anatomie | alpha HashLife | R2 | alpha naif | enveloppe | acc. a G max | Verdict | Robustesse |
|---|---|---:|---:|---:|---|---:|---|---|
| glider | periodique translatif p4 | 0,141 | 0,940 | 1,019 | [0,122; 0,145] | 78,73x | **REDUCIBLE** | **robuste** |
| acorn | methuselah chaotique | 1,235 | 0,998 | 1,550 | [1,121; 1,287] | **0,91x** | **IRREDUCIBLE** | **robuste** |
| soup-128-d35 | soupe chaotique | 0,609 | 0,982 | 0,808 | [0,573; 0,614] | 1,63x | **AMBIGUOUS** | **robuste** |
| blinker | periodique p2 | 0,042 | 0,162 | 0,947 | [0,014; 0,106] | 188,20x | REDUCIBLE | non robuste |
| block | immuable | 0,094 | 0,834 | 0,974 | [-0,027; 0,226] | 125,17x | REDUCIBLE | non robuste |
| gosper-gun | croissance reguliere | -0,189 | 0,851 | 1,615 | [-0,233; -0,096] | 2040,19x | REDUCIBLE | non robuste |
| pulsar | periodique p3 | 0,065 | 0,477 | 1,003 | [-0,013; 0,137] | 226,83x | REDUCIBLE | non robuste |
| soup-64-d30 | soupe chaotique | 0,532 | 0,954 | 0,900 | [0,486; 0,531] | 2,78x | AMBIGUOUS | non robuste |

L'acceleration est le rapport des medianes au plus grand G mesure pour le motif.
La colonne `enveloppe` est celle des `alpha` recalcules sur chacune des trois
repetitions ; elle ne mesure que la dispersion *intra-run*.

### Detail par motif

**glider** -- periodique translatif p4, alpha_hash = 0,141, REDUCIBLE robuste

| G | naif (s) | HashLife (s) | acceleration | population | empreinte d'etat final |
|---:|---:|---:|---:|---:|---|
| 256 | 0,0029 | 0,0044 | 0,67x | 5 | `3b9830860dd96ecc` |
| 1024 | 0,0128 | 0,0061 | 2,10x | 5 | `3b9830860dd96ecc` |
| 4096 | 0,0547 | 0,0072 | 7,62x | 5 | `3b9830860dd96ecc` |
| 16384 | 0,2148 | 0,0075 | 28,71x | 5 | `3b9830860dd96ecc` |
| 65536 | 0,8320 | 0,0106 | 78,73x | 5 | `3b9830860dd96ecc` |

Le planeur est le cas le plus parlant : il **se deplace**, donc l'ensemble des
cellules ne se repete jamais a l'identique -- et HashLife l'accelere quand meme
de 79x, parce que ce qui se repete est la structure du quadtree, pas la position.
La memoisation porte sur les cones causaux, pas sur la fenetre globale.
L'empreinte est identique a chaque G, ce qui est exact pour un motif de periode 4
mesure a des generations multiples de 4 : elle etablit que les deux voies
rendent la meme configuration, pas seulement le meme compte.

**acorn** -- methuselah chaotique, alpha_hash = 1,235, IRREDUCIBLE robuste

| G | naif (s) | HashLife (s) | acceleration | population | empreinte d'etat final |
|---:|---:|---:|---:|---:|---|
| 64 | 0,0094 | 0,0214 | 0,44x | 83 | `50f58b93159b6673` |
| 128 | 0,0194 | 0,0531 | 0,37x | 184 | `e19285a7f1034659` |
| 256 | 0,0616 | 0,1106 | 0,56x | 150 | `b2c5339bee8fffcd` |
| 512 | 0,2246 | 0,2965 | 0,76x | 254 | `98f19dc7fa84b4de` |
| 1024 | 0,5973 | 0,6540 | 0,91x | 468 | `52175d8b31a86d0f` |

L'empreinte change a **chaque** generation mesuree : aucun etat ne se repete.
`alpha_hash = 1,235 > 1`, et HashLife reste **plus lent** que la simulation naive
aux cinq echelles mesurees. L'ecart se resserre (0,44x puis 0,91x) mais ne se
renverse pas dans la plage mesuree : rien n'indique un point de bascule.

**soup-128-d35** -- soupe chaotique, alpha_hash = 0,609, AMBIGUOUS robuste

| G | naif (s) | HashLife (s) | acceleration | population | empreinte d'etat final |
|---:|---:|---:|---:|---:|---|
| 64 | 0,4517 | 0,6390 | 0,71x | 2214 | `8e5c397c991da591` |
| 256 | 1,3814 | 2,0330 | 0,68x | 1719 | `10c06a8aed70e3c4` |
| 1024 | 3,7432 | 4,2612 | 0,88x | 1422 | `4d58afc1401662e1` |
| 4096 | 13,5469 | 8,3302 | 1,63x | 1571 | `a131240e7882e762` |

La soupe **se decompose** (population 2214 -> 1422) puis se recompose a la fin
quand les residus interagissent (1571). Le cout par generation baisse donc en
cours de route, ce qui abaisse l'exposant global sans que le motif devienne
amortissable : c'est exactement pourquoi `0,5 < alpha < 0,8` est une bande
d'ignorance declaree, et non une zone tampon a forcer.

**blinker** -- periodique p2, alpha_hash = 0,042, REDUCIBLE non robuste

| G | naif (s) | HashLife (s) | acceleration | population | empreinte d'etat final |
|---:|---:|---:|---:|---:|---|
| 256 | 0,0025 | 0,0019 | 1,29x | 3 | `6be21bba9ced76c7` |
| 1024 | 0,0076 | 0,0017 | 4,35x | 3 | `6be21bba9ced76c7` |
| 4096 | 0,0294 | 0,0032 | 9,14x | 3 | `6be21bba9ced76c7` |
| 16384 | 0,1283 | 0,0022 | 57,32x | 3 | `6be21bba9ced76c7` |
| 65536 | 0,4348 | 0,0023 | 188,20x | 3 | `6be21bba9ced76c7` |

Le temps HashLife est **plat** (0,0019 -> 0,0023 s sur un facteur 256 de G) et
non monotone (0,0032 s a 4096). Un exposant ajuste sur du bruit vaut 0,042 et son
R2 tombe a 0,162 : la loi de puissance ne decrit pas cette serie. Le verdict
`REDUCIBLE` n'est donc pas porte par l'exposant mais par le **rapport** (188x) et
par le fait que le temps ne croit pas -- le critere declare est satisfait, son
*interpretation* ne l'est pas, et c'est ce que la colonne Robustesse signale.

**block** -- immuable, alpha_hash = 0,094, REDUCIBLE non robuste

| G | naif (s) | HashLife (s) | acceleration | population | empreinte d'etat final |
|---:|---:|---:|---:|---:|---|
| 256 | 0,0026 | 0,0029 | 0,90x | 4 | `bd268d043f76dee9` |
| 1024 | 0,0104 | 0,0028 | 3,75x | 4 | `bd268d043f76dee9` |
| 4096 | 0,0330 | 0,0036 | 9,26x | 4 | `bd268d043f76dee9` |
| 16384 | 0,1363 | 0,0035 | 38,84x | 4 | `bd268d043f76dee9` |
| 65536 | 0,6104 | 0,0049 | 125,17x | 4 | `bd268d043f76dee9` |

Meme mecanique que le blinker, en moins net : R2 0,834, sous le plancher de
linearite. L'enveloppe `[-0,027; 0,226]` **traverse zero**, ce qui est la
signature d'un temps constant mesure avec du bruit, pas d'une croissance.

**gosper-gun** -- croissance reguliere, alpha_hash = -0,189, REDUCIBLE non robuste

| G | naif (s) | HashLife (s) | acceleration | population | empreinte d'etat final |
|---:|---:|---:|---:|---:|---|
| 256 | 0,0700 | 0,0578 | 1,21x | 84 | `9a06b15137f600ad` |
| 1024 | 0,6704 | 0,0565 | 11,87x | 221 | `2a863bf2b3f2b038` |
| 4096 | 5,6980 | 0,0313 | 182,16x | 724 | `22860093be252756` |
| 16384 | 59,7781 | 0,0293 | 2040,19x | 2781 | `ba6d703f249da6c5` |

Ici l'exposant HashLife est **negatif** : le temps *decrescent* de 0,0578 s a
0,0293 s quand G quadruple, alors que la population est multipliee par 33. Ce
n'est pas une loi de puissance, et le R2 de 0,851 le confirme ; c'est
l'amortissement d'un cone causal qui grandit et se repete -- plus la simulation
est longue, plus la memoisation paie. `alpha_naif = 1,615` : la population croit
lineairement, donc le cout naif croit plus vite que G. Le verdict `REDUCIBLE` est
porte par le rapport 2040x, massif et sans ambiguite ; l'exposant, lui, n'est pas
un indicateur de complexite comparable d'une famille de motifs a l'autre.

**pulsar** -- periodique p3, alpha_hash = 0,065, REDUCIBLE non robuste

| G | naif (s) | HashLife (s) | acceleration | population | empreinte d'etat final |
|---:|---:|---:|---:|---:|---|
| 256 | 0,0338 | 0,0075 | 4,53x | 56 | `b16e8d30e9fda826` |
| 1024 | 0,1745 | 0,0102 | 17,16x | 56 | `b16e8d30e9fda826` |
| 4096 | 0,5094 | 0,0084 | 60,55x | 56 | `b16e8d30e9fda826` |
| 16384 | 2,4330 | 0,0107 | 226,83x | 56 | `b16e8d30e9fda826` |

Les quatre empreintes sont **identiques** parce que les quatre points tombent sur
des generations toutes congrues a 1 modulo 3 (256, 1024, 4096, 16384) : pour un
oscillateur de periode 3, l'etat y est le meme par construction. C'est le
temoin qui compte ici, et il est decisif : le motif precedent, ampute d'une partie
de ses cellules canoniques, produisait **quatre empreintes differentes** a
ces memes generations. Un emetteur ne revient pas sur son etat ; un oscillateur,
si. La population constante et la croissance reguliere du rapport
(4,5x, 17x, 61x, 227x) confirment la lecture.

Quatre points seulement, et l'ajustement est pauvre (R2 0,477) parce que le temps
HashLife est essentiellement **plat** (7,5 a 10,7 ms sur un facteur 64 de
generations) : l'exposant 0,065 decrit mal une serie que domine une constante,
et la robustesse n'est donc pas revendiquee. Le `REDUCIBLE` est porte par le
rapport 227x, pas par l'exposant -- meme lecture que pour `blinker`, `block` et
`gosper-gun`.

**soup-64-d30** -- soupe chaotique, alpha_hash = 0,532, AMBIGUOUS non robuste

| G | naif (s) | HashLife (s) | acceleration | population | empreinte d'etat final |
|---:|---:|---:|---:|---:|---|
| 64 | 0,0903 | 0,1639 | 0,55x | 506 | `32adb5e738a9e920` |
| 256 | 0,2890 | 0,4321 | 0,67x | 367 | `0e98cc43c5987a60` |
| 1024 | 0,9266 | 1,0637 | 0,87x | 413 | `d96b3e8344d33ab0` |
| 4096 | 3,9275 | 1,4152 | 2,78x | 434 | `d951b3914652227d` |

L'enveloppe `[0,486; 0,531]` **traverse le seuil 0,5** : selon la repetition, ce
motif est `REDUCIBLE` ou `AMBIGUOUS`. Le verdict median est publie `AMBIGUOUS`,
etiquete non robuste -- la frontiere n'est pas tranchee a cette precision, et le
document ne fait pas semblant qu'elle l'est.

## Verdict

**Trois verdicts sur huit sont robustes une fois l'incertitude prise en compte.**
Les cinq autres sont publies, etiquetes non robustes, avec la raison mesuree.
C'est le resultat du grain, pas une reserve ajoutee apres coup.

### Ce qui resiste

| Motif | Verdict robuste | Pourquoi il resiste |
|---|---|---|
| glider | `REDUCIBLE` | R2 0,940, enveloppe [0,122; 0,145] entierement sous 0,5 |
| acorn | `IRREDUCIBLE` | R2 0,998, enveloppe [1,121; 1,287] entierement au dessus de 0,8 |
| soup-128-d35 | `AMBIGUOUS` | R2 0,982, enveloppe [0,573; 0,614] entierement dans 0,5-0,8 |

Ces trois-la portent la these dans les deux sens : un motif a structure repetee
est massivement amortissable (79x), un motif chaotique isole ne l'est pas et
HashLife y est **plus lent** que la simulation naive (0,91x au mieux), et une
soupe chaotique tombe dans la bande declaree d'ignorance plutot que d'etre forcee
d'un cote.

### Ce qui ne resiste pas, et pourquoi

- **`blinker` (R2 0,162), `block` (0,834), `pulsar` (0,477), `gosper-gun`
  (0,851)** : la bande du verdict est tenue, mais la loi de puissance ne decrit
  pas la serie mesuree. Pour les trois motifs periodiques ou immuables, le temps
  HashLife est essentiellement **plat** ; un exposant ajuste la est un artefact,
  pas une mesure de croissance. Pour le canon de Gosper, l'exposant est
  **negatif** (-0,189) parce que la memoisation paie de plus en plus avec la
  duree. Dans les quatre cas le verdict `REDUCIBLE` est porte par le **rapport**
  (125x a 2040x) et non par l'exposant : l'exposant n'est pas l'instrument qui
  mesure ce que le verdict affirme.
- **`soup-64-d30`** : l'enveloppe `[0,486; 0,531]` traverse 0,5. Un run anterieur
  du meme organe la donnait a 0,571 (`AMBIGUOUS` franc) ; ce run la place a 0,532
  avec une queue sous le seuil. Le document ne conserve pas l'ancienne
  classification et ne tranche pas : a cette precision, la frontiere
  `REDUCIBLE` / `AMBIGUOUS` n'est pas decidee.

### Reserve declaree -- la derive entre runs n'est pas couverte par l'enveloppe

L'enveloppe mesure la dispersion des repetitions **d'un meme run**. Deux runs
canoniques du meme organe (sha256 identique) different pourtant :

| Motif | alpha (run precedent) | alpha (ce run) | ecart relatif |
|---|---:|---:|---:|
| acorn | 1,352 | 1,235 | -8,6 % |
| glider | 0,160 | 0,141 | -11,7 % |
| block | 0,158 | 0,094 | -40,6 % |
| pulsar | 0,117 | 0,065 | -44,2 % (voir note) |
| gosper-gun | 0,289 | -0,189 | changement de signe |
| soup-128-d35 | 0,675 | 0,609 | -9,8 % |
| soup-64-d30 | 0,571 | 0,532 | -6,9 % |
| blinker | 0,106 | 0,042 | -59,9 % |

Les temps absolus sont environ deux fois plus lents dans ce run (blinker a
G = 65 536 : 0,4348 s contre 0,2019 s), et l'interpreteur differe (Python 3.13.7
ici, 3.14.3 pour le run precedent) -- les deux sont enregistres dans le JSON.

**Note sur `pulsar`** : son ecart ne mesure pas la seule derive de run. Le motif
precedent etait ampute d'une partie de ses cellules canoniques et se comportait en
emetteur ; la valeur de ce run vient du motif corrige. L'ecart de `pulsar` n'est
donc pas comparable aux sept autres, qui mesurent, eux, la derive a motif
identique.

Consequence a retenir : **la liste des verdicts est plus stable que les valeurs
d'alpha qui la fondent**. Les huit verdicts sont identiques dans les deux runs,
alors que les exposants ont tous baisse et de facon tres inegale : de **-6,9 %**
(`soup-64-d30`) a **-59,9 %** (`blinker`), en passant par -40,6 % (`block`), et
jusqu'a un **changement de signe** pour `gosper-gun` (+0,289 -> -0,189). Un ecart
de cet ordre sur une grandeur qui peut changer de signe n'est pas une petite
imprecision de mesure : l'exposant n'est pas une grandeur transportable d'un run
a l'autre. Un pli ulterieur qui voudrait comparer des `alpha` entre machines doit
d'abord mesurer un motif de reference sur les deux, pas supposer l'invariance.

### Ce que ce verdict ne dit pas

Il ne mesure pas la *previsibilite* : un motif `REDUCIBLE` reste simule, seulement
moins souvent. Il ne porte que sur huit motifs d'une seule implementation Python ;
un motif artificiel peut toujours etre construit pour deplacer la frontiere.

## Reproduire

```bash
python scripts/hashlife/hashlife_speedup.py --repeats 3 \
    --json-out scripts/hashlife/hashlife_speedup_results.json
python -m pytest scripts/hashlife/tests/test_hashlife_speedup.py -q
```

Le script sort en code 1 si une seule population **ou une seule empreinte d'etat
final** diverge entre les deux moteurs : un desaccord invalide la mesure, il ne la
nuance pas.
