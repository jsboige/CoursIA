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
  code 1).
- **Isolation par sous-processus** : l'organe memoise globalement
  (`functools.lru_cache`, maxsize 2**24 sur `join` et `life`). Dans un meme
  processus, un motif rechauffe le cache du suivant. Mesure firsthand du defaut :
  le canon de Gosper rend **0,0265 s a G = 4096**, puis **0,0038 s a G = 16 384**
  -- un motif *plus long* rendu six fois *plus rapide*. Chaque (motif, G,
  repetition) tourne donc dans un interpreteur neuf (`--worker`), et le parent
  agrege la **mediane de 3 repetitions**.
- **Statistique du verdict** : exposant d'echelle `alpha` de la regression
  log-log du temps en fonction de G, separement pour HashLife et pour la ligne
  de base.

## Seuils, declares avant la mesure

| Constante | Valeur | Sens |
|---|---:|---|
| `ALPHA_REDUCIBLE_MAX` | 0,5 | en dessous : le temps ne suit pas G |
| `ALPHA_IRREDUCIBLE_MIN` | 0,8 | au dessus : le temps suit G, aucun raccourci |

`REDUCIBLE` si `alpha_hash < 0,5` -- `IRREDUCIBLE` si `alpha_hash >= 0,8` --
`AMBIGUOUS` entre les deux. Les seuils n'ont pas ete ajustes apres lecture des
resultats ; ils sont dans le source, au meme endroit que la classification.

## Mesure canonique

Commande unique, `hashlife_speedup_results.json` committe :

```bash
python scripts/hashlife/hashlife_speedup.py --repeats 3 \
    --json-out scripts/hashlife/hashlife_speedup_results.json
```

Organe mesure : sha256 `233303a1354a1d27...`, Python 3.14.3 (commits dans le JSON).

## Resultat — un spectre, pas une dichotomie

| Motif | Anatomie | alpha HashLife | alpha naif | acceleration a G max | Verdict |
|---|---|---:|---:|---:|---|
| blinker | periodique p2 | 0,106 | 1,026 | 153,02x | **REDUCIBLE** |
| pulsar | periodique p3 | 0,117 | 0,931 | 15,37x | **REDUCIBLE** |
| block | immuable | 0,158 | 1,030 | 106,92x | **REDUCIBLE** |
| glider | periodique translatif p4 | 0,160 | 0,994 | 95,37x | **REDUCIBLE** |
| gosper-gun | croissance reguliere | 0,289 | 1,917 | 1669,28x | **REDUCIBLE** |
| soup-64-d30 | soupe chaotique | 0,571 | 0,893 | 2,07x | **AMBIGUOUS** |
| soup-128-d35 | soupe chaotique | 0,675 | 0,834 | 1,17x | **AMBIGUOUS** |
| acorn | methuselah chaotique | 1,352 | 1,677 | **0,72x** | **IRREDUCIBLE** |

### Detail par motif

**blinker** -- periodique p2, alpha_hash = 0,106, REDUCIBLE

| G | naif (s) | HashLife (s) | acceleration | population |
|---:|---:|---:|---:|---:|
| 256 | 0,0007 | 0,0007 | 0,96x | 3 |
| 1024 | 0,0028 | 0,0008 | 3,35x | 3 |
| 4096 | 0,0113 | 0,0010 | 11,55x | 3 |
| 16384 | 0,0531 | 0,0012 | 45,53x | 3 |
| 65536 | 0,2019 | 0,0013 | 153,02x | 3 |

**pulsar** -- periodique p3, alpha_hash = 0,117, REDUCIBLE

| G | naif (s) | HashLife (s) | acceleration | population |
|---:|---:|---:|---:|---:|
| 256 | 0,0438 | 0,0877 | 0,50x | 206 |
| 1024 | 0,1521 | 0,1226 | 1,24x | 96 |
| 4096 | 0,5296 | 0,1546 | 3,43x | 96 |
| 16384 | 2,1382 | 0,1391 | 15,37x | 96 |

**block** -- immuable, alpha_hash = 0,158, REDUCIBLE

| G | naif (s) | HashLife (s) | acceleration | population |
|---:|---:|---:|---:|---:|
| 256 | 0,0009 | 0,0009 | 1,00x | 4 |
| 1024 | 0,0036 | 0,0013 | 2,78x | 4 |
| 4096 | 0,0159 | 0,0014 | 11,39x | 4 |
| 16384 | 0,0705 | 0,0016 | 43,57x | 4 |
| 65536 | 0,2659 | 0,0025 | 106,92x | 4 |

**glider** -- periodique translatif p4, alpha_hash = 0,160, REDUCIBLE

| G | naif (s) | HashLife (s) | acceleration | population |
|---:|---:|---:|---:|---:|
| 256 | 0,0018 | 0,0017 | 1,06x | 5 |
| 1024 | 0,0053 | 0,0021 | 2,58x | 5 |
| 4096 | 0,0263 | 0,0032 | 8,22x | 5 |
| 16384 | 0,0951 | 0,0029 | 32,98x | 5 |
| 65536 | 0,4153 | 0,0044 | 95,37x | 5 |

Le planeur est le cas le plus parlant : il **se deplace**, donc l'ensemble des cellules ne se repete jamais a l'identique -- et HashLife l'accelere quand meme de 95x, parce que ce qui se repete est la structure du quadtree, pas la position. La memoisation porte sur les cones causaux, pas sur la fenetre globale.

**gosper-gun** -- croissance reguliere, alpha_hash = 0,289, REDUCIBLE

| G | naif (s) | HashLife (s) | acceleration | population |
|---:|---:|---:|---:|---:|
| 256 | 0,0175 | 0,0092 | 1,90x | 84 |
| 1024 | 0,1447 | 0,0117 | 12,35x | 221 |
| 4096 | 2,0281 | 0,0174 | 116,51x | 724 |
| 16384 | 51,1438 | 0,0306 | 1669,28x | 2781 |

Ici `alpha_naif = 1,917` : la population croit lineairement, donc le cout naif croit plus vite que G. HashLife reste sous-lineaire malgre la croissance -- le canon produit un flux **regulier**. C'est la difference avec l'acorn, qui croit aussi mais de facon irreguliere.

**soup-64-d30** -- soupe chaotique, alpha_hash = 0,571, AMBIGUOUS

| G | naif (s) | HashLife (s) | acceleration | population |
|---:|---:|---:|---:|---:|
| 64 | 0,0583 | 0,1197 | 0,49x | 506 |
| 256 | 0,1879 | 0,3044 | 0,62x | 367 |
| 1024 | 0,5752 | 0,8196 | 0,70x | 413 |
| 4096 | 2,4846 | 1,2016 | 2,07x | 434 |

**soup-128-d35** -- soupe chaotique, alpha_hash = 0,675, AMBIGUOUS

| G | naif (s) | HashLife (s) | acceleration | population |
|---:|---:|---:|---:|---:|
| 64 | 0,2681 | 0,4848 | 0,55x | 2214 |
| 256 | 0,7445 | 1,2152 | 0,61x | 1719 |
| 1024 | 2,0035 | 3,3917 | 0,59x | 1422 |
| 4096 | 9,0985 | 7,7876 | 1,17x | 1571 |

**acorn** -- methuselah chaotique, alpha_hash = 1,352, IRREDUCIBLE

| G | naif (s) | HashLife (s) | acceleration | population |
|---:|---:|---:|---:|---:|
| 64 | 0,0038 | 0,0141 | 0,27x | 83 |
| 128 | 0,0141 | 0,0280 | 0,50x | 184 |
| 256 | 0,0382 | 0,0856 | 0,45x | 150 |
| 512 | 0,1468 | 0,2258 | 0,65x | 254 |
| 1024 | 0,3907 | 0,5408 | 0,72x | 468 |

## Verdict

**L'acceleration HashLife se comporte comme une mesure de reductibilite, sous les
reserves ecrites ci-dessous plutot que corrigees apres coup.**

1. **Les motifs a structure repetee sont amortissables, massivement.**
   `alpha_hash` va de 0,106 a 0,289 pour les cinq motifs periodiques ou a
   croissance reguliere : le temps HashLife ne suit pas G, et l'acceleration
   atteint 15x a 1669x au plus grand G mesure. Le planeur et le canon de Gosper
   montrent que la repetition pertinente est celle des **cones causaux**, pas
   celle de la fenetre.

2. **Le motif chaotique isole est non amortissable, et HashLife y est plus lent
   que la simulation naive.** Acorn : `alpha_hash = 1,352 > 1`, acceleration
   0,72x a G = 1024. Aucun raccourci n'apparait, et la structure de quadtree coute
   plus cher que le comptage de voisins. C'est la forme mesurable du « no
   shortcut is possible » cite plus haut -- mesuree sur notre organe, pas
   empruntee au texte.

3. **Reserve declaree -- les soupes tombent en `AMBIGUOUS`, et le critere seul ne
   les separe pas.** `alpha_hash` y vaut 0,571 et 0,675 : entre les deux seuils.
   La raison est visible dans les tableaux -- une soupe **se decompose** (la
   population decroit de 2214 a 1422, puis remonte a la fin quand les residus
   interagissent), donc le cout par generation baisse, ce qui abaisse l'exposant
   global sans que le motif devienne amortissable. Le **rapport final** les
   separe nettement (1,17x et 2,07x, contre 15x a 1669x pour les amortissables),
   mais ce rapport n'est pas le critere declare et n'a pas ete substitue apres
   lecture. Un pli ulterieur peut declarer un critere a deux variables (exposant
   **et** rapport) et le mesurer sur les memes motifs ; ce pli ne le fait pas, et
   ne requalifie donc pas les soupes.

4. **Ce que ce verdict ne dit pas.** Il ne mesure pas la *previsibilite* : un
   motif `REDUCIBLE` reste simule, seulement moins souvent. Et il ne porte que
   sur huit motifs d'une seule implementation Python ; un motif artificiel peut
   toujours etre construit pour deplacer la frontiere.

## Reproduire

```bash
python scripts/hashlife/hashlife_speedup.py --repeats 3 \
    --json-out scripts/hashlife/hashlife_speedup_results.json
python -m pytest scripts/hashlife/tests/test_hashlife_speedup.py -q
```

Le script sort en code 1 si une seule population diverge entre les deux moteurs :
un desaccord invalide la mesure, il ne la nuance pas.
