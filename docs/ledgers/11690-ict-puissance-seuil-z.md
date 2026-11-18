# ICT-35 — puissance reelle du seuil `|z| > 3` (la regle de detection)

**Ancre** : #11690 (EPIC consolidation ICT) · serie ICT-35 (carnets 35b/35c/35d) ·
complement de la lecture « null global sur le maximum » (PR #27208).

**Statut** : mesure publiee. Le module `ict/humor_power.py` et ses tests
(`ict/tests/test_humor_power.py`) sont la partie executable de cette lecture.

---

## 1. Ce que la lecture ajoute

ICT-35d conclut `AUCUNE_FEATURE_STABLE` : sur les 18 jambes du protocole
(3 couches x 3 types x trained/control), aucune feature ne franchit le
seuil `|z| > 3` du meme cote. La lecture « null global sur le maximum »
(PR #27208) a montre que **ce zero est l'issue typique du null** (96,7 % des
tirages nuls ne produisent aucune feature au-dela du seuil) : le verdict
n'est donc pas une absence de signal, c'est une absence de *puissance*.

La presente lecture quantifie la puissance : **quelle taille d'effet
faudrait-il pour que la regle de detection s'ecole ?** Sans cette reponse,
« aucune feature » ne peut pas etre lu comme « l'effet n'existe pas ».

## 2. Modele (declare)

Sous H1, la statistique observee d'une feature est

```text
z = z_nul + delta
```

où `z_nul` est un tirage du null de l'instrument (flip de signe intra-paire,
construction de `ict/humor_pairs.measure_humor_differential`) et `delta` est
le deplacement de la moyenne par paire exprime **en unites de dispersion
nulle** (la meme unite que le z). Le deplacement est suppose additif sur la
moyenne par paire : la dispersion de la statistique est alors inchangee, ce
qui rend le modele exact plutot qu'approximatif.

La regle de detection est celle de l'instrument, inchangee : **au moins
`min_same_side = 3` features au-dela de `threshold = 3`, du meme cote**.

Deux bornes structurent la lecture :

* **`|z| <= sqrt(n)`** — le z d'une feature vaut `<a_f, 1> / ||a_f||` ;
  Cauchy-Schwarz le borne par `sqrt(n)`. Avec 30 paires, le plafond est
  **`sqrt(30) = 5,477`** : aucune feature ne peut le depasser, quelle que
  soit la taille de l'effet. Une courbe qui monte au-dela decrit un effet
  inaccessible.
* **le seuil est une convention de l'instrument**, pas une propriete de la
  loi : la courbe se lit « si le seuil etait `t`, quel effet faudrait-il ? ».

## 3. Mesure

Traces : `humor35b_qwen35-2b-base_layer12of24_trained.npz` (layer 12/24,
Qwen3.5-2B-Base, SAE-Res-W32K-L0.50), 30 paires minimales du corpus
GT-24b. 1000 replicats, `seed=42`. Features plantees tirees uniformement
parmi les **5 642 features actives** (sur 32 768, les 27 126 autres ont une
différence de zone exactement nulle : elles ne peuvent porter aucun effet).

| `delta` | % du plafond | P(au moins 1 feature > 3) | **P(la regle s'ecole)** | features > 3 (moyenne) |
| ---: | ---: | ---: | ---: | ---: |
| 0,0 | 0 % | 0,026 | **0,000** | 0,026 |
| 1,0 | 18 % | 0,027 | **0,000** | 0,027 |
| 2,0 | 37 % | 0,263 | **0,001** | 0,295 |
| 2,5 | 46 % | 0,821 | **0,082** | 1,321 |
| 3,0 | 55 % | 0,871 | **0,119** | 1,514 |
| 3,5 | 64 % | 0,906 | **0,177** | 1,704 |
| 4,0 | 73 % | 0,940 | **0,240** | 1,885 |
| 4,5 | 82 % | 1,000 | **0,954** | 2,979 |
| 5,0 | 91 % | 1,000 | **0,998** | 3,024 |
| 5,4 | 99 % | 1,000 | **1,000** | 3,026 |

**Sensibilite au nombre de features affectees** (meme trace, meme seed) :

| `delta` | 0 | 2 | 3 | 3,5 | 4 | 4,5 | 5 |
|---| ---: | ---: | ---: | ---: | ---: |---:|---:|
| `k = 1`, P(regle) | 0,000 | 0,000 | 0,000 | 0,000 | 0,000 | 0,000 | 0,000 |
| `k = 3`, P(regle) | 0,000 | 0,001 | 0,119 | 0,177 | 0,240 | 0,954 | 0,998 |
| `k = 10`, P(regle) | 0,000 | 0,069 | 0,948 | 0,984 | 0,993 | 1,000 | 1,000 |

## 4. Ancre de coherence avec l'organe natif

| Mesure | Organe natif (PR #27208, ICT-35d « Lecture 5 bis ») | Ce module | Ecart |
| --- | ---: | ---: | --- |
| P(le null produit **zero** feature au-dela de 3) | 0,967 | 0,974 | 0,007 (1,4 sigma de l'estimateur, D = 2048 / 1000) |
| Features au-dela de 3 sur la jambe agregee observee | 0 | 0 | 0 |
| `max |z|` median sous null | 2,57 | 2,57 | 0 |

Les deux lectures sont **independantes** dans leur implementation (dispersion
empirique sur 2048 tirages d'un cote, formule exacte `||diffs_f||_2 / n` de
l'autre) et convergent : la formule exacte de la dispersion nulle est bien la
limite de l'estimation empirique de l'instrument.

## 5. Ce que la mesure dit (et ne dit pas)

1. **La regle n'a de puissance que dans le haut de la plage atteignable.**
   80 % de puissance exigent `delta ~ 4,3` (± 0,2), soit **~79 % du plafond
   theorique** `sqrt(30) = 5,477`. La fenetre de detection est etroite :
   `delta` compris entre 4,2 et 4,6.
2. **Le seuil franchi n'est pas le seuil detecte.** A `delta = 3` (l'effet
   qui fait franchir le seuil a une feature), une feature passe le seuil
   dans 87 % des cas mais **la regle ne s'ecole que dans 12 %** : les trois
   features doivent passer **du meme cote**, et une feature plantee sur un
   tirage de signes peut tomber du mauvais cote.
3. **Le nombre de features affectees compte davantage que leur taille.** A
   `delta = 3`, dix features affectees declenchent la regle dans 95 % des
   cas, trois dans 12 %.
4. **Consequence pour la lecture d'ICT-35d.** Le verdict `AUCUNE_FEATURE_STABLE`
   n'informe que si les effets plausibles se situent dans le haut de la
   plage atteignable. En deçà de `delta ~ 2,5` (46 % du plafond), la regle
   ne s'ecole **pas** — le zero observe est alors une propriete de
   l'instrument, pas une propriete des donnees. C'est la lecture
   complementaire de la « Lecture 7 » d'ICT-35d, qui declarait l'absence
   de preuve sans quantifier la preuve manquante.

## 6. Limites (declarees)

* Local au triplet **Qwen3.5-2B-Base x SAE-Res-W32K-L0.50 x couche 12/24**,
  aux 30 paires du corpus GT-24b. Rien ne transpose a un autre modele, SAE,
  corpus, couche ou nombre de paires.
* `delta` est exprime en **unites de dispersion nulle de la statistique**,
  pas en unites d'activation : `delta = 4` signifie que la moyenne par paire
  se deplace de quatre fois la dispersion nulle de cette moyenne.
* Le modele suppose un effet additif sur la moyenne par paire, de
  dispersion inchangee. Un effet qui modifie la dispersion (variance), ou
  heterogene d'une paire a l'autre, sort du modele.
* La realisation de l'effet est tiree uniformement parmi les features
  actives ; une concentration de l'effet sur des features de profil
  particulier (forte norme) n'est pas couverte.
* Le plafond `sqrt(n)` est une propriete de l'estimateur : **plus de paires
  l'elargissent**. Une lecture de puissance sur 100 paires donnerait un
  plafond de 10 et une fenetre de detection plus large. C'est la voie
  d'amelioration de l'instrument que la mesure designe.

## 7. Reproduction

```bash
cd MyIA.AI.Notebooks/IIT/ICT-Series
python -m pytest ict/tests/test_humor_power.py -q
```

La courbe se relit par :

```python
from ict.humor_pairs import build_pairs, load_corpus_dur
from ict.humor_power import zone_diffs, power_curve
d = zone_diffs("traces/humor35b_qwen35-2b-base_layer12of24_trained.npz",
               build_pairs(load_corpus_dur()))
power_curve(d, [0, 1, 2, 2.5, 3, 3.5, 4, 4.5, 5], n_planted=3,
            n_replicates=1000, seed=42)
```

Duree : 3,5 s pour 1000 replicats x 10 valeurs de `delta` sur 32 768
features (numpy seul, aucune resource GPU).
