# Évaluation BDH (Dragon Hatchling) — verdict complet

**Évaluation conduite les 2026-09-03 et 2026-09-12 ; note resynchronisée le 2026-09-15.**
Une note d'évaluation est datée de sa rédaction : les claims de reproductibilité et l'absence de
peer review ci-dessous se re-vérifient avant d'être ré-invoquées.

**Origine:** issue [#14489](https://github.com/jsboige/CoursIA/issues/14489) — évaluation du sérieux
de Pathway et de l'opportunité d'en parler dans le dépôt.
**Provenance du verdict:** la lecture du papier (62 p.) et la micro-reproduction ont été conduites
par la lane `myia-po-2024:CoursIA` (verdict du 2026-09-12, chiffres du même jour) ; la présente note
restitue ce verdict dans l'arbre. Elle **remplace** la version partielle du 2026-09-03 (PR
[#14501](https://github.com/jsboige/CoursIA/pull/14501), bornée à 15 pages sur 62 et déclarant la
micro-reproduction hors scope), dont deux conclusions sont depuis contredites par la mesure (§3).
**Sources lues firsthand:** papier arXiv:2509.26507 (62 p. intégrales, §1-8 + annexes A/B), second
papier BDH-CQ arXiv:2608.09888 (§4.2, §5), `README` + `bdh.py` + `train.py` du dépôt
`pathwaycom/bdh`, leaderboard ARC Prize, recherche OpenReview, page d'accueil Pathway.

## TL;DR — verdict 3 axes

| Axe | Verdict |
|---|---|
| **A. Sérieux scientifique** | **FIDÈLE** sur les nombres ; **PERTE PAR COMPLAISANCE** de contexte sur les trois headlines |
| **B. Reproductibilité** | **RECOVERABLE-LOCAL** pour le claim architectural du papier ; **INTRINSIC** pour les benchmarks produit |
| **C. Opportunité pédagogique** | **À REVENIR (6 mois)**, sous 4 conditions nommées (§6) |

**Aucune promotion de BDH dans le dépôt.** Cette note est un artefact d'évaluation, pas une
recommandation d'adoption : le verdict C est « à revenir », et le résultat le plus décisionnel du
dossier est un coût (§3), pas une performance.

## 1. Constat structurel : l'issue cite un papier, les chiffres viennent d'ailleurs

**Aucun des trois chiffres mis en avant par l'issue n'est dans le papier de 62 pages archivé.**
Recherche du fulltext extrait (≈ 250 K caractères) : `ARC`, `Sudoku`, `BABILong`, `pass@2`, `29.5`,
`97.4`, `150M`, `134M` → **0 occurrence**.

| Claim cité par l'issue | Source réelle | Statut vérifié |
|---|---|---|
| ARC-AGI-1 29,5 % pass@2 à 0,0007 $/tâche (150 M) | BDH-CQ (arXiv:2608.09888) §5 + blog du 11 août 2026 | Self-report sur le set public de 400 tâches ; pas d'entrée vérifiée au leaderboard |
| Sudoku Extreme 97,4 % (~250 k puzzles) | Blog Pathway + README du dépôt | Aucun papier ; le README dit lui-même que le dépôt public **ne reproduit pas** ce résultat |
| BABILong 95 % à 32 K (134 M) | Page d'accueil `pathway.com` uniquement | Aucun papier, aucun blog méthodologique — claim non documenté |
| « BDH rivals GPT2 at same params 10M–1B » | Papier de 62 p., §4.2 + Fig. 7 + annexe B | **Seul claim du lot adossé au papier archivé** — voir §4 |

L'abstract annonce « 10M to 1B » là où les tables B.4/B.5 mesurent **25 M – 800 M** : arrondi
d'abstract, sans conséquence sur le fond mais à ne pas citer comme plage mesurée.

## 2. Axe A — Fidélité des claims à leurs sources : **FIDÈLE, avec perte par complaisance**

Les trois nombres sont **fidèlement rapportés depuis leurs sources** ; ce que la reprise marketing
efface, ce sont les préconditions que ces sources avouent honnêtement.

- **ARC-AGI (BDH-CQ).** Le chiffre 29,5 % pass@2 à 0,00070 $ est exact. Quatre préconditions
  disparaissent dans la reprise : (a) le coût est **calculé** (0,85 s H200 × 3 $/h, auto-hébergé)
  comparé à des coûts de leaderboard qui mélangent estimations matérielles et prix d'API — bases
  hétérogènes ; (b) l'« independent evaluation » est un audit black-box par des **co-auteurs**
  (Bielik/NYU) sans accès aux poids, ce qui n'est pas une validation tierce ; (c) la page d'accueil
  Pathway porte elle-même *« BDH results are **pending final contamination checks, independent
  validation, and leaderboard review** »* ; (d) le blog admet que BDH-CQ est *« specialized for this
  kind of visual reasoning »* là où les systèmes comparés sont généralistes. La mixture
  d'entraînement (§4.2, divulguée) inclut le training set ARC-AGI-1, RE-ARC, ConceptARC, ARC-Heavy,
  ARC-GEN100K et des données privées, la recipe complète restant *« proprietary »* ; le générateur
  `pathwaycom/arc-task-gen` est déclaré *« distribution-matched to the public eval set »* — zone
  grise de contamination assumée, qui borne la portée du 29,5 %.
- **Sudoku.** 97,4 % top-1 fidèle au blog, mais la source est une implémentation **interne** ; le
  README public est explicite : *« The Sudoku Extreme result refers to Pathway's internal BDH
  implementation, not to the current open-source repository. This repository [...] does not reproduce
  the 97.4% benchmark result out of the box »*. Aucun papier, aucun artefact, aucune ré-exécution
  possible.
- **BABILong.** 95 % à 32 K (et 82 % à 128 K) n'existe que sur la page d'accueil. Aucune méthodologie
  publiée : non vérifiable au-delà de l'affirmation.
- **Concurrence.** Le résultat n'est pas exclusif à BDH : HRM (27 M, Sapient Intelligence) rapporte
  également des scores élevés sur Sudoku-Extreme. L'intérêt architectural est réel, l'exclusivité ne
  l'est pas.

**Identité et pedigree** (vérifiés sur arXiv et sur les publications) : Jan Chorowski (CTO,
co-auteur historique de l'attention avec Bahdanau/Bengio — arXiv:1506.07503, arXiv:1508.04395),
Adrian Kosowski (CSO, ACM SPAA Best Paper), Łukasz Kaiser (advisor, co-inventeur du Transformer
2017), Zuzanna Stamirowska (CEO, PhD systèmes complexes, École Polytechnique). Le pedigree est
authentique — ce que l'axe A qualifie est la **fidélité des claims**, pas la légitimité des auteurs.

**Peer review absente** au 2026-09-15 : aucune soumission NeurIPS/ICLR/ICML identifiée, arXiv v1
(30 septembre 2025) sans v2. Contexte commercial à noter : une levée de 500 M$ est intervenue le
13 août 2026, **avant** toute validation publique des benchmarks.

## 3. Axe B — Reproductibilité

### 3.1 Claim architectural du papier : **RECOVERABLE-LOCAL** (mesuré, pas supposé)

Le dépôt tourne réellement : `train.py` s'exécute de bout en bout sur son jeu de données jouet, et le
`bdh.py` du dépôt s'entraîne effectivement. Le livrable public correspond au papier (annexe E = le
`bdh.py` du dépôt, poids partagés entre couches, ~25 M params par défaut).

Le dépôt est minimal et **honnête sur ce qu'il est** : aucun test unitaire, aucune évaluation de
validation dans `train.py`, aucun checkpoint, aucun seed de scaling publié, aucune ligne de code
Sudoku/ARC/BABILong.

> **Correction de la version du 2026-09-03.** La note précédente concluait
> `RECOVERABLE-MACHINE (GPU recommandé)` et rangeait la micro-reproduction en « résiduel, GPU
> requis ». **C'était une projection, pas une mesure** : le run a été exécuté, et il est
> `RECOVERABLE-LOCAL`. La note elle-même invitait à cette re-vérification.

### 3.2 Claims produit : **INTRINSIC**

ARC, Sudoku et BABILong proviennent d'implémentations internes dont ni les checkpoints ni la recipe
complète ne sont publiés (BDH-CQ §4.2 : *« the complete internal training recipe remains
proprietary »*). Aucune machine du cluster ne peut les répliquer ; une éventuelle API Pathway ne
permettrait qu'un test black-box, pas une réplication. **Ce ne sont donc pas, aujourd'hui, des claims
falsifiables indépendamment.** Verdict `INTRINSIC` établi par l'échec des voies d'accès, et non par
une liste d'axes non testés : la voie manquante est l'**artefact** (poids, recipe), pas un binding.

## 4. Le claim central (« rivals GPT-2 à paramètres égaux ») — mesure

Protocole du papier (annexe B) : Europarl byte-level, baseline **GPTXL** (NanoGPT + ALiBi + cache
TransformerXL — une baseline maison, **pas** GPT-2 pré-entraîné), TBPTT, mêmes données et mêmes
tokens pour les deux. Aucun face-à-face empirique avec Mamba/RWKV/xLSTM/Hyena : §4.3 ne les discute
que qualitativement.

### 4.1 Micro-reproduction de référence — 10 M params, 3000 itérations

Conduite le 2026-09-12 par la lane `myia-po-2024:CoursIA` (RTX 3070, bf16 autocast). BDH 10,16 M
params (`mlp_internal_dim_multiplier=51`) contre GPT2-like 10,94 M params ; données identiques (tiny
Shakespeare byte-level, validation = 10 % final) ; budget identique (3000 it × 32 × 256 = 24,6 M
tokens) ; AdamW lr 1e-3 / wd 0.1 ; seed 1337. Évaluation de validation **ajoutée** — absente de
`train.py`, sans quoi le dépôt ne mesure rien pendant l'entraînement.

**Le coût — l'écart le plus net, et il n'est pas dans la perte :**

| modèle | params | wall-clock (3000 itérations, budget identique) |
|---|---:|---:|
| BDH (implémentation de référence) | 10,16 M | **27 263 s ≈ 7 h 34** |
| GPT2-like | 10,94 M | **143 s ≈ 2 min 23** |

**≈ 191× plus lent.** Décomposition : une analyse d'ordres de grandeur donne ~10× d'arithmétique par
itération supplémentaire pour BDH (têtes d'attention linéaire en dimension N = 3264 contre une
attention de d = 384) ; le facteur restant tient à l'exécution sur cette machine — allocateur saturé
(mesuré 7948-8006 MiB sur 8192 pendant tout le run) et `torch.compile` indisponible sous
Windows/triton alors que `train.py` l'utilise. Le 191× est donc **mesuré sous ces conditions**, mais
l'ordre de grandeur « plusieurs dizaines de fois plus cher à paramètres égaux » ne se réduit pas à un
artefact de VRAM.

**La perte — et pourquoi le chiffre final seul est trompeur :**

| | meilleure validation (ppl) | finale (ppl) |
|---|---:|---:|
| BDH | **4,31** (it. 1000) | 7,20 (it. 3000) |
| GPT2-like | **4,19** (it. 2000) | 4,39 (it. 3000) |

- **finale contre finale : ratio 1,64** → hors de la fenêtre ±10 %.
- **meilleure contre meilleure : ratio 1,03** → **dans la fenêtre ±10 %**.

L'écart entre ces deux lectures n'est pas cosmétique : la BDH du dépôt **culmine à l'itération 1000
puis se dégrade monotonement** (ppl 4,31 → 4,56 → 4,87 → 5,86 → 7,20) quand le GPT2-like reste
stable. Sur le début d'entraînement, BDH est **meilleur** (itération 500 : 4,70 contre 5,75 ;
itération 1000 : 4,31 contre 4,65).

Deux lectures possibles, **non tranchées** avec ces données : sur-apprentissage (le corpus fait
1,0 M caractères vus ~24 fois) ou instabilité d'optimisation (le lr 1e-3 du dépôt est calibré pour
son modèle 25 M compilé, pas pour 10 M sur ce corpus). Les pertes d'entraînement de la phase BDH
seraient nécessaires pour trancher ; elles n'ont pas été conservées (le run n'écrivait qu'un JSON
final). La remontée de +67 % de ppl de BDH sur ses 2000 dernières itérations, contre +4,8 % pour le
GPT, pointe vers l'instabilité — **hypothèse, pas mesure**.

### 4.2 Point indépendant à petite échelle — 0,43 M params, 400 itérations (CPU)

Mesuré le 2026-09-15 sur cette lane, sur le **code réel de l'auteur** (`bdh.py` de
`pathwaycom/bdh`, importé verbatim — aucune réimplémentation), pour tester si la direction du
résultat dépend de l'échelle. Protocole : BDH 425 984 params (`n_layer=2, n_embd=64, n_head=2,
multiplier=32`) contre GPT apparié automatiquement 425 088 params (n_layer=6, D=72, GELU 4×) ;
mêmes données (tiny Shakespeare byte-level), même budget (400 it × 16 × 128), AdamW lr 1e-3 /
wd 0.1, seed 1337, CPU.

| | params | ppl finale | wall-clock |
|---|---:|---:|---:|
| BDH | 425 984 | **6,05** | 52,0 s |
| GPT apparié | 425 088 | **10,18** | 64,2 s |

Ratio de paramètres 1,002 ; **BDH meilleur d'un facteur 1,68 en perplexité**.

Ce point **ne contredit pas** la mesure de 10 M — il la complète et **corrobore l'hypothèse
d'instabilité** (§4.1) plutôt que le sur-apprentissage : à 400 itérations, c'est-à-dire dans le
régime précoce où la mesure de 10 M voyait déjà BDH devant (itération 500 : 4,70 contre 5,75, soit
un avantage de 18 %), BDH mène largement. Les deux mesures s'accordent sur le fait que **l'avantage
de BDH est précoce et se résorbe avec l'entraînement**.

**Limites de ce point, explicites** : échelle 24× plus petite que la mesure de référence et
**sous** la plage du papier (25 M – 800 M) ; 1 corpus ; 1 seed ; 400 itérations là où la référence en
fait 3000 ; baseline maison. Il teste l'**esprit** du claim, pas sa lettre.

### 4.3 Portée de ces mesures

Ni confirmé ni réfuté. Un écart défavorable à 10 M ne réfuterait pas un claim mesuré à 25 M-800 M sur
Europarl avec une baseline ajustée par taille ; une parité locale ne le confirmerait pas non plus.
C'est une **indication locale**, pas un verdict sur le claim du papier.

## 5. Axe C — Opportunité pédagogique : **À REVENIR (6 mois)**

L'architecture est pédagogiquement intéressante et le papier est sérieux sur ses limites : attention
linéaire en haute dimension, activations positives sparses (~5 %), scalabilité en une dimension,
poids partagés entre couches, monosémanticité partielle mesurée (Mann-Whitney U p < 1e-14 sur deux
synapses). Trois angles théoriques existent pour le dépôt — interprétation edge-reweighting
≈ apprentissage hebbien (série ICT), lois d'échelle « rivals GPT2 » (série ML-Training-Pipeline),
attention linéaire positive-sparse face à Mamba/RWKV/xLSTM/Hyena (série Search/ML).

Mais : pas de peer review, pas d'écosystème pré-entraîné, dépôt minimal sans tests, trois headlines
non reproductibles, contamination ARC en cours de vérification par Pathway lui-même, coût
d'entraînement à paramètres égaux défavorable d'un ordre de grandeur (§4.1) — et un contexte
commercial qui presse le calendrier des claims. Aucun de ces angles n'est falsifiable dans l'arbre
aujourd'hui.

## 6. Conditions de révision (6 mois)

L'axe C repasse à « OUI, scope proposé » si, et seulement si :

1. **contamination checks** publiés par Pathway et/ou **entrée vérifiée** au leaderboard ARC Prize ;
2. **rapport technique BDH-CQ complet** avec méthodologie Sudoku et BABILong (aujourd'hui : blog et
   page d'accueil) ;
3. **reproduction tierce indépendante** — ni l'audit black-box par co-auteurs, ni nos micro-repros
   d'échelle ≤ 10 M ne satisfont ce critère ;
4. idéalement, **acceptation en conférence** (peer review).

Une reprise de la micro-reproduction à 10 M+ devrait par ailleurs corriger la limite de méthode
identifiée le 2026-09-12 : **écrire un artefact par étape et un log fichier**, sans quoi un run de
7 h 34 n'est ni surveillable ni reprenable — c'est cette lacune qui a coûté les pertes
d'entraînement nécessaires pour trancher §4.1.

## 7. Verdict global

**Ne pas promouvoir BDH dans le dépôt à ce stade.** Le papier de 62 pages est un travail
d'architecture honnête dont le claim central est **localement reproductible** — avec un coût de calcul
à paramètres égaux défavorable d'un ordre de grandeur, et un avantage précoce qui ne tient pas sur le
budget complet à 10 M params. Les trois chiffres mis en avant par l'issue sont des résultats
auto-déclarés d'implémentations internes non publiées : le premier adossé à un papier qui divulgue
ses zones grises, les deux autres sans artefact vérifiable.

Le dépôt conserve cette note comme **artefact d'évaluation** (protocole, mesures, conditions de
révision) — pas comme recommandation. Aucune mention de BDH n'est ajoutée ailleurs : ni README, ni
notebook, ni catalogue.

## Base factuelle de cette note

- Lecture intégrale du papier arXiv:2509.26507 (62 p., §1-8 + annexes A/B), texte extrait du PDF
  archivé (`G:\Mon Drive\MyIA\IA\Bibliographie IA\MachineLearning\2025 - Dragon Hatchling BDH -
  2509.26507.pdf`).
- Lecture des sections critiques du second papier BDH-CQ (arXiv:2608.09888, 17 p.) : §4.2
  (training mixture), §5 (évaluation ARC-AGI-1).
- Inspection `pathwaycom/bdh` : 9 fichiers, MIT — `bdh.py`, `train.py`, `README` (caveat Sudoku).
  Aucun test, aucun checkpoint, aucun code Sudoku/ARC/BABILong.
- Leaderboard ARC Prize : BDH non listé. Recherche OpenReview : aucune soumission identifiée.
- Page d'accueil Pathway : mention « pending final contamination checks, independent validation, and
  leaderboard review ».
- Micro-reproduction 10 M params (2026-09-12, GPU) et point indépendant 0,43 M params (2026-09-15,
  CPU) : protocoles et chiffres en §4.

## Voir aussi

- Issue [#14489](https://github.com/jsboige/CoursIA/issues/14489) — cahier des charges de cette
  évaluation (verdict et chiffres en commentaires du 2026-09-12)
- Issue #3801 — EPIC SOTA axe-2 (registre)
- [`tsad-benchmark-flaws.md`](tsad-benchmark-flaws.md) — précédent d'évaluation critique d'un
  benchmark ML publié
- `~/.claude/rules/bibliography-hygiene.md` — règle HARD archivage canonique
- `~/.claude/rules/sota-not-workaround.md` — 5 verdicts SOTA + procédure INTRINSIC
- `~/.claude/rules/audit-cross-source-distillation.md` — méthode FIDÈLE/PERTE/DIVERGENCE POSITIVE
