# Decision Index — verification locale du classement sur une carte 8 Go

Pli 1 de #18204. Issue de grain : #21910.

Cette page rend compte d'une **mesure locale** du classement des modeles de decision *Decision Index*, realisee sur la carte de la machine de travail (8 Go de VRAM). Elle est distincte de `decision-models.md`, qui reste hors perimetre de cette lane (couverte par une claim croisee) : cette page ne modifie pas ce fichier, elle **documente ce que la mesure y contredit**.

## Verdict en une phrase

La verification locale est **realisable** — et elle a ete realisee : l'obstacle n'etait pas la carte graphique, mais le fait que les **charges utiles de la suite gelee de l'index ne sont pas publiees**. Sur une tranche reconstruite depuis des jeux QCM publics, les modeles `jiwo-0.8b` v1 et v2 sont servis par leur **bibliotheque native** et produisent des exactitudes, une calibration (ECE, Brier) et un profil d'aires **mesurables**. En revanche, le score public de l'index (29.58 pour v2, 28.72 pour v1) **ne peut pas etre reproduit** avec les seules donnees publiques : cet echec est un echec de **donnees**, pas de materiel.

## 1. Le vrai obstacle : les charges utiles de l'index ne sont pas publiees

Le kit de reproduction public (`apolinario/decision-index`, espace `multimodalart/jev-decision-index`) tire ses charges utiles (`requests.jsonl`) d'un jeu de donnees Hugging Face **non publie** :

- `multimodalart/decision-index-suite-0.3` -> **401 / `RepositoryNotFoundError`** (mesure le 2026-10-21, client `huggingface_hub` puis API brute) ;
- le depot public du kit ne contient que des **identifiants** (`run_ids`, `group_ids`) — ni les charges utiles, ni les etiquettes.

Consequence directe : une relecture « tranche de l'index » **a l'identique** est impossible avec les seules donnees publiques. Toute mesure locale porte donc sur une **tranche reconstruite**, et la comparaison avec les valeurs publiees porte sur la **forme** (l'ordre, le profil), **pas sur les scores**.

C'est precisement ce que la page `decision-models.md` attribuait au materiel (« requiert un GPU 24 Go et sort du perimetre de cette lane (RTX 3070 8GB = `RECOVERABLE-MACHINE`) »). La mesure ci-dessous etablit que, pour la **liste courte mesuree ici** (`0.8b`), un GPU 8 Go suffit : l'affirmation est refutee pour cette liste.

## 2. Methode

### L'organe deja present, et ce que cette page ne refait pas

Le Pli 1 de #18204 a deja produit **`scripts/genai-stack/decision_index_report.py`** (PR #20221) : cet outil lit l'index public, classe les modeles par palier de taille servie et releve les licences, les depots de poids et la voie de service. Il **ne sert aucun modele** et ne mesure rien : son role s'arrete a la lecture de l'index publie.

La presente page ne le reimplemente pas et ne le contourne pas : **le cote publie** (scores de l'index, licences, paliers) vient de cet outil et de la carte modele ; **le cote mesure** (service local, exactitude, calibration) est ce qu'il ne fait pas. Les deux cotes sont mis en regard dans §3, explicitement.

### Modeles servis

Les modeles sont servis **localement** par leur bibliotheque native [`jiwo`](https://github.com/jiwidi/jiwo) (MIT) : `jiwo.model.DecisionModel.from_pretrained(depot, revision=..., device=...)` puis `.decide(...)`, qui renvoie le contrat du kit de l'index (`choice` / `score` / `noul`). Aucune API distante, aucun degrade.

Le moteur du kit (`jiwo.index_engine:JiwoEngine`) n'est **pas** utilise ici : il depend du paquet `decision_index` (le kit lui-meme), dont les charges utiles ne sont pas publiees ; le service natif du modele est suffisant et n'exige aucune donnee privee. C'est aussi pourquoi la mesure ne peut pas **remplacer** une tranche de l'index (voir §1) : il n'y a pas d'objet a rejouer.

| Modele | Depot | Revision | Origine du checkpoint |
|---|---|---|---|
| `eljiwo/jiwo-0.8b@v1` | `eljiwo/jiwo-0.8b` | tag `v1` | snapshot local (`model.safetensors` 1 504 820 888 o) |
| `eljiwo/jiwo-0.8b@v2` | `eljiwo/jiwo-0.8b` | tag `v2` | cache HF (`71b7911cf68f…`) |

`v1` et `v2` sont des **tags** du depot (mesure : `list_repo_refs` le 2026-10-21) ; `main` pointe sur le meme commit que le tag `v2`.

### Tranche reconstruite

| Jeu | Configuration | Role | Items | sha256 de la tranche |
|---|---|---|---:|---|
| `allenai/ai2_arc` | `ARC-Easy` (`test`) | knowledge | 300 | `fa4fb46267650ae1d8b0ae83b3ff3313e510d041171487e651db43ae29226359` |
| `allenai/openbookqa` | `main` (`test`) | knowledge | 300 | `61d3c51a6ef3cedfaf8fa5a1fb3bcef58b2c3a7cc52f0ad8c03ef68fdad28d74` |
| `tau/commonsense_qa` | `default` (`validation`) | language | 300 | `be46577a92d4f3d8c06b921eda43d7240c57c84e584e3bc566672fb9d38f59c8` |

Graine de melange **42**, limite **300 items par jeu**, melange **identique** pour les deux modeles (comparaison sur le meme sous-ensemble, 900 items). Le mapping jeu -> aire est une **reconstruction** (`arc_easy`/`openbookqa` -> knowledge, `commonsense_qa` -> language) : la taxonomie fine de l'index n'est pas publiee, ce qui borne la comparaison des aires (voir §5).

### Environnement de mesure

| Element | Valeur |
|---|---|
| Python | 3.12.15 |
| torch | 2.14.1+cu126 |
| `jiwo` | 0.1.0 |
| GPU | NVIDIA GeForce RTX 3070 Ti Laptop GPU |
| VRAM | **8 Go** (8192 MiB) |
| Pic VRAM mesure (allocation `torch`, par checkpoint) | **1,47 Go** pour `v1` comme pour `v2` |

## 3. Resultats mesures

### Exactitude, calibration

| Modele | Jeu | Items | Exactitude | Confiance moyenne | ECE | Brier |
|---|---|---:|---:|---:|---:|---:|
| `jiwo-0.8b@v1` | arc_easy | 300 | 86,33 % | 0,755 | 0,109 | 0,209 |
| | openbookqa | 300 | 56,00 % | 0,536 | 0,098 | 0,575 |
| | commonsense_qa | 300 | 67,00 % | 0,557 | 0,118 | 0,475 |
| | **global** | **900** | **69,78 %** | 0,616 | 0,089 | 0,419 |
| `jiwo-0.8b@v2` | arc_easy | 300 | 84,00 % | 0,683 | 0,157 | 0,240 |
| | openbookqa | 300 | 57,00 % | 0,454 | 0,118 | 0,559 |
| | commonsense_qa | 300 | 67,67 % | 0,556 | 0,128 | 0,468 |
| | **global** | **900** | **69,56 %** | 0,564 | 0,131 | 0,422 |

Lecture : les deux versions sont **quasi equivalentes** sur cette tranche (0,22 point d'ecart global, dans le bruit d'un echantillon de 900 items). v2 est **mieux calibre** sur `arc_easy` (ECE 0,157 contre 0,109, Brier 0,240 contre 0,209 pour une exactitude inferieure de 2,3 points : la confiance y est moins surestimee) et **moins bien calibre** globalement (ECE 0,131 contre 0,089).

Cout de la mesure (par checkpoint) : chargement **13,2 s** (`v1`) et **5,1 s** (`v2`), evaluation **210,4 s** et **209,5 s** pour 900 items (~0,23 s/item), pic VRAM **1,47 Go** dans les deux cas — les deux checkpoints tiennent dans le huitieme de la carte. La mesure a ete rejouee a l'identique (meme graine, memes empreintes de tranche) : les valeurs d'exactitude et de calibration sont **reproductibles**, seuls les temps varient.

### Ordre mesure contre ordre publie

| | `jiwo-0.8b@v2` | `jiwo-0.8b@v1` | Ordre |
|---|---:|---:|---|
| Score public de l'index (edition 0.3) | **29,58** | 28,72 | v2 > v1 |
| Exactitude mesuree (900 items reconstruits) | 69,56 % | **69,78 %** | v1 > v2 |

L'ordre **ne se retrouve pas** sur la tranche reconstruite : l'ecart mesure (0,22 point) est de signe oppose a l'ecart publie (0,86 point).

**Ce que cela ne dit pas** : l'ordre publie porte sur la suite gelee de l'index, l'ordre mesure sur une tranche reconstruite de 900 items QCM publics. Ce sont deux mesures de deux **jeux d'items differents**. Cette observation **ne refute donc pas** l'ordre publie de l'index ; elle etablit que, sur des QCM de connaissance et de sens commun, les deux versions sont indiscernables, lao que l'index les separe de 0,86 point.

### Profil d'aires

| Modele | Aire la plus faible mesuree | Aire la plus faible publiee | Aire la plus forte mesuree | Aire la plus forte publiee | Forme |
|---|---|---|---|---|---|
| `@v1` | language (67,0 %) | knowledge (10,3) | knowledge (71,2 %) | language (32,3) | **inversee** |
| `@v2` | language (67,7 %) | knowledge (10,9) | knowledge (70,5 %) | language (36,1) | **inversee** |

Les scores d'aire publies sont des **scores de skill x100**, pas des exactitudes : la comparaison porte sur la **forme** du profil, pas sur les valeurs. La forme mesuree (knowledge fort, language faible) est **inverse** de la forme publiee (knowledge faible, language fort). Deux reserves s'imposent, et elles sont fortes : (a) le mapping jeu -> aire est une reconstruction ; (b) l'index agrege des items d'une nature que les trois jeux publics ne reproduisent pas (le « language » de l'index passe par des items d'outils et de raisonnement multi-etapes, absents ici). Cette inversion est donc un **signal a investiguer**, pas une refutation.

### Plausibilite

| Modele | Exactitude mesuree (900 items) | Exactitude publiee sur « trois jeux publics non nommes » |
|---|---:|---:|
| `@v1` | 69,8 % | 54,6 % |
| `@v2` | 69,6 % | 61,3 % |

Les valeurs publiees (les cartes modele ne nomment pas ces trois jeux) servent de **repere de plausibilite**, pas de reproduction. Les ordres de grandeur concordent ; l'ecart (de 8 a 15 points) est attendu, les jeux n'etant pas les memes.

## 4. Correction demandee sur `docs/genai/decision-models.md`

La page affirme que la verification locale « requiert un GPU 24 Go » et classe le cas « RTX 3070 8GB » en `RECOVERABLE-MACHINE`. **La mesure refute cette affirmation pour la liste courte `0.8b`** : les deux checkpoints `jiwo-0.8b` ont ete servis sur une carte **8 Go**, avec un pic VRAM de **1,47 Go** et un cout de ~0,23 s par item (900 items en 210 s pour v1, 210 s pour v2).

La correction **n'est pas faite par cette lane** : `docs/genai/decision-models.md` est couvert par la claim d'une autre lane (`myia-ai-01:CoursIA-2`). La demande est adressee a son detenteur (DM `msg-20261021T222232-u6hll9`).

Formulation de replacement proposee :

> La verification locale est realisable sur une carte 8 Go pour les modeles `0.8b` (mesure : `jiwo-0.8b` v1 et v2 servis par la bibliotheque native `jiwo`, 900 items par modele, ~0,23 s/item, pic VRAM 1,47 Go). L'obstacle reel n'est pas la carte mais le **caractere non publie des charges utiles** de la suite gelee de l'index : le score public de l'index n'est donc pas reproductible en local. Les modeles `4b` restent hors de mesure ici (voir §5).

## 5. Ce qui n'est **pas** verifie

- **Le score de l'index** (29,58 / 28,72 pour `0.8b`, 45,76 / 46,06 pour `4b`) : **non reproduit**, charges utiles non publiees. C'est l'echec attendu et il est un echec de donnees.
- **La base non entrainee** (`Qwen3.5-0.8B` sur l'edition 0.2.1, 6,99 publie) : **non mesuree** — elle suppose l'index.
- **Les modeles `4b`** : **non mesures**. Un modele de 4 milliards de parametres en `bf16` represente ~8 Go de poids seuls, ce qui ne tient pas dans 8 Go de VRAM avec les activations ; les verifier demanderait soit un depot CPU (hors delai raisonnable), soit une carte plus large. L'affirmation « 24 Go » reste donc **non refutee pour `4b`** : elle est refutee pour `0.8b`.
- **L'ordre du classement au niveau modele** (`4b` v1/v2, `0.8b` v1/v2 sur l'index) : **non verifie** — c'est precisement ce que l'index publie et que la tranche reconstruite ne peut pas reproduire.
- **La taxonomie des aires** : le mapping mesure est une reconstruction ; l'inversion du profil est un signal, pas une preuve.

## 6. Reproduction

```bash
# env dedie (Python 3.12, torch cu126, jiwo)
C:/dev/envs/jiwo-py312/Scripts/python.exe scripts/genai-stack/decision_local_check.py \
  --model "eljiwo/jiwo-0.8b@v1" \
  --model "eljiwo/jiwo-0.8b@v2" \
  --local "eljiwo/jiwo-0.8b@v1=C:/dev/envs/jiwo-models/jiwo-0.8b-v1" \
  --json scripts/results/decision_local_2026-10-22.json
```

L'agregat ecrit par l'outil contient, pour chaque modele : exactitude, ECE, Brier et confiance moyenne par jeu et en global, les **lignes par item** (identifiant, verite, probabilite de la bonne reponse, confiance, score de Brier), les empreintes sha256 de chaque tranche, l'environnement de mesure, le classement mesure, le profil d'aires, les valeurs publiees de reference et la liste des limites. Il est **falsifiable** : chaque chiffre du tableau §3 se relit dans le JSON.

## 7. Sources

Les sources citees sont archivees dans la bibliographie GDrive partagee (`G:\Mon Drive\MyIA\IA\Bibliographie IA\MachineLearning`, regle `bibliography-hygiene`) :

| Source | Fichier |
|---|---|
| Carte modele `eljiwo/jiwo-0.8b` (edition v2, section Evaluation) | `2026 - eljiwo - jiwo-0.8b model card (web).md` |
| Carte modele `eljiwo/jiwo-0.8b` (edition v1) | `2026 - eljiwo - jiwo-0.8b model card v1 (web).md` |
| Kit de reproduction Decision Index (`apolinario/decision-index`) | `2026 - apolinario - decision-index - kit de reproduction (web).md` |

Jeux de donnees utilises : `allenai/ai2_arc` (ARC-Easy), `allenai/openbookqa`, `tau/commonsense_qa` — jeux publics, standards, sans contrainte de redistribution particuliere ; aucune copie n'est faite dans le depot (regle `bibliography-hygiene` : un jeu de donnees n'est pas une publication).

## 8. Limites de la tranche

- Les trois jeux sont des **QCM a une seule reponse** ; le contrat `choice` de l'index couvre des questions a choix multiples dont certains sont multi-reponses. La reconstruction ne couvre donc qu'une partie du contrat.
- Les items sont courts (question + options) : la longueur de prompt max (8192 jetons) n'est jamais atteinte, le regime de longues chaines de raisonnement de l'index n'est donc pas exerce.
- Les jeux sont bien distribues hors de l'entrainement presumee des modeles, mais cela n'est **pas verifie** ici (la carte modele ne publie pas la liste des jeux d'entrainement).
