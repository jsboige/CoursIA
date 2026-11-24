# Campagne ICT-25a — le run **instrumente** (checkpoints persistants + activations réelles)

**Statut** : le **code** du run instrumente est livre ; le **run GPU a ete
lance le 2026-11-24** sur le device 2 (charge de l'hote sous la barre a
11:40Z), apres correction de **deux defauts bloquants** mesures sur ce siege
(§1 bis) que la premiere execution revelait. Ce document dit ce que le run
fait, ce qu'il produit, et ce qu'il ne produit **pas**.

- Issue porteuse : [#5105](https://github.com/jsboige/CoursIA/issues/5105)
  (Gates 20-21, campagne ICT-25a).
- Pre-enregistrement du panel :
  [`ict25-panel-persona-pre-enregistrement.md`](ict25-panel-persona-pre-enregistrement.md)
  (§5 « ce qui bloque l'execution du panel », §6 « le run pre-enregistre »).
- Sceau de la campagne d'echelle (2B, **modifie en aucune ligne**) :
  [`ict25a-2b-pre-enregistrement.md`](ict25a-2b-pre-enregistrement.md) ·
  resultats mesures : [`ict25a-2b-resultats-2b.md`](ict25a-2b-resultats-2b.md).

---

## 1. Le blocage, mesure

Le panel persona doit lire des **activations reelles**, pas un `.npz`
synthetique. Lire des activations suppose qu'elles aient ete **echantillonnees
pendant l'entrainement**. Elles ne l'ont pas ete, et les runs existants **ne
sont pas re-exploitable** :

| Fait | Source | Consequence |
|---|---|---|
| `save_strategy="no"` | `ict25a_scaleup_grpo.py` | aucun checkpoint intermediaire n'est ecrit |
| `output_dir=tempfile.mkdtemp(prefix=f"ict25a_{arm}_{seed}_…")` | idem | la sortie d'entrainement est **ephemere et horodatee** : ni les poids finaux ni les checkpoints ne survivent |
| `records_sample` (64 tete + 64 queue) et `per_seed[].metrics` agrege | artefacts committes | les artefacts ne portent **ni serie par pas ni tenseur** |

Il n'existe donc **aucune** source d'apres laquelle reconstruire les
activations d'un checkpoint apres coup. D'ou la conclusion du §5 : « le panel
reel exige un **nouveau run instrumente** », et le cout mesure de ce run
(3,4 à 6,2 h de GPU par graine et par bras).

Ce qui manquait n'etait donc **pas** un script d'analyse : c'etait le **run**
lui-meme, et son instrumentation.

## 1 bis. Les deux defauts bloquants que le premier run a reveles (mesures du 2026-11-24)

Le code livre n'avait **jamais ete execute sur un GPU** : les deux barrierses
ci-dessous n'apparaissent qu'a la premiere instrumentation reelle, et
l'arret du run est **anterieur** a l'echantillonnage des activations.

| # | Defaut | Erreur mesuree | Correctif |
|---|---|---|---|
| 1 | Les entrees du tokenizer (tenseurs **CPU**) etaient envoyees telles quelles a un modele charge sur `cuda:0` | `RuntimeError: Expected all tensors to be on the same device, but got index is on cpu, different from other tensors on cuda:0` | `forward_transformers` deplace les entrees sur `model.device` (via l'attribut `device`, **sans import torch**) ; un modele sans `device` (CPU, modele de test) reste intact |
| 2 | Les activations sont en **bfloat16** ; `numpy` ne sait pas lire ce `ScalarType` | `TypeError: Got unsupported ScalarType BFloat16` | `_vers_numpy` convertit en `float32` **avant** le passage a numpy (et seulement en cas d'echec de la conversion directe) |

Les deux correctifs sont **couverts par des tests de regression**
(`scripts/tests/test_ict25a_probe_battery.py` : deplacement des entrees sur le
peripherique, non-deplacement d'un modele sans `device`, lecture d'un tenseur
bfloat16). Apres correction, le run **va au bout** sur le device 2 : 2 pas
d'entrainement + echantillonnage + `.npz` + manifeste + checkpoints
persistants, **sortie 0**.

> Ces deux defauts etaient **invisibles** aux tests CPU : le module
> s'appuie sur un modele de test sans `device` et sans bfloat16. Ils ne
> pouvaient etre reveles que par une execution GPU reelle — d'ou le fait que
> le present document ne les decrit qu'apres coup, et non avant.

## 2. Ce que cette PR livre

Le contrat du §6, en deux points, plus la partie qui le rend **falsifiable**.

### 2.1 Checkpoints persistants (§6.1)

`--checkpoint-dir <racine>` remplace le `mkdtemp` ephemere par une racine
**stable**, et `save_strategy="no"` par `save_strategy="steps"` (avec
`--save-steps N` pour le pas de sauvegarde). La racine passe par
`verifier_racine_stable()`, qui **refuse** un dossier sous le repertoire
temporaire du systeme : un artefact ecrit la ne survit pas au run, et c'est
exactement la cause mesuree du blocage.

### 2.2 Echantillonnage sur batterie fixe (§6.2)

`--probe-battery <fichier.json>` (ou la batterie par defaut, **ecrite** alors
dans la racine des checkpoints et **relue** depuis le disque) designe les
sondes. Le contrat :

- la batterie est **fixe** : memes prompts a tous les checkpoints, meme graine
  de generation (`PROBE_SEED`), et son **empreinte SHA-256** est declaree ;
- la **couche** (`--probe-layer`, index dans `hidden_states`, ou `last`) et la
  **position** (`--probe-position`, `last` ou `mean`) sont declarees — dans le
  `.npz` **et** dans le manifeste ;
- chaque echantillon porte un identifiant de prompt (`p01`…) ;
- le `.npz` (`ict25a_<bras>_s<graine>_step<etape>.npz`) et son manifeste
  (`….manifeste.json`) sont ecrits **cote a cote** du checkpoint.

### 2.3 Le manifeste : ce qui rend l'echantillon falsifiable

Le manifeste porte les declarations du run (bras, graine, etape, modele,
couche, position, graine de generation, empreinte de la batterie) et les
**empreintes SHA-256** du `.npz` **et de chaque vecteur d'activation**.

Consequence operationnelle : deux checkpoints se comparent **sans
reexecuter quoi que ce soit** — et une activation qui derive d'un checkpoint a
l'autre se voit dans le manifeste. Un test mesure exactement cela (controle
positif) : changer une seule activation change l'empreinte de ce vecteur et
celle du `.npz`, et **laisse intactes** les empreintes des autres vecteurs.

## 3. La commande

```bash
CUDA_DEVICE_ORDER=PCI_BUS_ID CUDA_VISIBLE_DEVICES=2 \
python MyIA.AI.Notebooks/IIT/ICT-Series/scripts/ict25a_scaleup_grpo.py \
  --model Qwen/Qwen3.5-2B-Base --arm N --seeds 0,1,7,42 --steps 120 \
  --think-close \
  --checkpoint-dir D:/Dev/ict25a_runs/N_2B --save-steps 30 \
  --probe-layer 18 --probe-position last \
  --out D:/Dev/ict25a_runs/N_2B/ict25a_N_2B.json
```

`--think-close` est **obligatoire** pour Qwen3.5 : sans lui, le budget de
completion se consomme dans le bloc `think` (mode no-think du template
chat). La campagne d'echelle 2B l'a utilise (`ict25a-2b-resultats-2b.md`
§commande) ; sa presence ici manquait.

Le `--out` est ecrit dans la **racine persistante** des artefacts, hors de
l'arbre du depot : ce sont des metriques, pas des poids, et les poids ne sont
jamais committes (contrainte de l'issue).

Les deux gardes de la **regie GPU** de la flotte s'appliquent comme toujours
(device 2 de cette machine ; la commande porte elle-meme
`CUDA_DEVICE_ORDER=PCI_BUS_ID` et `CUDA_VISIBLE_DEVICES=2`) ; la racine des
artefacts est un dossier **persistant** (`D:/Dev/…`), jamais `/tmp`.

## 4. Ce que ce run **ne** fait pas

- il ne rend **aucun verdict** sur le panel persona : les regles D1-D4 du §2
  du pre-enregistrement restent seules habilitees a trancher, et elles ne
  s'appliquent qu'a une mesure reelle ;
- il ne franchit **ni Gate 20 ni Gate 21** : la campagne d'echelle 2B a ete
  executee et lue (A1/A2/A4 declenches, cf.
  [`ict25a-2b-resultats-2b.md`](ict25a-2b-resultats-2b.md)) ; ce run fournit
  la **matiere** qui manquait au panel, pas un resultat de panel ;
- il ne remplace **pas** la cellule de lecture de persona du carnet
  ICT-25-InoculationRL : elle reste a ecrire, sur les activations reelles
  qu'un run instrumente produit ;
- les **poids** ne sont **jamais** committes (contrainte de l'issue) : seuls
  le `.npz` d'activations et son manifeste le sont, avec leurs empreintes.

## 5. Ce qui reste, et dans quel ordre

1. **executer** le run instrumente sur le device 2 (garde de charge comprise) ;
2. **commiter** le `.npz` + manifeste par bras et par graine (ou son manifeste
   et ses empreintes si le volume depasse le plafond `scripts/results/`) ;
3. rejouer les **controles** du §3 du pre-enregistrement sur les **vraies**
   series ;
4. ecrire la **cellule de lecture de persona** sur ces activations, et
   l'appliquer aux regles D1-D4.

Les etapes 3 et 4 ne demandent pas de GPU : elles peuvent etre preparees en
attendant que la charge de l'hote passe sous la barre.

## Voir aussi

- [notebook-conventions.md](../../.claude/rules/notebook-conventions.md) ·
  [sota-not-workaround.md](../../.claude/rules/sota-not-workaround.md) ·
  [anti-regression.md](../../.claude/rules/anti-regression.md)
- `MyIA.AI.Notebooks/IIT/ICT-Series/scripts/ict25a_probe_battery.py` (le
  contrat) · `.../scripts/ict25a_scaleup_grpo.py` (le runner) ·
  `.../scripts/tests/test_ict25a_probe_battery.py` (21 tests, CPU, sans torch)
