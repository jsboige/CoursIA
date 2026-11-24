# Artefacts de run — protocole onset ICT-25

Ce dossier porte les artefacts de mesure des runs d'entraînement de la série ICT.
Un artefact de mesure qui ne dit pas **sous quel régime de troncature** il a été
produit n'est pas relisible : deux bras comparés sous des budgets de complétion
différents ne se comparent pas (#21998). Cette note existe pour que ce régime soit
lisible depuis le dossier, sans avoir à reconstituer la révision du producteur.

## Régime de troncature des artefacts onset

| Artefact | Modèle | Graines | Pas | `max_completion_length` déclaré |
|---|---|---|---|---|
| `onset_qwen35_2b_base.json` | `Qwen/Qwen3.5-2B-Base` | 0, 1, 42 | 120 | absent — **80** (voir ci-dessous) |
| `onset_qwen35_9b_base.json` | `Qwen/Qwen3.5-9B-Base` | 0, 1, 42, 7 | 120 | absent — **80** (voir ci-dessous) |
| `onset_qwen35_9b_base_merged.json` | `Qwen/Qwen3.5-9B-Base` | 0, 1, 2, 3 | 120 | absent — **80** (voir ci-dessous) |

Aucun de ces trois fichiers ne porte la clé `max_completion_length`, et aucun ne
porte la clé `script` : ils précèdent tous le schéma de `ict/onset_artifact.py`.

## Pourquoi le cap vaut 80, et non 1024

Le schéma actuel pose `DEFAULT_MAX_COMPLETION_LENGTH = 1024`, qui est le régime des
artefacts `ict25_*` de la série. Il ne s'applique **pas** à ces trois fichiers.

`ict/onset_runner.py`, depuis sa création (`746809380085`, 2026-09-29) jusqu'au
commit `2bb204174ead` (2026-10-26), passait `max_completion_length=80` **en dur**
à `GRPOConfig`, sans option de ligne de commande pour le changer (`--model`,
`--seeds`, `--max-steps`, `--lr`, `--num-gen` seulement). Le cap 80 est le régime
que #13596 a mesuré comme tronquant systématiquement (EOS en butée sur toute la
trajectoire, masque de troncature actif). Un artefact produit par cette révision
a donc tourné sous 80 — c'est une lecture de la révision du producteur, pas une
hypothèse sur l'intention de l'auteur du run.

Le schéma qui rend le budget lisible (`script`, `max_completion_length` au niveau
de l'artefact et dans chaque résultat de graine) date de `ad2b817535a6`, mergé en
`9ab5eed36a4b` le 2026-10-26. Les runs postérieurs le portent.

## Campagne 2B (Gates 20-21, `Qwen/Qwen3.5-2B-Base`)

| Artefact | Bras | Graines | Pas | `max_completion_length` declare |
|---|---|---|---|---|
| `ict25a_N_2B.json` | N | 0, 1, 7, 42 | 120 | 80 (`protocol`) |
| `ict25a_Np_2B.json` | Np | 0, 1, 7, 42 | 120 | 80 (`protocol`) |
| `ict25a_N_2B.rewardspy_audit.json` | N | 0, 1, 7, 42 | — | fenetres `head` et `tail` traitees separement |
| `ict25a_Np_2B.rewardspy_audit.json` | Np | 0, 1, 7, 42 | — | idem |
| `ict25a_N_2B.rewardspy_audit_head.json` | N | 0, 1, 7, 42 | — | fenetre `head` seule (comparaison homogene) |
| `ict25a_Np_2B.rewardspy_audit_head.json` | Np | 0, 1, 7, 42 | — | idem |

Ces six fichiers sont produits par la campagne 2B du 2026-11-20 (device : GPU 2
de `myia-ai-01`). La lecture des criteres scelles (C1, C2, A1, A2, A4) est dans
[`docs/ict/ict25a-2b-resultats-2b.md`](../../../../docs/ict/ict25a-2b-resultats-2b.md).

**Une asymetrie d'echantillon, a lire avant de comparer les audits :** les
graines 7 et 42 du bras `Np` portent leurs 240 enregistrements dans
`records_sample` et **rien** dans `records_sample_tail`, alors que les quatre
graines du bras `N` portent 64 en tete et 64 en queue. L'ecriture de
l'artefact n'est donc pas symetrique entre les bras : les audits `head` seuls
sont la comparaison homogene graine par graine.

## Controle intra-famille 0.8B (`Qwen/Qwen3.5-0.8B`)

| Artefact | Bras | Graines | Pas | `max_completion_length` declare |
|---|---|---|---|---|
| `ict25a_N_0.8B.json` | N | 0, 1, 7, 42 | 120 | 80 (`protocol`) |
| `ict25a_Np_0.8B.json` | Np | 0, 1, 7, 42 | 120 | 80 (`protocol`) |
| `ict25a_N_0.8B.rewardspy_audit.json` | N | 0, 1, 7, 42 | — | fenetres `head` et `tail` |
| `ict25a_Np_0.8B.rewardspy_audit.json` | Np | 0, 1, 7, 42 | — | idem |
| `ict25a_N_0.8B.rewardspy_audit_head.json` | N | 0, 1, 7, 42 | — | fenetre `head` seule |
| `ict25a_Np_0.8B.rewardspy_audit_head.json` | Np | 0, 1, 7, 42 | — | idem |

Controle intra-famille scelle du pre-enregistrement (sections 2 et 6) : meme
famille que la campagne 2B, meme protocole (4 graines, 120 pas, cap 80), device
GPU 2 de `myia-ai-01`, campagne du 2026-11-20. Contrairement aux artefacts 2B,
l'ecriture est **symetrique** sur ce controle : chaque graine des deux bras
porte 64 enregistrements en tete et 64 en queue -- la comparaison `both` y est
homogene, en plus de la comparaison `head`.

Le controle rejoint la conclusion de la campagne : les bras divergent deja a
0.8B (fenetre `head` : `N` rend `PAS_DE_DOMINANCE` sur 3 graines sur 4, `Np`
n'a aucun verdict dominant) -- la divergence constatee a 2B n'est pas
emergente d'echelle.

## Ce que ces artefacts ne disent pas

La révision exacte du producteur (`git_commit`) n'est pas enregistrée par cette
version du runner : elle ne peut donc pas être citée graine par graine. Ce qui est
établi, et qui suffit à lire le régime de troncature, est la borne supérieure :
toute révision antérieure à `ad2b817535a6` produit des artefacts sans la clé, et
toutes fixent le cap à 80.

La lecture des résultats doit donc rester ce qu'elle est dans le corps de la PR :
un **verdict de tracking**, pas une comparaison de performance entre bras ou entre
modèles sous des caps différents.
