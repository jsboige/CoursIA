# Mesure du mur 8 Go — Qwen3-8B en GRPO/QLoRA sur l'étage pionnier (`myia-po-2024`)

**Grain** : DEEP/training, lane `myia-po-2024:CoursIA`. Préalable mesuré de la
nomination de l'étage moyen (#1454, étape 1 : « un lead qui bute sur 8 Go et
monte d'un cran »). Ligne hermes #15294 (close) — extension d'échelle côté
pionnier.

## Question

Le lead hermes GRPO a livré ses gains aux échelles 0.8B et 2B sur l'étage
pionnier (4 seeds chacun, `p15294_hermes_grpo/`, #24747). L'échelle suivante —
**Qwen3-8B** — peut-elle être défrichée sur la RTX 3070 8 Go avec le harnais
de campagne **inchangé** (`probe_15099_dapo_grpo.py`, GRPO/TRL + QLoRA,
32 complétions/step, completion 384) ?

## Mesure

- Commande : `probe_15099_dapo_grpo.py smoke --model qwen3_8b --dataset hermes --seed 0`
  (smoke = 3 steps + éval réduite — le protocole le plus léger du harnais).
- Carte : RTX 3070 Laptop **8 192 Mio**, idle au départ (0 Mio utilisé).
- Poids : cache HF local (`models--Qwen--Qwen3-8B`), **aucun téléchargement**.
- Env : `coursia-ml-training` (torch 2.14.1+cu126, TRL 1.12).
- Sampler : `probe_15099_vram_sampler.py` à 1 Hz — **60 échantillons** couvrant
  l'exécution entière (`vram_8b_grpo_8go.jsonl`).

## Résultat : OOM à la construction du trainer — avant toute génération

| | Valeur |
|---|---|
| Échec | `torch.OutOfMemoryError` dans `GRPOTrainer.__init__` → `from_pretrained` → `caching_allocator_warmup` |
| Tentative d'allocation | **6,80 Gio** (warmup fp16 de l'empreinte du modèle) pour **6,96 Gio libres** |
| Run | terminé à **t+59 s**, `rc=1`, **0 step, 0 génération, 0 évaluation** |
| Pic VRAM série | **123 Mio / 8 192 (1,5 %)** — le modèle n'a jamais résidé sur la carte |

Trace complète : `oom_traceback.txt`. Agrégats dérivés de la série :
`mur8go_aggregats.json` (rien n'est saisi à la main hors les champs texte).

## Lecture — où est le mur

Le contraste avec le probe léger du 2026-09-11
(`GenAI/PostTraining/_measurements/vram_probe_results_2026-09-11_8b.jsonl` :
Qwen3-8B QLoRA **FIT** sur cette même carte, 7,41 Gio alloués, 3 steps)
localise le mur avec précision : ce probe chargeait le modèle **sans** le
chemin TRL (pas de `GRPOTrainer`, pas de warmup d'empreinte complète). Le
harnais de campagne, lui, ne passe pas la construction du trainer.
**L'étage pionnier ne peut pas défricher le 8B** — même en smoke, même avant
la première génération. Les points FIT de #19490 sur 3080 Ti 16 Go
(7,85 → 11,77 Gio pour gen=8, completion 96 → 288) encadrent déjà le
territoire de l'étage moyen ; le protocole plein (gen=32, completion=384)
y est l'étape suivante.

## Ce que cette mesure ne dit pas

Ce n'est pas une mesure de Δ ni un verdict d'entraînabilité : aucun step n'a
tourné. Elle établit uniquement le mur de chargement sur 8 Gio, première main,
avec le harnais de campagne inchangé — le préalable que la nomination de
l'étage moyen (#1454) exigeait.
