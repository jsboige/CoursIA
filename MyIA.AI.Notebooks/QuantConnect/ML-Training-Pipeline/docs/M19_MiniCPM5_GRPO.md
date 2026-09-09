# M19 — Probe GRPO+QLoRA sur DAPO-Math-17k : MiniCPM5-2B vs Qwen3.5-0.8B

Issue #15099 (probe B). Livrable : `scripts/probe_15099_dapo_grpo.py` + résultats
`scripts/results/m19_minicpm5_grpo/`. Verdict : voir `summary.json` (mis à jour à
la fin des runs).

## Objectif

Porter la recette RL post-training de DAPO (GRPO, reward binaire de justesse
mathématique) sur des modèles 2B/0.8B en budget borné RTX 3090, et comparer
honnêtement MiniCPM5-2B à la baseline Qwen3.5-0.8B (même recette, ≥2 seeds).

## Anatomie du dataset (mesurée)

`BytedTsinghua-SIA/DAPO-Math-17k` (l'id `openbmb/...` n'existe pas — 401) :

- 1 791 700 lignes = **17 917 problèmes uniques × 100 répliques** (clé :
  `extra_info.index`) ; le « 17k » désigne les problèmes uniques.
- Colonnes : `data_source` (uniforme `math_dapo`), `prompt` (array chat
  user-only, consigne « step by step... last line `Answer: $X$` »), `ability`
  (MATH), `reward_model` (`{"ground_truth": "34", "style":
  "rule-lighteval/MATH_v2"}`), `extra_info` (uuid).
- Prompt : 259-3430 chars, médiane 455. 2 251 ground truths distincts.

## Environnement (po-2023, RTX 3090)

- venv `D:/Dev/venvs/trl-probe` : torch 2.14 cu126, trl 1.12.0, peft 0.20.0,
  bitsandbytes 0.50.2, transformers 5.16.1, datasets 5.0.1.
- Génération via **HF transformers** (vLLM natif non installable sous Windows —
  leçon probe A) ; GPU ciblé par `CUDA_VISIBLE_DEVICES=0` (ordre fastest-first :
  0 = 3090).
- TRL 1.12 : `max_prompt_length` n'existe plus (filtre données côté script) ;
  `apply_chat_template` retourne un dict en transformers 5.x (`return_dict=True`)
  ; `chat_template_kwargs` propage `enable_thinking` jusqu'à la génération du
  trainer ET au reward.

## Diagnosis pré-training (les écrans empiriques)

| Écran | MiniCPM5-2B | Qwen3.5-0.8B |
|---|---|---|
| thinking, 1024 tok, 8 gens (4 problèmes) | 2/8 émettent `Answer:`, 0/8 correct, truncation ~100 % | non testé (même budget → même mur) |
| non-thinking, 512 tok, 8 gens (4 problèmes) | 0/8 | 0/8 |
| non-thinking, 512 tok, pass@1 sur 50 problèmes eval | **0/50** | **0/50** |

Forensique (générations réelles inspectées) : le matcher est sain (selftest
10/10 : `Answer: $X$`, `\boxed`, fractions `1/2`≡`0.5`, séparateur LaTeX
`{,}`, nombres composés) ; ce sont les problèmes qui sont durs — DAPO a
précisément **curé les problèmes faciles** (curation papier). Géométrie
analytique en chinois, combinatoire de runs de longueur 2014, théorie des
jeux... Un 2B/0.8B non-thinking y est à ~0 % pass@1.

Conséquence pour GRPO : la viabilité ne se joue pas sur pass@1 mais sur la
**variance pass@8** (≥1 succès dans le groupe de 8 générations → avantage
non nul → gradient). Le pilot full-pool le mesure directement : si
`rewards/dapo_reward/mean` reste à 0.000 sur les 25 premiers steps, il n'y a
pas de signal ; sinon la matrice complète (2 modèles × 2 seeds) se justifie.

## Recette (mode non-thinking par défaut)

- GRPOConfig TRL 1.12 : `loss_type="dapo"` (défaut), `epsilon_high=0.28`
  (clip-higher), `beta=0.0` (pas de KL, pas de ref model), `scale_rewards=
  "group"`, `mask_truncated_completions=True`.
- QLoRA : NF4 double-quant, compute bf16, LoRA r=16 α=32 dropout 0.05
  `all-linear`.
- Budget borné (leçon #13596) : `max_steps=100` fixe, `logging_steps=1`,
  sauvegarde uniquement de l'adapter final (hors repo), 32 completions/step
  (4 prompts × 8 générations), `max_completion_length=512`, lr 2e-5 constant
  + warmup 5.
- Mode : `enable_thinking=False` via `chat_template_kwargs` (les deux modèles
  ont le toggle Qwen3-style dans leur `chat_template.jinja` — vérifié sur
  snapshot). Mode `--thinking` (budget 1024) disponible mais mesuré
  incompatible avec le mur de truncation ci-dessus.
- Reward : binaire, `Answer: $X$` → `\boxed` → dernier nombre ; normalisation
  LaTeX (fractions, `{,}`, `%`) + équivalence numérique rel 1e-6.
- Éval : 40 problèmes held-out × 4 générations, pré/post training, seed fixe
  par run. Split train/eval fixe (seed 15099) sur les problèmes uniques.

## Résultats (matrice complète 2 modèles × 2 seeds, 2026-09-08)

Éval held-out : 40 problèmes × 4 générations (160 générations par mesure),
seed fixe par run, reward = matcher binaire. Train : reward par step dans les
JSON de run (`log_history`), courbes dans `curves.png`.

| Run | pre-eval | post-eval | Δ | reward train (10 prem → 10 dern) | longueur train (tok) | wall |
|---|---|---|---|---|---|---|
| MiniCPM5-2B seed0 | 0.0188 | 0.0375 | **+0.0188** | 0.056 → 0.075 | 384 → 383 | 185 min |
| MiniCPM5-2B seed1 | 0.0313 | 0.0563 | **+0.0250** | 0.056 → 0.075 | 384 → 383 | 198 min |
| Qwen3.5-0.8B seed0 | 0.0250 | 0.0250 | 0.0000 | 0.063 → 0.009 | 384 → 384 | 146 min |
| Qwen3.5-0.8B seed1 | 0.0188 | 0.0313 | +0.0125 | 0.053 → 0.047 | 384 → 384 | 144 min |

| Agrégat (2 seeds) | pre moyen | post moyen | Δ moyen ± 1 std |
|---|---|---|---|
| **MiniCPM5-2B** | 0.0250 | 0.0469 | **+0.0219 ± 0.0031** |
| Qwen3.5-0.8B | 0.0219 | 0.0281 | +0.0063 ± 0.0063 |

## Verdict : **BEATS** (trainabilité RL relative)

- MiniCPM5-2B : les DEUX seeds progressent (+88 % d'accuracy relative en
  éval, 0.025 → 0.047), std serré (0.0031), reward train montant, longueur
  stable (aucun effondrement) → courbes saines au sens de l'acceptance.
- Qwen3.5-0.8B : un seed strictement plat, un seed modéré (+0.0125) ;
  reward train plat ou déclinant → apprentissage erratique.
- Intervalles ±1 std disjoints : 0.0219 − 0.0031 = 0.0188 > 0.0063 +
  0.0063 = 0.0125 → **BEATS** au sens de la règle annoncée.

Lecture honnête des limites :
- Les accuracies absolues restent faibles (2-6 %) — DAPO-Math-17k est
  olympiaque pour ces tailles (la curation DAPO retire les problèmes
  faciles). La claim porte sur la **trainabilité relative** (le modèle
  apprend-t-il du signal RL en budget borné), pas sur l'obtention d'un
  modèle math utilisable.
- Qwen3.5-0.8B est 2,5× plus petit (0.8B vs 2B) : baseline désignée par
  l'issue, mais le déséquilibre de capacité joue mécaniquement en faveur de
  MiniCPM5.
- Un reboot a tué le premier qwen35 seed0 pendant sa post-eval (training
  100/100 accompli, JSON perdu) — re-run from scratch ; `save_strategy="no"`
  interdit la reprise, assumé pour le budget disque.
- Génération HF transformers (pas vLLM, indisponible sous Windows) —
  ~75 s/step (2B) et ~55 s/step (0.8B) sur RTX 3090, budget total ~11 h GPU
  pour la matrice.
