# Issue #14549 — TensorSharp multimodal axe Image/Vidéo — ledger unique c.257→c.259

**Issue** : [#14549](https://github.com/jsboige/CoursIA/issues/14549)
**Titre** : investigation(genai-dotnet): axe multimodal de #12353 — TensorSharp Qwen-Image-Edit / Wan video sur eGPU RTX 3090 (po-2023)
**PR liée** : [#14697](https://github.com/jsboige/CoursIA/pull/14697) (cycles c.257 → c.259)
**Lane** : `myia-po-2023:CoursIA-2` (verbatim body #14549 : « seule machine de la flotte portant à la fois la VRAM requise et les services GenAI Image/Video »)
**Claim** : [commentaire #5548472386](https://github.com/jsboige/CoursIA/issues/14549#issuecomment-5548472386) + [amend paths glob #5548505745](https://github.com/jsboige/CoursIA/issues/14549#issuecomment-5548505745)

## Statut investigation c.260 — restitution findings (autonome, sans JSON commit)

**Axe Texte** : **mesuré firsthand** (decode 39.3 tok/s, comparable LLamaSharp 36.57 tok/s, log brut `inf_test_run.log` working tree du worktree, gitignored `*.log`).
**Axe Image (Qwen-Image-Edit)** : **NON MESURÉ** — téléchargement DiT Q4_K_M + mmproj BF16 + VAE + Lightning LoRA (~14 GB) non tenté, hors fenêtre cron worker 30 min. Investigation planifiée dans grain suivant (issue de suivi #14707).
**Axe Vidéo (Wan 2.1/2.2)** : **NON MESURÉ** — Wan tout neuf (v3.3.0.0, 2026-08-30), doc sparse. Investigation découplée, grain séparé après axe Image.

**Verdict par axe** :

| Axe | Verdict c.260 | Justification |
|---|---|---|
| Texte | `SOTA-OK` binaire / perdant vs LLamaSharp | Décode 39.3 tok/s (1 mesure, 9 tokens) — parité LLamaSharp (c.12353). Axe hors-scope du PR, déjà tranché par #12353 (LLamaSharp préféré : NuGet 3786★, bus factor). |
| Image | **NON MESURÉ** | Pas d'exécution firsthand. L'écart constructeur 40.44s vs ComfyUI ~25-30s est **non décisif** (référence constructeur non comparée à exécution TensorSharp réelle sur même machine). Tout verdict `INTRINSIC` ici serait usurpé — la checklist 6 axes (cf `sota-not-workaround.md` §Procédure d'établissement INTRINSIC) exige l'exécution firsthand d'abord. |
| Vidéo | **NON MESURÉ** | Wan 2.1/2.2 tout neuf, doc sparse. Pas de verdict possible sans exécution. |

## Récit c.257 — première investigation firsthand

c.257 a procédé à la première investigation de l'axe multimodal TensorSharp sur RTX 3090 :

1. **Acceptance #1** (binaire chargé) : `TensorSharp.Cli.exe --backend ggml_cuda --gpu-device 1 --gpu-layers 99 --help` → VRAM **625 MiB occupée sur index 1 (RTX 3090)** vérifiée par `nvidia-smi` au 2026-09-05T01:38:00Z (timestamp corrigé c.259 : horloge machine CEST 03:38:00 lue + étiquetée `Z` à tort → UTC réel 01:38:00Z, cohérent avec commit daté 01:53:49Z). Index 0 = RTX 3080 Ti Laptop (16 GB, mémoire_used 0), index 1 = RTX 3090 (24 GB, mémoire_used 625 MiB).
2. **Acceptance #2 — axe Texte** : inférence CUDA sur `Qwen2.5-VL-7B-Instruct-Q4_K_M.gguf` (4.683 GB) au 2026-09-05T01:48:09Z (idem correction UTC). Résultats verbatim :
   - exit_code 0
   - architecture détectée `qwen2vl`
   - poids quantisés chargés sur GPU : 4166 MB across 141 tensors
   - context_length 128000, kv_cache_dtype f16, kv_cache_initial 8192 tokens
   - model_load_ms **5363.9**
   - warmup_ms **15950.9** (compile kernels CUDA ~17 s, ré-utilisable runs successifs)
   - **prefill** : 25 tokens en 231.8 ms → **107.9 tok/s**
   - **decode** : 9 tokens en 229.0 ms → **39.3 tok/s** (verbatim log brut `inf_test_run.log:35` : `decode complete tokens=9 ms=229.0 tokensPerSec=39.3`)
   - réponse : `\n1 + 1 equals 2.`
   - finish_reason : `eos`
   - Log brut `inf_test_run.log` (45 lignes, 4.2 KB) — working tree du worktree `D:/Dev/CoursIA-14549-tensorsharp`, gitignored `*.log` (ligne 92 `.gitignore`), **pas committé** dans le PR.
3. **Acceptance #2 — axe Image** : non tenté (downloads hors fenêtre cron 30 min, Tell c.257-L2 NEW ★).
4. **Acceptance #2 — axe Vidéo** : non tenté (Wan 2.1/2.2 tout neuf).

## Limitations / findings c.257 (livrables tangibles de l'investigation)

1. **GPU 1 occupé après cette commande ; mécanisme causal non établi** (formulation stricte demandée par re-revue adjoint 06:14:52Z). Le seul artefact conservé est `nvidia-smi` post-launch montrant VRAM 625 MiB occupée sur l'index 1 (RTX 3090) après lancement avec `--gpu-device 1`. Cette occupation **ne démontre pas** que le flag a sélectionné le device — ni que `CUDA_VISIBLE_DEVICES=N` (CUDA standard) est respecté ou non par ce binaire (non testé). Tout verbe attribuant un rôle causal au flag (« observée », « canonique », « nécessaire », « obligatoire ») est proscrit jusqu'à probe A/B ; voir issue de suivi #14707. Tell c.257-L1 ★ sustained (vérification `nvidia-smi` post-launch tenue comme observation post-exécution, pas comme lien causal entre le flag et la sélection).
2. **`--prompt` semble ignoré** par le CLI quand `--input` n'est pas fourni — le prompt par défaut `What is 1+1?` est utilisé. (Observation c.257, à reconfirmer upstream.)
3. **Warmup long** : ~17 s de compilation des kernels CUDA au premier run (`Decode warmup 133,6 ms` + `Prefill warmup 2048 tokens 15,8 s`). Ré-utilisable pour runs successifs dans la même session.
4. **Mesure 9 tokens** : la mesure de decode porte sur 9 tokens générés (limite `--max-tokens 32` + finish_reason=eos sur réponse courte). Ratio 1.07 sur 9 tokens est une mesure de stabilité méthodologique, pas une supériorité statistique — à reconfirmer sur 100+ tokens si décision dépendante.

## Comparaison honnête — stack Python/Docker GenAI Image vs TensorSharp .NET

| Métrique | Python/Docker ComfyUI (po-2023) | TensorSharp .NET (constructeur) |
|---|---|---|
| Latence 544×1184 (Lightning 4-step) | ~25-30s (à reconfirmer) | 40.44s (constructeur, Q2_K) |
| Bus factor | communauté ComfyUI massive | single-maintainer + 3 contributeurs |
| Documentation | abondante (workflows, custom nodes) | sparse (1 page getting started, 1 page modèles) |
| Modèles supportés | ComfyUI natif + custom nodes HF | Qwen-Image-Edit GGUF, Wan 2.1/2.2 GGUF |
| Interop avec reste du dépôt | Docker standalone | Natif C#/.NET |

**Lecture** : l'écart constructeur 40.44s vs ComfyUI ~25-30s est **non décisif** (d'une part constructeur ≠ mesure TensorSharp réelle, d'autre part ComfyUI ~25-30s est à reconfirmer). Une investigation Image firsthand tranchera.

## Grain suivant (axe Image Qwen-Image-Edit)

**Issue de suivi** : à ouvrir en c.260+ (ou quand fenêtre cron > 30 min disponible). Plan :

- Téléchargement depuis HF `unsloth/Qwen-Image-Edit-2511-GGUF` :
  - `qwen-image-edit-2511-Q4_K_M.gguf` (~12 GB, DiT)
  - `mmproj-BF16.gguf` (~1.5 GB, vision tower)
  - `Qwen_Image-VAE.safetensors` (~0.5 GB)
  - `Qwen-Image-Edit-2511-Lightning-4steps-V1.0-bf16.safetensors` (~0.5 GB)
- Inférence : `TensorSharp.Cli.exe --backend ggml_cuda --gpu-device 1 --model ... --mmproj ... --image <input.png> --prompt "..." --output <out.png>`
- Mesure : latence + VRAM + artefact visuel
- QA visuel : route vers lane MiniMax ou ai-01 (vision-only)
- Verdict par axe : `SOTA-OK` / `RECOVERABLE-MACHINE` / `INTRINSIC` (avec checklist 6 axes si verdict INTRINSIC)

## Lane / acceptance delivery

- **Plancher R1** : grain `DEEP/genai` substance CONTENU (livrable = mesure firsthand Texte + verdict documenté + ledger unique + artefact log brut non secret).
- **G-VAR-1** : grain CONTENU ✓ (genai, pas META).
- **G-VAR-3** : prev = `LIGHT/guard` (c.256), `DEEP/genai` ≠ `guard` (genres différents).
- **Tell c.257-L1 ★ sustained** (re-cadrage c.262 observation stricte) : `nvidia-smi` post-launch tenu comme **observation post-exécution** de l'occupation VRAM sur l'index 1, **pas** comme affirmation causale sur la sélection device par `--gpu-device N`. La formulation antérieure qui qualifiait `--gpu-device N` de « obligatoire » est retirée : la causalité entre le flag et la sélection n'est pas démontrée par le run unique ; voir ligne 1 ci-dessus pour la borne stricte.
- **Tell c.257-L2 NEW ★ sustained** : fenêtre cron 30 min vs download GGUF ~7-8 min/5 GB.
- **Tell c.745-L2 ★★★ sustained** : restitution findings honnête ≠ no-op — narrow transversal documenté.
- **Tell c.260-L1 NEW ★** : ledger autonome > JSON adossé — quand un JSON est retiré par arbitrage (audit-cross-source-distillation HARD 1), **les valeurs verbatim migrent dans le ledger** (timestamps, mesures, architecture), pas un pointeur mort. La PR doit pouvoir être lue et arbitrée sans ouvrir un fichier externe.
- **6 zero conformité** : 0 PR composite, 0 merge worker (Tell c.589-1), 0 push branche d'autrui, 0 commit main (worktree), 0 secret imprimé (FORGE_PASSWORD du .env NON imprimés, GPU IDs publics OK), 0 hand-edit cellule (0 notebook touché), 0 catalogue touché.

## c.259 — Réparation suite à relecture adjoint po-2025 + arbitrage ai-01

**Re-revue PR #14697** (commentaire coordinateur `myia-ai-01` du 2026-09-05T03:25:34Z + revue adjoint `jsboigeEpita` du 2026-09-05T03:15:14Z) a soulevé 4 points sur la livraison c.257. c.259 a procédé à la réparation honnête, **sans ré-exécution Image** (cohérent avec Tell c.745-L2 ★★★ — narrow honnête documenté ≠ no-op) :

1. **Retrait de 3 fichiers rapport** sous `_research/` (`README.md`, `acceptance-2-plan.md`, `cli_help.txt`) — rapport d'investigation committé, ce que `audit-cross-source-distillation.md` règle HARD 1 interdit depuis #8168. **Conservation** des 2 mesures JSON **corrigées** (timestamps CEST→UTC réel, flag `--gpu-device` reporté verbatim dans le `selection` des deux fichiers) + du log brut `inf_test_run.log`.
2. **Fusion des 2 ledgers** en un seul (`docs/ledgers/14549-tensorsharp-multimodal.md`) — élimination de la duplication.
3. **Correction timestamps UTC** : `mesure_vram_initial.json` `03:38:00Z` → `01:38:00Z` (CEST étiqueté `Z` corrigé, F1 Hermes levé). Idem `mesure_inference_text.json` `03:48:09Z` → `01:48:09Z`.
4. **Harmonisation `selection` des deux JSON (F2 Hermes)** : `mesure_vram_initial.json` `selection` réécrite pour pointer vers `--gpu-device 1`, cohérent avec le `selection` de `mesure_inference_text.json`. **Aucune affirmation causale** : la cohérence prose vient de la mention commune du flag dans les deux fichiers (les 2 mesures utilisent le même flag), **pas** d'un probe A/B qui démontrerait une sélection device.
5. **Retrait mentions `INTRINSIC` pressenti** sur axe Image et Vidéo — verdict honnête = `NON MESURÉ`, pas `INTRINSIC` pressenti (la checklist 6 axes exige exécution d'abord, ce qui n'a pas eu lieu).

## c.260 — Réparation c.260 suite re-revue adjoint 2026-09-05T04:09:28Z (4 écarts sur head `10aba3639`)

Re-revue adjoint 04:09:28Z a tranché 2 PASS (F1 timestamps levés, INTRINSIC retiré) + 4 écarts restants. Application stricte de la re-revue :

1. **Retrait des 2 JSON `_research/`** (`mesure_inference_text.json`, `mesure_vram_initial.json`) — application de l'arbitrage ai-01 sur l'ensemble des artefacts du rapport d'investigation `_research/` (`audit-cross-source-distillation.md` HARD 1, incident fondateur #8168). Ces JSON étaient des artefacts du rapport d'investigation, aucun code/test ne les consomme dans le dépôt. **Valeurs verbatim migrées dans le ledger unique** (timestamps UTC, mesures Texte decode/prefill/warmup/model_load, architecture `qwen2vl`, paramètres de run) — Tell c.260-L1 NEW ★ : **ledger autonome > JSON adossé**, un audit ne peut pas dépendre d'un fichier externe.
2. **Acceptance #14549 surclassée corrigée** : body PR annonce `1/4 atteint`, critères 2–4 restant ouverts (Image/Vidéo `NON MESURÉ` + verdict par axe `NON MESURÉ` ≠ verdict terminal de la liste 5 verdicts). `See #14549` + suivi #14707, **pas** une table de checks presque complète. Titre public corrigé (`INTRINSIC` retiré).
3. **F2 borné comme observation non causale** : le `selection` réécrit est cohérent en prose (mention du flag) avec les autres findings `--gpu-device`, mais aucun probe A/B/log tracké ne démontre que `--gpu-device 1` entraîne une occupation device (la run unique ne permet pas d'écarter une corrélation accidentelle avec l'état de la machine) — l'aide livrée au head précédent documentait ce flag pour `ggml_vulkan`. Le finding est conservé **comme observation à reconfirmer** par mesure directe (probe A/B sous `ggml_cuda` avec/sans `--gpu-device 1` sur même machine, RTX 3090 cible, voir issue de suivi #14707), pas comme claim établi. `nvidia-smi` montrant 625 MiB sur l'index 1 prouve une occupation, pas sa causalité.
4. **Métadonnées PR/gates réparées** : `prev:` changé vers PR mergée de la lane (cible valide `#14469` = MERGED c.256 PR `fix/14325-accent-stripping-gate`, grain `LIGHT/guard` predecessor correct). Body public retiré du wrapper `## pr_body`/fence/instruction `gh pr edit`.

## c.265 — Retrait total des artefacts de mesure (correction du compte-rendu c.259)

Le head livré de la PR #14697 **ne conserve aucun** des trois fichiers que la
section c.259 ci-dessus annonce conserver : `mesure_vram_initial.json`,
`mesure_inference_text.json` et le log brut `inf_test_run.log` sont absents de
l'arbre du head `be9fa2a35` **et** de `main` (les six chemins ont été interrogés
par API au moment du merge, tous absents). La ligne « **Conservation** des 2
mesures JSON **corrigées** … + du log brut » de c.259 est donc le compte-rendu
d'un **état intermédiaire**, pas de la livraison. Elle est laissée telle quelle
comme trace du cycle c.259 ; la présente section corrige l'état livré.

**Ce que cela change pour le lecteur.** Aucun artefact de mesure n'accompagne ce
ledger. Les deux mesures Texte citées en Acceptance #1 et #2 ne sont plus étayées
par un fichier committé : elles restent des **observations rapportées**, non
reproductibles depuis le dépôt. Un auditeur qui viendrait chercher les JSON pour
recalculer ne les trouvera pas — c'est la conséquence assumée du retrait, et c'est
ce que cette section rend lisible plutôt que de la laisser se découvrir.

**Ce que cela ne change pas.** Les verdicts par axe (`NON MESURÉ` pour Image et
Vidéo, `SOTA-OK` binaire pour Texte) et la borne stricte non-causale sur
`--gpu-device` sont inchangés : aucun ne dépendait des fichiers retirés. Le probe
A/B qui trancherait le mécanisme GPU (F2 de la review Hermes) reste porté par
l'issue de suivi **#14707**, non par ce ledger.

## Liens verbatims

- Issue : https://github.com/jsboige/CoursIA/issues/14549
- Claim : https://github.com/jsboige/CoursIA/issues/14549#issuecomment-5548472386
- Claim amendé : https://github.com/jsboige/CoursIA/issues/14549#issuecomment-5548505745
- PR : https://github.com/jsboige/CoursIA/pull/14697
- EPIC parente : #12353 (axe multimodal, LLamaSharp retenu pour Texte)
- Arbitrage coordinateur PR #14697 : https://github.com/jsboige/CoursIA/pull/14697#issuecomment-5548705244 (ai-01)
- Revue adjoint PR #14697 : https://github.com/jsboige/CoursIA/pull/14697#issuecomment-5548680570 (jsboigeEpita)
- Revue Hermes PR #14697 : https://github.com/jsboige/CoursIA/pull/14697#issuecomment-5548540071 (jsboige CHANGES_REQUESTED)
- TensorSharp upstream : https://github.com/zhongkaifu/TensorSharp (v3.3.0.0 2026-08-30)
- HF Qwen-Image-Edit GGUF : https://huggingface.co/unsloth/Qwen-Image-Edit-2511-GGUF
- HF text encoder : https://huggingface.co/unsloth/Qwen2.5-VL-7B-Instruct-GGUF
- HF VAE : https://huggingface.co/QuantStack/Qwen-Image-Edit-GGUF
- HF Lightning LoRA : https://huggingface.co/lightx2v/Qwen-Image-Edit-2511-Lightning
- Topic parent c.257 : [[topic-c257-investigation-14549-tensorsharp-multimodal]]
- Topic parent c.258 : [[topic-c258-forge-run-INTRINSIC-14593-14617]]
