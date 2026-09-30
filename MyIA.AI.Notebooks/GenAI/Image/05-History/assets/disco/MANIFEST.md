# Manifeste des figures — GenAI/Image/05-History/assets/disco

Artefacts du notebook `05-1-DiscoDiffusion-CLIP-Guided-Diffusion.ipynb`.

> **QA visuelle déléguée (merge-gate)** : ce MANIFEST est rédigé sur la lane `myia-po-2023:CoursIA` (GLM, sans vision). Les champs mécaniques (dimensions PIL, poids octets, métriques CLIP calculées par outil) sont vérifiés par outil ; les champs descriptifs sont des descriptions de provenance — **la vérification visuelle firsthand est déléguée au merge-gate** (ai-01 ou lane CoursIA-2 MiniMax, doctrine vision des figures).

## Contexte commun aux runs DD

- **Moteur** : ré-exécution compacte du cœur DiscoDiffusion (runner local `disco_run.py` documenté dans le notebook) — UNet KL-openai 512×512 pixel-space, checkpoint `512x512_diffusion_uncond_finetune_008100.pt` (= `diffusion.pt` de DD v5), sha256 `9c111ab89e214862b76e1fa6a1b3f1d329b1a88281885943d2cdbe357ad57648` (vérifié contre le manifeste DD v5.7 ; miroir HF `lowlevelware/512x512_diffusion_unconditional_ImageNet` — le blob openaipublic originel renvoie 404).
- **Guidance** : CLIP ViT-L/14 (officiel openai/CLIP), cutouts (2 vues d'ensemble + 8 intérieurs, miroir/grayscale), distance sphérique, conditionnement Song et al. `eps − √(1−ᾱ)·∇`, 100 pas DDIM η=0, skip_frac 0.2, clamp_max 0.15, seed 0.
- **Prompt (tous les runs DD)** : « a beautiful painting of a vast Gothic cathedral in a desert canyon by gustave dore and albert bierstadt, trending on artstation ».
- **GPU** : RTX 3090 locale, ~90 s/image (hors contention). Runs du 18/09/2026, logs conservés dans l'outil local (`outputs_05_1/logs/*.log`).

## hero_gothic.png

- **Source** : run officiel du 18/09/2026, config `clip_gs=5000, sat=0`.
- **Contenu réel vérifié** : PNG 512×512 RGB (723 847 octets, dimensions PIL vérifiées). Métrique pleine-image ViT-L/14 : cos +0.318, dist sphérique 0.7780 (contrôles sans rapport : +0.02 à +0.16). Vérification visuelle déléguée merge-gate.
- **Alt-text (FR)** : Paysage gothique monumental généré par CLIP-guided diffusion — cathédrale dans un canyon désertique, style estampe académique.

## grid_gs2000_sat0.png · grid_gs12000_sat0.png · grid_gs2000_sat2500.png · grid_gs12000_sat2500.png

- **Source** : 4 runs officiels du 18/09/2026, grille `clip_gs ∈ {2000, 12000} × sat ∈ {0, 2500}`, même prompt, même graine (0).
- **Contenu réel vérifié** : PNG 512×512 RGB chacun (463 805 / 500 274 / 456 186 / 724 413 octets). cos pleine-image mesurés : +0.121 / +0.326 / +0.125 / +0.342 — croissant en clip_gs, +sat légèrement positif à forte guidance. Vérification visuelle déléguée merge-gate.
- **Alt-text (FR)** : Grille d'exploration de la guidance CLIP — même prompt et même graine à quatre réglages clip_guidance_scale × sat_scale.

## modern_zimage.png

- **Source** : génération Z-Image (Lumina-Next-SFT) via ComfyUI local (`comfyui-qwen`, endpoint `127.0.0.1:8188` du stack du cours, service mappé dans genai-services.md), workflow `LuminaDiffusersNode`, 30 pas, guidance 4.0, seed 0, 1024×1024, ~120 s (18/09/2026).
- **Contenu réel vérifié** : PNG 1024×1024 RGB (1 817 353 octets). Même prompt que les runs DD. cos pleine-image : +0.318 — égalité remarquable avec le hero DD sur la métrique CLIP. Vérification visuelle déléguée merge-gate.
- **Alt-text (FR)** : Le même prompt gothique rendu par Z-Image en espace latent — contraste pré-SD/post-SD.

## dd_vs_modern.png · grid_guidance.png

- **Source** : extraction directe des `image/png` des outputs d'exécution du notebook 05-1 (cellules « comparaison pré/post-SD » et « grille d'exploration »), exécution finale du 18/09/2026 (kernel python3, papermill).
- **Contenu réel vérifié** : PNG extraits des outputs (1 521 999 / 1 547 774 octets). Vérification visuelle déléguée merge-gate.
- **Alt-text (FR)** : diptyque DD contre Z-Image même prompt ; grille 2×2 de la guidance CLIP.
