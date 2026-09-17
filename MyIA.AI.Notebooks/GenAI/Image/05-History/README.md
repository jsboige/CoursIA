# 05-History — Racines pré-Stable-Diffusion

> **Argument pédagogique.** Ce rayon existe parce que la série GenAI/Image a accumulé une couverture exhaustive des modèles **postérieurs à août 2022** (DALL-E 3, GPT-5, SD XL/3.5, FLUX, Z-Image, Krea 2, Bonsai), mais qu'aucun notebook ne documente la **génération d'images d'avant** : la CLIP-guided diffusion en espace pixel (512×512), sans encodeur de texte dédié ni espace latent. La demande user du 17/09 2026 (« deux références pré-Stable-Diffusion qui me sont chères ») a déclenché la création du rayon. Les notebooks 01-04 conservent leur numérotation d'origine ; le rayon 05 est isolé numériquement pour signaler qu'il n'est pas un niveau « plus avancé », mais un **regard en arrière** sur la généalogie.

## Structure

```
05-History/
├── README.md                          # Ce fichier
├── 05-1-DiscoDiffusion-CLIP-Guided-Diffusion.ipynb            # DDIM + CLIP cutouts (UNet pixel-space 512×512) — #16477
├── 05-1-DiscoDiffusion-CLIP-Guided-Diffusion_output.ipynb     # Output Papermill (généré c.607)
├── 05-2-CLIPasso-Semantic-Sketching.ipynb                      # Esquisse sémantique par CLIP — #16478
├── assets/clipasso/                                              # figures de 05-2
└── (futurs : DALL-E 1 / GLIDE / Imagen 1 / etc. — non livrés)
```

## Notebooks

### 05-1 — DiscoDiffusion : la CLIP-guided diffusion pré-Stable-Diffusion

Notebook rétrospectif qui **ré-exécute réellement** le pipeline DD (UNet KL-openai 512×512 + CLIP ViT-B/32, ~100 steps DDIM + guidance CLIP par cutouts). Livré en réponse à l'issue #16477.

**Pourquoi ce notebook, maintenant ?**
- Combler le **trou généalogique** identifié à la review du 17/09.
- Permettre aux étudiants de reconnaître le **look DD** (paysages monumentaux gothiques, architectures illisibles, granularité « brushed ») à partir d'une *vraie* exécution locale, pas de captures d'écran d'époque.
- Montrer **comparativement** ce que l'espace latent de SD a changé (2022).

### 05-2 — CLIPasso : le sketching sémantique par CLIP

Notebook rétrospectif sur l'esquisse paramétrique à nombre de traits contrôlé (32/16/8/4). Livré en réponse à l'issue #16478 (#16595).

**Pourquoi ce notebook, maintenant ?**
- Le **versant géométrique** de la même année 2022 : là où DD explore l'espace pixel, CLIPasso réduit l'image à un petit nombre de Béziers guidés par CLIP.
- Permet la comparaison directe `DD (densité pixel) ↔ CLIPasso (densité traits)` dans le même rayon.

## Conformité

- **Tell c.C.1** : 0 `raise NotImplementedError` / `assert False` / `1/0` dans les cellules code exécutables (vérifié `c.606`).
- **Tell c.C.2** : notebook committé AVEC outputs (à exécuter Papermill c.607 — RTX 3090 dispo).
- **Tell c.H.3** : pre-commit refuse un `execution_count: None` (à vérifier post-Papermill c.607).
- **Tell c.sota-not-workaround §Prong A** : vrai outil SOTA (UNet `diffusion.pt` HF + CLIP ViT-B/32 HF), verdict `SOTA-OK` réel sur RTX 3090.
- **Tell c.notebook-accretion-numbering** : numéro `05-1` suit le pattern canonique `XX-N` des rayons existants, isolant le rayon en queue de numérotation pour signaler le statut *historique*.

## Bibliographie rangée au gisement GDrive

| Référence | Statut c.606 |
|---|---|
| Dhariwal, P. & Nichol, A. (2021). *Diffusion Models Beat GANs on Image Synthesis*. NeurIPS. | **À télécharger** au cycle c.607 |
| Radford, A. et al. (2021). *Learning Transferable Visual Models From Natural Language Supervision (CLIP)*. ICML. | **À télécharger** au cycle c.607 |
| Rombach, R. et al. (2022). *High-Resolution Image Synthesis with Latent Diffusion Models*. CVPR. | **Déjà présent** (`2022 - High-Resolution Image Synthesis with Latent Diffusion Models.pdf`) |

Nomenclature GDrive : `G:\Mon Drive\MyIA\IA\Bibliographie IA\MachineLearning\` — `YYYY - Auteur(s) - Titre.pdf` (Tell c.bibliography-hygiene).
