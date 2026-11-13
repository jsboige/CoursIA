# PAN 2 — modèle du monde et raisonnement simulatif (distillation sourcée)

> Distillation de la **technique** PAN 2 (Institute of Foundation Models, MBZUAI) dans les
> séries GenAI : le modèle est un **paramètre d'exécution**, pas un objet reproduit ici.
> Première application de la reorga des titres.
>
> **Grain** : #25846 · `Part of #25845` (EPIC reorga des titres) · parent série : GenAI.
> **Règle** [[bibliography-hygiene]] : les attributions au papier s'écrivent depuis la copie
> archivée, lue avant rédaction (voir §Sources).

## Sources (lues et archivées)

| Source | Contenu | Statut |
|---|---|---|
| **Article** — Xing, Deng, Hou, *Critique of World Model* (arXiv 2507.05169, juin 2026) | Formalisation GLP : thèse, 5 dimensions, architecture, instanciation PAN | **lu à la copie archivée** : `G:\Mon Drive\MyIA\IA\Bibliographie IA\AI\2026 - Xing Deng Hou - Critique of World Model (arXiv 2507.05169).pdf` (34 p.) |
| `https://huggingface.co/IFM/PAN2` | Model card : architecture, checkpoints, usage, benchmarks | **lue (fetch direct)** — vérifiée firsthand le 12/11 |
| `https://recipes.vllm.ai/IFM/PAN2` | Recette vLLM officielle (config de service) | **lue (fetch direct)** — vérifiée firsthand le 12/11 |
| `https://github.com/ifm-ai/PAN2` | README : training (FSDP2, Muon, context parallelism), inference, prompt-rewriter | lue par la lane de création de l'issue |
| `https://ifm.ai/blog/pan2/` | Blog d'annonce | 403 au robot ; contourné par model card + README |

---

## 1. La thèse : un modèle du monde est un simulateur de possibilités actionnables

Le papier ouvre sur *Dune* (le **Kwisatz Haderach**, qui « simule les issues de tous les
plans possibles pour tracer la meilleure voie ») et sur la notion de **hypothetical
thinking** de la littérature en psychologie. Sa thèse, en une phrase (Abstract, p. 1) :

> le but premier d'un modèle du monde est de **simuler toutes les possibilités actionnables
> du monde réel, pour un raisonnement et une action finalisés**.

Opérationnellement, un **World Model (WM)** est un modèle génératif qui, à l'état du monde
précédent $s$ et une action $a$, prédit/simule l'état suivant $s'$ par une transformation —
une distribution conditionnelle (Éq. 1, p. 2) :

$$s' \sim p(s' \mid s, a)$$

Le point de vue porteur, qui traverse tout le papier (p. 2) : un modèle du monde est
**fondateurement un simulateur, pas un générateur de contenu visuel** — c'est le substrat du
**raisonnement simulatif**, la capacité d'incarner mentalement des scénarios hypothétiques
(physiques, sociaux, stratégiques, abstraits) au service d'une décision finalisée.

## 2. Les cinq dimensions de design

Le papier structure l'examen du paysage autour de **cinq dimensions** (p. 2–3), et y place la
position GLP :

| Dimension | Question | Position GLP / PAN |
|---|---|---|
| **Data** | quelles données portent l'information voulue du monde ? | toutes les modalités d'expérience ; **densité d'information**, pas seulement le volume (§4.1) |
| **Representation** | quel espace latent pour l'état du monde ? | **mixte continu + discret**, hiérarchique, à plusieurs niveaux (§4.2) |
| **Architecture** | comment raisonner sur les représentations ? | **GLP** : bottleneck génératif + backbone LLM + prédicteur diffusion (§4.3) |
| **Objective** | quel objectif guide l'entraînement ? | **perte générative ancrée dans les données d'observation** (espace données, pas seulement latent) (§4.4) |
| **Usage** | comment le WM entre-t-il dans un système décisionnel ? | **simuler l'expérience pour entraîner des agents par RL** (§4.5) |

## 3. L'architecture GLP (Generative Latent Prediction)

### 3.1 Deux approches concurrentes (§4.3.1)

- **Encoder-décodeur** (Genie 2, NVIDIA Cosmos) : privilégie la **validation** — prédit
  directement l'observation suivante $o'$ à partir de $o$ et $a$, en **boucle fermée**
  (les prédictions sont confrontées aux données observables).
- **JEPA** : privilégie l'**abstraction** — design encodeur-encodeur, non autoregressif et
  non génératif, qui prédit l'état latent suivant directement, en **boucle ouverte**
  (sans reconstruire l'observation).

### 3.2 Le reproche à JEPA — et le rôle du décodeur comme diagnostic

JEPA définit deux opérateurs : $\hat s = h(o)$ (encodeur) et $\hat s' = f(\hat s, a)$
(modèle du monde). Leur application récursive est **fonctionnellement autoregressive et
générative**, bien qu'il n'y ait pas de décodeur probabiliste explicite. Plus précisément,
JEPA spécifie une **distribution conditionnelle dégénérée** (p. 12) :

$$p_f(\hat s' \mid \hat s, a) = \delta(\hat s' - f(\hat s, a))$$

où $\delta(\cdot)$ est une masse de Dirac centrée sur la prédiction déterministe. JEPA n'est
donc **pas générative au sens probabiliste** (il ne modélise pas l'incertitude), mais l'est
**au sens fonctionnel** (il simule récursivement l'évolution latente) — et subit les mêmes
problèmes que les modèles autoregressifs.

Le défaut structurel central (p. 13) : l'encodeur $h$ de JEPA est **délibérément perdant et
non inversible** — il jette l'information jugée non pertinente. **Si cet encodeur jette
l'information qui compte pour la dynamique prédite, le modèle du monde apprend les
transitions dans un espace d'état mal formé, et « aucune sophistication du prédicteur ne
peut récupérer ce qui a été jeté ».** Un encodeur perdant non inversible ne peut produire une
représentation **stateful** (une statistique suffisante de la dynamique).

C'est ici que la boucle fermée générative apporte un **mécanisme de diagnostic intégré** :
*si le décodeur ne peut reconstruire l'observation suivante à partir de l'état prédit,
l'encodeur était trop perdant.* Le décodeur sert donc non seulement de module de génération
mais **d'outil de diagnostic qui maintient en permanence la pression pour que la
représentation conserve toute l'information dynamiquement pertinente** (p. 13).

### 3.3 GLP comme synthèse — trois niveaux (§4.3.3)

Plutôt qu'abandonner le modèle génératif pour fuir la variabilité du signal, GLP adopte
l'**abstraction hiérarchique** : un **Encoder** $h$ et un **Decoder** $g$ forment un
**bottleneck génératif** qui ancre les prédictions dans les données observables, plus un
**Latent Reasoning Backbone** $f$ composé d'un **LLM enrichi** (raisonnement discret
conceptuel) et d'un **prédicteur de next-embedding par diffusion** (dynamique perceptuelle
continue). Le problème est décomposé en **plusieurs niveaux de prédiction latente** :

| Niveau | Mécanisme | Ce qu'il gère |
|---|---|---|
| **bas** | prédicteurs de **next-embedding** (diffusion latente) | stochastique et fine-grain des données perceptuelles continues (pixels, audio, proprioception) |
| **intermédiaire** | prédicteur de **next-token** (décodeur Transformer autoregressif) sur tokens modaux discrets (encodeurs type VQ-VAE) | structure symbolique et compositionnelle |
| **haut** | **LLM** opérant dans un « thought space » de tokens langue | planification long-horizon, simulation mentale, raisonnement contre-factuel |

GLP est un paradigme **inclusif** : le LLM backbone (produit du pré-entraînement génératif
à grande échelle) fournit des abstractions sémantiques « déjà faites », tandis que le
décodeur génératif garantit la **complétude** (il conserve l'information que la couche
sémantique ne savait pas nécessaire). Résultat : l'abstraction sémantique est rendue
**suffisante** par le backbone de raisonnement dédié, et maintenue **riche** par le décodeur
génératif (p. 14–15).

## 4. PAN 2 : l'instanciation concrète du GLP (§5.2)

PAN (Physical, Agentic, Nested) instancie le GLP en un monde à **représentation mixte** et
**raisonnement multi-échelle** :

- **Sensory Encoder $h$** : voie **dual** — (i) un tokenizer mappe hiérarchiquement le signal
  brut en **tokens discrets** (tokens abstraits type VQ-VAE + mots concrets de la langue
  naturelle), à nombre flexible, **stateful par construction** (ancrés dans un vocabulaire
  persistant, réadressables, tenus en mémoire sur les longs horizons) ; (ii) les détails
  bas-niveau en **embeddings latents continus** pour l'expérience perceptuelle nuancée.
  Ensemble : un état du monde en couches $\hat s = \{\hat s_i\}_{i=1}^{N}$.
- **World Model Backbone $f$** : un **LLM enrichi** (raisonne sur tokens langue + vocabulaire
  conceptuel appris) **et** un **prédicteur de next-latent-embedding par diffusion**
  (raisonnement rapide, bas-niveau, souvent sous-conscient — réponses incarnées). Un
  **Learned Switch** combine adaptativement le backbone LLM, les vocabulaires et le prédicteur
  diffusion selon la demande de la tâche.
- **Multimodal Decoder $g$** : reconstruit l'observation suivante $\hat o'$ — pas seulement la
  vidéo, mais l'**expérience sensorielle complète** (son, température, mouvement, douleur,
  signaux incarnés, texte) — et la compare à $o'$. Cette **supervision générative** ancre
  l'état prédit $\hat s'$ dans la réalité sensorielle.

La factorisation formelle (p. 22–23) :

$$p_{PAN}(o' \mid o, a) = \sum_{\hat s, \hat s'} \underbrace{p_h(\hat s \mid o)}_{\text{encodeur}} \;\underbrace{p_f(\hat s' \mid \hat s, a)}_{\text{modèle du monde}} \;\underbrace{p_g(o' \mid \hat s')}_{\text{décodeur}}$$

avec, à l'intérieur, une inférence d'état hiérarchique (produit sur $i$) et une prédiction
d'état suivant par switch (produit sur $j$). C'est ce **décodeur** $g$ — absent de JEPA — qui
ferme la boucle et distingue le GLP d'un JEPA.

## 5. Le modèle PAN 2 — faits de la model card et de la recette vLLM

Fait relevé **firsthand** (model card + recette vLLM, lues le 12/11) :

- **PAN 2** (IFM, MBZUAI) est un **modèle du monde généraliste** : il simule comment le monde
  change en réponse à des actions. Entrée = observation (image optionnelle + texte) et actions
  décrites en texte ; sortie = **vidéo de l'issue, jusqu'à 20 s**. Cas d'usage :
  **raisonnement simulatif** — un agent imagine les issues de ses actions candidates avant de
  choisir.
- Il suit l'architecture **GLP** (formalisée dans *Critique of World Models*, arXiv
  2507.05169) et couple **raisonnement conceptuel** (un LLM) et **raisonnement perceptuel**
  (un modèle de diffusion latente).
- Le backbone **perceptuel** est un **MMDiT de 29 B paramètres** ; le simulateur génératif est
  un **diffusion transformer dual-stream multimodal (MMDiT)** : l'état et la vidéo sont deux flux, chacun
  avec ses propres projections et réseaux feed-forward, **reliés par auto-attention à chaque
  couche** (recette vLLM).
- **Checkpoints** : configs livrées `config/pretrain_29B_720p.yaml` et
  `config/sft_29B_720p.yaml` (model card, §Training).
- **Recette vLLM** (firsthand) : « 13 s de vidéo 704×1248 en ~119 s sur 4×B300 (CFG parallel ×
  Ulysses 2) » ; config par défaut **8× H200 · BF16** ;
  `vllm serve IFM/PAN2 --num-gpus 4 --cfg-parallel-size 2 --usp 2 --vae-patch-parallel-size 4 --vae-parallel-mode tile --omni`
  (exige vLLM ≥ 0.33.0 + VLLM-Omni pour le chemin de génération).
- **Licence** : Apache-2.0 pour le modèle (model card) ; les composants du pipeline sont sous leurs licences propres. Pipeline : Image-Text-to-Video (Diffusers, Safetensors).

## 6. Borne de périmètre — ce que cette distillation NE fait PAS

- **Ne reproduit pas le modèle** : PAN 2 pèse 29 B et se sert sur 4×B300 / 8×H200. La
  distillation porte la **technique** (thèse, dimensions, architecture GLP, instanciation
  PAN), pas les poids. Le modèle reste un **paramètre d'exécution**.
- **Le carnet « sur la technique » est défermé** : le grain #25846 demande « un carnet sur la
  technique » ; il est **reporté** par le **veto user Q-015** (pas de carnet neuf jusqu'à
  levée écrite). Une **issue fille** est ouverte pour le porter après levée. La technique est
  portée ici par la cartographie + l'outil rejouable, qui en sont la substance.
- **Aucun benchmark rejoué** ici : les « Headline Results » de la model card sont rapportés,
  pas reproduits (cela nécessiterait le modèle GPU).

## 7. Outil rejouable

[`scripts/genai/pan2/world_model_formalism.py`](../../scripts/genai/pan2/world_model_formalism.py)
encodé en Python standard (CPU, sans dépendance) : les 5 dimensions, les 3 niveaux du GLP, la
distribution **dégénérée** de JEPA (masse de Dirac) opposée à une distribution générative
propre, et la factorisation $p_{PAN}(o'\mid o,a)=p_h\,p_f\,p_g$ — avec un mode `--check`
auto-test (sortie 0/1/2). Il rend la formalisation **vérifiable** sans le modèle 29 B.

## Attribution et licence

- **Modèle PAN 2** : Apache-2.0 (model card IFM/PAN2) ; © Institute of Foundation Models,
  MBZUAI.
- **Papier** : Xing, Deng, Hou — *Critique of World Model*, arXiv 2507.05169 (juin 2026).
  Copie archivée citée en tête. Aucune publication sous droits n'est committée dans CoursIA.
