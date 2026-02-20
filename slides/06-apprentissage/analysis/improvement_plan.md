# Deck 06 - Apprentissage : Analyse Visuelle et Plan d'Amélioration

**Date d'analyse** : 2026-02-13
**Fichier source** : `06-IA-Cours-Apprentissage.pptx`
**Statistiques** : 124 slides, 140 images, 7888 mots, 9.84 MB
**Dernière mise à jour** : Décembre 2024
**Sections** :
- Apprentissage supervisé (paramétrique, non-paramétrique)
- Apprentissage et logique
- Apprentissage probabiliste
- Apprentissage par renforcement

---

## 1. Diagnostic global

### Points forts

- **Deck le plus complet** : 124 slides - couverture exhaustive du ML classique et moderne
- **Visuels excellents** : 140 images, ratio 1.13/slide - bonne densité visuelle
- **Slides techniques de qualité** :
  - Slide 40 : Rétropropagation avec pseudo-code + équations (layout split efficace)
  - Slide 60 : SVM Classifier Margin avec scatter plot et frontière de décision (visuel pédagogique fort)
  - Slide 110 : Boucle agent-environnement RL + MDP grid (excellent schéma)
- **Mise à jour récente** : Décembre 2024 - contenu relativement moderne
- **Structure pédagogique** : Progression logique supervisé → logique → probabiliste → renforcement
- **Slides "Questions?"** : Présents comme pauses (à conserver selon préférence utilisateur)

### Problèmes identifiés

1. **Erreur numérotation titre** : Slide 1 indique "IA - V" mais devrait être "IA - VI" (6e deck)
2. **Images sous copyright** : Slides SVM (autour du 60) affichent "Copyright 2001, 2003" - nécessite remplacement ou attribution formelle
3. **Taille excessive** : 9.84 MB - la plus lourde des 3 decks analysés, peut causer problèmes de chargement
4. **Densité variable** : Certaines slides trop chargées (>250 mots), d'autres trop légères
5. **Manque de liens notebooks** : Cross-références absentes vers `ML/ML.Net/` (5 notebooks) et `RL/stable_baseline_*.ipynb`
6. **Absence d'architectures modernes** : Pas de Transformers, diffusion models, LLMs dans partie supervisée
7. **Section RL datée** : Pas de mention RLHF, PPO moderne, InstructGPT/ChatGPT

### Métriques visuelles estimées

- Slides avec visuels pertinents : ~75%
- Slides trop denses (>250 mots ou >4 équations) : ~12%
- Slides nécessitant modernisation contenu : ~20%
- Slides avec copyright issues : ~5-8 slides (estimation)
- Taille fichier optimisable : ~30% (9.84 MB → ~6-7 MB avec compression images)

---

## 2. Recommandations par section

### Apprentissage supervisé (slides 1-60)

**Conserver** :
- Slide 1 : Plan détaillé - excellente vue d'ensemble (CORRIGER "IA - V" → "IA - VI")
- Slide 40 : Rétropropagation split layout - visuel pédagogique optimal
- Slide 60 : SVM Margin - excellent scatter plot (**REMPLACER image copyright**)

**Améliorer** :
1. **URGENT - Copyright** : Identifier toutes images SVM sous copyright (slides ~55-65), les remplacer par :
   - Recréation avec matplotlib/seaborn (scripts Python disponibles)
   - Images libres de droits (Wikimedia Commons, papers open access)
   - Ajout attribution formelle si utilisation fair use éducatif
2. **Moderniser partie réseaux de neurones** (slides 35-50) :
   - Ajouter 3-4 slides sur architectures modernes :
     - "Transformers et attention mechanism" (BERT, GPT architecture)
     - "Vision Transformers (ViT)" pour remplacer/compléter CNN classiques
     - "Diffusion models" (DALL-E, Stable Diffusion comme supervisé conditionné)
   - Mettre à jour slide 40 rétropropagation : ajouter mention automatic differentiation (PyTorch, TensorFlow)
3. **Ajouter cross-références notebooks** :

| Slide(s) | Concept | Notebooks |
|-----------|---------|-----------|
| 10-25 | Régression, arbres de décision | `ML/ML.Net/ML-101.ipynb` |
| 26-35 | Classification, k-NN | `ML/ML.Net/ML-102-Classification.ipynb` |
| 36-50 | Réseaux de neurones, backprop | `GenAI/transformers-*.ipynb` (cross-référence) |
| 51-60 | SVM, kernel methods | `ML/ML.Net/ML-103-SVM.ipynb` |

---

### Apprentissage et logique (slides 61-80)

**Conserver** :
- Slide 80 : Version space learning avec diagramme - bon visuel conceptuel

**Améliorer** :
1. **Développer section trop courte** : 20 slides pour "Apprentissage et logique" vs 60 pour supervisé - déséquilibre
   - Ajouter 5-10 slides sur :
     - Inductive logic programming (ILP) moderne
     - Neural-symbolic integration (DeepProbLog, Logic Tensor Networks)
     - Neurosymbolic AI (connexion avec `SymbolicAI/` notebooks)
2. **Créer slide "Logique et LLMs"** :
   - Chain-of-thought reasoning (GPT-4, Claude)
   - Formal verification of neural networks
   - Symbolic knowledge injection dans transformers
3. **Ajouter cross-références** :

| Slide(s) | Concept | Notebooks |
|-----------|---------|-----------|
| 61-75 | Apprentissage de concepts | `SymbolicAI/Tweety-*.ipynb` (logique formelle) |
| 76-80 | Version space learning | `ML/ML.Net/ML-104-Active-Learning.ipynb` (si disponible) |

---

### Apprentissage probabiliste (slides 81-100)

**Conserver** :
- Structure existante - bonne introduction aux modèles graphiques

**Améliorer** :
1. **Éviter redondance avec Deck 04** : Probabilités couvre réseaux bayésiens (slides 15-30)
   - Recentrer section sur **apprentissage des paramètres/structure**, pas théorie bayésienne
   - Cross-référencer Deck 04 pour fondamentaux : "Voir Deck 04 - Probabilités pour rappels Bayes"
2. **Moderniser avec modèles génératifs** :
   - Ajouter 4-5 slides sur :
     - VAE (Variational Autoencoders)
     - GANs (brief, en préparation diffusion)
     - Diffusion models (DDPM, DDIM) - connexion GenAI
     - Flow-based models (Normalizing Flows)
3. **Créer slide "Apprentissage probabiliste et GenAI"** :
   - Latent diffusion models (Stable Diffusion)
   - Probabilistic forecasting (GPT-next-token prediction)
4. **Ajouter cross-références** :

| Slide(s) | Concept | Notebooks |
|-----------|---------|-----------|
| 81-90 | EM algorithm, HMM learning | `Probas/Infer/Infer-9-Learning.ipynb` |
| 91-100 | Réseaux bayésiens, structure learning | `Probas/Infer/Infer-10-Structure-Learning.ipynb` |
| Nouveau | VAE, diffusion models | `GenAI/diffusion-models.ipynb`, `GenAI/stable-diffusion-*.ipynb` |

---

### Apprentissage par renforcement (slides 101-124)

**Conserver** :
- Slide 110 : Boucle agent-environnement + MDP grid - visuel pédagogique excellent
- Slide 124 : Merci - bon closing
- Slides "Questions?" entre sous-sections

**Améliorer** :
1. **CRITIQUE - Moderniser section RL** : Contenu daté (2024), manque :
   - Deep RL moderne (DQN, A3C, PPO, SAC)
   - RLHF (Reinforcement Learning from Human Feedback) - **essentiel pour LLMs**
   - Multi-agent RL (connexion Deck 05 - Théorie des Jeux)
2. **Restructurer slides 101-124** :
   - Garder 101-115 : RL classique (Q-learning, MDP, value iteration)
   - Ajouter 116-120 : Deep RL (DQN architecture, replay buffer, target network)
   - Ajouter 121-125 : **RLHF et LLMs** (InstructGPT, ChatGPT, Claude Constitutional AI)
   - Nouveau slide 126 : "RL et robotique moderne" (manipulation, locomotion)
3. **Créer 5 nouvelles slides "RLHF - De RL aux LLMs"** :
   - Slide A : "Problème : Aligner les LLMs avec préférences humaines"
   - Slide B : "Pipeline RLHF : SFT → Reward Model → PPO fine-tuning"
   - Slide C : "Reward modeling : Bradley-Terry model sur comparaisons humaines"
   - Slide D : "PPO optimization : InstructGPT, ChatGPT architecture"
   - Slide E : "Constitutional AI : RLAIF sans labels humains (Anthropic Claude)"
4. **Améliorer slide 110** (déjà bonne) :
   - Ajouter annotation "Base pour RLHF : reward = préférence humaine"
   - Créer parallèle visuel MDP classique vs MDP langage (état = prompt+réponse)
5. **Ajouter cross-références notebooks** :

| Slide(s) | Concept | Notebooks |
|-----------|---------|-----------|
| 101-110 | MDP, Q-learning classique | `GameTheory/GameTheory-14b-RL-Basics.ipynb` |
| 111-115 | Value iteration, policy iteration | `Probas/Infer/Infer-12-Decision.ipynb` |
| 116-120 | Deep RL (DQN, PPO) | `RL/stable_baseline_cartpole.ipynb`, `RL/stable_baseline_dqn.ipynb` |
| 121-125 | RLHF, LLMs | `GenAI/llm-finetuning.ipynb` (si disponible, sinon créer démo) |
| 126 | Multi-agent RL | `GameTheory/GameTheory-15b-Multi-Agent-RL.ipynb` |

---

## 3. Cross-references notebooks

### Mapping complet proposé

| Slide(s) | Concept | Notebooks |
|-----------|---------|-----------|
| 1-15 | Introduction ML, types d'apprentissage | `ML/ML.Net/ML-101.ipynb` |
| 16-30 | Régression linéaire, logistique | `ML/ML.Net/ML-102-Classification.ipynb` |
| 31-45 | Réseaux de neurones, backprop | `GenAI/transformers-basics.ipynb` (cross-ref architectures) |
| 46-60 | SVM, kernel methods | `ML/ML.Net/ML-103-SVM.ipynb` |
| 61-75 | Apprentissage de concepts, logique | `SymbolicAI/Tweety-Logic.ipynb` |
| 76-80 | Version space, active learning | `ML/ML.Net/ML-104-Active-Learning.ipynb` |
| 81-95 | EM, HMM learning, Bayes nets | `Probas/Infer/Infer-9-Learning.ipynb`, `Infer-10-Structure-Learning.ipynb` |
| 96-100 | Modèles génératifs (VAE, GANs) | `GenAI/vae-*.ipynb`, `GenAI/diffusion-models.ipynb` |
| 101-115 | RL classique (Q-learning, MDP) | `GameTheory/GameTheory-14b-RL-Basics.ipynb` |
| 116-120 | Deep RL (DQN, PPO, SAC) | `RL/stable_baseline_cartpole.ipynb`, `RL/stable_baseline_dqn.ipynb` |
| 121-125 | RLHF et LLMs | `GenAI/llm-finetuning.ipynb` (créer si absent) |
| 126 | Multi-agent RL | `GameTheory/GameTheory-15b-Multi-Agent-RL.ipynb` |

**Action** : Créer slide récapitulative (nouvelle slide 123) avec QR codes vers notebooks avant slide "Merci" (devient slide 124).

---

## 4. Plan d'amélioration prioritaire

### P1 : Corrections immédiates (2.5h)

1. **URGENT - Corriger numérotation** : Slide 1 "IA - V" → "IA - VI" (titre + propriétés fichier)
2. **URGENT - Copyright images SVM** :
   - Identifier toutes images sous copyright (slides ~55-65, chercher watermark "Copyright 2001, 2003")
   - Remplacer par images libres ou recréer avec matplotlib (~1.5h)
   - Script Python disponible : `scripts/generate_svm_plots.py` (créer si absent)
3. **Optimiser taille fichier** : 9.84 MB → ~6-7 MB
   - Compresser images (PowerPoint : "Compress Pictures" → 150 ppi)
   - Supprimer slides cachées si existantes
   - Sauvegarder en .pptx moderne (Office 2024)
4. **Vérifier slides "Questions?"** : S'assurer présence entre chaque section majeure (conserver selon préférence)

### P2 : Améliorations visuelles et expansion (6h)

1. **Étendre section RLHF** (slides 121-125) - **PRIORITÉ HAUTE** :
   - Créer 5 nouvelles slides sur pipeline RLHF (voir section RL ci-dessus)
   - Inclure schémas : SFT → Reward Model → PPO (créer avec draw.io ou PowerPoint SmartArt)
   - Ajouter logos/exemples : ChatGPT, Claude, Llama 3 fine-tuned
   - Estimation : ~3h (recherche + design + intégration)
2. **Moderniser partie réseaux de neurones** (slides 35-50) :
   - Ajouter 4 slides : Transformers, ViT, attention mechanism, diffusion models
   - Créer schémas architecture (réutiliser `GenAI/` notebooks visualizations)
   - Estimation : ~2h
3. **Développer apprentissage et logique** (slides 61-80) :
   - Ajouter 5 slides : ILP, neurosymbolic AI, logique dans LLMs
   - Estimation : ~1h
4. **Ajouter slide récapitulative notebooks** :
   - Tableau cross-référence complet avec QR codes (nouvelle slide 123)
   - Estimation : ~30min

### P3 : Modernisation contenu (5h)

1. **Enrichir exemples avec applications 2024-2026** :
   - Remplacer exemples génériques par cas concrets :
     - Slide 30 : Classification → Spam detection Gmail, modération contenu Meta
     - Slide 50 : Deep learning → GPT-4, Claude Opus architectures
     - Slide 100 : Modèles génératifs → DALL-E 3, Midjourney, Sora
     - Slide 120 : RL → AlphaGo, Dota 2 OpenAI Five, robotique Boston Dynamics
2. **Créer section "ML et GenAI moderne"** (3-4 nouvelles slides avant conclusion) :
   - "Transfer learning et foundation models" (BERT, GPT-3 pre-training)
   - "Few-shot learning" (GPT-4, Claude in-context learning)
   - "Multimodal learning" (GPT-4V, Gemini, Claude 3 vision)
   - "Scaling laws" (Chinchilla, emergent abilities)
3. **Améliorer coordination inter-decks** :
   - Ajouter cross-références explicites vers Deck 04 (Probabilités) pour partie bayésienne
   - Cross-référencer Deck 05 (Game Theory) pour multi-agent RL
   - Créer "roadmap des decks" : slide 2 avec parcours conseillé
4. **Enrichir bibliographie** :
   - Ajouter papers fondamentaux 2017-2026 :
     - "Attention Is All You Need" (Vaswani et al., 2017) - Transformers
     - "Deep Reinforcement Learning from Human Preferences" (Christiano et al., 2017) - RLHF précurseur
     - "Training language models to follow instructions with human feedback" (Ouyang et al., 2022) - InstructGPT
     - "Constitutional AI" (Bai et al., 2022) - Claude Anthropic
     - "Scaling Laws for Neural Language Models" (Kaplan et al., 2020)
5. **Intégration notebooks** :
   - Créer slides de transition avec captures d'écran notebooks `ML/`, `RL/`, `GenAI/`
   - Ajouter instructions pratiques : "Exercice : ouvrir `ML/ML.Net/ML-101.ipynb`"
   - Note .NET : Mentionner installation .NET Interactive kernel (voir `CLAUDE.md`)

### Estimation totale : ~13.5h d'améliorations

**Ordre recommandé** : P1 (corrections urgentes copyright + numérotation) → P2 (expansion RLHF prioritaire) → P3 (modernisation long terme)

---

## 5. Considérations spécifiques

### Équilibre densité du deck

- **124 slides acceptable** pour session 2x90min (pause entre supervisé et RL)
- Alternative : **Découper en 2 decks** :
  - Deck 6A - Apprentissage supervisé (65 slides)
  - Deck 6B - Apprentissage avancé (65 slides : logique + probabiliste + RL)
- Décision dépend du format cours (1 session longue vs 2 sessions)

### Gestion copyright images

**Process recommandé** :
1. Audit complet : `grep -r "Copyright" slides/06-apprentissage/` dans notes PowerPoint
2. Pour chaque image protégée :
   - **Option A** : Recréer avec matplotlib (script `scripts/generate_svm_plots.py`)
   - **Option B** : Chercher équivalent Wikimedia Commons (licence CC-BY-SA)
   - **Option C** : Attribution formelle si fair use éducatif (ajouter slide "Crédits")
3. Tester rendu PDF pour vérifier qualité images recréées

### Notebooks ML.NET et .NET Interactive

- **5 notebooks disponibles** dans `ML/ML.Net/`
- Nécessite .NET 9.0 + .NET Interactive kernel
- Installation : `dotnet tool install -g Microsoft.dotnet-interactive`
- Voir `CLAUDE.md` section "Configuration" pour setup complet

### Coordination avec autres decks

| Deck | Overlap | Stratégie |
|------|---------|-----------|
| Deck 04 (Probabilités) | Apprentissage probabiliste (slides 81-100) | Cross-référencer pour théorie, focus sur learning algorithms |
| Deck 05 (Game Theory) | Multi-agent RL (slide 126) | Brève mention, renvoyer vers Deck 05 pour MARL approfondi |
| GenAI notebooks | Transformers, diffusion (slides 35-50, 96-100) | Intégrer schémas, renvoyer vers notebooks pour code |

---

## 6. Checklist qualité post-amélioration

Après implémentation du plan, vérifier :

- [ ] Numérotation titre corrigée ("IA - VI")
- [ ] Aucune image sous copyright non attribuée
- [ ] Taille fichier <7 MB (compression images effectuée)
- [ ] Footer cohérent sur toutes slides ("CoursIA - Apprentissage")
- [ ] Slides "Questions?" présents entre sections (selon préférence utilisateur)
- [ ] Cross-références notebooks fonctionnelles (QR codes testés)
- [ ] Section RLHF complète (5 slides minimum sur InstructGPT/Claude)
- [ ] Bibliographie moderne (papers 2017-2026 inclus)
- [ ] Exemples actualisés (2024-2026, pas d'exemples pré-2020)
- [ ] Rendu PDF testé (pagination, qualité images)
- [ ] Tests exécution notebooks cross-référencés :
  ```bash
  scripts/notebook_tools.py validate ML/ML.Net/ --quick
  scripts/notebook_tools.py validate RL/ --quick
  scripts/notebook_tools.py validate GenAI/ --quick
  ```

---

## Notes d'implémentation

- Utiliser PowerPoint 2024 ou LibreOffice Impress pour édition
- Sauvegarder version originale en `06-IA-Cours-Apprentissage_v2024.pptx` avant modification
- Pour recréer images SVM, utiliser :
  ```python
  # scripts/generate_svm_plots.py
  import matplotlib.pyplot as plt
  from sklearn import svm, datasets
  # [code pour générer scatter + frontière décision + margins]
  ```
- Tester rendu sur projecteur (contraste, lisibilité police 18pt minimum)
- Valider QR codes avec smartphone avant finalisation
- Commit atomique : `git commit -m "fix(slides-06): Correct title to IA-VI, replace copyright SVM images, add RLHF section"`
