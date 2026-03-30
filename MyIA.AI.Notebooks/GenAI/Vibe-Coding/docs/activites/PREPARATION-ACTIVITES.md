# Préparation Session - Activités GenAI

*Document de synthèse pour l'enseignant*

## ✅ Vue d'Ensemble

Cette session contient **10 activités pratiques complètes** sur l'IA Générative, conçues pour une durée totale de **4 heures**.

**Document principal** : [Activites-GenAI.md](./Activites-GenAI.md)

## 📋 Liste des Activités

### Bloc 1 : Fondements (1h)

#### 1. Sources de Données (15 min)
- Identification des types de données d'entraînement
- Pipeline technique : Acquisition → Nettoyage → Préparation → Annotation
- Exercice par équipe sur catégories (Classe, Maison, Transport, Loisirs)

#### 2. Mind-Meld - Proximité Sémantique (20 min)
- Compréhension des embeddings et espace vectoriel
- Exercice pratique en binômes
- Convergence sémantique progressive

#### 3. Mots Polysémiques et Attention (15 min)
- Mécanisme d'attention des Transformers
- Résolution d'ambiguïté contextuelle
- Exercice : Créer phrases avec mots polysémiques

#### 4. Expérimentation Paramètres (10 min)
- Température, Top-k, Top-p
- Impact sur créativité vs cohérence
- Extension : Paramètres génération d'images (N-steps, CFG-scale)

### Bloc 2 : Applications Créatives (1h30 + 15 min pause)

#### 5. Campagne Marketing Fictive : Nouveau Soda (45 min)
- Création multimodale (texte + images)
- Techniques de prompt engineering appliquées
- Livrables : Slogan, visuel, posts réseaux sociaux, scénario pub
- **5 points** pour la meilleure campagne (vote équipes)

#### 6. Prévision Trading Crypto par Graphiques (30 min)
- Analyse multimodale (GPT-4V, Claude)
- Identification de patterns techniques
- Discussion sur limitations et biais

### 🕐 Pause (15 min)

### Bloc 3 : Aspects Critiques (1h30)

#### 7. Dataset Biaisé : Conception et Détection (30 min)
- Création intentionnelle de biais
- Méthodes de détection
- Techniques de mitigation (debiasing)

#### 8. Auditeur IA : Recommandation de Voyage (30 min)
- Tests de fairness et équité
- Métriques de qualité (uptime, précision, recall, F1)
- Principes d'IA responsable (Microsoft)

#### 9. Constitutional AI : Définir les Valeurs (30 min)
- Rédaction de principes éthiques
- Traduction en prompts système
- Tests avec requêtes limites
- Discussion sur ablitération

### Bloc 4 : Vision et Synthèse (30 min)

#### 10. Propositions Novatrices : IA pour le Bien Commun (20 min)
- Applications sociétales et environnementales
- Catégories : Environnement, Santé, Éducation, Inclusion
- Évaluation : Faisabilité, Impact, Éthique, Originalité
- Présentations 3 min par équipe

**Synthèse Générale** (10 min)

## ⏱️ Planification Détaillée

| Horaire | Activité | Durée | Points |
|---------|----------|-------|--------|
| 13:30-13:45 | Activité 1 : Sources données | 15 min | 5 |
| 13:45-14:05 | Activité 2 : Mind-Meld | 20 min | 5 |
| 14:05-14:20 | Activité 3 : Polysémie | 15 min | 5 |
| 14:20-14:30 | Activité 4 : Paramètres | 10 min | 5 |
| 14:30-15:15 | Activité 5 : Campagne Marketing | 45 min | 5 |
| 15:15-15:45 | Activité 6 : Trading Crypto | 30 min | 5 |
| 15:45-16:00 | **PAUSE** | 15 min | - |
| 16:00-16:30 | Activité 7 : Dataset biaisé | 30 min | 5 |
| 16:30-17:00 | Activité 8 : Auditeur IA | 30 min | 5 |
| 17:00-17:30 | Activité 9 : Constitutional AI | 30 min | 5 |
| 17:30-17:50 | Activité 10 : Innovations | 20 min | 5 |
| 17:50-18:00 | Synthèse | 10 min | - |

**Total** : 50 points + 10 points bonus collaboration

## 📦 Ressources Disponibles

### Documents de Support

| Fichier | Contenu |
|---------|---------|
| [Activites-GenAI.md](./Activites-GenAI.md) | Document principal avec les 10 activités |
| [INTRO-GENAI.md](../INTRO-GENAI.md) | Introduction outils GenAI |
| `Intelligence Artificielle - 8 - IA Générative.pptx` | Slides de cours |

### Environnement Technique

**Outils recommandés** :
- **Open WebUI** : Interface locale pour LLMs - https://pauwels.open-webui.myia.io/
- **Roo Code / Claude Code** : Assistants IA intégrés VS Code
- **Stable Diffusion** : Génération d'images (ComfyUI/Forge)
- **Interfaces en ligne** :
  - HiDream : https://hidream.org/
  - Vivago AI : https://vivago.ai/img-generation
  - Stable UI : https://aqualxx.github.io/stable-ui/

**Modèles suggérés** :
- **Texte** : Llama 3.1 8B, Mistral 7B, Qwen 2.5
- **Images** : Stable Diffusion 1.5/XL, Flux.1, DALL-E 3
- **Multimodal** : GPT-4V, Claude, LLaVA

## 🎯 Objectifs d'Apprentissage

### Connaissances Techniques
- ✅ Compréhension des **tokens, embeddings, attention**
- ✅ Maîtrise des **paramètres de génération**
- ✅ Sensibilisation aux **biais et limitations**
- ✅ Architecture **Transformers** et mécanismes

### Compétences Pratiques
- ✅ **Prompt engineering** créatif et critique
- ✅ Évaluation de **systèmes d'IA** génératifs
- ✅ Application **éthique et responsable**
- ✅ Techniques avancées : **RAG, CoT, Few-shot**

### Vision Stratégique
- ✅ Applications **sectorielles et sociétales**
- ✅ Enjeux **économiques et environnementaux**
- ✅ Perspectives d'**évolution et régulation**

## 🛠️ Préparation Technique

### Vérifications Pré-session

- [ ] **Accès Open WebUI** : Tester connexion et modèles
- [ ] **Installation Roo/Claude Code** : Vérifier sur quelques postes
- [ ] **Exemples datasets biaisés** : Préparer fichiers
- [ ] **Graphiques crypto récents** : Télécharger pour Activité 6
- [ ] **Connexion internet** : Vérifier stabilité
- [ ] **Backup offline** : Ressources hors-ligne disponibles

### Matériel Pédagogique

- [ ] **Consignes activités** : Imprimer si nécessaire
- [ ] **Grilles d'évaluation** : Par équipe
- [ ] **Exemples constitutions AI** : Préparer templates
- [ ] **Slides PowerPoint** : Mise à jour et test
- [ ] **FAQ** : Questions fréquentes documentées

### Outils et Logiciels

**À installer / vérifier** :
- VS Code + Roo Code ou Claude Code
- Python 3.8+ avec bibliothèques :
  ```bash
  pip install openai tiktoken pandas numpy jupyter matplotlib
  ```
- Navigateur avec accès aux interfaces GenAI
- Open WebUI (optionnel, local)

## 👥 Organisation

### Formation des Équipes
- **Taille** : 3-4 étudiants par équipe
- **Rotation des rôles** : Encourager participation de tous
- **Documentation** : Demander aux équipes de documenter résultats
- **Évaluation croisée** : Équipes s'évaluent mutuellement (Activité 5)

### Matériel par Équipe
- 1 ordinateur avec accès internet
- Compte Open WebUI ou accès API
- Bloc-notes pour documentation
- Accès partagé aux ressources (Google Drive / Moodle)

## 🔧 Troubleshooting Courant

### Problèmes Techniques Possibles

**1. Modèles locaux lents**
- **Solution** : Utiliser APIs externes (OpenAI, Anthropic via OpenRouter)
- **Backup** : Exemples pré-générés disponibles

**2. Génération d'images échoue**
- **Solution** : Exemples pré-générés fournis
- **Alternative** : Interfaces web (HiDream, Vivago)
- **Plan C** : Démonstration enseignant uniquement

**3. Roo/Claude Code non installé**
- **Solution** : Mode démo via interface web
- **Alternative** : Travail en binômes avec machines fonctionnelles

**4. Réseau limité / coupé**
- **Solution** : Ressources offline dans demo-roo-code/
- **Alternative** : Modèles locaux (Ollama)
- **Plan C** : Activités papier théoriques

### Alternatives Pédagogiques

**Activités hands-off** :
- Discussions théoriques sur les concepts
- Analyses de cas d'usage
- Débats éthiques

**Simulations papier** :
- Activité 2 (Mind-Meld) : Peut se faire sans IA
- Activité 9 (Constitutional AI) : Rédaction manuelle possible
- Activité 10 (Propositions) : Brainstorming traditionnel

**Démonstrations enseignant** :
- Si installations étudiantes échouent
- Projeter en grand écran
- Interaction via questions/suggestions

## 📊 Système d'Évaluation

### Répartition des Points

**50 points au total** :
- Activités 1-4 (Fondements) : 4 × 5 pts = 20 pts
- Activités 5-7 (Applications) : 3 × 5 pts = 15 pts
- Activités 8-10 (Éthique) : 3 × 5 pts = 15 pts

**10 points bonus** :
- Collaboration et esprit d'équipe
- Qualité des échanges
- Aide aux autres équipes

**Total possible** : 60 points

### Critères d'Évaluation

**Par activité** :
- **Participation active** : Toute l'équipe impliquée
- **Qualité analyse** : Profondeur et pertinence
- **Créativité** : Originalité des propositions
- **Documentation** : Résultats bien documentés

**Bonus équipe** :
- Collaboration constructive
- Entraide entre équipes
- Questions pertinentes
- Esprit critique développé

## 📚 Concepts Techniques Clés

Pour référence rapide lors des activités :

### Prompt Engineering

**Techniques couvertes** :
- **Zero-shot** : Instructions directes sans exemples
- **Few-shot** : Exemples pour guider style et format
- **Chain-of-Thought (CoT)** : Raisonnement étape par étape
- **Self-refine** : Auto-amélioration itérative
- **Maieutic** : Questions socratiques
- **Metaprompts** : Instructions système

### RAG (Retrieval Augmented Generation)

**Processus** :
1. Knowledge Base → Chunks → Embeddings
2. User Query → Query vector
3. Retrieval → Top-k chunks pertinents
4. Augmented Generation → LLM avec contexte

### Génération d'Images

**DALL-E** :
- Architecture hybride (CLIP + Transformateur)
- Embeddings cross-modaux texte ↔ images

**Stable Diffusion** :
- N-steps : 10-50 étapes de débruitage
- CFG-scale : 7-15 (Classifier-Free Guidance)
- Denoising strength : 0.3-1.0 (img2img)

## 📖 Ressources Complémentaires

### Pour les Étudiants

**Avant la session** :
- Lire [Activites-GenAI.md](./Activites-GenAI.md)
- Créer compte OpenRouter (optionnel)
- Installer Roo/Claude Code (recommandé)

**Pendant la session** :
- Documenter résultats de chaque activité
- Poser questions au fur et à mesure
- Collaborer activement en équipe

**Après la session** :
- Compléter activités non finies
- Explorer notebooks Python fournis
- Préparer questions pour session suivante

### Pour l'Enseignant

**Lectures recommandées** :
- [Attention Is All You Need](https://arxiv.org/abs/1706.03762) (Vaswani et al., 2017)
- [Constitutional AI](https://www.anthropic.com/constitutional-ai) (Anthropic)
- [Microsoft Generative AI for Beginners](https://github.com/microsoft/generative-ai-for-beginners)

**Notebooks de référence** :
- Code Python complet dans [Activites-GenAI.md](./Activites-GenAI.md)
- [Semantic Kernel Samples](https://github.com/microsoft/semantic-kernel-samples)

## 🎬 Déroulement Type

### Début de Session (10 min)
1. Accueil et présentation objectifs
2. Formation des équipes
3. Distribution matériel
4. Vérification accès outils

### Pendant les Activités
1. Timer visible pour chaque activité
2. Circulation entre équipes
3. Aide ciblée si blocages
4. Encouragement participation

### Transitions
- Résumé rapide de l'activité précédente
- Annonce de la suivante
- Gestion du temps (strict mais flexible)

### Fin de Session (10 min)
1. Synthèse des apprentissages
2. Questions ouvertes
3. Annonce session suivante
4. Feedback rapide (optionnel)

## ✅ Checklist Finale

### Veille de la Session
- [ ] Tous supports à jour
- [ ] Accès Open WebUI testé
- [ ] Exemples et ressources prêts
- [ ] Salle équipée et réservée
- [ ] Rappel email aux étudiants

### Jour J - 30 min Avant
- [ ] Projecteur et slides testés
- [ ] Connexion internet vérifiée
- [ ] Open WebUI accessible
- [ ] Matériel distribué (si physique)
- [ ] Timer/chronomètre prêt

### Pendant la Session
- [ ] Chronométrer chaque partie
- [ ] Noter questions récurrentes
- [ ] Observer engagement équipes
- [ ] Ajuster rythme si nécessaire

### Après la Session
- [ ] Recueillir feedback
- [ ] Mettre à jour FAQ
- [ ] Répondre questions Moodle
- [ ] Préparer session suivante

---

## 📞 Contacts et Support

**Ressources techniques** :
- Guides dans [docs/](../)
- Roo Code : [Ateliers-roo-code/](../../Ateliers-roo-code/)
- Claude Code : [docs/claude-code/](../claude-code/)

**Communauté** :
- Microsoft Semantic-Kernel : https://github.com/microsoft/semantic-kernel
- OpenRouter Documentation : https://openrouter.ai/docs
- Awesome Claude Code : https://github.com/hesreallyhim/awesome-claude-code

---

**Statut** : ✅ PRÊT POUR LA SESSION

*Préparé pour EPF 2026 - MSMIN5IN52 IA Générative et Chatbots*
*Format : Travaux pratiques en équipes avec évaluations croisées*
*Dernière mise à jour : Janvier 2026*
