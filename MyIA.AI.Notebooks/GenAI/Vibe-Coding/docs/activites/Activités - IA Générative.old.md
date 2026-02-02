# Activités - IA Générative

## 1. Sources de données

L'IA générative dépend entièrement de la qualité et de la diversité des données d'entraînement. Pour bien comprendre l'origine des connaissances d'un modèle, il est essentiel d'analyser les types de sources utilisées.

**Activité :** Par équipe, identifiez pour chaque catégorie ci-dessous les types de données textuelles que pourrait contenir un dataset d'entraînement d'un LLM :
- **Classe** : Quels contenus éducatifs ?
- **Maison** : Quelles informations domestiques ?
- **Transport** : Quelles données de mobilité ?
- **Loisirs** : Quels contenus de divertissement ?

**Pipeline technique :** Acquisition → Nettoyage → Préparation → Annotation

**Objectif :** Comprendre la diversité des sources nécessaires pour créer un modèle génératif polyvalent et le processus technique de traitement.

**Indices :**
- Pensez aux formats variés : livres, articles, forums, manuels, sites web...
- Considérez les différences de registre de langue et de formalité
- Réfléchissez aux biais potentiels de chaque source (genre, culture, contexte géographique)
- **Alternative moderne :** Données synthétiques pour protéger la confidentialité
- **Défis techniques :** Scalabilité, coût énergétique, datacenters verts, modèles distillés

---

## 2. Mind-Meld : Comprendre la proximité sémantique

Les modèles de langage utilisent des "embeddings" pour représenter les mots dans un espace vectoriel où la distance indique la proximité sémantique.

**Activité :** 
1. **Phase 1** : Par binômes, choisissez simultanément un mot aléatoire sans concertation
2. **Phase 2** : Trouvez ensemble un mot qui soit à "mi-distance" sémantique entre vos deux mots initiaux
3. **Phase 3** : Répétez l'exercice et observez la convergence

**Exemple :** 
- Mots initiaux : "Chien" et "Ordinateur"
- Mot mi-distance possible : "Robot" (artificiel comme ordinateur, compagnon comme chien)

**Objectif :** Intuition sur la représentation vectorielle des concepts et l'attention contextuelle.

**Contexte technique :**
- **Tokens :** Représentation numérique des mots (vocabulaire 50k-128k)
- **Embeddings :** Représentation vectorielle permettant le calcul de proximité sémantique
- **Lien théorique :** Cette activité illustre le principe "King - Man + Woman = Queen" des embeddings

---

## 3. Mots polysémiques et mécanisme d'attention

Le mécanisme d'attention permet aux modèles de comprendre le sens d'un mot selon son contexte, résolvant ainsi l'ambiguïté des mots polysémiques.

**Activité :** 
1. Choisissez un mot polysémique (ex: "souris", "feuille", "avocat")
2. Créez 3 phrases utilisant ce mot dans des sens différents
3. Pour chaque phrase, dessinez des "flèches d'attention" montrant quels autres mots du contexte aident à déterminer le sens
4. Expliquez la définition du mot dans chaque contexte

**Exemple avec "avocat" :**
- "L'avocat plaide au tribunal" → flèches vers "plaide", "tribunal"
- "J'ai mangé un avocat" → flèches vers "mangé"
- "L'avocat coûte 2€" → contexte ambigu, nécessite plus d'informations

**Exemple classique anglais :**
- "I saw the man with the telescope" → Qui a la lunette ? (ambiguïté syntaxique)

**Objectif :** Comprendre comment l'attention contextuelle résout l'ambiguïté linguistique.

---

## 4. Expérimentation des paramètres de génération

Les paramètres de génération contrôlent la créativité et la cohérence des modèles génératifs. Une même seed (graine aléatoire) permet la reproductibilité.

**Activité :** Avec un même prompt et une seed fixe, testez l'impact de différents paramètres :

**Prompt de test :** "Écris une courte histoire sur un robot jardinier."

**Paramètres à tester :**
- **Température** : 0.1, 0.7, 1.2
- **Top-k** : 10, 50, infini
- **Top-p** : 0.5, 0.9, 1.0

**Extension génération d'images :** Testez aussi les paramètres de diffusion :
- **N-steps** : Nombre d'étapes de débruitage (10, 25, 50)
- **CFG-scale** : Conformité au conditionnement (5, 10, 15)
- **Denoising strength** : Quantité de changement (0.3, 0.7, 1.0)

**Questions :**
1. Quel paramètre produit le texte le plus cohérent ?
2. Lequel génère le plus de créativité ?
3. Observez-vous des répétitions ou des incohérences ?
4. **Reproductibilité :** Comment la seed fixe impact-t-elle les résultats ?

**Objectif :** Maîtriser le réglage des paramètres selon l'usage souhaité (créatif vs factuel) et la modalité (texte/image).

---

## 5. Campagne Marketing fictive : Nouveau Soda

L'IA générative excelle dans la création de contenu marketing multimodal. Cette activité combine génération de texte et d'images.

**Cahier des charges :** Créez une campagne complète pour le lancement d'un nouveau soda avec :
1. **Un slogan** accrocheur et mémorable
2. **Un visuel** (logo ou image de produit) généré par IA
3. **3 posts réseaux sociaux** (Instagram, LinkedIn, TikTok) adaptés aux audiences
4. **Un scénario de publicité télévisée** de 30 secondes

**Contraintes :**
- Public cible : 18-35 ans
- Positionnement : Soda écologique et local
- Ton : Moderne et authentique

**Outils suggérés :** ChatGPT/Claude pour les textes, Stable Diffusion/DALL-E pour les visuels.

**Évaluation :** Cohérence de la campagne, originalité, adaptation aux canaux.

**Points attribués :** 5 points à l'équipe avec la campagne la plus convaincante (vote des autres équipes).

---

## 6. Prévision Trading Crypto par analyse graphique

L'IA peut analyser des graphiques financiers et identifier des patterns, mais ses limites doivent être comprises.

**Activité :** 
1. Soumettez à un modèle multimodal (GPT-4V, Claude) des graphiques de cryptomonnaies avec indicateurs techniques (RSI, MACD, moyennes mobiles)
2. Demandez une analyse et une prévision de tendance
3. Comparez les prédictions avec l'évolution réelle (données historiques)

**Questions d'analyse :**
- Le modèle identifie-t-il correctement les patterns techniques ?
- Les prédictions sont-elles cohérentes avec l'analyse technique traditionnelle ?
- Quels sont les biais et limitations observés ?

**Mise en garde :** Cette activité illustre les capacités ET les limites de l'IA en finance. Aucune décision d'investissement ne doit être basée uniquement sur l'IA.

**Objectif :** Compréhension critique des applications de l'IA en analyse financière.

---

## 7. Dataset biaisé : Conception et détection

Les biais dans les données d'entraînement se propagent dans les modèles. Cette activité sensibilise à leur identification.

**Activité :** 
1. **Conception** : Créez un petit dataset synthétique intentionnellement biaisé
   - Exemple : Descriptions de métiers avec répartition genrée déséquilibrée
   - 20 descriptions de "médecins" (18 hommes, 2 femmes)
   - 20 descriptions d'"infirmiers" (2 hommes, 18 femmes)

2. **Entraînement simulé** : Observez quels stéréotypes le modèle pourrait apprendre

3. **Détection** : Proposez des méthodes pour identifier ce biais
   - Tests avec prompts neutres
   - Analyse statistique des associations
   - Audit sur des groupes de contrôle

**Questions :**
- Comment le biais se manifeste-t-il dans les générations ?
- Quelles stratégies de mitigation proposez-vous ?

**Ressources :** Documentation sur les techniques de debiasing et les métriques de fairness.

---

## 8. Auditeur IA : Recommandation de voyage

Un auditeur IA teste la fiabilité et les biais d'un système d'IA en conditions réelles.

**Scénario :** Vous auditez un système de recommandation de voyages utilisant l'IA générative.

**Activité :**
1. **Analyse des sources** : Identifiez quelles données le système utilise (in) et exclut (out)
2. **Tests de biais** : Soumettez des profils variés :
   - Différents budgets (100€ vs 10.000€)
   - Différentes origines culturelles
   - Familles vs célibataires vs couples
3. **Évaluation** : Les recommandations sont-elles équitables et personnalisées ?

**Questions d'audit :**
- Le système discrimine-t-il certains groupes ?
- Les recommandations reflètent-elles des stéréotypes culturels ?
- La transparence des critères est-elle suffisante ?

**Livrables :** Rapport d'audit avec recommandations d'amélioration.

**Objectif :** Développer un œil critique sur les systèmes d'IA en production.

---

## 9. Constitutional AI : Définir les valeurs d'un modèle

Constitutional AI est une approche qui encode explicitement des principes éthiques dans le comportement d'un modèle.

**Activité :**
1. **Définition d'une Constitution** : Rédigez 5 principes éthiques pour un assistant IA éducatif
   - Exemple : "Ne jamais donner de réponses qui pourraient nuire à l'apprentissage autonome"
   
2. **Création d'un prompt système** : Traduisez ces principes en instructions techniques
   
3. **Test sur modèle** : Utilisez votre prompt système sur un modèle et testez avec des requêtes limites
   - Demandes de triche aux examens
   - Raccourcis dangereux
   - Contenu inapproprié pour l'âge

**Questions :**
- Le modèle respecte-t-il vos principes ?
- Comment gérer les conflits entre principes ?
- L'**ablitération** (suppression des garde-fous) est-elle détectable ?
- **Note :** Un modèle ablitéré a ses mécanismes de sécurité supprimés

**Ressources :** Documentation Anthropic sur Constitutional AI, exemples de constitutions.

**Objectif :** Comprendre l'alignement des valeurs en IA.

---

## 10. Propositions novatrices : IA pour le bien commun

L'IA générative peut adresser des défis sociétaux et environnementaux majeurs.

**Activité :** Proposez des applications innovantes de l'IA générative pour résoudre des problèmes réels :

**Catégories et exemples concrets :**
- **Environnement** : Surveiller la déforestation, gestion des ressources en eau, solutions écologiques
- **Santé publique** : Accès aux soins, prévention, sensibilisation dans zones sous-développées
- **Éducation** : Réduction des inégalités, personnalisation, supports pédagogiques adaptatifs
- **Inclusion sociale** : Accessibilité, diversité, égalité des chances

**Format :**
1. **Avec guidance** : Utilisez l'IA pour générer des idées puis les affiner
2. **Sans guidance** : Brainstorming traditionnel puis validation par IA

**Évaluation :**
- Faisabilité technique
- Impact social potentiel
- Considérations éthiques
- Originalité

**Présentation :** 3 minutes par équipe + questions

**Objectif :** Vision positive et responsable de l'IA générative.

---

## Installation et Configuration

Pour ces activités, vous utiliserez :

**Environnements recommandés :**
- **Open WebUI** : Interface locale pour LLMs
- **Roo** : Assistant IA intégré à VS Code
- **Stable Diffusion** : Génération d'images (ComfyUI/Forge)

**Modèles suggérés :**
- **Texte** : Llama 3.1 8B, Mistral 7B, Qwen 2.5
- **Images** : Stable Diffusion 1.5/XL, Flux.1
- **Multimodal** : LLaVA, Qwen-VL

**Documentation complète :** Voir les guides `INSTALLATION-ROO.md` et `INTRO-GENAI.md`

---

**Ressources et Références**

**Notebooks pédagogiques Microsoft :**
- Curriculum "generative-ai-for-beginners" : https://github.com/microsoft/generative-ai-for-beginners
- Samples Semantic-Kernel : https://github.com/microsoft/semantic-kernel-samples

**Librairies et outils actualisés :**
- **Interface conversationnelle :** Open-webui, SillyTavern
- **Modèles locaux :** Ollama, Oobabooga, vLLM
- **Génération d'images :** ComfyUI, Forge, Stable Diffusion
- **APIs :** Hugging Face, OpenAI, Anthropic
- **Orchestration :** Semantic-Kernel, LangChain, Dify

**Modèles recommandés 2025 :**
- **Texte :** Llama 3.1, Mistral 7B, Qwen 2.5, DeepSeek
- **Images :** Stable Diffusion XL, Flux.1
- **Code :** GitHub Copilot, Claude-Code, Roo

**Lectures approfondies :**
- "Attention Is All You Need" (Vaswani et al., 2017)
- Documentation Anthropic sur l'alignement des modèles
- Constitutional AI principles et techniques de débiaisage

---

## Évaluation et Points

**Répartition des points :**
- **Activités 1-4** : Compréhension des concepts fondamentaux (4 × 5 pts = 20 pts)
- **Activités 5-7** : Applications pratiques créatives (3 × 5 pts = 15 pts)
- **Activités 8-10** : Analyse critique et éthique (3 × 5 pts = 15 pts)

**Critères d'évaluation :**
- Participation active et collaboration
- Qualité des analyses critiques sur les biais et limites
- Créativité et faisabilité des propositions
- Compréhension des enjeux éthiques et sociétaux

**Bonus collaboration :** 10 points supplémentaires pour l'esprit d'équipe et les échanges constructifs

**Total possible :** 60 points (50 + 10 bonus)

---

*Document préparé pour EPF - Session IA Générative 2026*
*Durée estimée : 4 heures de travaux pratiques*

**Lectures approfondies :**
- "Attention Is All You Need" (Vaswani et al., 2017)
- Documentation Anthropic sur l'alignement des modèles
- Constitutional AI principles et techniques de débiaisage

**Évaluation :**
- Participation active aux activités
- Qualité des analyses critiques
- Créativité des propositions d'applications responsables

---

*Total des points : 50 points répartis sur les 10 activités*
*Bonus collaboration et esprit critique : 10 points supplémentaires*