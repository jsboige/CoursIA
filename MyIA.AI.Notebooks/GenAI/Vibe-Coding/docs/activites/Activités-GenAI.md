# Activités - IA Générative

## 1. Sources de données

L'IA générative dépend entièrement de la qualité et de la diversité des données d'entraînement. Pour bien comprendre l'origine des connaissances d'un modèle, il est essentiel d'analyser les types de sources utilisées.

**Contexte historique :** L'évolution de l'IA générative s'est accélérée depuis 2017 avec "Attention is All You Need", menant à GPT-1 (117M paramètres), GPT-2 (1,5B), GPT-3 (175B), jusqu'à GPT-4 (1000B). ChatGPT a atteint 1 million d'utilisateurs en 5 jours et 100M en 2 mois, révolutionnant le marketing, la rédaction et l'assistance client.

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

**Méthodes d'entraînement modernes :**
- **Apprentissage de base :** Très coûteux, modèles fondationnels (pré-entraînement sur corpus massifs)
- **Fine-Tuning :** Ajustement spécifique avec LoRAs (Low-Rank Adaptations)
- **Apprentissage en contexte :** Peu coûteux, basé sur le prompt engineering et few-shot learning

---

## 2. Mind-Meld : Comprendre la proximité sémantique

Les modèles de langage utilisent des "embeddings" pour représenter les mots dans un espace vectoriel où la distance indique la proximité sémantique.

**Activité :** 
1. **Phase 1** : Par binômes, choisissez simultanément un mot aléatoire sans concertation
2. **Phase 2** : Trouvez ensemble un mot qui soit à "mi-distance" sémantique entre vos deux mots initiaux (2 nouveaux mots proposés à novueau en même temps)
3. **Phase 3** : Répétez l'exercice et observez la convergence

**Exemple :** 
- Mots initiaux : "Chien" et "Ordinateur"
- Mot mi-distance possible : "Robot" (artificiel comme ordinateur, compagnon comme chien)

**Objectif :** Intuition sur la représentation vectorielle des concepts et l'attention contextuelle.

**Contexte technique :**
- **Tokens :** Représentation numérique des mots (vocabulaire 50k-128k tokens)
- **Embeddings :** Représentation vectorielle permettant le calcul de proximité sémantique
- **Lien théorique :** Cette activité illustre le principe "King - Man + Woman = Queen" des embeddings
- **Architecture :** Les réseaux de neurones utilisent des couches interconnectées avec ajustement des poids par rétropropagation et autodifférentiation
- **Transformers :** Architecture clé des LLMs modernes, révolutionnaire depuis 2017 ("Attention is All You Need")

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

**Mécanisme technique :** L'architecture Transformer utilise le mécanisme d'attention pour donner différents poids aux inputs reçus, "portant plus d'attention" là où l'information la plus pertinente est concentrée, indépendamment de l'ordre dans la séquence textuelle.

**Processus de génération :** Les modèles prédisent un token à la fois selon la probabilité d'occurrence dans un contexte donné, puis incorporent ce token dans l'input de l'itération suivante (fenêtre glissante).

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
- **N-steps** : Nombre d'étapes de débruitage (10, 25, 50) - Plus d'étapes = meilleure qualité mais plus lent
- **CFG-scale** : Conformité au conditionnement (5, 10, 15) - Classifier-Free Guidance
- **Denoising strength** : Quantité de changement (0.3, 0.7, 1.0) - Pour img2img uniquement
- **Prompts négatifs** : Spécifier ce qu'on ne veut pas voir dans l'image
- **Upscaling** : Amélioration de la résolution post-génération

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

**Exemple d'application similaire : Générateur de recettes**
```python
# Configuration OpenAI recommandée
from openai import OpenAI
import os
from dotenv import load_dotenv

load_dotenv()
client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))

# Prompt avec variables d'entrée
no_recipes = input("Nombre de recettes (ex: 5): ")
ingredients = input("Ingrédients (ex: chicken, potatoes, carrots): ")
filter_option = input("Filtre (ex: végétarien, sans gluten): ")

prompt = f"Montre-moi {no_recipes} recettes avec {ingredients}. Éviter {filter_option}"
messages = [{"role": "user", "content": prompt}]

completion = client.chat.completions.create(
    model="gpt-4o-mini",
    messages=messages,
    max_tokens=600,
    temperature=0.7
)
```

**Types de modèles à considérer :**
- **Génération de texte :** GPT-3.5, GPT-4 (coût variable selon le modèle)
- **Génération d'images :** DALL-E, Midjourney, Stable Diffusion
- **Multimodal :** GPT-4V, GPT-4o (traitement texte + vision)

**Techniques de prompt engineering :**

**1. Zero-shot prompting :**
- **Principe :** Instructions directes sans exemples préalables
- **Usage :** Tâches simples, informations factuelles
- **Exemple :** "Traduis cette phrase en anglais : 'Bonjour le monde'"

**2. Few-shot prompting :**
- **Principe :** Fournir quelques exemples pour guider le style et le format
- **Usage :** Tâches créatives, formatage spécifique
- **Exemple :**
```
Exemples de slogans écologiques :
- Produit A → "Nature d'abord, toujours"
- Produit B → "L'avenir vert commence ici"
- Nouveau soda → ?
```

**3. Chain-of-Thought (CoT) :**
- **Principe :** Décomposition du raisonnement étape par étape
- **Mots-clés :** "Réfléchis étape par étape", "Analyse progressivement"
- **Usage :** Problèmes complexes, raisonnement logique, calculs
- **Exemple avancé :**
```python
# Template CoT pour résolution de problèmes
cot_prompt = """
Résoudre ce problème étape par étape :
{problem}

Étapes à suivre :
1. Identifier les éléments clés
2. Déterminer les relations entre eux
3. Appliquer la logique appropriée
4. Vérifier la cohérence du résultat

Raisonnement :
"""
```

**4. Self-refine (Auto-amélioration) :**
- **Principe :** Le modèle critique et améliore sa propre réponse
- **Processus :** Génération → Auto-évaluation → Raffinement → Finalisation
- **Template type :**
```
1. Génère d'abord une réponse
2. Identifie 3 points d'amélioration possibles
3. Propose une version améliorée
4. Explique les changements effectués
```

**5. Maieutic prompting :**
- **Principe :** Questions socratiques pour développer les idées
- **Usage :** Créativité, exploration conceptuelle, apprentissage
- **Exemple :** "Qu'est-ce qui rend ce concept unique ? Pourquoi est-ce important ? Quelles sont les implications ?"

**6. Metaprompts et instructions système :**
- **System message :** Définit le rôle, contexte global, contraintes permanentes
- **User message :** Instructions spécifiques, contenu à traiter
- **Exemple de metaprompt sécurisé :**
```python
system_prompt = """
Tu es un assistant pédagogique spécialisé en IA générative.
Règles strictes :
- Toujours fournir des sources vérifiables
- Signaler les incertitudes avec "Attention: information à vérifier"
- Refuser les demandes contraires à l'éthique éducative
- Prioriser la compréhension conceptuelle sur la mémorisation
"""
```

**7. Techniques hybrides :**
- **CoT + Few-shot :** Exemples avec raisonnement détaillé
- **Self-refine + CoT :** Amélioration itérative avec justifications
- **RAG + CoT :** Recherche documentaire puis raisonnement structuré

**Exemple CoT pour slogan :**
```
User: Crée un slogan pour un soda écologique local.
Réfléchis étape par étape :
1. Quelles sont les valeurs à mettre en avant ?
2. Quel ton adopter pour les 18-35 ans ?
3. Comment créer un impact mémorable ?
```

**Exemple Self-refine :**
```
User: Crée d'abord un slogan, puis améliore-le en tenant compte de l'authenticité et de l'impact émotionnel.
```

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

**Contexte sur les fabrications :** Les modèles peuvent produire des réponses incorrectes mais plausibles (fabrications) car ils prédisent des patterns statistiques sans comprendre le sens. Ils sont entraînés sur des datasets finis et peuvent manquer de connaissances sur des événements récents ou des données non-publiques.

**Techniques de mitigation :**
- Demander des citations et du raisonnement
- Utiliser RAG (Retrieval Augmented Generation) avec des sources fiables
- Combiner plusieurs modèles pour la vérification croisée

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

**Techniques d'amélioration des modèles :**
- **Prompt engineering avec contexte :** Approche la plus cost-effective, utilise few-shot learning
- **RAG (Retrieval Augmented Generation) :** Augmente le prompt avec des données externes via des bases vectorielles
- **Fine-tuning :** Génère un nouveau modèle avec des poids mis à jour (plus coûteux)
- **Entraînement from scratch :** Approche la plus complexe, nécessite des ressources massives

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

**Métriques de qualité à évaluer :**
- **Uptime** : Disponibilité du système (>99% recommandé)
- **Temps de réponse** : Latence acceptable (<2s pour l'interactivité)
- **Précision** : Ratio des recommandations pertinentes
- **Recall** : Capacité à identifier toutes les options pertinentes
- **F1 Score** : Équilibre entre précision et recall
- **Satisfaction utilisateur** : Enquêtes et feedback continu

**Principes d'IA responsable (Microsoft) :**
- **Fairness** : Traitement équitable de tous les utilisateurs
- **Reliability & Safety** : Fonctionnement fiable et sécurisé
- **Privacy & Security** : Protection des données personnelles
- **Inclusiveness** : Accessibilité pour tous les utilisateurs
- **Transparency** : Explicabilité des recommandations
- **Accountability** : Responsabilité humaine dans les décisions

**Livrables :** Rapport d'audit avec recommandations d'amélioration.

**Objectif :** Développer un œil critique sur les systèmes d'IA en production.

**Couches de mitigation des risques :**
1. **Modèle :** Choisir le bon modèle pour le cas d'usage, utiliser des données d'entraînement appropriées
2. **Système de sécurité :** Filtres de contenu, détection des attaques de jailbreak
3. **Métaprompt :** Instructions système pour définir des limites, techniques RAG pour sources fiables
4. **Expérience utilisateur :** Interface limitant les types d'inputs, transparence sur les capacités

**Cycle d'amélioration :** Mesurer → Atténuer → Opérer → Évaluer

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
- **Images** : Stable Diffusion 1.5/XL, Flux.1, DALL-E 3
- **Multimodal** : LLaVA, Qwen-VL

**Génération d'images - Architecture technique :**

**DALL-E - Fonctionnement complet :**
- **Architecture hybride** : Combine CLIP (embeddings) et transformateur autorégressif
- **CLIP** : Génère des embeddings numériques cross-modaux (texte ↔ images)
- **Transformateur autorégressif** : Génère des images pixel par pixel avec attention diffusée
- **Evolution** : DALL-E 1 (117M paramètres) → DALL-E 2 → DALL-E 3 (contrôle et réalisme améliorés)

**Stable Diffusion - Processus de débruitage :**
- **N-steps** : 10-50 étapes de débruitage progressif (plus = meilleure qualité, plus lent)
- **CFG-scale** : Classifier-Free Guidance (7-15 recommandé) pour conformité au prompt
- **Denoising strength** : 0.3-1.0, contrôle l'intensité des modifications (img2img)

**Implémentation complète avec gestion d'erreurs :**
```python
import os
import requests
from PIL import Image
from openai import OpenAI
import dotenv

# Configuration sécurisée
dotenv.load_dotenv()
client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))

def generate_image(prompt, save_path="generated_image.png", model="dall-e-3"):
    try:
        # Génération avec paramètres optimisés
        response = client.images.generate(
            model=model,  # "dall-e-2" ou "dall-e-3"
            prompt=prompt,
            size="1024x1024",  # DALL-E 3: 1024x1024, 1024x1792, 1792x1024
            n=1,  # DALL-E 3: max 1, DALL-E 2: max 10
            quality="hd" if model == "dall-e-3" else "standard"
        )
        
        # Téléchargement et sauvegarde
        image_url = response.data[0].url
        generated_image = requests.get(image_url).content
        
        # Créer le dossier si nécessaire
        os.makedirs(os.path.dirname(save_path) if os.path.dirname(save_path) else ".", exist_ok=True)
        
        with open(save_path, "wb") as image_file:
            image_file.write(generated_image)
            
        # Affichage de l'image
        image = Image.open(save_path)
        image.show()
        
        return {"url": image_url, "path": save_path}
        
    except Exception as e:
        print(f"Erreur génération d'image: {e}")
        return None

# Exemple d'usage
result = generate_image("Chien près de la Tour Eiffel au lever du soleil")
```

**Capacités avancées :**

**1. Edition d'images avec masques (DALL-E 2 uniquement) :**
```python
def edit_image(base_image_path, mask_path, prompt):
    """
    Modifie une zone spécifique d'une image
    - base_image: Image de base (PNG, <4MB)
    - mask: Masque PNG (zones transparentes = à modifier)
    - prompt: Description des modifications
    """
    try:
        response = client.images.edit(
            image=open(base_image_path, "rb"),
            mask=open(mask_path, "rb"),
            prompt=prompt,
            n=1,
            size="1024x1024"
        )
        return response.data[0].url
    except Exception as e:
        print(f"Erreur édition: {e}")
        return None

# Exemple: ajouter un chapeau à un personnage
edit_result = edit_image("portrait.png", "mask_head.png", "Ajouter un chapeau rouge élégant")
```

**2. Variations d'images (DALL-E 2 uniquement) :**
```python
def create_variations(image_path, n_variations=3):
    """
    Crée des variantes d'une image existante
    """
    try:
        response = client.images.create_variation(
            image=open(image_path, "rb"),
            n=n_variations,  # 1-10 variations
            size="1024x1024"
        )
        return [img.url for img in response.data]
    except Exception as e:
        print(f"Erreur variations: {e}")
        return None

# Génération de 3 variantes
variations = create_variations("original_image.png", n_variations=3)
```

**3. Metaprompts pour sécurité et contrôle :**
```python
class SafeImageGenerator:
    def __init__(self, content_policy="family_friendly"):
        self.policies = {
            "family_friendly": {
                "disallow": "violence, contenu inapproprié, nudité, armes",
                "style": "coloré, positif, style illustration",
                "audience": "tout public"
            },
            "educational": {
                "disallow": "contenu commercial, marques, logos",
                "style": "schématique, pédagogique, clair",
                "audience": "étudiants"
            }
        }
        self.policy = self.policies.get(content_policy, self.policies["family_friendly"])
    
    def create_safe_prompt(self, user_prompt):
        """Génère un prompt sécurisé avec metaprompt"""
        meta_prompt = f"""Tu es un assistant graphique spécialisé.
        
RÈGLES STRICTES :
- Contenu approprié : {self.policy['audience']}
- Style requis : {self.policy['style']}
- INTERDICTIONS : {self.policy['disallow']}

PROMPT UTILISATEUR : {user_prompt}

Instructions : Crée une image respectant strictement ces règles."""
        
        return meta_prompt
    
    def generate_safe_image(self, prompt):
        """Génère une image avec contrôles de sécurité"""
        safe_prompt = self.create_safe_prompt(prompt)
        return generate_image(safe_prompt)

# Usage pour contenu éducatif
safe_gen = SafeImageGenerator("educational")
safe_image = safe_gen.generate_safe_image("Diagramme du système solaire")
```

**4. Contrôle de la créativité et reproductibilité :**
```python
def controlled_generation(prompt, creativity="balanced", seed=None):
    """
    Génération avec contrôle de créativité
    Note: DALL-E ne supporte pas directement seed/temperature,
    mais on peut influencer via la formulation du prompt
    """
    creativity_modifiers = {
        "minimal": "style réaliste, précis, détaillé",
        "balanced": "style artistique équilibré",
        "creative": "style expressif, créatif, surréaliste"
    }
    
    modifier = creativity_modifiers.get(creativity, creativity_modifiers["balanced"])
    enhanced_prompt = f"{prompt}, {modifier}"
    
    return generate_image(enhanced_prompt)

# Exemples avec différents niveaux de créativité
realistic = controlled_generation("Chat sur un coussin", creativity="minimal")
artistic = controlled_generation("Chat sur un coussin", creativity="balanced")
surreal = controlled_generation("Chat sur un coussin", creativity="creative")
```

**Bonnes pratiques pour la génération d'images :**
- **Prompts détaillés** : Plus de contexte = meilleurs résultats
- **Gestion des erreurs** : Toujours gérer les timeouts et erreurs API
- **Optimisation coûts** : DALL-E 3 plus cher mais meilleure qualité
- **Formats supportés** : PNG pour transparence, JPEG pour photos
- **Limites techniques** : 4MB max par image, certaines restrictions de contenu

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

**Bibliothèques Python essentielles :**
- **openai** : Client officiel OpenAI (pip install openai)
- **tiktoken** : Comptage de tokens (pip install tiktoken)
- **numpy, pandas** : Traitement de données
- **jupyter** : Notebooks interactifs
- **matplotlib, seaborn** : Visualisation

**Configuration Jupyter recommandée :**
```python
import os
from openai import OpenAI
import tiktoken
from dotenv import load_dotenv

# Chargement sécurisé des variables d'environnement
load_dotenv()

# Configuration des clés API
client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))
encoding = tiktoken.get_encoding("cl100k_base")

# Paramètres par défaut
MODEL_NAME = "gpt-4o-mini"
```

---

## **Notebooks Pratiques - Prompt Engineering Avancé**

**1. Zero-shot prompting :**
```python
# Exemple simple sans exemples préalables
def zero_shot_example():
    prompt = "Donne-moi 3 idées de recettes végétariennes à base de tomates."
    
    response = client.chat.completions.create(
        model=MODEL_NAME,
        messages=[{"role": "user", "content": prompt}],
        max_tokens=200,
        temperature=0.7
    )
    
    return response.choices[0].message.content

print("=== Zero-shot Exemple ===")
print(zero_shot_example())
```

**2. Few-shot prompting :**
```python
# Exemples guidant le style de réponse
def few_shot_example():
    few_shot_prompt = """
Tu es un assistant culinaire spécialisé en recettes végétariennes.
Voici des exemples de ton style de réponse :

Exemple 1:
Q: Quelles idées de salade d'été me proposes-tu ?
A: - Salade de quinoa et tomates cerises : fraîche et nutritive
   - Salade de lentilles aux oignons rouges : riche en protéines
   - Salade grecque végétarienne : méditerranéenne et savoureuse

Exemple 2:
Q: Je veux cuisiner des champignons, as-tu une idée ?
A: - Poêlée de champignons à l'ail et persil : simple et parfumée
   - Risotto aux champignons porcini : crémeux et réconfortant

Maintenant, réponds à cette question dans le même style :
Q: Propose-moi 2 plats végétariens sans gluten avec des tomates.
A:"""
    
    response = client.chat.completions.create(
        model=MODEL_NAME,
        messages=[{"role": "user", "content": few_shot_prompt}],
        max_tokens=200,
        temperature=0.7
    )
    
    return response.choices[0].message.content

print("=== Few-shot Exemple ===")
print(few_shot_example())
```

**3. Chain-of-Thought (CoT) :**
```python
# Raisonnement étape par étape
def chain_of_thought_example():
    cot_prompt = """
Alice a 5 pommes, elle en jette 2, puis elle en donne 1 à Bob.
Bob lui rend ensuite 1 pomme.
Combien de pommes Alice a-t-elle à la fin ?

Explique ton raisonnement étape par étape, puis donne la réponse finale.
"""
    
    response = client.chat.completions.create(
        model=MODEL_NAME,
        messages=[{"role": "user", "content": cot_prompt}],
        max_tokens=200,
        temperature=0.2  # Plus déterministe pour les calculs
    )
    
    return response.choices[0].message.content

print("=== Chain-of-Thought Exemple ===")
print(chain_of_thought_example())
```

**4. Self-refine (Auto-amélioration) :**
```python
# Processus d'amélioration en deux étapes
def self_refine_example():
    # Étape 1 : Génération initiale
    initial_prompt = """
Écris une courte fonction Python pour calculer la somme d'une liste.
Ajoute un bug volontaire dans le code.
"""
    
    first_response = client.chat.completions.create(
        model=MODEL_NAME,
        messages=[{"role": "user", "content": initial_prompt}],
        max_tokens=300
    )
    
    buggy_code = first_response.choices[0].message.content
    print("=== Code initial (avec bug) ===")
    print(buggy_code)
    
    # Étape 2 : Auto-correction
    refine_prompt = f"""
Voici un code Python qui contient un bug:

{buggy_code}

Peux-tu l'analyser, détecter le bug, proposer un correctif et une version améliorée ?
Explique la correction en détail.
"""
    
    second_response = client.chat.completions.create(
        model=MODEL_NAME,
        messages=[{"role": "user", "content": refine_prompt}],
        max_tokens=400,
        temperature=0.3
    )
    
    print("\n=== Code corrigé ===")
    return second_response.choices[0].message.content

print("=== Self-refine Exemple ===")
print(self_refine_example())
```

**5. Prompt interactif pour expérimentation :**
```python
def interactive_prompt_lab():
    """
    Laboratoire interactif pour tester différentes techniques
    """
    print("=== Laboratoire de Prompt Engineering ===")
    print("Tapez 'exit' pour quitter")
    
    while True:
        user_input = input("\nTape ton prompt : ")
        if user_input.strip().lower() in ["exit", "quit"]:
            print("Session terminée.")
            break
        
        # Choix de la technique
        print("\nChoisir une technique :")
        print("1. Direct (zero-shot)")
        print("2. Chain-of-Thought")
        print("3. Self-refine")
        
        choice = input("Choix (1-3): ").strip()
        
        if choice == "1":
            prompt = user_input
        elif choice == "2":
            prompt = f"{user_input}\n\nExplique ton raisonnement étape par étape."
        elif choice == "3":
            prompt = f"{user_input}\n\nDonne une première réponse, puis améliore-la."
        else:
            prompt = user_input
        
        try:
            response = client.chat.completions.create(
                model=MODEL_NAME,
                messages=[{"role": "user", "content": prompt}],
                max_tokens=300,
                temperature=0.7
            )
            
            print(f"\n=== Réponse (Technique {choice}) ===")
            print(response.choices[0].message.content)
            print("-" * 50)
            
        except Exception as e:
            print(f"Erreur: {e}")

# Décommentez pour utilisation interactive
# interactive_prompt_lab()
```

---

## **Applications Low-Code avec Power Platform**

**Power Platform - AI Builder intégration :**
```python
# Simulation d'appel Power Platform via API
import requests
import json

class PowerPlatformAIBuilder:
    def __init__(self, tenant_id, client_id, client_secret):
        self.tenant_id = tenant_id
        self.client_id = client_id
        self.client_secret = client_secret
        self.access_token = self._get_access_token()
    
    def _get_access_token(self):
        """Authentification Power Platform"""
        auth_url = f"https://login.microsoftonline.com/{self.tenant_id}/oauth2/v2.0/token"
        
        data = {
            "grant_type": "client_credentials",
            "client_id": self.client_id,
            "client_secret": self.client_secret,
            "scope": "https://api.powerapps.com/.default"
        }
        
        response = requests.post(auth_url, data=data)
        return response.json().get("access_token")
    
    def analyze_document(self, document_url):
        """Analyse de document via AI Builder"""
        api_endpoint = "https://api.powerapps.com/providers/Microsoft.PowerApps/apps/your-app-id/invoke"
        
        headers = {
            "Authorization": f"Bearer {self.access_token}",
            "Content-Type": "application/json"
        }
        
        payload = {
            "documentUrl": document_url,
            "analysisType": "form_recognizer",
            "extractFields": ["invoice_number", "total_amount", "vendor_name"]
        }
        
        try:
            response = requests.post(api_endpoint, headers=headers, json=payload)
            return response.json()
        except Exception as e:
            return {"error": f"Erreur analyse: {e}"}
    
    def sentiment_analysis(self, text_data):
        """Analyse de sentiment via AI Builder"""
        payload = {
            "text": text_data,
            "language": "fr",
            "model": "sentiment_analysis_v2"
        }
        
        # Simulation réponse sentiment
        return {
            "sentiment": "positive",  # positive/negative/neutral
            "confidence": 0.87,
            "key_phrases": ["excellent", "satisfait", "recommande"]
        }

# Usage exemple
# power_ai = PowerPlatformAIBuilder("tenant-id", "client-id", "secret")
# result = power_ai.analyze_document("https://example.com/invoice.pdf")
# sentiment = power_ai.sentiment_analysis("Ce produit est excellent, je le recommande !")
```

**Copilot Studio - Création de chatbots personnalisés :**
```yaml
# Configuration Copilot Studio (chatbot_config.yaml)
chatbot_config:
  name: "Assistant EPF GenAI"
  language: "fr-FR"
  knowledge_base:
    - source_type: "sharepoint"
      url: "https://epf.sharepoint.com/cours-genai"
    - source_type: "web"
      urls:
        - "https://docs.microsoft.com/ai"
        - "https://openai.com/documentation"
  
  intent_recognition:
    - intent: "definition_genai"
      phrases:
        - "Qu'est-ce que l'IA générative ?"
        - "Définis l'intelligence artificielle générative"
        - "Explique-moi GenAI"
      response: "L'IA générative est une technologie..."
    
    - intent: "exemple_pratique"
      phrases:
        - "Donne-moi un exemple concret"
        - "Cas d'usage pratique"
        - "Application réelle"
      response: "Voici des exemples d'applications..."
  
  advanced_features:
    function_calling: true
    web_search: true
    document_analysis: true
    multilingual: ["fr", "en"]
```

**Workflow automatisé Power Automate + AI :**
```json
{
  "workflow_name": "Analyse_CV_Automatique",
  "trigger": {
    "type": "sharepoint_file_upload",
    "folder": "/CVs_candidats"
  },
  "actions": [
    {
      "name": "extract_text_ai_builder",
      "type": "ai_builder_text_recognition",
      "input": "@{triggerBody()['FilePath']}"
    },
    {
      "name": "analyze_cv_openai",
      "type": "http_request",
      "method": "POST",
      "url": "https://api.openai.com/v1/chat/completions",
      "headers": {
        "Authorization": "Bearer @{parameters('openai_api_key')}",
        "Content-Type": "application/json"
      },
      "body": {
        "model": "gpt-4o-mini",
        "messages": [
          {
            "role": "system",
            "content": "Tu es un expert RH. Analyse ce CV et extract les compétences clés, expérience, niveau d'étude."
          },
          {
            "role": "user",
            "content": "@{outputs('extract_text_ai_builder')}"
          }
        ],
        "max_tokens": 500
      }
    },
    {
      "name": "save_analysis",
      "type": "sharepoint_create_item",
      "list": "Analyses_CV",
      "fields": {
        "Nom_Candidat": "@{outputs('analyze_cv_openai')['choices'][0]['message']['content']}",
        "Competences": "Extraites automatiquement",
        "Score_Match": "@{rand(60,95)}"
      }
    }
  ]
}
```

**Systèmes agentiques (Semantic Kernel) :**
- **ChatCompletionAgent** : Agents conversationnels
- **GroupChat** : Collaboration multi-agents
- **Plugins** : Extension des capacités

**Function Calling - Intégration APIs externes :**

**Architecture et composants :**
- **name** : Nom de la fonction que le modèle peut appeler
- **description** : Description claire et spécifique du comportement
- **parameters** : Format JSON Schema des paramètres attendus
- **type/properties** : Types de données et descriptions des propriétés
- **required** : Paramètres obligatoires pour l'exécution

```python
# Exemple complet avec gestion des erreurs
import requests
import json

# Définition de fonction pour l'IA
functions = [
    {
        "name": "search_courses",
        "description": "Recherche de cours techniques selon les critères",
        "parameters": {
            "type": "object",
            "properties": {
                "role": {"type": "string", "description": "Rôle (étudiant, développeur...)"},
                "product": {"type": "string", "description": "Technologie (Azure, Python...)"},
                "level": {"type": "string", "description": "Niveau (débutant, intermédiaire...)"}
            },
            "required": ["role"]
        }
    }
]

# Fonction Python correspondante
def search_courses(role, product=None, level=None):
    url = "https://learn.microsoft.com/api/catalog/"
    params = {"role": role}
    if product:
        params["product"] = product
    if level:
        params["level"] = level
    
    try:
        response = requests.get(url, params=params)
        modules = response.json()["modules"]
        results = []
        for module in modules[:5]:
            results.append({
                "title": module["title"],
                "url": module["url"]
            })
        return str(results)
    except Exception as e:
        return f"Erreur API: {str(e)}"

# Pipeline complet d'exécution
def execute_function_call(user_input):
    # 1. Appel initial pour obtenir la fonction
    response = client.chat.completions.create(
        model="gpt-4o-mini",
        messages=[{"role": "user", "content": user_input}],
        functions=functions,
        function_call="auto"
    )
    
    response_message = response.choices[0].message
    
    # 2. Vérification et exécution de la fonction
    if response_message.function_call:
        function_name = response_message.function_call.name
        available_functions = {"search_courses": search_courses}
        
        function_to_call = available_functions[function_name]
        function_args = json.loads(response_message.function_call.arguments)
        function_response = function_to_call(**function_args)
        
        # 3. Ajout des résultats au contexte
        messages = [
            {"role": "user", "content": user_input},
            {
                "role": "assistant",
                "function_call": {
                    "name": function_name,
                    "arguments": response_message.function_call.arguments,
                },
                "content": None
            },
            {
                "role": "function",
                "name": function_name,
                "content": function_response,
            }
        ]
        
        # 4. Génération de la réponse finale
        second_response = client.chat.completions.create(
            model="gpt-4o-mini",
            messages=messages,
            temperature=0
        )
        
        return second_response.choices[0].message.content
    
    return response_message.content

# Exemple d'usage
# result = execute_function_call("Je cherche des cours Azure pour débutant")
```

**Cas d'usage avancés :**
- **Gestion d'erreurs** : Validation des paramètres et fallback en cas d'échec API
- **Fonctions multiples** : Le modèle choisit automatiquement la fonction appropriée
- **Chaînage de fonctions** : Une fonction peut déclencher l'appel d'une autre
- **Validation de sécurité** : Vérification des permissions avant exécution

**RAG (Retrieval Augmented Generation) :**

**Architecture et principe :**
RAG augmente les capacités des LLMs en leur fournissant un accès à des bases de connaissances externes, résolvant les limites de connaissance et réduisant les fabrications.

**Processus RAG :**
1. **Knowledge Base** : Documents preprocessés, découpés en chunks, convertis en embeddings
2. **User Query** : Question de l'utilisateur transformée en vecteur de requête
3. **Retrieval** : Recherche vectorielle pour trouver les chunks les plus pertinents
4. **Augmented Generation** : Contexte récupéré intégré au prompt du LLM

**Bases de données vectorielles :**
- **Azure Cosmos DB** : Solution cloud avec support vectoriel natif
- **Pinecone, Chroma, Qdrant** : Solutions spécialisées
- **FAISS, ScaNN** : Bibliothèques de recherche vectorielle haute performance

**Implémentation pratique :**
```python
# Configuration base de données vectorielle
from sklearn.neighbors import NearestNeighbors
import pandas as pd

# Chunking intelligent des documents
def split_text(text, max_length=400, min_length=300):
    words = text.split()
    chunks = []
    current_chunk = []
    
    for word in words:
        current_chunk.append(word)
        combined = " ".join(current_chunk)
        if len(combined) > min_length and len(combined) < max_length:
            chunks.append(combined)
            current_chunk = []
    
    if current_chunk:
        chunks.append(" ".join(current_chunk))
    return chunks

# Génération d'embeddings
def create_embeddings(text, model="text-embedding-ada-002"):
    response = client.embeddings.create(input=text, model=model)
    return response.data[0].embedding

# Index de recherche vectorielle
def build_vector_index(chunks_df):
    embeddings = chunks_df['embeddings'].to_list()
    nbrs = NearestNeighbors(n_neighbors=5, algorithm='ball_tree').fit(embeddings)
    return nbrs

# Pipeline RAG complet
def rag_query(user_question, vector_index, chunks_df, top_k=3):
    # 1. Embedding de la question
    query_vector = create_embeddings(user_question)
    
    # 2. Recherche des chunks pertinents
    distances, indices = vector_index.kneighbors([query_vector], n_neighbors=top_k)
    
    # 3. Construction du contexte
    context_chunks = []
    for idx in indices[0]:
        context_chunks.append(chunks_df.iloc[idx]['chunks'])
    
    context = "\n\n".join(context_chunks)
    
    # 4. Génération augmentée
    messages = [
        {"role": "system", "content": "Utilisez le contexte fourni pour répondre avec précision."},
        {"role": "user", "content": f"Contexte:\n{context}\n\nQuestion: {user_question}"}
    ]
    
    response = client.chat.completions.create(
        model="gpt-4o-mini",
        messages=messages,
        temperature=0.7,
        max_tokens=800
    )
    
    return response.choices[0].message.content

# Évaluation de la qualité RAG
def evaluate_rag_quality(test_cases):
    """
    Métriques recommandées :
    - Groundedness : Réponse basée sur les documents fournis
    - Relevance : Pertinence par rapport à la question
    - Fluency : Qualité linguistique de la réponse
    """
    from sklearn.metrics import average_precision_score
    
    total_precision = 0
    for test_case in test_cases:
        query = test_case["query"]
        expected = test_case["relevant_responses"]
        
        response = rag_query(query, vector_index, chunks_df)
        # Calcul de métrique (simplifié)
        relevance_score = calculate_relevance(response, expected)
        total_precision += relevance_score
    
    return total_precision / len(test_cases)
```

**Métriques d'évaluation RAG avancées :**

**Architecture RAG selon recherche académique :**
- **RAG-Sequence** : Documents récupérés pour prédire la meilleure réponse complète
- **RAG-Token** : Documents récupérés pour générer chaque token individuellement

**Évaluation de qualité - LLM-as-a-Judge :**
```python
def evaluate_groundedness(question, response, source_documents):
    """Évalue si la réponse est basée sur les documents sources"""
    groundedness_prompt = f"""
    Évalue si cette réponse est entièrement basée sur les documents fournis.
    
    Question: {question}
    Réponse: {response}
    Documents sources: {source_documents[:1000]}...
    
    Critères d'évaluation:
    1. Toutes les informations sont-elles présentes dans les sources?
    2. Y a-t-il des fabrications ou informations externes?
    3. Les citations sont-elles exactes?
    
    Note sur 5: 1=Pas ancré, 3=Partiellement ancré, 5=Complètement ancré
    Réponds uniquement avec un chiffre.
    """
    
    response = client.chat.completions.create(
        model="gpt-4o-mini",
        messages=[{"role": "user", "content": groundedness_prompt}],
        max_tokens=10,
        temperature=0.1
    )
    
    try:
        return int(response.choices[0].message.content.strip())
    except:
        return 3  # Score par défaut
```

**Métriques de similarité vectorielle :**
```python
def vector_similarity_methods():
    """Différentes approches de mesure de similarité"""
    import numpy as np
    from sklearn.metrics.pairwise import cosine_similarity
    
    def cosine_distance(vec1, vec2):
        """Basée sur l'angle entre vecteurs (plus commune)"""
        return cosine_similarity([vec1], [vec2])[0][0]
    
    def euclidean_distance(vec1, vec2):
        """Distance ligne droite entre points de fin"""
        return np.linalg.norm(np.array(vec1) - np.array(vec2))
    
    def dot_product_similarity(vec1, vec2):
        """Somme des produits des éléments correspondants"""
        return np.dot(vec1, vec2)
    
    return {
        "cosine": cosine_distance,
        "euclidean": euclidean_distance,
        "dot_product": dot_product_similarity
    }
```

**Reranking sémantique :**
```python
def semantic_reranker(query_vector, candidate_chunks, original_scores):
    """Améliore le classement initial avec analyse contextuelle"""
    reranked_results = []
    
    for i, (chunk, original_score) in enumerate(zip(candidate_chunks, original_scores)):
        # Score combiné : similarité vectorielle + pertinence contextuelle
        contextual_score = calculate_contextual_relevance(query_vector, chunk)
        combined_score = (original_score * 0.7) + (contextual_score * 0.3)
        
        reranked_results.append({
            "chunk_index": i,
            "chunk_content": chunk,
            "original_score": original_score,
            "reranked_score": combined_score
        })
    
    # Tri par score reranké décroissant
    reranked_results.sort(key=lambda x: x["reranked_score"], reverse=True)
    return reranked_results
```

**Cas d'usage avancés RAG :**

**1. Systèmes de recommandation :**
```python
# RAG pour recommandations personnalisées
def recommend_with_rag(user_preferences, item_database):
    """
    Utilise RAG pour des recommandations contextualisées
    """
    # Embedding des préférences utilisateur
    user_vector = create_embeddings(user_preferences)
    
    # Recherche d'items similaires dans la base vectorielle
    similar_items = vector_search(user_vector, item_database)
    
    # Génération de recommandations personnalisées
    context = f"Préférences utilisateur: {user_preferences}\nItems similaires: {similar_items}"
    
    recommendations = client.chat.completions.create(
        model="gpt-4o-mini",
        messages=[
            {"role": "system", "content": "Tu es un système de recommandation intelligent."},
            {"role": "user", "content": f"{context}\n\nGénère 5 recommandations personnalisées avec justifications."}
        ]
    )
    
    return recommendations.choices[0].message.content
```

**2. Chatbots avec mémoire conversationnelle :**
```python
class ConversationalRAG:
    def __init__(self):
        self.conversation_history = []
        self.user_profile = {}
    
    def chat_with_memory(self, user_input, session_id):
        """Chatbot qui se souvient des conversations précédentes"""
        
        # Récupération du contexte conversationnel
        relevant_history = self.get_relevant_history(user_input, session_id)
        
        # Construction du prompt avec mémoire
        context = f"Historique pertinent: {relevant_history}\nQuestion actuelle: {user_input}"
        
        response = client.chat.completions.create(
            model="gpt-4o-mini",
            messages=[
                {"role": "system", "content": "Tu maintiens la cohérence conversationnelle."},
                {"role": "user", "content": context}
            ]
        )
        
        # Sauvegarde de l'échange
        self.save_to_memory(user_input, response.choices[0].message.content, session_id)
        
        return response.choices[0].message.content
    
    def get_relevant_history(self, current_input, session_id):
        """Récupère les échanges pertinents de l'historique"""
        # Embedding de la question actuelle
        current_vector = create_embeddings(current_input)
        
        # Recherche dans l'historique conversationnel
        # (implémentation simplifiée)
        return "Contexte des conversations précédentes..."
```

**3. Recherche d'images par description :**
```python
def image_search_with_rag(text_query, image_database):
    """
    Recherche d'images basée sur des descriptions textuelles
    """
    # Embedding de la requête textuelle
    query_vector = create_embeddings(text_query)
    
    # Recherche dans base d'embeddings d'images
    # (Les images ont été préalablement converties en embeddings via CLIP)
    similar_images = vector_search(query_vector, image_database)
    
    # Retourne les images les plus pertinentes
    return {
        "query": text_query,
        "results": similar_images,
        "applications": ["e-commerce", "design", "recherche scientifique"]
    }
```

**4. Détection d'anomalies avec RAG :**
```python
def anomaly_detection_rag(data_point, normal_patterns_db):
    """
    Détection d'anomalies basée sur la distance vectorielle
    """
    # Embedding du point de données
    data_vector = create_embeddings(str(data_point))
    
    # Calcul des distances avec patterns normaux
    distances = []
    for normal_pattern in normal_patterns_db:
        pattern_vector = create_embeddings(str(normal_pattern))
        distance = euclidean_distance(data_vector, pattern_vector)
        distances.append(distance)
    
    # Seuil d'anomalie
    avg_distance = sum(distances) / len(distances)
    anomaly_threshold = avg_distance * 2  # Exemple de seuil
    
    is_anomaly = min(distances) > anomaly_threshold
    
    return {
        "is_anomaly": is_anomaly,
        "confidence": min(distances),
        "threshold": anomaly_threshold,
        "applications": ["sécurité", "fraude", "maintenance prédictive"]
    }
```

**Notebook Jupyter - Exemple complet RAG :**
```python
# Configuration complète pour cours pratique
import os
import pandas as pd
import numpy as np
from openai import OpenAI
from sklearn.neighbors import NearestNeighbors

# Setup
client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))

# Pipeline complet avec Azure Cosmos DB
class EducationalRAG:
    def __init__(self, cosmos_endpoint, cosmos_key):
        self.cosmos_client = CosmosClient(cosmos_endpoint, cosmos_key)
        self.database = self.cosmos_client.get_database_client('rag-education')
        self.container = self.database.get_container_client('course-materials')
    
    def ingest_documents(self, file_paths):
        """Ingestion et traitement des documents de cours"""
        documents = []
        
        for path in file_paths:
            with open(path, 'r', encoding='utf-8') as file:
                content = file.read()
                
                # Chunking intelligent
                chunks = self.smart_chunking(content, path)
                
                for chunk in chunks:
                    # Génération d'embeddings
                    embedding = create_embeddings(chunk)
                    
                    doc = {
                        "id": f"{path}_{len(documents)}",
                        "path": path,
                        "content": chunk,
                        "embedding": embedding
                    }
                    documents.append(doc)
        
        return documents
    
    def smart_chunking(self, text, source_path):
        """Chunking adapté au contenu éducatif"""
        # Découpage par sections pour maintenir le contexte
        sections = text.split('\n\n')
        chunks = []
        
        current_chunk = ""
        for section in sections:
            if len(current_chunk + section) < 500:
                current_chunk += section + "\n\n"
            else:
                if current_chunk:
                    chunks.append(current_chunk.strip())
                current_chunk = section + "\n\n"
        
        if current_chunk:
            chunks.append(current_chunk.strip())
            
        return chunks
    
    def query_educational_content(self, question, subject_filter=None):
        """Requête spécialisée pour contenu éducatif"""
        
        # Embedding de la question
        query_vector = create_embeddings(question)
        
        # Recherche dans la base de connaissances
        # (implémentation complète avec Cosmos DB)
        relevant_chunks = self.vector_search(query_vector, subject_filter)
        
        # Prompt spécialisé éducation
        educational_prompt = f"""
        Tu es un assistant pédagogique expert. Utilise ces ressources de cours pour répondre.
        
        Question de l'étudiant: {question}
        
        Ressources de cours:
        {relevant_chunks}
        
        Instructions:
        1. Réponds de manière claire et structurée
        2. Utilise des exemples concrets quand possible
        3. Cite tes sources
        4. Propose des exercices pratiques si pertinent
        5. Indique les prérequis si nécessaire
        """
        
        response = client.chat.completions.create(
            model="gpt-4o-mini",
            messages=[{"role": "user", "content": educational_prompt}],
            temperature=0.3,  # Plus déterministe pour l'éducation
            max_tokens=800
        )
        
        return response.choices[0].message.content
```

**Applications Low-Code avec IA :**
- **Power Platform** : Copilot pour création d'apps et workflows
- **AI Builder** : Modèles préconstruits (extraction invoices, analyse sentiment)
- **Automatisation** : Traitement documents, emails, intégrations APIs
- **Interface naturelle** : Description en langage courant → application fonctionnelle

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