# Tutorial Complet : GPT-5 Multimodal - Analyse d'Images pour CoursIA

## Table des Matières
1. [Introduction](#introduction)
2. [Configuration OpenRouter](#configuration-openrouter)
3. [Analyse d'Images et Description](#analyse-images)
4. [Conversations Multimodales Avancées](#conversations-multimodales)
5. [Templates Cas Pédagogiques](#templates-pedagogiques)
6. [Alt Text et Accessibilité](#alt-text-accessibilite)
7. [Intégration avec DALL-E](#integration-dalle)
8. [Performance et Cost Management](#performance-cost)

---

## Introduction

GPT-5 représente une avancée majeure dans l'analyse multimodale, combinant compréhension textuelle et visuelle. Ce guide explore son utilisation via OpenRouter pour créer des expériences pédagogiques enrichies dans CoursIA.

### Capacités Clés GPT-5
- **Vision avancée** : Analyse détaillée d'images complexes
- **Contexte étendu** : 200K+ tokens pour conversations longues
- **Raisonnement spatial** : Compréhension géométrique et positionnelle
- **Extraction structurée** : Données depuis graphiques, diagrammes
- **Multi-langue** : Support français natif
- **Précision pédagogique** : Descriptions adaptées au niveau scolaire

### Cas d'Usage Éducatifs
- Analyse documents historiques
- Extraction données graphiques scientifiques
- Description illustrations pour accessibilité
- Évaluation travaux visuels étudiants
- Génération questions depuis images
- Correction exercices visuels

---

## Configuration OpenRouter

### Setup Initial

```python
import os
import base64
from openai import OpenAI
from PIL import Image
import requests
from io import BytesIO

# Configuration OpenRouter pour GPT-5
client = OpenAI(
    api_key=os.getenv("OPENROUTER_API_KEY"),
    base_url="https://openrouter.ai/api/v1"
)

# Modèle GPT-5
GPT5_MODEL = "openai/gpt-5-preview"

def verify_openrouter_config():
    """Vérifie configuration OpenRouter"""
    try:
        response = client.chat.completions.create(
            model=GPT5_MODEL,
            messages=[{"role": "user", "content": "Test connection"}],
            max_tokens=10
        )
        print("✅ OpenRouter configuré correctement")
        return True
    except Exception as e:
        print(f"❌ Erreur configuration: {e}")
        return False
```

### Préparation Images

```python
def encode_image_base64(image_path):
    """
    Encode image en base64 pour API
    
    Args:
        image_path: Chemin vers l'image
    
    Returns:
        String base64 de l'image
    """
    with open(image_path, "rb") as image_file:
        return base64.b64encode(image_file.read()).decode('utf-8')

def encode_image_url(image_url):
    """
    Télécharge et encode image depuis URL
    
    Args:
        image_url: URL de l'image
    
    Returns:
        String base64 de l'image
    """
    response = requests.get(image_url)
    return base64.b64encode(response.content).decode('utf-8')

def resize_image_for_api(image_path, max_size=(2048, 2048)):
    """
    Redimensionne image pour optimiser coûts API
    
    Args:
        image_path: Chemin image
        max_size: Dimensions maximales
    """
    img = Image.open(image_path)
    img.thumbnail(max_size, Image.Resampling.LANCZOS)
    
    # Sauvegarde temporaire
    temp_path = f"temp_resized_{os.path.basename(image_path)}"
    img.save(temp_path, optimize=True)
    
    return temp_path
```

### Format Messages Multimodaux

```python
def create_image_message(image_path, prompt, detail="auto"):
    """
    Crée message avec image pour GPT-5
    
    Args:
        image_path: Chemin image locale
        prompt: Question/instruction textuelle
        detail: 'low' (rapide/économique), 'high' (détaillé), 'auto'
    
    Returns:
        Format message OpenAI
    """
    base64_image = encode_image_base64(image_path)
    
    return {
        "role": "user",
        "content": [
            {
                "type": "text",
                "text": prompt
            },
            {
                "type": "image_url",
                "image_url": {
                    "url": f"data:image/jpeg;base64,{base64_image}",
                    "detail": detail
                }
            }
        ]
    }
```

---

## Analyse d'Images et Description

### Analyse de Base

```python
def analyze_image(image_path, prompt="Décris cette image en détail"):
    """
    Analyse basique d'une image avec GPT-5
    
    Args:
        image_path: Chemin image
        prompt: Instructions d'analyse
    
    Returns:
        Description textuelle
    """
    try:
        message = create_image_message(image_path, prompt)
        
        response = client.chat.completions.create(
            model=GPT5_MODEL,
            messages=[message],
            max_tokens=500,
            temperature=0.7
        )
        
        description = response.choices[0].message.content
        print(f"✅ Analyse complétée ({response.usage.total_tokens} tokens)")
        
        return {
            'description': description,
            'tokens_used': response.usage.total_tokens,
            'model': GPT5_MODEL
        }
        
    except Exception as e:
        print(f"❌ Erreur analyse: {e}")
        return None
```

### Analyse Structurée

```python
def analyze_image_structured(image_path, analysis_type="educational"):
    """
    Analyse structurée selon type pédagogique
    
    Args:
        image_path: Chemin image
        analysis_type: Type d'analyse (educational, scientific, historical)
    
    Returns:
        Analyse structurée par sections
    """
    prompts = {
        "educational": """Analyse cette image de manière pédagogique:

1. DESCRIPTION GÉNÉRALE (2-3 phrases)
2. ÉLÉMENTS CLÉS (liste bullet points)
3. CONCEPTS PÉDAGOGIQUES (notions enseignables)
4. NIVEAU SCOLAIRE RECOMMANDÉ
5. QUESTIONS PÉDAGOGIQUES (3-5 questions)

Format: Markdown structuré, français clair.""",

        "scientific": """Analyse scientifique de cette image:

1. TYPE DE DOCUMENT (diagramme, graphique, photo, etc.)
2. DONNÉES VISUELLES (mesures, valeurs, échelles)
3. CONCEPTS SCIENTIFIQUES (théories illustrées)
4. INTERPRÉTATION (ce que montre l'image)
5. APPLICATIONS PÉDAGOGIQUES

Format: Précis et technique.""",

        "historical": """Analyse historique de cette image:

1. PÉRIODE HISTORIQUE (estimation)
2. CONTEXTE (événement, lieu, personnages)
3. ÉLÉMENTS HISTORIQUES (vêtements, architecture, objets)
4. SIGNIFICATION HISTORIQUE
5. LIENS PROGRAMME SCOLAIRE

Format: Contextualisé et pédagogique.""",

        "artistic": """Analyse artistique de cette image:

1. STYLE ARTISTIQUE (mouvement, technique)
2. COMPOSITION (éléments visuels, couleurs)
3. TECHNIQUE (médium, méthode)
4. INTERPRÉTATION ARTISTIQUE
5. EXPLOITATION PÉDAGOGIQUE

Format: Descriptif et inspirant."""
    }
    
    prompt = prompts.get(analysis_type, prompts["educational"])
    return analyze_image(image_path, prompt)
```

### Extraction d'Informations Spécifiques

```python
def extract_text_from_image(image_path):
    """Extrait texte visible dans image (OCR multimodal)"""
    prompt = """Identifie et transcris TOUT le texte visible dans cette image.

Format:
- Liste chaque élément textuel
- Préserve formatage si pertinent
- Indique position approximative
- Note langues différentes"""
    
    return analyze_image(image_path, prompt)

def extract_data_from_chart(image_path):
    """Extrait données depuis graphique ou tableau"""
    prompt = """Extrait les données de ce graphique/tableau:

1. TYPE DE GRAPHIQUE/TABLEAU
2. AXES/COLONNES (labels et unités)
3. DONNÉES (valeurs numériques)
4. LÉGENDE (si présente)
5. TITRE/CAPTION

Format: Structure JSON ou tableau Markdown."""
    
    return analyze_image(image_path, prompt)

def identify_objects_and_concepts(image_path, subject_area="general"):
    """Identifie objets et concepts pertinents par domaine"""
    prompts = {
        "sciences": "Identifie tous les éléments scientifiques (organismes, appareils, phénomènes) avec nomenclature précise.",
        "mathématiques": "Identifie figures géométriques, symboles mathématiques, formules, mesures visibles.",
        "histoire": "Identifie éléments historiques (personnages, lieux, objets d'époque, symboles).",
        "géographie": "Identifie éléments géographiques (relief, cours d'eau, végétation, aménagements).",
        "général": "Identifie et catégorise tous les objets, personnes, lieux, concepts visibles."
    }
    
    prompt = prompts.get(subject_area, prompts["général"])
    return analyze_image(image_path, prompt)
```

---

## Conversations Multimodales Avancées

### Dialogue Contextuel

```python
class MultimodalConversation:
    """Gestion conversations multimodales avec contexte"""
    
    def __init__(self, subject="général"):
        self.subject = subject
        self.conversation_history = []
        self.images_analyzed = []
    
    def add_image(self, image_path, initial_prompt):
        """Ajoute image à la conversation"""
        message = create_image_message(image_path, initial_prompt)
        self.conversation_history.append(message)
        self.images_analyzed.append(image_path)
        
        # Réponse initiale
        response = self._get_response()
        return response
    
    def ask_followup(self, question):
        """Pose question de suivi sur images précédentes"""
        self.conversation_history.append({
            "role": "user",
            "content": question
        })
        
        response = self._get_response()
        return response
    
    def compare_images(self, image_path_1, image_path_2, comparison_prompt):
        """Compare deux images dans le contexte"""
        # Image 1
        msg1 = create_image_message(
            image_path_1, 
            "Image 1 pour comparaison:"
        )
        
        # Image 2
        msg2 = create_image_message(
            image_path_2,
            "Image 2 pour comparaison:"
        )
        
        # Prompt de comparaison
        comparison_msg = {
            "role": "user",
            "content": f"Maintenant compare ces deux images: {comparison_prompt}"
        }
        
        self.conversation_history.extend([msg1, msg2, comparison_msg])
        response = self._get_response()
        
        return response
    
    def _get_response(self):
        """Obtient réponse GPT-5 avec historique"""
        try:
            response = client.chat.completions.create(
                model=GPT5_MODEL,
                messages=self.conversation_history,
                max_tokens=1000,
                temperature=0.7
            )
            
            assistant_message = response.choices[0].message.content
            
            # Ajoute à l'historique
            self.conversation_history.append({
                "role": "assistant",
                "content": assistant_message
            })
            
            return {
                'response': assistant_message,
                'tokens': response.usage.total_tokens
            }
            
        except Exception as e:
            return {'error': str(e)}
    
    def get_summary(self):
        """Résumé de la conversation"""
        summary_prompt = f"""Résume notre conversation sur {len(self.images_analyzed)} image(s):

1. Images analysées
2. Thèmes principaux
3. Conclusions clés
4. Points pédagogiques importants

Format: Markdown structuré."""
        
        return self.ask_followup(summary_prompt)
```

**Exemple d'utilisation** :
```python
# Conversation pédagogique
conv = MultimodalConversation(subject="biologie")

# Analyse initiale
result1 = conv.add_image(
    "cellule_vegetale.png",
    "Décris cette cellule végétale en détail pour des élèves de collège"
)
print(result1['response'])

# Questions de suivi
result2 = conv.ask_followup(
    "Quelles différences principales avec une cellule animale?"
)

result3 = conv.ask_followup(
    "Génère 3 questions d'évaluation sur cette image"
)

# Résumé
summary = conv.get_summary()
```

### Analyse Comparative Multi-Images

```python
def compare_multiple_images(image_paths, comparison_criteria):
    """
    Compare plusieurs images selon critères spécifiques
    
    Args:
        image_paths: Liste de chemins d'images
        comparison_criteria: Critères de comparaison
    
    Returns:
        Analyse comparative structurée
    """
    messages = []
    
    # Ajout de chaque image
    for i, path in enumerate(image_paths):
        messages.append(
            create_image_message(
                path,
                f"Image {i+1}/{len(image_paths)} pour analyse comparative:"
            )
        )
    
    # Prompt de comparaison
    comparison_prompt = f"""Compare ces {len(image_paths)} images selon:

{comparison_criteria}

Structure ta réponse:
1. TABLEAU COMPARATIF (markdown)
2. SIMILITUDES
3. DIFFÉRENCES MAJEURES
4. ANALYSE PÉDAGOGIQUE
5. APPLICATIONS EN CLASSE

Format: Clair et structuré."""
    
    messages.append({
        "role": "user",
        "content": comparison_prompt
    })
    
    # Génération réponse
    response = client.chat.completions.create(
        model=GPT5_MODEL,
        messages=messages,
        max_tokens=1500,
        temperature=0.7
    )
    
    return response.choices[0].message.content
```

---

## Templates Cas Pédagogiques

### Sciences Naturelles

```python
SCIENCE_TEMPLATES = {
    "anatomie": {
        "prompt": """Analyse anatomique pédagogique:

1. Identification structure/organe
2. Composants principaux (avec annotations)
3. Fonction biologique
4. Relations avec autres systèmes
5. Niveau de complexité (primaire/collège/lycée)
6. Exercices suggérés (3 questions progressives)""",
        
        "followup_questions": [
            "Quelles expériences pratiques pour illustrer cette structure?",
            "Quelles erreurs communes des élèves sur ce sujet?",
            "Comment simplifier pour élèves en difficulté?"
        ]
    },
    
    "expérience": {
        "prompt": """Analyse d'expérience scientifique:

1. Type d'expérience
2. Matériel visible
3. Protocole probable
4. Phénomène observé
5. Concepts scientifiques illustrés
6. Précautions sécurité
7. Adaptations pédagogiques par niveau""",
        
        "safety_check": "Identifie tous risques potentiels pour classe"
    }
}

def analyze_science_image(image_path, template_type="anatomie"):
    """Analyse image scientifique avec template pédagogique"""
    template = SCIENCE_TEMPLATES.get(template_type)
    
    result = analyze_image(image_path, template['prompt'])
    
    # Questions complémentaires optionnelles
    if 'followup_questions' in template:
        conv = MultimodalConversation(subject="sciences")
        conv.add_image(image_path, template['prompt'])
        
        followups = []
        for q in template['followup_questions']:
            followups.append(conv.ask_followup(q))
        
        result['followup_analysis'] = followups
    
    return result
```

### Histoire et Documents

```python
HISTORY_TEMPLATES = {
    "document_historique": {
        "prompt": """Analyse historique pédagogique:

1. Type de document (photo, tableau, affiche, etc.)
2. Datation estimée (indices visuels)
3. Contexte historique (événement, période)
4. Personnages/lieux identifiables
5. Signification historique
6. Biais ou propagande potentiels
7. Exploitation pédagogique:
   - Niveau scolaire
   - Thèmes programme
   - Questions analyse documentaire (3-5)
   - Activités suggérées""",
        
        "critical_thinking": "Analyse critique: Que révèle/cache ce document? Quel point de vue représente-t-il?"
    },
    
    "chronologie": {
        "prompt": """Analyse chronologique:

1. Éléments datables (vêtements, technologie, architecture)
2. Estimation période historique
3. Évolution visible (avant/après si comparaison)
4. Marqueurs temporels clés
5. Intégration frise chronologique
6. Exercices repérage temporel"""
    }
}

def analyze_historical_document(image_path, template_type="document_historique"):
    """Analyse document historique avec approche critique"""
    template = HISTORY_TEMPLATES.get(template_type)
    
    # Analyse principale
    result = analyze_image(image_path, template['prompt'])
    
    # Analyse critique optionnelle
    if 'critical_thinking' in template:
        conv = MultimodalConversation(subject="histoire")
        conv.add_image(image_path, template['prompt'])
        critical = conv.ask_followup(template['critical_thinking'])
        result['critical_analysis'] = critical
    
    return result
```

### Mathématiques et Géométrie

```python
MATH_TEMPLATES = {
    "géométrie": {
        "prompt": """Analyse géométrique:

1. Figures identifiées (noms précis)
2. Propriétés géométriques visibles
3. Mesures/angles notés
4. Relations spatiales (parallèles, perpendiculaires, etc.)
5. Théorèmes applicables
6. Niveau difficulté (école/collège/lycée)
7. Exercices générables (3 progressifs)""",
        
        "problem_generation": "Crée 3 problèmes de difficulté croissante basés sur cette figure"
    },
    
    "graphique": {
        "prompt": """Analyse graphique mathématique:

1. Type de graphique (fonction, statistique, etc.)
2. Données/valeurs extractibles
3. Domaine et image (si fonction)
4. Propriétés mathématiques (croissance, extrema, etc.)
5. Interprétation mathématique
6. Questions exploitation (5 niveaux progressifs)"""
    }
}

def analyze_math_diagram(image_path, template_type="géométrie"):
    """Analyse diagramme mathématique avec génération d'exercices"""
    template = MATH_TEMPLATES.get(template_type)
    
    result = analyze_image(image_path, template['prompt'])
    
    # Génération problèmes optionnelle
    if 'problem_generation' in template:
        conv = MultimodalConversation(subject="mathématiques")
        conv.add_image(image_path, template['prompt'])
        problems = conv.ask_followup(template['problem_generation'])
        result['generated_problems'] = problems
    
    return result
```

---

## Alt Text et Accessibilité

### Génération Alt Text

```python
def generate_alt_text(image_path, context="educational", max_length=125):
    """
    Génère alt text accessible selon WCAG 2.1
    
    Args:
        image_path: Chemin image
        context: Contexte d'utilisation
        max_length: Longueur maximale (WCAG recommande <125 char)
    
    Returns:
        Alt text optimisé
    """
    prompts = {
        "educational": f"""Génère alt text pour cette image pédagogique (max {max_length} caractères):

Règles WCAG 2.1:
- Décris contenu essentiel
- Contexte pédagogique clair
- Pas "image de..." (implicite)
- Concis mais informatif
- Français correct

Format: Texte brut, une phrase.""",

        "decorative": "Cette image est-elle purement décorative? Si oui, réponds 'DECORATIVE'. Sinon, génère alt text court.",
        
        "complex": f"""Alt text pour image complexe (diagramme/graphique):

Court alt text ({max_length} char max): [description succincte]
Description longue (séparée): [description détaillée pour longdesc]"""
    }
    
    result = analyze_image(image_path, prompts.get(context, prompts["educational"]))
    
    # Validation longueur
    alt_text = result['description'].strip()
    if len(alt_text) > max_length:
        # Raccourcir si nécessaire
        truncate_prompt = f"Raccourcis ce alt text à maximum {max_length} caractères en gardant l'essentiel: {alt_text}"
        alt_text = analyze_image(image_path, truncate_prompt)['description'].strip()
    
    return alt_text

def generate_long_description(image_path, alt_text):
    """
    Génère description longue pour images complexes (longdesc)
    
    Args:
        image_path: Chemin image
        alt_text: Alt text court déjà généré
    """
    prompt = f"""Description longue détaillée pour accessibilité.

Alt text court existant: "{alt_text}"

Génère description longue HTML (<longdesc>) incluant:
1. Description complète et structurée
2. Toutes données/informations visuelles
3. Relations spatiales importantes
4. Interprétation si pertinent

Format: HTML avec structure sémantique (headings, lists)."""
    
    return analyze_image(image_path, prompt)
```

### Audit Accessibilité Batch

```python
def audit_images_accessibility(image_directory):
    """
    Audite accessibilité de plusieurs images
    
    Args:
        image_directory: Répertoire contenant images
    
    Returns:
        Rapport accessibilité avec recommandations
    """
    import glob
    
    images = glob.glob(f"{image_directory}/*.png") + glob.glob(f"{image_directory}/*.jpg")
    
    audit_report = []
    
    for img_path in images:
        print(f"🔍 Audit: {os.path.basename(img_path)}")
        
        # Alt text
        alt = generate_alt_text(img_path)
        
        # Classification
        classification_prompt = """Classifie cette image selon WCAG:

1. DECORATIVE (purement esthétique)
2. INFORMATIVE (contenu essentiel)
3. FUNCTIONAL (bouton, lien, contrôle)
4. COMPLEX (diagramme, graphique nécessitant description longue)

Réponds juste la catégorie."""
        
        classification = analyze_image(img_path, classification_prompt)['description'].strip()
        
        # Recommandations
        needs_longdesc = classification == "COMPLEX"
        
        audit_report.append({
            'filename': os.path.basename(img_path),
            'alt_text': alt,
            'classification': classification,
            'needs_longdesc': needs_longdesc,
            'wcag_compliant': len(alt) <= 125 if classification != "DECORATIVE" else True
        })
    
    return audit_report
```

---

## Intégration avec DALL-E

### Pipeline Génération → Analyse

```python
class ImageCreationAnalysisPipeline:
    """Pipeline intégré DALL-E génération + GPT-5 analyse"""
    
    def __init__(self):
        self.dalle_client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))
        self.gpt5_client = OpenAI(
            api_key=os.getenv("OPENROUTER_API_KEY"),
            base_url="https://openrouter.ai/api/v1"
        )
    
    def generate_and_validate(self, prompt, validation_criteria):
        """
        Génère image et valide qualité automatiquement
        
        Args:
            prompt: Prompt DALL-E
            validation_criteria: Critères de validation
        
        Returns:
            Image + rapport validation
        """
        # Génération DALL-E
        print("🎨 Génération image...")
        dalle_response = self.dalle_client.images.generate(
            model="dall-e-3",
            prompt=prompt,
            size="1024x1024",
            quality="standard",
            n=1
        )
        
        image_url = dalle_response.data[0].url
        revised_prompt = dalle_response.data[0].revised_prompt
        
        # Téléchargement
        temp_path = "temp_validation.png"
        response = requests.get(image_url)
        with open(temp_path, 'wb') as f:
            f.write(response.content)
        
        # Validation GPT-5
        print("🔍 Validation qualité...")
        validation_prompt = f"""Valide cette image générée selon critères:

PROMPT ORIGINAL: {prompt}
PROMPT RÉVISÉ: {revised_prompt}

CRITÈRES DE VALIDATION:
{validation_criteria}

Évalue:
1. Respect du prompt (0-10)
2. Qualité pédagogique (0-10)
3. Clarté visuelle (0-10)
4. Problèmes détectés
5. Suggestions amélioration

Format: JSON structuré."""
        
        validation = analyze_image(temp_path, validation_prompt)
        
        return {
            'image_url': image_url,
            'image_path': temp_path,
            'original_prompt': prompt,
            'revised_prompt': revised_prompt,
            'validation': validation['description']
        }
    
    def iterate_until_valid(self, base_prompt, validation_criteria, max_iterations=3):
        """
        Itère génération jusqu'à validation réussie
        
        Args:
            base_prompt: Prompt de base
            validation_criteria: Critères validation
            max_iterations: Nombre max d'itérations
        """
        iterations = []
        current_prompt = base_prompt
        
        for i in range(max_iterations):
            print(f"\n{'='*60}")
            print(f"Itération {i+1}/{max_iterations}")
            
            result = self.generate_and_validate(current_prompt, validation_criteria)
            iterations.append(result)
            
            # Vérification validation
            if "10/10" in result['validation'] or "excellent" in result['validation'].lower():
                print("✅ Image validée!")
                break
            
            # Prompt amélioration
            if i < max_iterations - 1:
                improvement_prompt = f"""Améliore ce prompt DALL-E basé sur validation:

PROMPT ACTUEL: {current_prompt}
VALIDATION: {result['validation']}

Génère prompt amélioré (garde style pédagogique)."""
                
                # Utilisation GPT-5 pour amélioration
                improvement = self.gpt5_client.chat.completions.create(
                    model=GPT5_MODEL,
                    messages=[{"role": "user", "content": improvement_prompt}],
                    max_tokens=300
                )
                
                current_prompt = improvement.choices[0].message.content.strip()
                print(f"🔄 Prompt amélioré: {current_prompt}")
        
        return iterations
    
    def generate_with_accessibility(self, prompt, subject_area):
        """Génère image avec alt text automatique"""
        # Génération
        result = self.generate_and_validate(
            prompt,
            "Image claire, pédagogique, accessible"
        )
        
        # Alt text
        alt_text = generate_alt_text(result['image_path'], context="educational")
        
        # Description longue si complexe
        complexity_check = analyze_image(
            result['image_path'],
            "Cette image est-elle complexe (diagramme, graphique)? Réponds OUI ou NON."
        )
        
        if "OUI" in complexity_check['description']:
            long_desc = generate_long_description(result['image_path'], alt_text)
            result['long_description'] = long_desc['description']
        
        result['alt_text'] = alt_text
        return result
```

**Exemple d'utilisation** :
```python
pipeline = ImageCreationAnalysisPipeline()

# Génération avec validation
result = pipeline.iterate_until_valid(
    base_prompt="Diagramme cellule végétale avec labels français",
    validation_criteria="""
    - Tous organites visibles et labelés
    - Labels en français correct
    - Style pédagogique clair
    - Adapté niveau collège
    """,
    max_iterations=3
)

# Génération avec accessibilité
accessible_result = pipeline.generate_with_accessibility(
    prompt="Diagramme photosynthèse étapes principales",
    subject_area="sciences"
)

print(f"Alt text: {accessible_result['alt_text']}")
```

---

## Performance et Cost Management

### Optimisation Coûts

```python
class GPT5CostOptimizer:
    """Optimise coûts utilisation GPT-5 multimodal"""
    
    # Tarifs approximatifs (vérifier OpenRouter)
    COST_PER_1K_INPUT_TOKENS = 0.01
    COST_PER_1K_OUTPUT_TOKENS = 0.03
    IMAGE_COST_LOW_DETAIL = 0.002  # ~85 tokens
    IMAGE_COST_HIGH_DETAIL = 0.006  # ~255 tokens
    
    def __init__(self):
        self.total_cost = 0
        self.usage_log = []
    
    def estimate_cost(self, prompt_length, max_tokens, num_images=0, detail="auto"):
        """Estime coût avant appel API"""
        # Tokens prompt
        input_tokens = prompt_length / 4  # Approximation
        
        # Tokens images
        image_tokens = 0
        if detail == "low":
            image_tokens = num_images * 85
        elif detail == "high":
            image_tokens = num_images * 255
        else:  # auto
            image_tokens = num_images * 170  # Moyenne
        
        # Coût total
        input_cost = (input_tokens + image_tokens) / 1000 * self.COST_PER_1K_INPUT_TOKENS
        output_cost = max_tokens / 1000 * self.COST_PER_1K_OUTPUT_TOKENS
        
        total = input_cost + output_cost
        
        return {
            'estimated_cost': total,
            'input_tokens': input_tokens + image_tokens,
            'output_tokens': max_tokens
        }
    
    def analyze_cost_effective(self, image_path, prompt, detail="auto"):
        """Analyse avec tracking coût"""
        estimate = self.estimate_cost(len(prompt), 500, num_images=1, detail=detail)
        
        print(f"💰 Coût estimé: ${estimate['estimated_cost']:.4f}")
        
        result = analyze_image(image_path, prompt)
        
        # Coût réel
        actual_cost = (result['tokens_used'] / 1000) * (self.COST_PER_1K_INPUT_TOKENS + self.COST_PER_1K_OUTPUT_TOKENS)
        
        self.total_cost += actual_cost
        self.usage_log.append({
            'timestamp': datetime.now().isoformat(),
            'prompt': prompt[:50],
            'tokens': result['tokens_used'],
            'cost': actual_cost
        })
        
        result['cost'] = actual_cost
        return result
    
    def batch_optimize(self, images_and_prompts):
        """Optimise batch d'analyses"""
        # Trie par priorité
        # Utilise cache si images similaires
        # Regroupe prompts similaires
        
        results = []
        for img, prompt in images_and_prompts:
            # Utilise detail="low" par défaut pour économie
            result = self.analyze_cost_effective(img, prompt, detail="low")
            results.append(result)
        
        print(f"\n📊 Total batch: ${self.total_cost:.4f}")
        return results
    
    def get_usage_report(self):
        """Rapport utilisation et coûts"""
        return {
            'total_cost': self.total_cost,
            'total_requests': len(self.usage_log),
            'average_cost_per_request': self.total_cost / len(self.usage_log) if self.usage_log else 0,
            'detailed_log': self.usage_log
        }
```

### Cache et Réutilisation

```python
import json
import hashlib
from datetime import datetime, timedelta

class AnalysisCache:
    """Cache analyses pour éviter duplications"""
    
    def __init__(self, cache_dir="cache/gpt5_analyses"):
        self.cache_dir = Path(cache_dir)
        self.cache_dir.mkdir(parents=True, exist_ok=True)
        self.cache_index = self._load_index()
    
    def _load_index(self):
        """Charge index cache"""
        index_file = self.cache_dir / "index.json"
        if index_file.exists():
            with open(index_file, 'r') as f:
                return json.load(f)
        return {}
    
    def _save_index(self):
        """Sauvegarde index"""
        with open(self.cache_dir / "index.json", 'w') as f:
            json.dump(self.cache_index, f, indent=2)
    
    def _get_cache_key(self, image_path, prompt):
        """Génère clé cache unique"""
        # Hash image
        with open(image_path, 'rb') as f:
            image_hash = hashlib.md5(f.read()).hexdigest()
        
        # Hash prompt
        prompt_hash = hashlib.md5(prompt.encode()).hexdigest()
        
        return f"{image_hash}_{prompt_hash}"
    
    def get(self, image_path, prompt, max_age_hours=24):
        """Récupère depuis cache si existe et récent"""
        cache_key = self._get_cache_key(image_path, prompt)
        
        if cache_key in self.cache_index:
            entry = self.cache_index[cache_key]
            cached_time = datetime.fromisoformat(entry['timestamp'])
            
            # Vérification âge
            if datetime.now() - cached_time < timedelta(hours=max_age_hours):
                cache_file = self.cache_dir / f"{cache_key}.json"
                with open(cache_file, 'r') as f:
                    print(f"✅ Cache hit: {cache_key[:16]}...")
                    return json.load(f)
        
        return None
    
    def set(self, image_path, prompt, result):
        """Sauvegarde dans cache"""
        cache_key = self._get_cache_key(image_path, prompt)
        
        # Sauvegarde résultat
        cache_file = self.cache_dir / f"{cache_key}.json"
        with open(cache_file, 'w') as f:
            json.dump(result, f, indent=2)
        
        # Mise à jour index
        self.cache_index[cache_key] = {
            'image': os.path.basename(image_path),
            'prompt_preview': prompt[:100],
            'timestamp': datetime.now().isoformat()
        }
        self._save_index()
        
        print(f"💾 Cached: {cache_key[:16]}...")
    
    def analyze_with_cache(self, image_path, prompt):
        """Analyse avec cache automatique"""
        # Vérification cache
        cached = self.get(image_path, prompt)
        if cached:
            return cached
        
        # Analyse si pas en cache
        result = analyze_image(image_path, prompt)
        self.set(image_path, prompt, result)
        
        return result
```

**Exemple d'utilisation optimisée** :
```python
# Avec optimisation coûts
optimizer = GPT5CostOptimizer()
cache = AnalysisCache()

# Analyse avec cache
result = cache.analyze_with_cache(
    "diagram.png",
    "Analyse ce diagramme pédagogiquement"
)

# Tracking coût
tracked_result = optimizer.analyze_cost_effective(
    "diagram.png",
    "Analyse détaillée",
    detail="low"  # Économique
)

# Rapport final
report = optimizer.get_usage_report()
print(f"Coût total session: ${report['total_cost']:.4f}")
```

---

## Ressources Complémentaires

### Documentation
- [OpenRouter API Docs](https://openrouter.ai/docs)
- [OpenAI Vision Guide](https://platform.openai.com/docs/guides/vision)
- [WCAG 2.1 Guidelines](https://www.w3.org/WAI/WCAG21/quickref/)

### Notebooks CoursIA
- `01-2-Generation-Image-API.ipynb` : Introduction GPT-5
- `04-1-Educational-Content-Generation.ipynb` : Applications pédagogiques
- `04-2-Creative-Workflows.ipynb` : Workflows avancés

### Templates Réutilisables
- `examples/science-diagrams.ipynb` : Analyses scientifiques
- `examples/history-geography.ipynb` : Documents historiques
- `examples/literature-visual.ipynb` : Illustrations littéraires

---

**Version**: 1.0.0  
**Dernière mise à jour**: 2025-10-08  
**Auteur**: Équipe CoursIA  
**Licence**: Projet Éducatif CoursIA