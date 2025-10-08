# Tutorial Complet : DALL-E 3 pour CoursIA

## Table des Matières
1. [Introduction](#introduction)
2. [Getting Started avec OpenAI API](#getting-started)
3. [Prompt Engineering pour Images](#prompt-engineering)
4. [Variations et Éditions Avancées](#variations-editions)
5. [Intégration Workflows CoursIA](#integration-coursia)
6. [Troubleshooting](#troubleshooting)
7. [Cas d'Usage Pédagogiques](#cas-usage)
8. [Code Examples Réutilisables](#code-examples)

---

## Introduction

DALL-E 3 est le modèle de génération d'images le plus avancé d'OpenAI, optimisé pour créer des images réalistes et artistiques à partir de descriptions textuelles. Ce guide complet vous accompagne dans l'utilisation de DALL-E 3 pour vos besoins pédagogiques dans CoursIA.

### Caractéristiques Principales
- **Haute résolution** : Jusqu'à 1024x1792 pixels
- **Compréhension contextuelle** : Interprétation nuancée des prompts
- **Styles variés** : Réalisme, art, illustration technique
- **Safety filters** : Contenu approprié pour l'éducation
- **Rapidité** : Génération en ~30-60 secondes

### Prérequis
- Clé API OpenAI valide
- Environnement Python 3.10+
- Bibliothèques : `openai`, `Pillow`, `requests`
- Budget API : ~$0.04-0.08 par image

---

## Getting Started avec OpenAI API

### Configuration Initiale

```python
import os
from openai import OpenAI
from PIL import Image
import requests
from io import BytesIO

# Configuration API
client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))

# Vérification configuration
def verify_api_config():
    """Vérifie que l'API est correctement configurée"""
    try:
        models = client.models.list()
        print("✅ Configuration API valide")
        return True
    except Exception as e:
        print(f"❌ Erreur configuration : {e}")
        return False
```

### Première Génération d'Image

```python
def generate_basic_image(prompt, size="1024x1024"):
    """
    Génère une image simple avec DALL-E 3
    
    Args:
        prompt: Description textuelle de l'image
        size: Dimensions (1024x1024, 1024x1792, 1792x1024)
    
    Returns:
        URL de l'image générée
    """
    try:
        response = client.images.generate(
            model="dall-e-3",
            prompt=prompt,
            size=size,
            quality="standard",  # ou "hd"
            n=1
        )
        
        image_url = response.data[0].url
        print(f"✅ Image générée : {image_url}")
        return image_url
        
    except Exception as e:
        print(f"❌ Erreur génération : {e}")
        return None
```

### Téléchargement et Sauvegarde

```python
def download_and_save_image(url, filename):
    """
    Télécharge et sauvegarde une image depuis URL
    
    Args:
        url: URL de l'image
        filename: Nom du fichier de sortie
    """
    response = requests.get(url)
    img = Image.open(BytesIO(response.content))
    img.save(filename)
    print(f"✅ Image sauvegardée : {filename}")
    return img
```

**Exemple d'utilisation** :
```python
# Génération simple
prompt = "Un professeur enseignant les mathématiques à des élèves dans une classe moderne"
url = generate_basic_image(prompt)

# Sauvegarde
download_and_save_image(url, "teaching_scene.png")
```

---

## Prompt Engineering pour Images

### Principes Fondamentaux

**1. Structure de Prompt Efficace**
```
[Sujet principal] + [Action/Contexte] + [Style artistique] + [Détails techniques]
```

**2. Éléments Clés à Inclure**
- **Sujet** : Qui ou quoi est représenté
- **Action** : Ce qui se passe dans la scène
- **Environnement** : Où se déroule l'action
- **Style** : Réaliste, artistique, schématique
- **Éclairage** : Naturel, dramatique, doux
- **Perspective** : Vue frontale, aérienne, rapprochée

### Templates de Prompts Pédagogiques

#### Sciences
```python
science_prompts = {
    "biologie": "Diagramme scientifique détaillé de [organisme], style manuel scolaire, labels français, fond blanc, vue en coupe, illustration pédagogique précise",
    
    "physique": "Schéma technique montrant [concept physique], flèches de force annotées, style manuel technique, couleurs codées, légendes françaises",
    
    "chimie": "Représentation moléculaire 3D de [molécule], structure de Lewis, liaisons covalentes colorées, style manuel chimie, labels atomiques"
}
```

#### Histoire-Géographie
```python
humanities_prompts = {
    "histoire": "Scène historique de [événement], style peinture d'époque, costumes authentiques, [date], composition dramatique, détails historiques précis",
    
    "géographie": "Carte illustrée de [région], relief en 3D, légendes françaises, style cartographie moderne, couleurs géographiques standards"
}
```

#### Mathématiques
```python
math_prompts = {
    "géométrie": "Diagramme géométrique de [figure], axes annotés, mesures en degrés, style manuel mathématique, couleurs pédagogiques, fond quadrillé",
    
    "statistiques": "Graphique [type] représentant [données], axes clairement labelés, légende française, style infographie moderne, couleurs distinctives"
}
```

### Techniques Avancées

**1. Spécification du Style**
```python
style_modifiers = {
    "réaliste": "photographie haute résolution, éclairage naturel, détails réalistes",
    "illustration": "illustration numérique, style manuel scolaire, couleurs vives",
    "schématique": "diagramme technique, lignes nettes, style infographie",
    "artistique": "peinture numérique, style artistique, composition esthétique"
}
```

**2. Contrôle de la Composition**
```python
composition_guides = {
    "centré": "composition centrée, symétrique, sujet au centre du cadre",
    "dramatique": "angle dynamique, composition asymétrique, point focal prononcé",
    "pédagogique": "vue claire et dégagée, éléments bien espacés, lisibilité maximale"
}
```

**3. Gestion de la Qualité**
```python
def generate_hd_image(prompt, size="1024x1024"):
    """Génère une image en qualité HD pour impression"""
    response = client.images.generate(
        model="dall-e-3",
        prompt=f"{prompt}, haute résolution, détails précis, qualité professionnelle",
        size=size,
        quality="hd",  # Mode HD : 2x le coût mais qualité supérieure
        n=1
    )
    return response.data[0].url
```

---

## Variations et Éditions Avancées

### Génération de Variations

```python
def generate_variations(base_prompt, variations, size="1024x1024"):
    """
    Génère plusieurs variations d'un même concept
    
    Args:
        base_prompt: Prompt de base
        variations: Liste de modifications à appliquer
        size: Dimensions des images
    
    Returns:
        Liste d'URLs des variations
    """
    images = []
    
    for i, variation in enumerate(variations):
        full_prompt = f"{base_prompt}, {variation}"
        print(f"🎨 Variation {i+1}/{len(variations)}: {variation}")
        
        url = generate_basic_image(full_prompt, size)
        if url:
            images.append({
                'variation': variation,
                'url': url
            })
    
    return images
```

**Exemple - Variations Stylistiques** :
```python
base = "Un professeur enseignant les mathématiques dans une classe"

styles = [
    "style illustration moderne, couleurs vives",
    "style photographie réaliste, lumière naturelle",
    "style dessin manga, traits dynamiques",
    "style peinture aquarelle, touches douces"
]

variations = generate_variations(base, styles)
```

### Séries Thématiques

```python
def generate_educational_series(topic, count=4):
    """
    Génère une série d'images sur un thème pédagogique
    
    Args:
        topic: Thème éducatif
        count: Nombre d'images à générer
    """
    series_prompts = {
        "photosynthèse": [
            "Diagramme 1/4: Lumière solaire atteignant feuille verte, rayons annotés",
            "Diagramme 2/4: Absorption lumière par chloroplastes, vue microscopique",
            "Diagramme 3/4: Production glucose dans feuille, molécules annotées",
            "Diagramme 4/4: Libération oxygène, cycle complet illustré"
        ],
        
        "révolution française": [
            "Scène 1/4: Prise de la Bastille 1789, foule révolutionnaire",
            "Scène 2/4: Déclaration Droits de l'Homme, assemblée constituante",
            "Scène 3/4: Procès Louis XVI, tribunal révolutionnaire",
            "Scène 4/4: Terreur 1793-1794, Robespierre et Comité salut public"
        ]
    }
    
    images = []
    for prompt in series_prompts.get(topic, [])[:count]:
        url = generate_basic_image(prompt + ", style manuel scolaire, pédagogique")
        images.append({'prompt': prompt, 'url': url})
    
    return images
```

### Optimisation Itérative

```python
def refine_image_iteratively(initial_prompt, refinements):
    """
    Affine progressivement une image par itérations
    
    Args:
        initial_prompt: Prompt initial
        refinements: Liste d'améliorations successives
    """
    history = []
    current_prompt = initial_prompt
    
    for i, refinement in enumerate(refinements):
        print(f"\n🔄 Itération {i+1}: {refinement}")
        current_prompt = f"{current_prompt}, {refinement}"
        
        url = generate_basic_image(current_prompt)
        history.append({
            'iteration': i+1,
            'refinement': refinement,
            'prompt': current_prompt,
            'url': url
        })
    
    return history
```

---

## Intégration Workflows CoursIA

### Pipeline de Production

```python
class ImageGenerationPipeline:
    """Pipeline complet de génération d'images pour CoursIA"""
    
    def __init__(self, project_name):
        self.project_name = project_name
        self.output_dir = f"outputs/{project_name}"
        os.makedirs(self.output_dir, exist_ok=True)
        self.client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))
    
    def generate_course_materials(self, lesson_plan):
        """
        Génère supports visuels pour un plan de cours
        
        Args:
            lesson_plan: Dict avec structure du cours
        """
        materials = []
        
        for section in lesson_plan['sections']:
            print(f"\n📚 Section: {section['title']}")
            
            for visual in section['visuals']:
                # Génération image
                url = self._generate_with_retry(
                    prompt=visual['prompt'],
                    size=visual.get('size', '1024x1024')
                )
                
                # Téléchargement
                filename = f"{self.output_dir}/{section['id']}_{visual['id']}.png"
                self._download_image(url, filename)
                
                materials.append({
                    'section': section['title'],
                    'visual_id': visual['id'],
                    'filename': filename,
                    'url': url
                })
        
        return materials
    
    def _generate_with_retry(self, prompt, size, max_retries=3):
        """Génération avec retry en cas d'erreur"""
        for attempt in range(max_retries):
            try:
                response = self.client.images.generate(
                    model="dall-e-3",
                    prompt=prompt,
                    size=size,
                    quality="standard",
                    n=1
                )
                return response.data[0].url
            except Exception as e:
                print(f"⚠️ Tentative {attempt+1} échouée: {e}")
                if attempt == max_retries - 1:
                    raise
        return None
    
    def _download_image(self, url, filename):
        """Télécharge et sauvegarde image"""
        response = requests.get(url)
        img = Image.open(BytesIO(response.content))
        img.save(filename)
        return filename
```

**Exemple d'utilisation** :
```python
lesson = {
    'title': 'Introduction à la Photosynthèse',
    'sections': [
        {
            'id': 'intro',
            'title': 'Concepts de Base',
            'visuals': [
                {
                    'id': 'chloroplaste',
                    'prompt': 'Diagramme détaillé chloroplaste, labels français, style manuel biologie',
                    'size': '1024x1024'
                }
            ]
        }
    ]
}

pipeline = ImageGenerationPipeline('photosynthese_course')
materials = pipeline.generate_course_materials(lesson)
```

### Batch Processing

```python
def batch_generate_images(prompts_file, output_dir):
    """
    Génération batch depuis fichier de prompts
    
    Args:
        prompts_file: CSV avec colonnes (id, prompt, size)
        output_dir: Répertoire de sortie
    """
    import pandas as pd
    
    # Lecture prompts
    df = pd.read_csv(prompts_file)
    
    results = []
    for idx, row in df.iterrows():
        print(f"\n🎨 {idx+1}/{len(df)}: {row['id']}")
        
        # Génération
        url = generate_basic_image(
            prompt=row['prompt'],
            size=row.get('size', '1024x1024')
        )
        
        # Sauvegarde
        if url:
            filename = f"{output_dir}/{row['id']}.png"
            download_and_save_image(url, filename)
            
            results.append({
                'id': row['id'],
                'prompt': row['prompt'],
                'filename': filename,
                'success': True
            })
        else:
            results.append({
                'id': row['id'],
                'prompt': row['prompt'],
                'success': False
            })
    
    # Sauvegarde résultats
    pd.DataFrame(results).to_csv(f"{output_dir}/generation_log.csv", index=False)
    return results
```

---

## Troubleshooting

### Erreurs Communes

**1. Content Policy Violation**
```python
def handle_policy_violation(original_prompt):
    """Adapte prompt en cas de violation policy"""
    # Ajout modérateurs
    safe_prompt = f"{original_prompt}, style éducatif approprié, contenu pédagogique"
    
    # Termes à éviter
    avoid_terms = ['violence', 'arme', 'sang', 'nudité']
    
    # Remplacements
    replacements = {
        'guerre': 'conflit historique',
        'bataille': 'événement militaire historique',
        'explosion': 'réaction chimique'
    }
    
    for old, new in replacements.items():
        safe_prompt = safe_prompt.replace(old, new)
    
    return safe_prompt
```

**2. Rate Limiting**
```python
import time
from tenacity import retry, wait_exponential, stop_after_attempt

@retry(wait=wait_exponential(min=1, max=60), stop=stop_after_attempt(5))
def generate_with_rate_limit(prompt, size="1024x1024"):
    """Génération avec gestion rate limiting"""
    try:
        return generate_basic_image(prompt, size)
    except Exception as e:
        if "rate_limit" in str(e).lower():
            print("⏳ Rate limit atteint, attente...")
            time.sleep(60)
            raise
        else:
            raise
```

**3. Qualité Insuffisante**
```python
def enhance_prompt_quality(basic_prompt):
    """Améliore qualité du prompt"""
    quality_modifiers = [
        "haute résolution",
        "détails précis",
        "composition professionnelle",
        "éclairage optimal",
        "couleurs équilibrées"
    ]
    
    return f"{basic_prompt}, {', '.join(quality_modifiers)}"
```

### Best Practices

**1. Gestion des Coûts**
```python
def estimate_generation_cost(num_images, quality="standard"):
    """Estime le coût de génération"""
    prices = {
        "standard": 0.040,  # $/image 1024x1024
        "hd": 0.080         # $/image HD
    }
    
    cost = num_images * prices[quality]
    print(f"💰 Coût estimé: ${cost:.2f} pour {num_images} images en qualité {quality}")
    return cost
```

**2. Validation des Résultats**
```python
def validate_generated_image(image_path, requirements):
    """Valide qu'une image respecte les exigences"""
    img = Image.open(image_path)
    
    checks = {
        'resolution': img.size == requirements['size'],
        'format': img.format == requirements.get('format', 'PNG'),
        'file_size': os.path.getsize(image_path) < requirements.get('max_size', 5*1024*1024)
    }
    
    return all(checks.values()), checks
```

---

## Cas d'Usage Pédagogiques

### 1. Sciences Biologiques

```python
biology_use_cases = {
    "anatomie": {
        "prompt": "Diagramme anatomique détaillé de [organe], vue en coupe, labels français, style atlas médical, fond blanc, annotations pédagogiques",
        "applications": ["Cours anatomie", "Supports révision", "Posters classe"]
    },
    
    "écosystème": {
        "prompt": "Illustration écosystème [type], chaîne alimentaire visible, espèces labelées français, style manuel SVT, composition claire",
        "applications": ["Écologie", "Biodiversité", "Sciences environnementales"]
    }
}
```

### 2. Histoire

```python
history_use_cases = {
    "événement_historique": {
        "prompt": "Reconstitution historique [événement] en [année], costumes d'époque authentiques, architecture période, style peinture historique réaliste",
        "applications": ["Cours histoire", "Présentations", "Études documentaires"]
    },
    
    "personnage_historique": {
        "prompt": "Portrait [personnage historique], vêtements d'époque, contexte historique suggéré, style portrait officiel [siècle]",
        "applications": ["Biographies", "Frises chronologiques", "Exposés"]
    }
}
```

### 3. Mathématiques & Physique

```python
stem_use_cases = {
    "géométrie": {
        "prompt": "Diagramme géométrique [concept], angles mesurés, axes annotés français, style manuel mathématique, couleurs distinctives, fond quadrillé",
        "applications": ["Démonstrations", "Exercices", "Théorèmes visuels"]
    },
    
    "physique": {
        "prompt": "Schéma physique [phénomène], forces vectorielles colorées, labels français, style manuel scientifique, légendes explicatives",
        "applications": ["Mécanique", "Électricité", "Optique"]
    }
}
```

---

## Code Examples Réutilisables

### Template Complet Production

```python
# educational_image_generator.py
"""
Module de génération d'images pédagogiques avec DALL-E 3
Pour CoursIA - Production Ready
"""

import os
import json
from datetime import datetime
from pathlib import Path
from openai import OpenAI
from PIL import Image
import requests
from io import BytesIO

class EducationalImageGenerator:
    """Générateur d'images pédagogiques optimisé"""
    
    def __init__(self, project_name, api_key=None):
        self.project_name = project_name
        self.api_key = api_key or os.getenv("OPENAI_API_KEY")
        self.client = OpenAI(api_key=self.api_key)
        
        # Répertoires
        self.base_dir = Path(f"outputs/{project_name}")
        self.images_dir = self.base_dir / "images"
        self.logs_dir = self.base_dir / "logs"
        
        # Création structure
        self.images_dir.mkdir(parents=True, exist_ok=True)
        self.logs_dir.mkdir(parents=True, exist_ok=True)
        
        # Logs
        self.log_file = self.logs_dir / f"generation_log_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
        self.generation_history = []
    
    def generate(self, prompt, category, image_id, size="1024x1024", quality="standard"):
        """
        Génère une image pédagogique
        
        Args:
            prompt: Description de l'image
            category: Catégorie pédagogique (sciences, histoire, etc.)
            image_id: Identifiant unique
            size: Dimensions
            quality: 'standard' ou 'hd'
        
        Returns:
            Dict avec résultats génération
        """
        timestamp = datetime.now()
        
        try:
            # Génération
            print(f"🎨 Génération: {image_id}")
            response = self.client.images.generate(
                model="dall-e-3",
                prompt=self._enhance_educational_prompt(prompt, category),
                size=size,
                quality=quality,
                n=1
            )
            
            url = response.data[0].url
            revised_prompt = response.data[0].revised_prompt
            
            # Téléchargement
            filename = self._generate_filename(category, image_id)
            filepath = self.images_dir / filename
            self._download_image(url, filepath)
            
            # Logging
            result = {
                'image_id': image_id,
                'category': category,
                'original_prompt': prompt,
                'revised_prompt': revised_prompt,
                'url': url,
                'filepath': str(filepath),
                'size': size,
                'quality': quality,
                'timestamp': timestamp.isoformat(),
                'success': True
            }
            
            self.generation_history.append(result)
            self._save_log()
            
            print(f"✅ Sauvegardé: {filepath}")
            return result
            
        except Exception as e:
            # Logging erreur
            error_result = {
                'image_id': image_id,
                'category': category,
                'original_prompt': prompt,
                'error': str(e),
                'timestamp': timestamp.isoformat(),
                'success': False
            }
            
            self.generation_history.append(error_result)
            self._save_log()
            
            print(f"❌ Erreur: {e}")
            return error_result
    
    def _enhance_educational_prompt(self, prompt, category):
        """Enrichit prompt avec contexte pédagogique"""
        educational_context = {
            'sciences': 'style manuel scientifique, précis et pédagogique, labels français',
            'histoire': 'style illustration historique, détails d\'époque authentiques',
            'mathématiques': 'style diagramme mathématique, annotations claires',
            'géographie': 'style carte pédagogique, légendes françaises',
            'littérature': 'style illustration littéraire, composition artistique'
        }
        
        context = educational_context.get(category, 'style pédagogique professionnel')
        return f"{prompt}, {context}, approprié pour enseignement"
    
    def _generate_filename(self, category, image_id):
        """Génère nom de fichier structuré"""
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        safe_id = image_id.replace(' ', '_').replace('/', '-')
        return f"{category}_{safe_id}_{timestamp}.png"
    
    def _download_image(self, url, filepath):
        """Télécharge et sauvegarde image"""
        response = requests.get(url)
        img = Image.open(BytesIO(response.content))
        img.save(filepath, 'PNG')
        return filepath
    
    def _save_log(self):
        """Sauvegarde historique génération"""
        with open(self.log_file, 'w', encoding='utf-8') as f:
            json.dump(self.generation_history, f, indent=2, ensure_ascii=False)
    
    def generate_batch(self, batch_config):
        """
        Génération batch depuis configuration
        
        Args:
            batch_config: Liste de dicts avec clés (prompt, category, image_id)
        """
        results = []
        total = len(batch_config)
        
        for i, config in enumerate(batch_config, 1):
            print(f"\n{'='*60}")
            print(f"Image {i}/{total}")
            
            result = self.generate(
                prompt=config['prompt'],
                category=config['category'],
                image_id=config['image_id'],
                size=config.get('size', '1024x1024'),
                quality=config.get('quality', 'standard')
            )
            
            results.append(result)
        
        print(f"\n{'='*60}")
        print(f"✅ Batch terminé: {sum(r['success'] for r in results)}/{total} réussis")
        
        return results
    
    def get_statistics(self):
        """Statistiques de génération"""
        total = len(self.generation_history)
        success = sum(1 for r in self.generation_history if r['success'])
        
        return {
            'total_generations': total,
            'successful': success,
            'failed': total - success,
            'success_rate': (success / total * 100) if total > 0 else 0,
            'by_category': self._stats_by_category()
        }
    
    def _stats_by_category(self):
        """Statistiques par catégorie"""
        stats = {}
        for record in self.generation_history:
            cat = record.get('category', 'unknown')
            if cat not in stats:
                stats[cat] = {'total': 0, 'success': 0}
            
            stats[cat]['total'] += 1
            if record['success']:
                stats[cat]['success'] += 1
        
        return stats


# Exemple d'utilisation
if __name__ == "__main__":
    # Initialisation
    generator = EducationalImageGenerator(project_name="cours_biologie_2024")
    
    # Configuration batch
    batch = [
        {
            'prompt': 'Diagramme cellule végétale avec chloroplastes',
            'category': 'sciences',
            'image_id': 'cellule_vegetale_01',
            'size': '1024x1024',
            'quality': 'standard'
        },
        {
            'prompt': 'Illustration photosynthèse étapes principales',
            'category': 'sciences',
            'image_id': 'photosynthese_steps',
            'size': '1024x1024',
            'quality': 'hd'
        }
    ]
    
    # Génération
    results = generator.generate_batch(batch)
    
    # Statistiques
    stats = generator.get_statistics()
    print(f"\n📊 Statistiques:")
    print(json.dumps(stats, indent=2))
```

---

## Ressources Complémentaires

### Documentation Officielle
- [OpenAI DALL-E 3 Guide](https://platform.openai.com/docs/guides/images)
- [API Reference](https://platform.openai.com/docs/api-reference/images)
- [Safety Guidelines](https://openai.com/policies/usage-policies)

### Notebooks CoursIA
- `01-1-OpenAI-DALL-E-3.ipynb` : Introduction pratique
- `04-1-Educational-Content-Generation.ipynb` : Applications pédagogiques
- `04-2-Creative-Workflows.ipynb` : Workflows créatifs

### Support
- Issues GitHub: [CoursIA Repository](https://github.com/jsboige/CoursIA)
- Documentation CoursIA: `docs/genai-images-user-guide.md`

---

**Version**: 1.0.0  
**Dernière mise à jour**: 2025-10-08  
**Auteur**: Équipe CoursIA  
**Licence**: Projet Éducatif CoursIA