#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Script de retouche d'image utilisant l'API OpenAI GPT-4o
Ce script prend une image en entrée, l'envoie à l'API OpenAI pour retouche,
et sauvegarde l'image retouchée.
"""

import os
import base64
import requests
import json
from pathlib import Path
from dotenv import load_dotenv
import argparse

# Charger les variables d'environnement depuis le fichier .env à la racine du projet
# Cela permet de ne pas exposer la clé API dans le code
load_dotenv(Path(__file__).resolve().parents[2] / '.env')

def encode_image(image_path):
    """
    Encode une image en base64 pour l'envoi à l'API OpenAI.
    
    Args:
        image_path (str): Chemin vers l'image à encoder
        
    Returns:
        str: Image encodée en base64
    """
    with open(image_path, "rb") as image_file:
        return base64.b64encode(image_file.read()).decode('utf-8')

def retouche_image(image_path, instructions, output_path):
    """
    Retouche une image en utilisant l'API OpenAI GPT-4o.
    
    Args:
        image_path (str): Chemin vers l'image à retoucher
        instructions (str): Instructions de retouche pour l'IA
        output_path (str): Chemin où sauvegarder l'image retouchée
        
    Returns:
        bool: True si la retouche a réussi, False sinon
    """
    # Récupérer la clé API depuis les variables d'environnement
    api_key = os.getenv("OPENAI_API_KEY")
    if not api_key:
        print("Erreur: Clé API OpenAI non trouvée. Vérifiez votre fichier .env")
        return False
    
    # Encoder l'image en base64
    base64_image = encode_image(image_path)
    
    # Préparer les headers pour la requête API
    headers = {
        "Content-Type": "application/json",
        "Authorization": f"Bearer {api_key}"
    }
    
    # Préparer le payload pour la requête API
    payload = {
        "model": "gpt-4o",
        "messages": [
            {
                "role": "system",
                "content": "Vous êtes un expert en retouche photo professionnelle."
            },
            {
                "role": "user",
                "content": [
                    {
                        "type": "text",
                        "text": instructions
                    },
                    {
                        "type": "image_url",
                        "image_url": {
                            "url": f"data:image/png;base64,{base64_image}"
                        }
                    }
                ]
            }
        ],
        "max_tokens": 4096
    }
    
    try:
        # Envoyer la requête à l'API OpenAI
        print("Envoi de la requête à l'API OpenAI...")
        response = requests.post(
            "https://api.openai.com/v1/chat/completions",
            headers=headers,
            json=payload
        )
        
        # Vérifier si la requête a réussi
        response.raise_for_status()
        
        # Extraire l'URL de l'image générée de la réponse
        response_data = response.json()
        
        # Vérifier si la réponse contient une image
        if "content" in response_data["choices"][0]["message"]:
            content = response_data["choices"][0]["message"]["content"]
            
            # Chercher l'URL de l'image dans la réponse
            # Note: Le format exact peut varier selon la version de l'API
            # Cette partie peut nécessiter des ajustements
            if "![" in content and "](" in content:
                # Format markdown
                image_url = content.split("](")[1].split(")")[0]
            else:
                # Chercher une URL directe
                import re
                url_pattern = r'https?://\S+'
                urls = re.findall(url_pattern, content)
                if urls:
                    image_url = urls[0]
                else:
                    print("Erreur: Aucune URL d'image trouvée dans la réponse")
                    return False
            
            # Télécharger l'image générée
            print(f"Téléchargement de l'image retouchée...")
            img_response = requests.get(image_url)
            img_response.raise_for_status()
            
            # Sauvegarder l'image
            with open(output_path, 'wb') as f:
                f.write(img_response.content)
            
            print(f"Image retouchée sauvegardée avec succès: {output_path}")
            return True
        else:
            print("Erreur: La réponse ne contient pas d'image")
            return False
            
    except requests.exceptions.RequestException as e:
        print(f"Erreur lors de la requête API: {e}")
        if hasattr(e, 'response') and e.response is not None:
            print(f"Détails: {e.response.text}")
        return False
    except Exception as e:
        print(f"Erreur inattendue: {e}")
        return False

def main():
    """Fonction principale du script"""
    # Configurer l'analyseur d'arguments
    parser = argparse.ArgumentParser(description='Retouche d\'image avec l\'API OpenAI GPT-4o')
    parser.add_argument('--image', type=str, default='Alberic.png',
                        help='Chemin vers l\'image à retoucher (par défaut: Alberic.png)')
    parser.add_argument('--output', type=str, default='Alberic_retouche.png',
                        help='Chemin où sauvegarder l\'image retouchée (par défaut: Alberic_retouche.png)')
    
    # Analyser les arguments
    args = parser.parse_args()
    
    # Obtenir les chemins absolus
    script_dir = Path(__file__).parent
    image_path = script_dir / args.image
    output_path = script_dir / args.output
    
    # Vérifier si l'image existe
    if not image_path.exists():
        print(f"Erreur: L'image {image_path} n'existe pas")
        return
    
    # Instructions de retouche pour l'API
    instructions = """
    Retouchez cette image d'un homme en costume d'époque pour:
    1. Améliorer la netteté et le contraste global
    2. Rehausser légèrement les couleurs pour les rendre plus vibrantes sans paraître artificielles
    3. Adoucir subtilement les rides du visage tout en préservant le caractère naturel
    4. Éclaircir légèrement les zones d'ombre sur le visage pour mieux faire ressortir les traits
    5. Améliorer la définition des détails du costume
    6. Rendre l'arrière-plan légèrement plus flou pour mettre davantage l'accent sur le sujet
    7. Équilibrer la luminosité générale de l'image
    
    Générez une version améliorée de cette photo qui conserve son authenticité tout en la rendant plus professionnelle.
    Retournez uniquement l'image retouchée, sans texte ni explication.
    """
    
    # Lancer la retouche
    print(f"Retouche de l'image: {image_path}")
    retouche_image(image_path, instructions, output_path)

if __name__ == "__main__":
    main()