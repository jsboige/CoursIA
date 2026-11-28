# -*- coding: utf-8 -*-
"""
Script pour la génération automatisée de Dossiers de Compétences (DC)
en utilisant une approche parallèle et asynchrone pour traiter les combinaisons
consultant/fiche de poste.

Cible de chat (#22783)
----------------------
Par défaut, le service local du cluster (vLLM, alias Swift). Si le point d'entrée
local ne répond pas, repli **annoncé** sur le modèle de chat courant du mapping
(`gpt-5.6-luna`) : le repli est affiché, jamais silencieux.

Historique : ce script visait `gpt-4o-mini` (service OpenAI). Ce nom est obsolète
pour une exécution ; la cible recommandée est le vLLM local (alias `swift-1.5-27b`),
ou `gpt-5.6-luna` hors service local.
# obsolescence: DOC
"""

import os
import asyncio
import urllib.error
import urllib.request
from pathlib import Path

import pandas as pd
import semantic_kernel as sk
from dotenv import load_dotenv
from openai import AsyncOpenAI
from semantic_kernel.connectors.ai.open_ai import OpenAIChatCompletion
from semantic_kernel.functions import KernelArguments, KernelFunctionFromPrompt

# Le .env de la série GenAI porte VLLM_API_KEY / VLLM_BASE_URL : il est lu au
# chargement du module, donc avant la lecture des variables ci-dessous.
_GENAI_DIR = Path(__file__).resolve().parents[5]  # GenAI/
load_dotenv(_GENAI_DIR / ".env")

# --- Étape 1 : Configuration et Constantes ---
OUTPUT_DIR = "corriges/03-generation-dc/output"
CHUNK_SIZE = 25  # Traiter 25 tâches en parallèle à la fois

# Cible de chat (#22783) : le vLLM local du cluster (Swift) par défaut — même
# couple (VLLM_BASE_URL, VLLM_API_KEY) et même alias que
# MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/llm_client.py.
_LOCAL_BASE_URL = (
    os.getenv("VLLM_BASE_URL") or "http://192.168.0.47:5002/v1"
).rstrip("/")
_LOCAL_MODEL = os.getenv("VLLM_MODEL_ID") or "swift-1.5-27b"
# Repli hors service local : le modèle de chat courant du mapping
# (docs/genai/model-mapping-openai.md).
_FALLBACK_MODEL = "gpt-5.6-luna"


def service_local_disponible(base_url: str, api_key: str) -> bool:
    """Le vLLM local répond-il ? Sonde GET /models, 5 s, sans lever d'exception."""
    requete = urllib.request.Request(
        f"{base_url}/models",
        headers={"Authorization": f"Bearer {api_key}"},
    )
    try:
        with urllib.request.urlopen(requete, timeout=5) as reponse:
            return 200 <= reponse.status < 300
    except (urllib.error.URLError, OSError, TimeoutError):
        return False


def construire_service() -> OpenAIChatCompletion | None:
    """Service de chat : Swift local s'il répond, sinon repli explicite.

    Le repli est affiche avant tout appel : une campagne qui part sur la cible de
    secours ne doit jamais pouvoir se confondre avec une campagne sur le modele
    courant du mapping.
    """
    api_key_locale = os.getenv("VLLM_API_KEY")
    if api_key_locale and service_local_disponible(_LOCAL_BASE_URL, api_key_locale):
        print(f"Service de chat local : {_LOCAL_BASE_URL} (modèle {_LOCAL_MODEL}).")
        client = AsyncOpenAI(api_key=api_key_locale, base_url=_LOCAL_BASE_URL)
        return OpenAIChatCompletion(
            service_id="local",
            ai_model_id=_LOCAL_MODEL,
            async_client=client,
        )

    api_key_repli = os.getenv("OPENAI_API_KEY")
    if not api_key_repli:
        print(
            "Erreur : ni VLLM_API_KEY (service local) ni OPENAI_API_KEY (repli) "
            "ne sont définies."
        )
        return None
    print(
        f"Service local indisponible ({_LOCAL_BASE_URL}) : repli explicite sur "
        f"le modèle courant du mapping ({_FALLBACK_MODEL})."
    )
    client = AsyncOpenAI(api_key=api_key_repli)
    return OpenAIChatCompletion(
        service_id="repli",
        ai_model_id=_FALLBACK_MODEL,
        async_client=client,
    )

def slugify(text):
    """
    Convertit une chaîne de caractères en un nom de fichier valide.
    """
    text = text.lower().replace(" ", "_")
    return "".join(c for c in text if c.isalnum() or c in ('_', '-'))

async def generer_un_dc(consultant, poste, kernel, function):
    """
    Génère un seul Dossier de Compétences de manière asynchrone.
    """
    consultant_details = f"""
    Nom : {consultant['Nom']}
    Spécialité : {consultant['Poste']}
    Compétences techniques : {consultant['Compétences']}
    Expériences clés : {consultant['Expériences clés']}
    """
    job_requirements = f"""
    Titre du poste : {poste['Titre']}
    Mission : {poste['Description brute']}
    Compétences requises : {poste['Compétences clés']}
    """
    
    # Générer un nom de fichier unique et sûr
    consultant_nom_slug = slugify(consultant['Nom'])
    poste_titre_slug = slugify(poste['Titre'])
    file_name = f"DC_{consultant_nom_slug}_pour_{poste_titre_slug}.md"
    output_path = os.path.join(OUTPUT_DIR, file_name)

    # Vérifier si le fichier existe déjà pour éviter de le régénérer
    if os.path.exists(output_path):
        print(f"-> Skip : Fichier '{file_name}' existe déjà.")
        return output_path

    print(f"Préparation de la tâche pour '{file_name}'...")

    arguments = KernelArguments(
        consultant_details=consultant_details,
        job_requirements=job_requirements
    )

    try:
        resultat_dc = await kernel.invoke(function, arguments)
        
        # Sauvegarde asynchrone (nécessiterait aiofiles pour être non bloquant)
        with open(output_path, "w", encoding="utf-8") as f:
            f.write(str(resultat_dc))
        
        print(f"-> Succès : Fichier '{file_name}' sauvegardé.")
        return output_path
        
    except Exception as e:
        print(f"-> Erreur pour '{file_name}': {e}")
        return None

async def main():
    """
    Fonction principale pour orchestrer la génération des DC en parallèle.
    """
    # --- Étape 1 : Chargement de la Configuration ---
    load_dotenv()
    print("Variables d'environnement chargées.")

    # --- Étape 2 : Préparation de l'Environnement et des Données ---
    os.makedirs(OUTPUT_DIR, exist_ok=True)
    print(f"Répertoire de sortie '{OUTPUT_DIR}' prêt.")

    try:
        df_consultants = pd.read_csv("ateliers/data_metier_csv/Base consultants.csv", sep=',')
        df_postes = pd.read_csv("ateliers/data_metier_csv/Fiches de poste client.csv", sep=',')
        print("Fichiers CSV chargés avec succès.")
    except FileNotFoundError as e:
        print(f"Erreur : Fichier CSV non trouvé. {e}")
        return

    # --- Étape 3 : Initialisation du Kernel et de la Fonction Sémantique ---
    kernel = sk.Kernel()
    service = construire_service()
    if service is None:
        return
        
    kernel.add_service(service)
    print("Kernel Semantic Kernel initialisé avec le service de chat retenu.")

    prompt_template = """
    En tant qu'expert en recrutement spécialisé dans les profils Tech, rédige un Dossier de Compétences (DC) personnalisé et percutant.

    Objectif : Mettre en valeur l'adéquation entre le profil du consultant et les exigences de la fiche de poste.

    Structure attendue du DC :
    1.  **Titre Accrocheur** : "Proposition de collaboration : [Nom du Consultant] pour le poste de [Titre du poste]"
    2.  **Résumé Synthétique** : Un paragraphe court (3-4 phrases) qui met en avant l'expertise clé du consultant et son adéquation avec la mission.
    3.  **Tableau d'Adéquation Compétences** : Un tableau Markdown avec deux colonnes : "Compétence Requise" (issue de la fiche de poste) et "Expérience du Consultant" (justifiant la maîtrise de la compétence avec des exemples concrets).
    4.  **Expériences Pertinentes** : Sélectionne et détaille les 1 ou 2 expériences les plus significatives du consultant qui résonnent avec la fiche de poste.
    5.  **Conclusion** : Une phrase de clôture affirmant que le consultant est le candidat idéal pour ce rôle.

    ---
    **Profil du Consultant :**
    {{$consultant_details}}
    ---
    **Fiche de Poste :**
    {{$job_requirements}}
    ---
    """
    generer_dc_function = KernelFunctionFromPrompt(
        function_name="GenererDC",
        plugin_name="Redaction",
        prompt=prompt_template,
    )

    # --- Étape 4 : Stratégie de Traitement Parallèle ---
    print("\n--- Préparation des tâches de génération ---")
    tasks_to_run = []
    for _, consultant in df_consultants.iterrows():
        for _, poste in df_postes.iterrows():
            tasks_to_run.append((consultant, poste))
    
    print(f"{len(tasks_to_run)} tâches à exécuter.\n")

    print("--- Début du traitement par lots ---")
    for i in range(0, len(tasks_to_run), CHUNK_SIZE):
        batch = tasks_to_run[i:i + CHUNK_SIZE]
        print(f"\nTraitement du lot {i//CHUNK_SIZE + 1}...")
        
        coroutines = [
            generer_un_dc(consultant, poste, kernel, generer_dc_function)
            for consultant, poste in batch
        ]
        
        results = await asyncio.gather(*coroutines)
        
        # Optionnel : traiter les résultats (ex: compter les succès/échecs)
        success_count = sum(1 for r in results if r is not None)
        print(f"Lot {i//CHUNK_SIZE + 1} terminé. {success_count}/{len(batch)} succès.")

    print("\n--- Traitement de tous les lots terminé. ---\n")

if __name__ == "__main__":
    # Correction pour l'exécution sous Windows si nécessaire
    if os.name == 'nt':
        asyncio.set_event_loop_policy(asyncio.WindowsSelectorEventLoopPolicy())
    asyncio.run(main())