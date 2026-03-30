import asyncio
import os
import shutil
import time
import logging
import pandas as pd
import pytest
import pytest_asyncio
from dotenv import load_dotenv
import uuid

# Assurer que le PYTHONPATH inclut la racine du projet pour les imports
import sys
# Il faut remonter de deux niveaux pour être à la racine de 'solution-matching-cv'
project_root_path = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..'))
sys.path.insert(0, project_root_path)

from app.matching import (
    initialize_kernel,
    index_consultants,
    index_jobs,
    find_matches,
    load_data as load_advanced
)
from semantic_kernel.connectors.chroma import ChromaStore
import chromadb

# Configuration du logging
logging.basicConfig(level=logging.DEBUG, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

# Charger les variables d'environnement
load_dotenv(os.path.join(project_root_path, '.env'))

# --- Fixtures de Données ---

@pytest.fixture(scope="module")
def consultants_data():
    """Charge les données des consultants une seule fois et filtre les données de test."""
    path = os.path.join(project_root_path, 'data', 'consultants.csv')
    df, _ = load_advanced(path, path, logger) # Hack pour charger un seul fichier
    return df[~df['Nom'].str.startswith('Test Consultant')]

@pytest.fixture(scope="module")
def jobs_data():
    """Charge les données des offres d'emploi une seule fois et filtre les données de test."""
    path = os.path.join(project_root_path, 'data', 'fiches_de_poste.csv')
    _, df = load_advanced(path, path, logger) # Hack pour charger un seul fichier
    return df[~df['Titre'].str.startswith('Test Job')]

# --- Fixture Principale pour l'environnement de test ---

@pytest_asyncio.fixture(scope="function")
async def setup_collections(consultants_data, jobs_data):
    """
    Initialise un client ChromaDB persistant et un kernel SK frais pour chaque test.
    La persistance sur disque assure le cache entre les exécutions.
    La portée 'function' assure un client réseau propre pour chaque test.
    """
    api_key = os.getenv("OPENAI_API_KEY")
    if not api_key:
        pytest.fail("La clé API OpenAI n'est pas configurée.")
    
    _, service = initialize_kernel(api_key, logger)
    
    test_db_path = os.path.join(project_root_path, "data", "chroma_db_unit_test")
    os.makedirs(test_db_path, exist_ok=True)
    
    chroma_client = chromadb.PersistentClient(path=test_db_path)
    vector_store = ChromaStore(client=chroma_client, embedding_generator=service)
 
    consultants_collection_name = "perf_test_consultants"
    jobs_collection_name = "perf_test_jobs"

    # Log pour déboguer l'état de la base de données au démarrage du test
    consultants_collection = chroma_client.get_or_create_collection(name=consultants_collection_name)
    jobs_collection = chroma_client.get_or_create_collection(name=jobs_collection_name)
    logger.info(f"[DEBUG] Au début du test, la collection '{consultants_collection_name}' contient {consultants_collection.count()} éléments.")
    logger.info(f"[DEBUG] Au début du test, la collection '{jobs_collection_name}' contient {jobs_collection.count()} éléments.")

    try:
        await asyncio.wait_for(
            index_consultants(vector_store, consultants_data, logger, consultants_collection_name),
            timeout=120.0
        )
        await asyncio.wait_for(
            index_jobs(vector_store, jobs_data, logger, jobs_collection_name),
            timeout=120.0
        )
    except asyncio.TimeoutError:
        pytest.fail("L'indexation a dépassé le temps imparti.")
    
    return vector_store, service, chroma_client, consultants_collection_name, jobs_collection_name


@pytest.mark.asyncio
async def test_consultant_indexing_count(setup_collections, consultants_data):
    """
    Vérifie que la collection 'consultants' contient le bon nombre d'enregistrements.
    """
    vector_store, _, chroma_client, consultants_collection_name, _ = setup_collections
    await index_consultants(vector_store, consultants_data, logger=logger, collection_name=consultants_collection_name)
    
    # Attendre que l'indexation soit terminée
    await asyncio.sleep(1)

    collection = chroma_client.get_collection(name=consultants_collection_name)
    count = collection.count()

    assert count == 55, f"Le nombre de consultants indexés ({count}) est incorrect. Attendu: 55."


@pytest.mark.asyncio
async def test_job_indexing_count(setup_collections, jobs_data):
    """
    Vérifie que la collection 'jobs' contient le bon nombre d'enregistrements.
    """
    vector_store, _, chroma_client, _, jobs_collection_name = setup_collections
    await index_jobs(vector_store, jobs_data, logger=logger, collection_name=jobs_collection_name)
    
    # Attendre que l'indexation soit terminée
    await asyncio.sleep(1)

    collection = chroma_client.get_collection(name=jobs_collection_name)
    count = collection.count()
    
    assert count == 41, f"Le nombre de jobs indexés ({count}) est incorrect. Attendu: 41."

@pytest.mark.asyncio
async def test_semantic_search_performance(setup_collections, jobs_data):
    """
    Teste et mesure la performance de la recherche sémantique sur la collection des consultants.
    """
    vector_store, service, _, consultants_collection_name, jobs_collection_name = setup_collections
    
    logger.debug("Début du test de performance sémantique...")
    start_time = time.time()
    
    jobs_to_test = jobs_data.head(2)
    logger.debug(f"Test de recherche pour {len(jobs_to_test)} offres.")

    # Recherche des consultants correspondants pour les 2 premières offres d'emploi.
    search_results = await find_matches(
        vector_store,
        jobs_to_test,
        logger,
        consultant_collection_name=consultants_collection_name,
        job_collection_name=jobs_collection_name
    )
    
    logger.debug("Appel à find_matches terminé.")
    end_time = time.time()
    duration = end_time - start_time
    
    print(f"\n--- PERFORMANCE RECHERCHE ---")
    print(f"Temps total pour la recherche : {duration:.2f} secondes pour {len(jobs_data.head(2))} jobs.")
    print(f"----------------------------\n")

    assert duration > 0
    assert len(search_results) > 0, "La recherche sémantique n'a retourné aucun résultat."
