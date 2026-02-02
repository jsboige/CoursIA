import pytest
import time
import shutil
import os
import uuid
from pathlib import Path
import pandas as pd
import logging

from semantic_kernel.connectors.chroma import ChromaStore
from semantic_kernel.connectors.ai.open_ai import OpenAITextEmbedding
import chromadb

from app.matching import (
    initialize_kernel,
    load_data,
    index_consultants,
    index_jobs,
)

# Configuration du logger pour les tests
logger = logging.getLogger(__name__)

# Définir les chemins
ROOT_DIR = Path(__file__).parent.parent.parent
CHROMA_PERSIST_DIR = ROOT_DIR / "data" / "chroma_cache_perf_test_db"
# Les données sont dans le répertoire data de la solution
CONSULTANTS_PATH = ROOT_DIR / "data" / "consultants.csv"
JOBS_PATH = ROOT_DIR / "data" / "fiches_de_poste.csv"

@pytest.fixture(scope="module")
def api_key():
    """Fixture pour charger la clé API OpenAI."""
    return os.getenv("OPENAI_API_KEY")

@pytest.fixture(scope="module")
def kernel(api_key):
    """Fixture pour initialiser le kernel sémantique."""
    sk_kernel, _ = initialize_kernel(api_key, logger)
    return sk_kernel

@pytest.fixture(scope="module")
def dataframes():
    """Fixture pour charger les dataframes."""
    consultants_df, jobs_df = load_data(CONSULTANTS_PATH, JOBS_PATH, logger)
    return consultants_df, jobs_df

@pytest.fixture(scope="function")
def persistent_client_setup():
    """
    Configure et nettoie un client ChromaDB persistant dans un répertoire unique.
    Utilise 'yield' pour s'assurer que le nettoyage a lieu après l'exécution du test.
    """
    db_path = CHROMA_PERSIST_DIR / str(uuid.uuid4())
    db_path.mkdir(parents=True, exist_ok=True)
    
    client = chromadb.PersistentClient(path=str(db_path))
    
    yield client, db_path  # Fournit le client et le chemin au test
    
    # Nettoyage après le test
    del client
    time.sleep(1) # Laisse le temps de libérer les verrous
    try:
        if db_path.exists():
            shutil.rmtree(db_path)
    except PermissionError:
        logger.warning(f"Impossible de supprimer le répertoire de test {db_path} en raison d'un verrou de fichier.")

@pytest.fixture(scope="function")
def volatile_client():
    """Configure un client ChromaDB volatile (en mémoire)."""
    return chromadb.Client()

@pytest.mark.asyncio
async def test_indexing_performance_persistent(kernel, dataframes, persistent_client_setup, caplog):
    """Teste la performance avec un cache persistant."""
    caplog.set_level(logging.INFO)
    consultants_df, jobs_df = dataframes
    client, db_path = persistent_client_setup
    
    embedding_generator = kernel.get_service(service_id="text-embedding-3-small")
    vector_store = ChromaStore(client=client, embedding_generator=embedding_generator)

    logger.info("--- Test de performance avec CACHE PERSISTANT ---")

    # Première passe (Warm-up)
    start_time_1 = time.time()
    await index_consultants(vector_store, consultants_df, logger, "consultants_perf")
    await index_jobs(vector_store, jobs_df, logger, "jobs_perf")
    duration_1 = time.time() - start_time_1
    logger.info(f"[PERSISTENT] Première passe (sans cache) : {duration_1:.4f} secondes.")

    # Seconde passe (Avec cache)
    start_time_2 = time.time()
    await index_consultants(vector_store, consultants_df, logger, "consultants_perf")
    await index_jobs(vector_store, jobs_df, logger, "jobs_perf")
    duration_2 = time.time() - start_time_2
    logger.info(f"[PERSISTENT] Seconde passe (avec cache) : {duration_2:.4f} secondes.")

    assert duration_2 < duration_1, "La seconde passe devrait être significativement plus rapide."
    assert "Aucun nouveau" in caplog.text, "Les logs devraient indiquer que les collections sont à jour."

@pytest.mark.asyncio
async def test_indexing_performance_volatile(kernel, dataframes, volatile_client, caplog):
    """Teste la performance sans cache (en mémoire)."""
    caplog.set_level(logging.INFO)
    consultants_df, jobs_df = dataframes
    
    embedding_generator = kernel.get_service(service_id="text-embedding-3-small")
    vector_store = ChromaStore(client=volatile_client, embedding_generator=embedding_generator)

    logger.info("--- Test de performance SANS CACHE (volatile) ---")

    start_time = time.time()
    await index_consultants(vector_store, consultants_df, logger, "consultants_perf_volatile")
    await index_jobs(vector_store, jobs_df, logger, "jobs_perf_volatile")
    duration = time.time() - start_time
    logger.info(f"[VOLATILE] Passe unique (sans cache) : {duration:.4f} secondes.")

    assert duration > 1, "L'indexation sans cache devrait prendre un certain temps (appels API)."
