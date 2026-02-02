import os
import shutil
import pytest
import chromadb
from chromadb.config import Settings
import logging

# Configuration du logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Définir le chemin de la base de données de test
project_root_path = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..'))
TEST_DB_PATH = os.path.join(project_root_path, "data", "chroma_persistence_test_db")
COLLECTION_NAME = "persistence_test_collection"

@pytest.fixture(scope="module")
def test_client():
    """
    Crée un client et nettoie la base de données avant et après les tests du module.
    """
    if os.path.exists(TEST_DB_PATH):
        shutil.rmtree(TEST_DB_PATH)
    os.makedirs(TEST_DB_PATH, exist_ok=True)
    logger.info(f"Environnement de test nettoyé et prêt à : {TEST_DB_PATH}")
    
    client = chromadb.PersistentClient(
        path=TEST_DB_PATH,
        settings=Settings(allow_reset=True)
    )
    
    yield client
    
    logger.info("--- Nettoyage après les tests du module ---")
    try:
        client.reset()  # Vide la base de données
    except chromadb.errors.InternalError as e:
        logger.warning(f"Erreur lors du reset de ChromaDB, possiblement un bug ou un état instable : {e}")
    # shutil.rmtree(TEST_DB_PATH) # Peut causer des PermissionError si le client n'est pas bien fermé
    logger.info(f"Environnement de test nettoyé après les tests.")

def test_initial_write(test_client):
    """
    Teste l'écriture initiale dans la base de données persistante.
    """
    logger.info("--- Démarrage de test_initial_write ---")
    from chromadb.utils import embedding_functions
    default_ef = embedding_functions.DefaultEmbeddingFunction()
    collection = test_client.get_or_create_collection(name=COLLECTION_NAME, embedding_function=default_ef)
    
    test_ids = ["id1", "id2"]
    collection.add(
        ids=test_ids,
        metadatas=[{"source": "test1"}, {"source": "test1"}],
        documents=["document 1", "document 2"]
    )
    
    count = collection.count()
    logger.info(f"Client 1: La collection contient {count} éléments après ajout.")
    assert count == 2
    
    retrieved = collection.get(ids=["id1"])
    logger.info(f"Client 1: Données récupérées pour id1: {retrieved}")
    assert retrieved['ids'] == ["id1"]
    logger.info("--- Fin de test_initial_write ---")

def test_read_after_write(test_client):
    """
    Teste la lecture des données avec le MÊME client pour vérifier la persistance en mémoire.
    Un test avec un client différent serait nécessaire pour la persistance sur disque.
    """
    logger.info("--- Démarrage de test_read_after_write ---")
    from chromadb.utils import embedding_functions
    default_ef = embedding_functions.DefaultEmbeddingFunction()
    collection = test_client.get_collection(name=COLLECTION_NAME, embedding_function=default_ef)
    
    count = collection.count()
    logger.info(f"Client 2: La collection contient {count} éléments au démarrage.")
    assert count == 2
    
    retrieved = collection.get(ids=["id1", "id2"])
    logger.info(f"Client 2: Données récupérées pour id1 et id2: {retrieved}")
    
    assert sorted(retrieved['ids']) == sorted(["id1", "id2"])
    logger.info("--- Fin de test_read_after_write ---")
