import pytest
import pytest_asyncio
import pandas as pd
import asyncio
import shutil
from app.matching import (
    run_best_score_matching,
    run_stable_matching,
    load_data,
    initialize_kernel,
    index_consultants,
    index_jobs,
    find_matches,
)
from semantic_kernel.connectors.chroma import ChromaStore
import os
import chromadb
from dotenv import load_dotenv

# Définir le chemin racine du projet pour localiser les fichiers de données et .env
project_root_path = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..'))
load_dotenv(os.path.join(project_root_path, '.env'))


# Fixture pour charger les données et préparer les scores de similarité
# Fixture pour charger les données et préparer les scores de similarité
@pytest_asyncio.fixture(scope="function")
async def similarity_scores_data():
    """
    Prépare les données de test, initialise un client persistant et un kernel frais,
    indexe les données de manière idempotente et retourne les scores de similarité.
    """
    class MockLogger:
        def info(self, msg): pass
        def warning(self, msg): pass
        def error(self, msg, exc_info=False): pass
        def debug(self, msg): pass
    logger = MockLogger()

    consultants_path = os.path.join(project_root_path, 'data', 'consultants.csv')
    jobs_path = os.path.join(project_root_path, 'data', 'fiches_de_poste.csv')
    consultants_df, jobs_df = load_data(consultants_path, jobs_path, logger)
    
    test_consultants = consultants_df[consultants_df['Nom'].str.startswith('Test Consultant')].copy()
    test_jobs = jobs_df[jobs_df['Titre'].str.startswith('Test Job')].copy()

    # Ajouter manuellement les IDs car _preprocess_data ne le fait plus
    test_consultants['ID'] = 'consultant_' + test_consultants.index.astype(str)
    test_jobs['ID'] = 'job_' + test_jobs.index.astype(str)

    api_key = os.getenv("OPENAI_API_KEY")
    if not api_key:
        pytest.fail("La clé API OpenAI n'est pas configurée.")
    
    _, service = initialize_kernel(api_key=api_key, logger=logger)
    
    test_db_path = os.path.join(project_root_path, "data", "chroma_db_utility_test")
    os.makedirs(test_db_path, exist_ok=True)
    chroma_client = chromadb.PersistentClient(path=test_db_path)
    vector_store = ChromaStore(client=chroma_client, embedding_generator=service)

    # Log pour déboguer l'état de la base de données au démarrage du test
    consultants_collection = chroma_client.get_or_create_collection(name="utility_test_consultants")
    jobs_collection = chroma_client.get_or_create_collection(name="utility_test_jobs")
    logger.info(f"[DEBUG] Au début du test, la collection 'utility_test_consultants' contient {consultants_collection.count()} éléments.")
    logger.info(f"[DEBUG] Au début du test, la collection 'utility_test_jobs' contient {jobs_collection.count()} éléments.")

    await index_consultants(vector_store, test_consultants, logger=logger, collection_name="utility_test_consultants")
    await index_jobs(vector_store, test_jobs, logger=logger, collection_name="utility_test_jobs")

    similarity_scores = await find_matches(
        vector_store,
        test_jobs,
        logger=logger,
        consultant_collection_name="utility_test_consultants",
        job_collection_name="utility_test_jobs"
    )
        
    return test_consultants, test_jobs, pd.DataFrame(similarity_scores)

@pytest.mark.asyncio
async def test_compare_matching_utility(similarity_scores_data):
    """
    Compare l'utilité totale (somme des scores) des algorithmes
    'best_score' et 'stable_matching'.
    """
    consultants_df, jobs_df, similarity_df = similarity_scores_data

    # Simuler le logger
    class MockLogger:
        def info(self, msg): print(f"INFO: {msg}")
        def warning(self, msg): print(f"WARNING: {msg}")
        def error(self, msg, exc_info=False): print(f"ERROR: {msg}")
        def debug(self, msg): print(f"DEBUG: {msg}")

    logger = MockLogger()

    # 1. Exécuter l'algorithme "Meilleur Score"
    best_score_results = run_best_score_matching(
        jobs_df.copy(), consultants_df.copy(), similarity_df.copy(), logger
    )
    
    # 2. Exécuter l'algorithme "Mariage Stable"
    stable_matching_results = run_stable_matching(
        jobs_df.copy(), consultants_df.copy(), similarity_df.copy(), logger
    )

    assert not best_score_results.empty, "Le matching par meilleur score ne devrait pas être vide."
    assert not stable_matching_results.empty, "Le matching stable ne devrait pas être vide."

    # 3. Calculer l'utilité totale pour chaque algorithme
    best_score_utility = best_score_results['matching_score'].sum()
    stable_matching_utility = stable_matching_results['matching_score'].sum()

    print(f"Utilité totale (Meilleur Score): {best_score_utility:.4f}")
    print(f"Utilité totale (Mariage Stable): {stable_matching_utility:.4f}")

    # 4. Vérifier que le mariage stable produit une utilité globale supérieure ou égale
    #    (il optimise la stabilité, ce qui peut mener à une utilité égale ou supérieure)
    assert stable_matching_utility >= best_score_utility

@pytest.mark.asyncio
async def test_compare_stable_matching_roles(similarity_scores_data):
    """
    Compare les résultats des algorithmes de mariage stable optimisés
    pour les consultants et pour les jobs.
    """
    consultants_df, jobs_df, similarity_df = similarity_scores_data

    class MockLogger:
        def info(self, msg): print(f"INFO: {msg}")
        def warning(self, msg): print(f"WARNING: {msg}")
        def error(self, msg, exc_info=False): print(f"ERROR: {msg}")
        def debug(self, msg): print(f"DEBUG: {msg}")

    logger = MockLogger()

    # 1. Exécuter l'algorithme optimisé pour les consultants
    consultant_optimal_results = run_stable_matching(
        jobs_df.copy(), consultants_df.copy(), similarity_df.copy(), logger, proposing_party='consultants'
    )

    # 2. Exécuter l'algorithme optimisé pour les jobs
    job_optimal_results = run_stable_matching(
        jobs_df.copy(), consultants_df.copy(), similarity_df.copy(), logger, proposing_party='jobs'
    )

    assert not consultant_optimal_results.empty
    assert not job_optimal_results.empty

    consultant_utility = consultant_optimal_results['matching_score'].sum()
    job_utility = job_optimal_results['matching_score'].sum()

    print(f"Utilité (consultant-optimal): {consultant_utility:.4f}")
    print(f"Utilité (job-optimal): {job_utility:.4f}")

    # Les deux doivent produire des résultats valides
    assert consultant_utility > 0
    assert job_utility > 0