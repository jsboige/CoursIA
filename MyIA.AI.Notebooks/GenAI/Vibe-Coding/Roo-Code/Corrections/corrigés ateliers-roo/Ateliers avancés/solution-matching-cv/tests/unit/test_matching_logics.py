import pytest
import pandas as pd
import os
import sys
import time
import logging

# Ajout pour rendre les modules app et src importables
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..')))
from app import matching
from app import simple_matching

# Configuration du logger pour les tests
logger = logging.getLogger(__name__)
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

@pytest.fixture
def mock_consultants_df():
    """Crée un DataFrame de consultants pour les tests."""
    data = {
        'ID': ['C1', 'C2', 'C3'],
        'Nom': ['Alice', 'Bob', 'Charlie'],
        'Poste': ['Développeur Python', 'Data Scientist', 'Chef de Projet'],
        'Compétences': ['Python, Flask, SQL', 'Python, Pandas, Scikit-learn', 'Gestion de projet, Agile, Jira'],
        'Expériences clés': ['Développement API REST', 'Modélisation prédictive', 'Planification de sprints']
    }
    return pd.DataFrame(data)

@pytest.fixture
def mock_jobs_df():
    """Crée un DataFrame de fiches de poste pour les tests."""
    data = {
        'ID': ['J1', 'J2'],
        'Titre': ['Développeur Backend', 'Manager Agile'],
        'Description brute': ['Recherche développeur pour projet Flask', 'Recherche manager pour équipe Agile'],
        'Compétences clés': ['Python, SQL', 'Agile, Jira, Scrum']
    }
    return pd.DataFrame(data)

@pytest.fixture
def mock_similarity_scores():
    """Crée une liste de scores de similarité pour les tests."""
    return [
        {'job_id': 'J1', 'consultant_id': 'C1', 'score_de_similarite': 0.9},
        {'job_id': 'J1', 'consultant_id': 'C2', 'score_de_similarite': 0.7},
        {'job_id': 'J1', 'consultant_id': 'C3', 'score_de_similarite': 0.2},
        {'job_id': 'J2', 'consultant_id': 'C1', 'score_de_similarite': 0.1},
        {'job_id': 'J2', 'consultant_id': 'C2', 'score_de_similarite': 0.4},
        {'job_id': 'J2', 'consultant_id': 'C3', 'score_de_similarite': 0.8}
    ]

# --- Tests pour simple_matching ---

def test_run_simple_matching(mock_consultants_df, mock_jobs_df):
    """Teste la fonction run_simple_matching."""
    start_time = time.time()
    results_df = simple_matching.run_simple_matching(mock_consultants_df, mock_jobs_df)
    end_time = time.time()

    print(f"\n[PERFORMANCE] run_simple_matching a pris {end_time - start_time:.6f} secondes.")

    assert isinstance(results_df, pd.DataFrame)
    assert not results_df.empty
    assert 'job_id' in results_df.columns
    assert 'consultant_name' in results_df.columns
    assert 'matching_score' in results_df.columns
    assert results_df['matching_score'].iloc[0] == 2 # Alice pour le poste J1 (Python, SQL)
    assert results_df[results_df['job_title'] == 'Développeur Backend']['consultant_name'].iloc[0] == 'Alice'

# --- Tests pour matching (avancé) ---

def test_run_best_score_matching(mock_jobs_df, mock_consultants_df, mock_similarity_scores):
    """Teste la fonction run_best_score_matching."""
    start_time = time.time()
    results_df = matching.run_best_score_matching(mock_jobs_df, mock_consultants_df, mock_similarity_scores, logger)
    end_time = time.time()

    print(f"\n[PERFORMANCE] run_best_score_matching a pris {end_time - start_time:.6f} secondes.")

    assert isinstance(results_df, pd.DataFrame)
    assert not results_df.empty
    assert len(results_df) == 2  # Un meilleur match pour chaque poste
    assert 'job_title' in results_df.columns
    assert 'consultant_name' in results_df.columns
    assert 'matching_score' in results_df.columns
    
    # Vérifier que le meilleur consultant a été choisi pour chaque poste
    assert results_df[results_df['job_title'] == 'Développeur Backend']['consultant_name'].iloc[0] == 'Alice'
    assert results_df[results_df['job_title'] == 'Manager Agile']['consultant_name'].iloc[0] == 'Charlie'

def test_run_stable_matching_consultant_optimal(mock_jobs_df, mock_consultants_df, mock_similarity_scores):
    """Teste la fonction run_stable_matching en mode consultant-optimal."""
    start_time = time.time()
    results_df = matching.run_stable_matching(mock_jobs_df, mock_consultants_df, mock_similarity_scores, logger, proposing_party='consultants')
    end_time = time.time()

    print(f"\n[PERFORMANCE] run_stable_matching (consultant-optimal) a pris {end_time - start_time:.6f} secondes.")

    assert isinstance(results_df, pd.DataFrame)
    assert not results_df.empty
    # Comme il y a plus de consultants que de postes, le nombre de matchs sera égal au nombre de postes
    assert len(results_df) == len(mock_jobs_df)
    assert 'job_title' in results_df.columns
    assert 'consultant_name' in results_df.columns
    assert 'matching_score' in results_df.columns

def test_run_stable_matching_job_optimal(mock_jobs_df, mock_consultants_df, mock_similarity_scores):
    """Teste la fonction run_stable_matching en mode job-optimal."""
    start_time = time.time()
    results_df = matching.run_stable_matching(mock_jobs_df, mock_consultants_df, mock_similarity_scores, logger, proposing_party='jobs')
    end_time = time.time()

    print(f"\n[PERFORMANCE] run_stable_matching (job-optimal) a pris {end_time - start_time:.6f} secondes.")

    assert isinstance(results_df, pd.DataFrame)
    assert not results_df.empty
    assert len(results_df) == len(mock_jobs_df)
    assert 'job_title' in results_df.columns
    assert 'consultant_name' in results_df.columns
    assert 'matching_score' in results_df.columns
