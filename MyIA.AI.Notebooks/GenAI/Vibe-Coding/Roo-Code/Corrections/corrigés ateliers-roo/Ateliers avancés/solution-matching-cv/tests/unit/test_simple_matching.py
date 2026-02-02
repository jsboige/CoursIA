import pytest
import pandas as pd
import os
import sys
import logging
from werkzeug.datastructures import FileStorage
 
 # Ajout pour rendre le module app importable
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..')))
from app import simple_matching
from app import matching
 
# Configuration du logger pour les tests
logger = logging.getLogger(__name__)
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

# Définir le chemin vers le répertoire de données réelles
APP_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..'))
DATA_DIR = os.path.join(APP_DIR, 'data')

@pytest.fixture
def real_data_files():
    """Fournit les objets FileStorage pour les données réelles."""
    consultants_path = os.path.join(DATA_DIR, 'consultants.csv')
    jobs_path = os.path.join(DATA_DIR, 'fiches_de_poste.csv')
    
    consultants_file = FileStorage(
        stream=open(consultants_path, 'rb'),
        filename="consultants.csv",
        content_type="text/csv",
    )
    jobs_file = FileStorage(
        stream=open(jobs_path, 'rb'),
        filename="fiches_de_poste.csv",
        content_type="text/csv",
    )
    
    yield consultants_file, jobs_file

    # Nettoyage
    consultants_file.close()
    jobs_file.close()

def test_simple_matching_logic_real_data(real_data_files):
    """
    Test de la logique de matching simple avec les données réelles.
    """
    consultants_file, jobs_file = real_data_files
    # Réinitialiser la position du flux
    consultants_file.stream.seek(0)
    jobs_file.stream.seek(0)

    # 1. Chargement des données
    consultants_df, jobs_df = matching.load_data(consultants_file, jobs_file, logger)
    assert consultants_df is not None and not consultants_df.empty
    assert jobs_df is not None and not jobs_df.empty
 
     # 2. Exécution du matching
    results_df = simple_matching.run_simple_matching(consultants_df, jobs_df)

    # 3. Validation des résultats
    assert not results_df.empty
    assert len(results_df) > 0
    # La fonction retourne 'job_id', 'consultant_name', 'matching_score', 'common_skills'
    # Elle ne retourne pas 'job_title'
    assert all(col in results_df.columns for col in ['job_id', 'consultant_name', 'matching_score', 'common_skills'])
    
    print(f"\nTest de la logique de matching simple avec données réelles réussi. {len(results_df)} correspondances trouvées.")