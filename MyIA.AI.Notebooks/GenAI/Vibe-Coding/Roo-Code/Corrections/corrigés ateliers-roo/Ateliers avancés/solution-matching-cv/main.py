import os
import asyncio
import logging
import time
from flask import Flask, render_template, request
import pandas as pd
import uuid
from dotenv import load_dotenv

# Charger les variables d'environnement du fichier .env
load_dotenv()

# Configuration du logging
logging.basicConfig(
    level=logging.INFO, # Niveau de log standard
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('app.log', mode='w'),
        logging.StreamHandler() # Ajout du logging vers la console
    ]
)
logger = logging.getLogger(__name__)

def get_performance_logger():
    """
    Configure et retourne un logger pour les mesures de performance,
    activé uniquement si la variable d'environnement ENABLE_PERFORMANCE_LOGS est à 'True'.
    """
    perf_logger = logging.getLogger('performance')
    # S'assurer de ne pas ajouter plusieurs handlers si la fonction est appelée plusieurs fois
    if not perf_logger.handlers:
        perf_logger.setLevel(logging.INFO)
        handler = logging.StreamHandler() # Afficher dans la console
        formatter = logging.Formatter('%(asctime)s - [PERFORMANCE] - %(message)s')
        handler.setFormatter(formatter)
        perf_logger.addHandler(handler)
    
    # Activer/désactiver le logger en fonction de la variable d'environnement
    if os.getenv('ENABLE_PERFORMANCE_LOGS', 'False').lower() == 'true':
        perf_logger.disabled = False
    else:
        perf_logger.disabled = True
        
    return perf_logger

# Importer la logique de matching
from app.simple_matching import run_simple_matching
from app.matching import (
    load_data as load_advanced,
    initialize_kernel,
    index_consultants,
    index_jobs,
    find_matches,
    run_best_score_matching,
    run_stable_matching
)
from semantic_kernel.connectors.chroma import ChromaStore

app = Flask(__name__)

# --- Pré-chargement des données au démarrage ---
PRELOADED_CONSULTANTS_DF = None
PRELOADED_JOBS_DF = None
DATA_PATH = 'data'
CONSULTANTS_DEFAULT_PATH = os.path.join(DATA_PATH, 'consultants.csv')
JOBS_DEFAULT_PATH = os.path.join(DATA_PATH, 'fiches_de_poste.csv')

try:
    if os.path.exists(CONSULTANTS_DEFAULT_PATH) and os.path.exists(JOBS_DEFAULT_PATH):
        PRELOADED_CONSULTANTS_DF = pd.read_csv(CONSULTANTS_DEFAULT_PATH)
        PRELOADED_JOBS_DF = pd.read_csv(JOBS_DEFAULT_PATH)
        logger.info("Fichiers de données par défaut (consultants.csv, fiches_de_poste.csv) pré-chargés avec succès.")
    else:
        logger.warning("Fichiers de données par défaut non trouvés. L'upload manuel sera nécessaire.")
except Exception as e:
    logger.error(f"Erreur lors du pré-chargement des fichiers de données : {e}")
# -----------------------------------------
# Créer un dossier temporaire pour les uploads du matching avancé
TEMP_FOLDER = 'temp_uploads'
os.makedirs(TEMP_FOLDER, exist_ok=True)
app.config['TEMP_FOLDER'] = TEMP_FOLDER

async def advanced_matching_wrapper(consultants_source, jobs_source, matching_algorithm, use_preloaded_data=False, proposing_party='consultants'):
    """
    Wrapper pour exécuter le pipeline de matching avancé de manière asynchrone.
    Gère soit les fichiers uploadés, soit les dataframes pré-chargés.
    """
    perf_logger = get_performance_logger()
    start_time = time.time()
    logger.info(f"Début du processus de matching avancé pour l'algorithme : {matching_algorithm}.")
    
    consultants_path = None
    jobs_path = None

    try:
        t0 = time.time()
        logger.info("ÉTAPE 1: Chargement des données.")
        
        if use_preloaded_data:
            # Les sources sont déjà des DataFrames
            consultants_df, jobs_df = consultants_source.copy(), jobs_source.copy()
        else:
            # Les sources sont des objets FileStorage, il faut les sauvegarder
            session_id = str(uuid.uuid4())
            consultants_filename = f"{session_id}_consultants.csv"
            jobs_filename = f"{session_id}_jobs.csv"
            consultants_path = os.path.join(app.config['TEMP_FOLDER'], consultants_filename)
            jobs_path = os.path.join(app.config['TEMP_FOLDER'], jobs_filename)
            
            logger.info(f"Sauvegarde temporaire des fichiers : {consultants_path}, {jobs_path}")
            consultants_source.save(consultants_path)
            jobs_source.save(jobs_path)
            
            consultants_df, jobs_df = load_advanced(consultants_path, jobs_path, logger=logger)
        perf_logger.info(f"Chargement des données terminé en {time.time() - t0:.2f} secondes.")
        if consultants_df is None or jobs_df is None:
            logger.error("Échec du chargement des données.")
            return pd.DataFrame()

        logger.info("ÉTAPE 2: Exécution du pipeline de matching sémantique.")
        api_key = os.getenv("OPENAI_API_KEY")
        if not api_key:
            logger.error("Clé API OpenAI non trouvée.")
            raise ValueError("La clé API OpenAI n'est pas configurée.")
        
        logger.info("Initialisation du kernel sémantique.")
        t0 = time.time()
        kernel, service = initialize_kernel(api_key=api_key, logger=logger)
        perf_logger.info(f"Initialisation du kernel sémantique terminée en {time.time() - t0:.2f} secondes.")
        if not kernel:
            return pd.DataFrame()

        logger.info("Configuration de la mémoire sémantique.")
        # Utiliser ChromaDB pour la persistance des embeddings
        # Utiliser ChromaDB pour la persistance des embeddings avec la nouvelle API
        vector_store = ChromaStore(
            persist_directory="./data/chroma_memory",
            embedding_generator=service
        )
        
        t0 = time.time()
        await index_consultants(vector_store, consultants_df, logger=logger)
        perf_logger.info(f"Indexation des consultants terminée en {time.time() - t0:.2f} secondes.")

        t0 = time.time()
        await index_jobs(vector_store, jobs_df, logger=logger)
        perf_logger.info(f"Indexation des fiches de poste terminée en {time.time() - t0:.2f} secondes.")
 
        t0 = time.time()
        similarity_scores = await find_matches(vector_store, jobs_df, logger=logger)
        perf_logger.info(f"Recherche des correspondances terminée en {time.time() - t0:.2f} secondes.")

        t0 = time.time()
        # --- AJOUT DE LOGS POUR LE DEBUG ---
        logger.info(f"Données avant matching pour '{matching_algorithm}':")
        logger.info(f"  - consultants_df: {consultants_df.shape[0]} lignes, colonnes: {list(consultants_df.columns)}")
        logger.info(f"  - jobs_df: {jobs_df.shape[0]} lignes, colonnes: {list(jobs_df.columns)}")
        # Créer un DataFrame à partir des scores pour l'analyse
        scores_df = pd.DataFrame(similarity_scores)
        logger.info(f"  - similarity_scores: {len(similarity_scores)} scores trouvés.")
        if not scores_df.empty:
            logger.info(f"Aperçu des scores:\n{scores_df.head().to_string()}")
        # --- FIN DES LOGS ---

        results_df = pd.DataFrame()
        if matching_algorithm == 'best_score_semantic':
            results_df = run_best_score_matching(jobs_df, consultants_df.copy(), scores_df.copy(), logger)
            perf_logger.info(f"Matching 'Meilleur score' terminé en {time.time() - t0:.2f} secondes.")

        elif matching_algorithm == 'stable_semantic':
            results_df = run_stable_matching(
                jobs_df,
                consultants_df.copy(),
                similarity_scores,
                logger=logger,
                proposing_party=proposing_party
            )
            if results_df is None or results_df.empty:
                 logger.warning("Le matching stable n'a retourné aucun résultat.")
                 return pd.DataFrame()
            perf_logger.info(f"Matching 'Stable' (optimisé pour {proposing_party}) terminé en {time.time() - t0:.2f} secondes.")
        
        return results_df

    except Exception as e:
        logger.error(f"Erreur majeure dans advanced_matching_wrapper: {e}", exc_info=True)
        return pd.DataFrame() # Retourner un dataframe vide en cas d'erreur
    finally:
        perf_logger.info(f"Durée totale du matching avancé : {time.time() - start_time:.2f} secondes.")
        logger.info("Nettoyage des fichiers temporaires.")
        # Nettoyer les fichiers temporaires seulement s'ils ont été créés
        if consultants_path and os.path.exists(consultants_path):
            os.remove(consultants_path)
        if jobs_path and os.path.exists(jobs_path):
            os.remove(jobs_path)


@app.route('/', methods=['GET', 'POST'])
async def index():
    if request.method == 'POST':
        consultants_file = request.files.get('consultants_file')
        jobs_file = request.files.get('jobs_file')
        matching_algorithm = request.form.get('matching_algorithm')
        results_df = pd.DataFrame()

        # Utiliser les fichiers pré-chargés si aucun fichier n'est uploadé
        use_preloaded_data = not consultants_file.filename and not jobs_file.filename
        
        if use_preloaded_data:
            logger.info("Utilisation des données pré-chargées.")
            consultants_df_source = PRELOADED_CONSULTANTS_DF
            jobs_df_source = PRELOADED_JOBS_DF
            if consultants_df_source is None or jobs_df_source is None:
                return render_template('index.html', error="Fichiers par défaut non chargés au démarrage. Veuillez les uploader.")
        else:
            logger.info("Utilisation des fichiers uploadés.")
            consultants_df_source = consultants_file
            jobs_df_source = jobs_file
            if not consultants_file or not jobs_file:
                 return render_template('index.html', error="Veuillez sélectionner les deux fichiers.")

        try:
            if matching_algorithm == 'simple':
                if use_preloaded_data:
                    consultants_df = consultants_df_source.copy()
                    jobs_df = jobs_df_source.copy()
                else:
                    # Pour les uploads, il faut toujours lire les données
                    consultants_df = pd.read_csv(consultants_df_source)
                    jobs_df = pd.read_csv(jobs_df_source)
                
                results_df = run_simple_matching(consultants_df, jobs_df)
            
            elif matching_algorithm in ['best_score_semantic', 'stable_semantic']:
                # L'adaptation pour le matching avancé se fera dans une étape suivante.
                # Pour l'instant, nous nous concentrons sur le simple et la structure.
                # Note: Le wrapper avancé devra être modifié pour accepter des DataFrames.
                proposing_party = request.form.get('proposing_party', 'consultants')
                results_df = await advanced_matching_wrapper(consultants_df_source, jobs_df_source, matching_algorithm, use_preloaded_data, proposing_party)
            
            else:
                return render_template('index.html', error="Algorithme de matching non valide sélectionné.")

            if results_df.empty:
                return render_template('index.html', no_results=True)
            else:
                return render_template('index.html', results=results_df.to_html(classes='table table-striped', index=False))
        
        except Exception as e:
            return render_template('index.html', error=f"Une erreur est survenue : {e}")
            
    return render_template('index.html')

if __name__ == '__main__':
    app.run(debug=True)
