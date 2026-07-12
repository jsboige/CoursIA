import os
import asyncio
import logging
import time
import threading
from flask import Flask, render_template, request
import pandas as pd
import uuid
from dotenv import load_dotenv

# Charger les variables d'environnement du fichier .env
load_dotenv()

# Configuration du logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('app.log', mode='w'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)


def get_performance_logger():
    """
    Configure et retourne un logger pour les mesures de performance,
    active uniquement si ENABLE_PERFORMANCE_LOGS='true'.
    """
    perf_logger = logging.getLogger('performance')
    if not perf_logger.handlers:
        perf_logger.setLevel(logging.INFO)
        handler = logging.StreamHandler()
        formatter = logging.Formatter('%(asctime)s - [PERFORMANCE] - %(message)s')
        handler.setFormatter(formatter)
        perf_logger.addHandler(handler)

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

app = Flask(__name__)

# --- Pre-chargement des donnees au demarrage ---
PRELOADED_CONSULTANTS_DF = None
PRELOADED_JOBS_DF = None
DATA_PATH = 'data'
CONSULTANTS_DEFAULT_PATH = os.path.join(DATA_PATH, 'consultants.csv')
JOBS_DEFAULT_PATH = os.path.join(DATA_PATH, 'fiches_de_poste.csv')

try:
    if os.path.exists(CONSULTANTS_DEFAULT_PATH) and os.path.exists(JOBS_DEFAULT_PATH):
        PRELOADED_CONSULTANTS_DF = pd.read_csv(CONSULTANTS_DEFAULT_PATH)
        PRELOADED_JOBS_DF = pd.read_csv(JOBS_DEFAULT_PATH)
        logger.info("Fichiers de donnees par defaut pre-charges avec succes.")
    else:
        logger.warning("Fichiers de donnees par defaut non trouves. L'upload manuel sera necessaire.")
except Exception as e:
    logger.error(f"Erreur lors du pre-chargement des fichiers de donnees : {e}")

# Creer un dossier temporaire pour les uploads du matching avance
TEMP_FOLDER = 'temp_uploads'
os.makedirs(TEMP_FOLDER, exist_ok=True)
app.config['TEMP_FOLDER'] = TEMP_FOLDER


async def advanced_matching_wrapper(consultants_source, jobs_source, matching_algorithm,
                                    use_preloaded_data=False, proposing_party='consultants'):
    """
    Wrapper pour executer le pipeline de matching avance de maniere asynchrone.
    Gere soit les fichiers uploades, soit les dataframes pre-charges.
    """
    perf_logger = get_performance_logger()
    start_time = time.time()
    logger.info(f"Debut du processus de matching avance pour l'algorithme : {matching_algorithm}.")

    consultants_path = None
    jobs_path = None

    try:
        t0 = time.time()
        logger.info("ETAPE 1: Chargement des donnees.")

        if use_preloaded_data:
            consultants_df, jobs_df = consultants_source.copy(), jobs_source.copy()
        else:
            session_id = str(uuid.uuid4())
            consultants_filename = f"{session_id}_consultants.csv"
            jobs_filename = f"{session_id}_jobs.csv"
            consultants_path = os.path.join(app.config['TEMP_FOLDER'], consultants_filename)
            jobs_path = os.path.join(app.config['TEMP_FOLDER'], jobs_filename)

            logger.info(f"Sauvegarde temporaire des fichiers : {consultants_path}, {jobs_path}")
            consultants_source.save(consultants_path)
            jobs_source.save(jobs_path)

            consultants_df, jobs_df = load_advanced(consultants_path, jobs_path, logger=logger)

        perf_logger.info(f"Chargement des donnees termine en {time.time() - t0:.2f} secondes.")
        if consultants_df is None or jobs_df is None:
            logger.error("Echec du chargement des donnees.")
            return pd.DataFrame()

        logger.info("ETAPE 2: Execution du pipeline de matching semantique.")
        api_key = os.getenv("OPENAI_API_KEY")
        if not api_key:
            logger.error("Cle API OpenAI non trouvee.")
            raise ValueError("La cle API OpenAI n'est pas configuree.")

        logger.info("Initialisation du kernel semantique.")
        t0 = time.time()
        kernel, service = initialize_kernel(api_key=api_key, logger=logger)
        perf_logger.info(f"Initialisation du kernel semantique terminee en {time.time() - t0:.2f} secondes.")
        if not kernel:
            return pd.DataFrame()

        logger.info("Configuration de la memoire semantique.")
        from semantic_kernel.connectors.chroma import ChromaStore

        vector_store = ChromaStore(
            persist_directory="./data/chroma_memory",
            embedding_generator=service
        )

        t0 = time.time()
        await index_consultants(vector_store, consultants_df, logger=logger)
        perf_logger.info(f"Indexation des consultants terminee en {time.time() - t0:.2f} secondes.")

        t0 = time.time()
        await index_jobs(vector_store, jobs_df, logger=logger)
        perf_logger.info(f"Indexation des fiches de poste terminee en {time.time() - t0:.2f} secondes.")

        t0 = time.time()
        similarity_scores = await find_matches(vector_store, jobs_df, logger=logger)
        perf_logger.info(f"Recherche des correspondances terminee en {time.time() - t0:.2f} secondes.")

        t0 = time.time()
        logger.info(f"Donnees avant matching pour '{matching_algorithm}':")
        logger.info(f"  - consultants_df: {consultants_df.shape[0]} lignes, colonnes: {list(consultants_df.columns)}")
        logger.info(f"  - jobs_df: {jobs_df.shape[0]} lignes, colonnes: {list(jobs_df.columns)}")
        scores_df = pd.DataFrame(similarity_scores)
        logger.info(f"  - similarity_scores: {len(similarity_scores)} scores trouves.")
        if not scores_df.empty:
            logger.info(f"Apercu des scores:\n{scores_df.head().to_string()}")

        results_df = pd.DataFrame()
        if matching_algorithm == 'best_score_semantic':
            results_df = run_best_score_matching(jobs_df, consultants_df.copy(), scores_df.copy(), logger)
            perf_logger.info(f"Matching 'Meilleur score' termine en {time.time() - t0:.2f} secondes.")

        elif matching_algorithm == 'stable_semantic':
            results_df = run_stable_matching(
                jobs_df,
                consultants_df.copy(),
                similarity_scores,
                logger=logger,
                proposing_party=proposing_party
            )
            if results_df is None or results_df.empty:
                logger.warning("Le matching stable n'a retourne aucun resultat.")
                return pd.DataFrame()
            perf_logger.info(f"Matching 'Stable' (optimise pour {proposing_party}) termine en {time.time() - t0:.2f} secondes.")

        return results_df

    except Exception as e:
        logger.error(f"Erreur majeure dans advanced_matching_wrapper: {e}", exc_info=True)
        return pd.DataFrame()
    finally:
        perf_logger.info(f"Duree totale du matching avance : {time.time() - start_time:.2f} secondes.")
        logger.info("Nettoyage des fichiers temporaires.")
        if consultants_path and os.path.exists(consultants_path):
            os.remove(consultants_path)
        if jobs_path and os.path.exists(jobs_path):
            os.remove(jobs_path)


def _run_async(coro):
    """Run an async coroutine from synchronous Flask context."""
    try:
        loop = asyncio.get_running_loop()
    except RuntimeError:
        loop = None

    if loop and loop.is_running():
        # We're inside an existing event loop — run in a new thread
        result = [None]
        exception = [None]

        def worker():
            try:
                result[0] = asyncio.run(coro)
            except Exception as e:
                exception[0] = e

        thread = threading.Thread(target=worker)
        thread.start()
        thread.join()
        if exception[0]:
            raise exception[0]
        return result[0]
    else:
        return asyncio.run(coro)


@app.route('/', methods=['GET', 'POST'])
def index():
    """Route principale — synchrone, delegue l'async a _run_async."""
    if request.method == 'POST':
        consultants_file = request.files.get('consultants_file')
        jobs_file = request.files.get('jobs_file')
        matching_algorithm = request.form.get('matching_algorithm')
        results_df = pd.DataFrame()

        # Determiner si on utilise les donnees pre-chargees
        has_consultants = consultants_file and consultants_file.filename
        has_jobs = jobs_file and jobs_file.filename
        use_preloaded_data = not has_consultants and not has_jobs

        if use_preloaded_data:
            logger.info("Utilisation des donnees pre-chargees.")
            consultants_df_source = PRELOADED_CONSULTANTS_DF
            jobs_df_source = PRELOADED_JOBS_DF
            if consultants_df_source is None or jobs_df_source is None:
                return render_template('index.html', error="Fichiers par defaut non charges au demarrage. Veuillez les uploader.")
        else:
            if not has_consultants or not has_jobs:
                return render_template('index.html', error="Veuillez selectionner les deux fichiers.")
            logger.info("Utilisation des fichiers uploades.")
            consultants_df_source = consultants_file
            jobs_df_source = jobs_file

        try:
            if matching_algorithm == 'simple':
                if use_preloaded_data:
                    consultants_df = consultants_df_source.copy()
                    jobs_df = jobs_df_source.copy()
                else:
                    consultants_df = pd.read_csv(consultants_df_source)
                    jobs_df = pd.read_csv(jobs_df_source)

                results_df = run_simple_matching(consultants_df, jobs_df)

            elif matching_algorithm in ['best_score_semantic', 'stable_semantic']:
                proposing_party = request.form.get('proposing_party', 'consultants')
                results_df = _run_async(
                    advanced_matching_wrapper(
                        consultants_df_source, jobs_df_source,
                        matching_algorithm, use_preloaded_data, proposing_party
                    )
                )

            else:
                return render_template('index.html', error="Algorithme de matching non valide selectionne.")

            if results_df is None or results_df.empty:
                return render_template('index.html', no_results=True)
            else:
                return render_template('index.html', results=results_df.to_html(classes='table table-striped', index=False))

        except Exception as e:
            logger.error(f"Erreur dans la route index : {e}", exc_info=True)
            return render_template('index.html', error=f"Une erreur est survenue : {e}")

    return render_template('index.html')


if __name__ == '__main__':
    app.run(debug=True)
