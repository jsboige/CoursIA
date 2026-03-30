import os
import time
import pandas as pd
import hashlib
import semantic_kernel as sk
from semantic_kernel.connectors.ai.open_ai import OpenAITextEmbedding
from semantic_kernel.data.vector import VectorStoreField, VectorStoreCollectionDefinition
from semantic_kernel.exceptions import KernelException
from matching.games import StableMarriage

def _preprocess_data(consultants_df, jobs_df, logger):
    """
    Prétraite les dataframes en remplissant les NaN et en assurant des IDs uniques.
    """
    consultants_df.fillna('', inplace=True)
    jobs_df.fillna('', inplace=True)

    # Les IDs seront générés de manière déterministe lors de l'indexation.
    # Il n'est plus nécessaire de les créer ici.
    return consultants_df, jobs_df

def load_data(consultants_source, jobs_source, logger):
    """
    Charge les données depuis des chemins de fichiers ou directement depuis des DataFrames.
    """
    try:
        if isinstance(consultants_source, str):
            consultants_df = pd.read_csv(consultants_source)
        else:
            consultants_df = pd.read_csv(consultants_source)

        if isinstance(jobs_source, str):
            jobs_df = pd.read_csv(jobs_source)
        else:
            jobs_df = pd.read_csv(jobs_source)

        consultants_df, jobs_df = _preprocess_data(consultants_df, jobs_df, logger)

        logger.info(f"{len(consultants_df)} profils de consultants chargés.")
        logger.info(f"{len(jobs_df)} offres d'emploi chargées.")
        return consultants_df, jobs_df
        
    except Exception as e:
        logger.error(f"Erreur inattendue lors du chargement ou du traitement des données: {e}", exc_info=True)
        return None, None

def initialize_kernel(api_key, logger):
    """
    Initialise et configure le kernel sémantique avec le service d'embedding.
    """
    logger.info("Tentative d'initialisation du kernel sémantique.")
    kernel = sk.Kernel()
    try:
        embedding_service = OpenAITextEmbedding(
            ai_model_id="text-embedding-3-small",
            api_key=api_key
        )
        kernel.add_service(embedding_service)
        logger.info("Kernel sémantique initialisé avec succès.")
        return kernel, embedding_service
    except KernelException as e:
        logger.error(f"Erreur lors de l'initialisation du service Semantic Kernel : {e}", exc_info=True)
        return None, None

# Définition de la structure des données pour le VectorStore
# Conforme à la nouvelle API v1.34+ de Semantic Kernel
consultant_record_definition = VectorStoreCollectionDefinition(
    fields=[
        VectorStoreField('key', name='id'),
        VectorStoreField('data', name='content', is_full_text_indexed=True),
        VectorStoreField('vector', name='vector', dimensions=1536),
    ]
)

# Définition de la structure pour les fiches de poste
job_record_definition = VectorStoreCollectionDefinition(
    fields=[
        VectorStoreField('key', name='id'),
        VectorStoreField('data', name='content', is_full_text_indexed=True),
        VectorStoreField('vector', name='vector', dimensions=1536),
    ]
)
 
def _generate_deterministic_id(text):
    """Génère un ID déterministe basé sur le hash du contenu textuel."""
    return hashlib.sha256(text.encode('utf-8')).hexdigest()

async def index_consultants(vector_store, consultants_df, logger, collection_name="consultants"):
    """
    Indexe les profils des consultants de manière idempotente en utilisant un ID basé sur le contenu.
    """
    logger.info(f"Début de l'indexation idempotente pour la collection '{collection_name}'...")
    try:
        collection = vector_store.get_collection(
            collection_name=collection_name,
            record_type=dict,
            definition=consultant_record_definition
        )
        await collection.ensure_collection_exists()

        # Pré-calculer les IDs et les descriptions
        all_records = []
        for _, row in consultants_df.iterrows():
            description = (
                f"Titre: {row['Poste']}. "
                f"Expérience: {row['Expériences clés']}. "
                f"Compétences: {row['Compétences']}."
            )
            record_id = _generate_deterministic_id(description)
            all_records.append({'id': record_id, 'content': description, 'vector': description})

        all_ids = [record['id'] for record in all_records]
        # Accéder à la collection ChromaDB native via la méthode privée pour utiliser son API `get`
        native_collection = collection._get_collection()
        existing_records = native_collection.get(include=[])  # Ne récupère que les métadonnées (IDs)
        existing_ids = set(existing_records['ids'])

        records_to_upsert = [record for record in all_records if record['id'] not in existing_ids]

        if records_to_upsert:
            logger.info(f"Indexation de {len(records_to_upsert)} nouveaux consultants dans '{collection_name}'...")
            await collection.upsert(records_to_upsert)
            logger.info(f"{len(records_to_upsert)} consultants indexés avec succès.")
        else:
            logger.info(f"Aucun nouveau consultant à indexer. La collection '{collection_name}' est à jour.")
            
    except Exception as e:
        logger.error(f"Erreur inattendue lors de l'indexation des consultants : {e}", exc_info=True)


async def index_jobs(vector_store, jobs_df, logger, collection_name="jobs"):
    """
    Indexe les fiches de poste de manière idempotente en utilisant un ID basé sur le contenu.
    """
    logger.info(f"Début de l'indexation idempotente pour la collection '{collection_name}'...")
    try:
        collection = vector_store.get_collection(
            collection_name=collection_name,
            record_type=dict,
            definition=job_record_definition
        )
        await collection.ensure_collection_exists()

        # Pré-calculer les IDs et les descriptions
        all_records = []
        for _, row in jobs_df.iterrows():
            description = (
                f"Titre du poste: {row['Titre']}. "
                f"Description: {row['Description brute']}. "
                f"Compétences requises: {row['Compétences clés']}"
            )
            record_id = _generate_deterministic_id(description)
            all_records.append({'id': record_id, 'content': description, 'vector': description})

        all_ids = [record['id'] for record in all_records]
        # Accéder à la collection ChromaDB native via la méthode privée pour utiliser son API `get`
        native_collection = collection._get_collection()
        existing_records = native_collection.get(include=[])  # Ne récupère que les métadonnées (IDs)
        existing_ids = set(existing_records['ids'])

        records_to_upsert = [record for record in all_records if record['id'] not in existing_ids]

        if records_to_upsert:
            logger.info(f"Indexation de {len(records_to_upsert)} nouvelles fiches de poste dans '{collection_name}'...")
            await collection.upsert(records_to_upsert)
            logger.info(f"{len(records_to_upsert)} fiches de poste indexées avec succès.")
        else:
            logger.info(f"Aucune nouvelle fiche de poste à indexer. La collection '{collection_name}' est à jour.")
            
    except Exception as e:
        logger.error(f"Erreur inattendue lors de l'indexation des fiches de poste : {e}", exc_info=True)

async def find_matches(vector_store, jobs_df, logger, consultant_collection_name="consultants", job_collection_name="jobs"):
    """
    Recherche des correspondances en récupérant les embeddings des jobs depuis leur collection.
    """
    logger.info("Début de la recherche de correspondances optimisée avec les collections vectorielles...")
    results = []
    try:
        consultant_collection = vector_store.get_collection(record_type=dict, collection_name=consultant_collection_name, definition=consultant_record_definition)
        job_collection = vector_store.get_collection(record_type=dict, collection_name=job_collection_name, definition=job_record_definition)

        # Étape 1: Récupérer tous les jobs et leurs vecteurs depuis la collection
        logger.info(f"Récupération des embeddings pour {len(jobs_df)} fiches de poste depuis la collection '{job_collection_name}'...")
        
        # Recréer les IDs déterministes pour les jobs afin de les récupérer
        job_ids = []
        for _, row in jobs_df.iterrows():
            description = (
                f"Titre du poste: {row['Titre']}. "
                f"Description: {row['Description brute']}. "
                f"Compétences requises: {row['Compétences clés']}"
            )
            job_ids.append(_generate_deterministic_id(description))

        job_records = await job_collection.get(ids=job_ids, include_vectors=True)
        
        if not job_records:
            logger.warning("Aucun enregistrement de fiche de poste trouvé dans la collection. Impossible de continuer.")
            return []

        logger.info(f"{len(job_records)} embeddings de fiches de poste récupérés.")

        # Étape 2: Itérer sur les postes récupérés pour la recherche
        for record in job_records:
            job_id = record['id']
            query_vector = record['vector']
            
            logger.debug(f"Recherche de correspondances pour le poste ID {job_id}...")
            
            search_results = await consultant_collection.search(
                vector=query_vector,
                top=5
            )
            
            async for match in search_results.results:
                results.append({
                    "job_id": job_id,
                    "consultant_id": match.record['id'],
                    "score_de_similarite": round(match.score, 4)
                })

    except Exception as e:
        logger.error(f"Erreur inattendue lors de la recherche : {e}", exc_info=True)

    logger.info(f"Processus de recherche terminé. {len(results)} correspondances totales trouvées.")
    return results

def run_best_score_matching(jobs_df, consultants_df, similarity_scores, logger):
    """
    Trouve le meilleur consultant pour chaque poste basé sur le score de similarité.
    Ne requiert pas un nombre égal de consultants et de postes.
    """
    # Copie des dataframes pour éviter les effets de bord
    jobs_df = jobs_df.copy()
    consultants_df = consultants_df.copy()
    
    logger.info("Début de l'algorithme de matching par meilleur score.")
    
    similarity_df = pd.DataFrame(similarity_scores)
    if similarity_df.empty:
        logger.warning("Le dataframe des scores de similarité est vide. Aucun appariement possible.")
        return pd.DataFrame()


    # S'assurer que les IDs sont des chaînes de caractères pour les fusions
    if 'ID' not in consultants_df.columns:
        consultants_df['ID'] = consultants_df.index
    consultants_df['ID'] = consultants_df['ID'].astype(str)
    if 'ID' not in jobs_df.columns:
        jobs_df['ID'] = jobs_df.index
    jobs_df['ID'] = jobs_df['ID'].astype(str)
    similarity_df['consultant_id'] = similarity_df['consultant_id'].astype(str)
    similarity_df['job_id'] = similarity_df['job_id'].astype(str)

    # Logique d'assignation unique basée sur le meilleur score global
    all_matches = similarity_df.sort_values(by='score_de_similarite', ascending=False)

    final_matches_list = []
    assigned_consultants = set()
    assigned_jobs = set()

    for _, match in all_matches.iterrows():
        if match['consultant_id'] not in assigned_consultants and match['job_id'] not in assigned_jobs:
            final_matches_list.append(match)
            assigned_consultants.add(match['consultant_id'])
            assigned_jobs.add(match['job_id'])

    if not final_matches_list:
        return pd.DataFrame()

    best_matches = pd.DataFrame(final_matches_list)
    logger.info(f"Meilleurs matchs uniques trouvés : \n{best_matches.to_string()}")
    
    # Fusionner pour obtenir les noms et les titres
    results_df = pd.merge(best_matches, jobs_df, left_on='job_id', right_on='ID', how='left')
    results_df = pd.merge(results_df, consultants_df, left_on='consultant_id', right_on='ID', how='left')

    # Renommer et sélectionner les colonnes finales
    results_df = results_df.rename(columns={
        'Titre': 'job_title',
        'Nom': 'consultant_name',
        'score_de_similarite': 'matching_score'
    })
    
    final_columns = ['job_id', 'job_title', 'consultant_id', 'consultant_name', 'matching_score']
    results_df = results_df[final_columns]
    
    logger.info(f"{len(results_df)} correspondances trouvées par meilleur score.")
    
    return results_df

def run_stable_matching(jobs_df, consultants_df, similarity_scores, logger, proposing_party='consultants'):
    """
    Exécute l'algorithme de mariage stable pour apparier les consultants et les postes.
    """
    logger.info(f"Début de l'algorithme de mariage stable, optimisé pour : {proposing_party}.")
    
    # S'assurer que les IDs sont présents et correctement formatés pour les fusions
    if 'ID' not in consultants_df.columns:
        consultants_df['ID'] = consultants_df.index.astype(str)
    consultants_df['ID'] = consultants_df['ID'].astype(str)
    
    if 'ID' not in jobs_df.columns:
        jobs_df['ID'] = jobs_df.index.astype(str)
    jobs_df['ID'] = jobs_df['ID'].astype(str)

    similarity_df = pd.DataFrame(similarity_scores)
    if similarity_df.empty:
        logger.warning("Le dataframe des scores de similarité est vide. Aucun appariement stable possible.")
        return pd.DataFrame()

    # Créer les listes de préférences
    consultant_preferences = {
        cid: similarity_df[similarity_df['consultant_id'] == cid]
        .sort_values('score_de_similarite', ascending=False)['job_id']
        .tolist()
        for cid in similarity_df['consultant_id'].unique()
    }
    job_preferences = {
        jid: similarity_df[similarity_df['job_id'] == jid]
        .sort_values('score_de_similarite', ascending=False)['consultant_id']
        .tolist()
        for jid in similarity_df['job_id'].unique()
    }

    try:
        # Instancier et résoudre le jeu de mariage stable
        # Utiliser l'algorithme HospitalResident, qui gère les groupes de tailles inégales
        from matching.games import HospitalResident

        # Déterminer qui propose
        # La partie qui propose est considérée comme "résident" dans la terminologie de la bibliothèque
        if proposing_party == 'consultants':
            resident_prefs = consultant_preferences
            hospital_prefs = job_preferences
            # Chaque poste (hôpital) a une capacité de 1
            hospital_capacities = {job: 1 for job in job_preferences}
        else:  # 'jobs' propose
            resident_prefs = job_preferences
            hospital_prefs = consultant_preferences
            # Chaque consultant (hôpital) a une capacité de 1
            hospital_capacities = {consultant: 1 for consultant in consultant_preferences}

        game = HospitalResident.create_from_dictionaries(resident_prefs, hospital_prefs, hospital_capacities)
        stable_matches_dict = game.solve()

        if not stable_matches_dict:
            logger.warning("L'algorithme de mariage stable n'a trouvé aucune correspondance.")
            return pd.DataFrame()

        # Conversion robuste des résultats en DataFrame
        matches_list = []
        # Le dictionnaire de résultats est de la forme {hopital: [residents]}
        if proposing_party == 'consultants':
            # Les hôpitaux sont les jobs
            for job, residents in stable_matches_dict.items():
                for consultant in residents:
                    matches_list.append({'job_id': str(job), 'consultant_id': str(consultant)})
        else:
            # Les hôpitaux sont les consultants
            for consultant, residents in stable_matches_dict.items():
                for job in residents:
                    matches_list.append({'consultant_id': str(consultant), 'job_id': str(job)})
        
        if not matches_list:
            return pd.DataFrame()
            
        matches_df = pd.DataFrame(matches_list)

        # Fusionner avec les scores de similarité
        results_df = pd.merge(matches_df, similarity_df, on=['consultant_id', 'job_id'], how='left')

        # Préparer les dataframes pour la fusion finale
        consultants_info = consultants_df[['ID', 'Nom']].rename(columns={'ID': 'consultant_id', 'Nom': 'consultant_name'})
        jobs_info = jobs_df[['ID', 'Titre']].rename(columns={'ID': 'job_id', 'Titre': 'job_title'})

        # Fusionner pour obtenir les noms et les titres
        results_df = pd.merge(results_df, consultants_info, on='consultant_id', how='left')
        results_df = pd.merge(results_df, jobs_info, on='job_id', how='left')
        
        # Renommer la colonne de score
        results_df = results_df.rename(columns={'score_de_similarite': 'matching_score'})

        # Sélectionner et ordonner les colonnes finales
        final_columns = ['job_id', 'job_title', 'consultant_id', 'consultant_name', 'matching_score']
        results_df = results_df[final_columns].sort_values(by='matching_score', ascending=False).reset_index(drop=True)
        
        logger.info(f"{len(results_df)} correspondances stables trouvées.")
        return results_df

    except Exception as e:
        logger.error(f"Erreur lors de la résolution du jeu de mariage stable : {e}", exc_info=True)
        return pd.DataFrame()