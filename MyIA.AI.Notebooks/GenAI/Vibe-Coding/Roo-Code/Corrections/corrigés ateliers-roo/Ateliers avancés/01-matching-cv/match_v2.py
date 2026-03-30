import asyncio
import os
import pandas as pd
from dotenv import load_dotenv

import semantic_kernel as sk
from semantic_kernel.connectors.ai.open_ai import OpenAITextEmbedding
from semantic_kernel.memory.semantic_text_memory import SemanticTextMemory
from semantic_kernel.memory.volatile_memory_store import VolatileMemoryStore

# 1. Initialisation
async def main():
    """
    Fonction principale pour exécuter le matching sémantique.
    """
    print("Initialisation du script...")
    load_dotenv()
    api_key = os.getenv("OPENAI_API_KEY")
    if not api_key:
        raise ValueError("La clé API OpenAI n'a pas été trouvée. Vérifiez votre fichier .env.")

    # 2. Chargement et préparation des données
    print("Chargement et préparation des données...")
    
    # Utilisation de os.path.join pour des chemins de fichiers robustes
    base_dir = "exercice-1-v2"
    data_dir = os.path.join(base_dir, "data")
    consultants_path = os.path.join(data_dir, "Base consultants.csv")
    jobs_path = os.path.join(data_dir, "Fiches de poste client.csv")

    try:
        consultants_df = pd.read_csv(consultants_path)
        jobs_df = pd.read_csv(jobs_path)
        print(f"{len(consultants_df)} profils de consultants chargés.")
        print(f"{len(jobs_df)} offres d'emploi chargées.")
    except FileNotFoundError as e:
        print(f"Erreur: Fichier de données non trouvé - {e}")
        return

    consultants_df.fillna('', inplace=True)
    jobs_df.fillna('', inplace=True)

    # 3. Mise en place du moteur sémantique
    print("Configuration du moteur sémantique...")
    kernel = sk.Kernel()
    try:
        embedding_service = OpenAITextEmbedding(
            ai_model_id="text-embedding-3-small",
            api_key=api_key
        )
        kernel.add_service(embedding_service)
    except sk.KernelException as e:
        print(f"Erreur lors de l'initialisation du service Semantic Kernel : {e}")
        return
    
    memory_store = VolatileMemoryStore()
    memory = SemanticTextMemory(storage=memory_store, embeddings_generator=embedding_service)
    collection_name = "consultants"

    # 4. Indexation optimisée des consultants (en batch)
    print("Indexation des profils de consultants...")
    try:
        # Préparation des données pour l'indexation en batch
        consultant_records = []
        for index, row in consultants_df.iterrows():
            description = (
                f"Titre: {row['Poste']}. "
                f"Expérience: {row['Expériences clés']}. "
                f"Compétences: {row['Compétences']}."
            )
            record_id = str(row.get('ID', index))
            consultant_records.append({
                "id": record_id,
                "text": description,
                "description": f"Profil du consultant: {row['Poste']}"
            })

        # Appel unique pour sauvegarder toutes les informations
        await memory.save_informations(
            collection=collection_name,
            records=consultant_records
        )
        print(f"{len(consultants_df)} consultants indexés avec succès.")

    except sk.KernelException as e:
        print(f"Une erreur est survenue lors de l'indexation des consultants : {e}")
        return

    # 5. Processus de Matching
    print("Lancement du processus de matching...")
    results = []
    try:
        for index, job in jobs_df.iterrows():
            job_description = (
                f"Titre du poste: {job['Titre']}. "
                f"Description: {job['Description brute']}. "
                f"Compétences requises: {job['Compétences clés']}"
            )
            
            search_results = await memory.search(
                collection=collection_name,
                query=job_description,
                limit=5,
                min_relevance_score=0.7
            )
            
            job_id = job.get('ID', index)
            for consultant_match in search_results:
                results.append({
                    "job_id": job_id,
                    "consultant_id": consultant_match.id,
                    "score_de_similarite": round(consultant_match.relevance, 4)
                })
    except sk.KernelException as e:
        print(f"Une erreur est survenue lors de la recherche de similarité : {e}")
        return

    print(f"{len(results)} correspondances trouvées.")
    
    # 6. Génération des Résultats
    if results:
        results_df = pd.DataFrame(results)
        output_path = os.path.join(base_dir, "results_v2.csv")
        results_df.to_csv(output_path, index=False)
        print(f"Les résultats ont été sauvegardés dans : {output_path}")
    else:
        print("Aucune correspondance pertinente n'a été trouvée avec les paramètres actuels.")

if __name__ == "__main__":
    asyncio.run(main())