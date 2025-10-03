#!/usr/bin/env python3
"""
Script de correction des doublons dans argumentum_fallacies_taxonomy.csv

PROBLÈME IDENTIFIÉ :
- ValueError: Index has duplicate keys: Index([520, 1000], dtype='int64', name='PK')
- Le fichier CSV contient des clés primaires dupliquées

SOLUTION :
- Lecture du CSV
- Détection et suppression des doublons en gardant la première occurrence
- Sauvegarde du fichier corrigé

Auteur : Mission SDDD - Validation SymbolicAI Argument Analysis
Date : 2025-10-03
"""

import pandas as pd
import os
from pathlib import Path
import logging

# Configuration du logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

def fix_csv_duplicates():
    """
    Corrige les doublons dans le fichier taxonomie des sophismes
    """
    
    # Chemin vers le fichier CSV
    csv_path = Path("data/argumentum_fallacies_taxonomy.csv")
    backup_path = csv_path.with_suffix('.csv.backup')
    
    try:
        # Vérification de l'existence du fichier
        if not csv_path.exists():
            logger.error(f"❌ Fichier non trouvé : {csv_path}")
            return False
            
        logger.info(f"📂 Lecture du fichier : {csv_path}")
        
        # Lecture du CSV sans définir PK comme index pour éviter l'erreur
        df = pd.read_csv(csv_path)
        
        logger.info(f"📊 Fichier chargé : {len(df)} lignes")
        logger.info(f"📋 Colonnes : {list(df.columns)}")
        
        # Vérification si la colonne PK existe
        if 'PK' not in df.columns:
            logger.error("❌ Colonne 'PK' non trouvée dans le CSV")
            return False
            
        # Analyse des doublons
        duplicated_pks = df[df['PK'].duplicated(keep=False)]['PK'].unique()
        logger.info(f"🔍 PK dupliquées trouvées : {duplicated_pks}")
        
        # Affichage détaillé des doublons
        for pk in duplicated_pks:
            dup_rows = df[df['PK'] == pk]
            logger.info(f"  PK {pk} : {len(dup_rows)} occurrences")
            for idx, row in dup_rows.iterrows():
                logger.info(f"    Ligne {idx}: {row.to_dict()}")
        
        # Sauvegarde de sécurité
        df.to_csv(backup_path, index=False)
        logger.info(f"💾 Sauvegarde créée : {backup_path}")
        
        # Suppression des doublons (garde la première occurrence)
        df_clean = df.drop_duplicates(subset=['PK'], keep='first')
        
        removed_count = len(df) - len(df_clean)
        logger.info(f"🧹 {removed_count} doublons supprimés")
        logger.info(f"📊 Fichier nettoyé : {len(df_clean)} lignes")
        
        # Vérification finale - aucun doublon ne doit rester
        remaining_duplicates = df_clean['PK'].duplicated().sum()
        if remaining_duplicates > 0:
            logger.error(f"❌ {remaining_duplicates} doublons restants après nettoyage")
            return False
        
        # Sauvegarde du fichier corrigé
        df_clean.to_csv(csv_path, index=False)
        logger.info(f"✅ Fichier corrigé sauvegardé : {csv_path}")
        
        # Validation finale - test de lecture avec PK comme index
        try:
            df_test = pd.read_csv(csv_path, index_col='PK')
            logger.info("✅ Validation : Le fichier peut maintenant être lu avec PK comme index")
            return True
        except ValueError as e:
            logger.error(f"❌ Validation échouée : {e}")
            return False
            
    except Exception as e:
        logger.error(f"❌ Erreur lors du traitement : {e}")
        return False

def main():
    """Point d'entrée principal"""
    logger.info("🚀 Démarrage du script de correction des doublons CSV")
    logger.info("=" * 60)
    
    success = fix_csv_duplicates()
    
    logger.info("=" * 60)
    if success:
        logger.info("🎉 SUCCÈS : Correction des doublons terminée")
    else:
        logger.info("💥 ÉCHEC : Correction des doublons échouée")
    
    return success

if __name__ == "__main__":
    main()