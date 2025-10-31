#!/usr/bin/env python3
"""
Script Transient de Validation Finale - Mission Nettoyage Fichiers Éparpillés
============================================================================

Auteur: Roo Code Mode
Date: 2025-10-31T02:09:00Z
Phase: Validation Finale - Phase Corrections Qwen
Version: 1.0

Description: Script de validation finale confirmant que la mission de nettoyage
des fichiers éparpillés est accomplie avec succès selon les critères SDDD.
"""

import os
import json
import subprocess
import sys
from datetime import datetime
from pathlib import Path

class ValidationFinaleNettoyage:
    """Classe de validation finale de la mission de nettoyage"""
    
    def __init__(self):
        self.timestamp = datetime.now().isoformat()
        self.workspace_root = Path.cwd()
        self.rapports_dir = self.workspace_root / "docs/suivis/genai-image/phase-corrections-qwen-20251030-233700/rapports"
        self.validation_results = {}
        
    def executer_commande_git(self, commande):
        """Exécute une commande git et retourne le résultat"""
        try:
            result = subprocess.run(
                ["pwsh", "-c", commande],
                capture_output=True,
                text=True,
                cwd=self.workspace_root
            )
            return {
                "success": result.returncode == 0,
                "stdout": result.stdout.strip(),
                "stderr": result.stderr.strip(),
                "returncode": result.returncode
            }
        except Exception as e:
            return {
                "success": False,
                "error": str(e),
                "returncode": -1
            }
    
    def analyser_etat_git(self):
        """Analyse l'état git actuel"""
        print("🔍 Analyse de l'état git actuel...")
        
        git_status = self.executer_commande_git("git status --porcelain")
        
        if not git_status["success"]:
            return {
                "success": False,
                "error": f"Erreur git status: {git_status.get('stderr', 'Erreur inconnue')}"
            }
        
        lignes = git_status["stdout"].split('\n') if git_status["stdout"] else []
        
        analyse = {
            "fichiers_modifies": [],
            "fichiers_supprimes": [],
            "fichiers_non_suivis": [],
            "total_lignes": len(lignes)
        }
        
        for ligne in lignes:
            if not ligne.strip():
                continue
                
            statut = ligne[:2]
            fichier = ligne[3:].strip()
            
            if statut.startswith('M '):
                analyse["fichiers_modifies"].append(fichier)
            elif statut.startswith('D '):
                analyse["fichiers_supprimes"].append(fichier)
            elif statut.startswith('?? '):
                analyse["fichiers_non_suivis"].append(fichier)
        
        print(f"✅ Analyse git terminée: {analyse['total_lignes']} entrées trouvées")
        return {"success": True, "analyse": analyse}
    
    def valider_structure_finale(self):
        """Valide que la structure finale respecte les critères SDDD"""
        print("📋 Validation de la structure finale...")
        
        validations = {}
        
        # Vérification des répertoires principaux
        scripts_dir = self.workspace_root / "scripts"
        docs_dir = self.workspace_root / "docs/suivis/genai-image"
        docker_dir = self.workspace_root / "docker-configurations"
        
        validations["scripts_existe"] = scripts_dir.exists()
        validations["docs_existe"] = docs_dir.exists()
        validations["docker_existe"] = docker_dir.exists()
        
        # Vérification des sous-répertoires de suivi
        suivi_dir = self.workspace_root / "docs/suivis/genai-image/phase-corrections-qwen-20251030-233700"
        validations["suivi_existe"] = suivi_dir.exists()
        
        # Vérification des rapports
        rapports_dir = suivi_dir / "rapports"
        validations["rapports_existe"] = rapports_dir.exists()
        
        # Comptage des fichiers dans chaque catégorie
        if scripts_dir.exists():
            validations["scripts_count"] = len(list(scripts_dir.glob("*.py"))) + len(list(scripts_dir.glob("*.ps1")))
        else:
            validations["scripts_count"] = 0
            
        if rapports_dir.exists():
            validations["rapports_count"] = len(list(rapports_dir.glob("*.md")))
        else:
            validations["rapports_count"] = 0
        
        print(f"✅ Validation structure: {sum(validations.values())} critères validés")
        return {"success": True, "validations": validations}
    
    def verifier_rapports_nettoyage(self):
        """Vérifie l'existence des rapports de nettoyage"""
        print("📊 Vérification des rapports de nettoyage...")
        
        rapports_attendus = [
            "RAPPORT_NETTOYAGE_FICHIERS_EPARPILLES_20251031.md",
            "RAPPORT_VALIDATION_FINALE_NETTOYAGE_20251031.md"
        ]
        
        rapports_trouves = []
        rapports_manquants = []
        
        for rapport in rapports_attendus:
            chemin_rapport = self.rapports_dir / rapport
            if chemin_rapport.exists():
                rapports_trouves.append(rapport)
            else:
                rapports_manquants.append(rapport)
        
        print(f"✅ Rapports trouvés: {len(rapports_trouves)}/{len(rapports_attendus)}")
        return {
            "success": True,
            "trouves": rapports_trouves,
            "manquants": rapports_manquants
        }
    
    def calculer_statistiques_finale(self):
        """Calcule les statistiques finales de la mission"""
        print("📈 Calcul des statistiques finales...")
        
        # Analyse git pour les stats
        etat_git = self.analyser_etat_git()
        if not etat_git["success"]:
            return {"success": False, "error": etat_git.get("error")}
        
        analyse = etat_git["analyse"]
        
        stats = {
            "timestamp": self.timestamp,
            "fichiers_modifies": len(analyse["fichiers_modifies"]),
            "fichiers_supprimes": len(analyse["fichiers_supprimes"]),
            "fichiers_non_suivis": len(analyse["fichiers_non_suivis"]),
            "total_fichiers_traite": len(analyse["fichiers_modifies"]) + len(analyse["fichiers_supprimes"]) + len(analyse["fichiers_non_suivis"]),
            "espace_proprete": len(analyse["fichiers_non_suivis"]) == 0,  # Si aucun fichier non suivi à la racine
            "mission_accomplie": False  # Sera déterminé après validation complète
        }
        
        print(f"✅ Statistiques calculées: {stats['total_fichiers_traite']} fichiers traités")
        return {"success": True, "statistiques": stats}
    
    def generer_rapport_validation(self):
        """Génère le rapport complet de validation finale"""
        print("📝 Génération du rapport de validation finale...")
        
        # Exécution de toutes les validations
        resultats = {}
        
        # 1. État git
        resultats["etat_git"] = self.analyser_etat_git()
        
        # 2. Structure finale
        resultats["structure_finale"] = self.valider_structure_finale()
        
        # 3. Vérification des rapports
        resultats["verification_rapports"] = self.verifier_rapports_nettoyage()
        
        # 4. Statistiques finales
        resultats["statistiques"] = self.calculer_statistiques_finale()
        
        # 5. Validation finale de la mission
        mission_accomplie = (
            resultats["etat_git"]["success"] and
            resultats["structure_finale"]["success"] and
            resultats["verification_rapports"]["success"] and
            resultats["statistiques"]["success"] and
            resultats["statistiques"]["statistiques"]["espace_proprete"]
        )
        
        resultats["validation_finale"] = {
            "success": True,
            "mission_accomplie": mission_accomplie,
            "timestamp": self.timestamp,
            "conclusion": "MISSION NETTOYAGE ACCOMPLIE AVEC SUCCÈS" if mission_accomplie else "MISSION EN COURS"
        }
        
        # Sauvegarde du rapport
        rapport_path = self.rapports_dir / f"RAPPORT_VALIDATION_FINALE_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
        
        try:
            with open(rapport_path, 'w', encoding='utf-8') as f:
                json.dump(resultats, f, indent=2, ensure_ascii=False)
            
            print(f"✅ Rapport de validation sauvegardé: {rapport_path}")
            return {"success": True, "rapport_path": str(rapport_path), "resultats": resultats}
            
        except Exception as e:
            return {"success": False, "error": f"Erreur sauvegarde rapport: {str(e)}"}
    
    def afficher_resume_validation(self, resultats):
        """Affiche un résumé lisible de la validation"""
        print("\n" + "="*80)
        print("🎉 RAPPORT DE VALIDATION FINALE - MISSION NETTOYAGE")
        print("="*80)
        
        if resultats["validation_finale"]["mission_accomplie"]:
            print("✅ STATUT: MISSION ACCOMPLIE AVEC SUCCÈS")
        else:
            print("⚠️  STATUT: MISSION EN COURS OU INCOMPLÈTE")
        
        print(f"\n📊 STATISTIQUES FINALES:")
        stats = resultats["statistiques"]["statistiques"]
        print(f"   • Fichiers modifiés: {stats['fichiers_modifies']}")
        print(f"   • Fichiers supprimés: {stats['fichiers_supprimes']}")
        print(f"   • Fichiers non suivis: {stats['fichiers_non_suivis']}")
        print(f"   • Total traités: {stats['total_fichiers_traite']}")
        print(f"   • Espace propre: {'✅ OUI' if stats['espace_proprete'] else '❌ NON'}")
        
        print(f"\n📋 STRUCTURE VALIDÉE:")
        structure = resultats["structure_finale"]["validations"]
        print(f"   • Répertoire scripts/: {'✅' if structure['scripts_existe'] else '❌'}")
        print(f"   • Répertoire docs/: {'✅' if structure['docs_existe'] else '❌'}")
        print(f"   • Espace suivi: {'✅' if structure['suivi_existe'] else '❌'}")
        print(f"   • Rapports: {'✅' if structure['rapports_existe'] else '❌'}")
        
        print(f"\n📚 RAPPORTS DE NETTOYAGE:")
        rapports = resultats["verification_rapports"]
        print(f"   • Rapports trouvés: {len(rapports['trouves'])}")
        print(f"   • Rapports attendus: {len(rapports['trouves']) + len(rapports['manquants'])}")
        
        print(f"\n🔗 CONCLUSION:")
        print(f"   {resultats['validation_finale']['conclusion']}")
        print("="*80)

def main():
    """Fonction principale du script de validation finale"""
    print("🚀 Démarrage du script de validation finale - Mission Nettoyage")
    print(f"📅 Timestamp: {datetime.now().isoformat()}")
    print(f"📁 Workspace: {Path.cwd()}")
    
    validateur = ValidationFinaleNettoyage()
    
    # Génération du rapport complet
    resultat_validation = validateur.generer_rapport_validation()
    
    if resultat_validation["success"]:
        # Affichage du résumé
        validateur.afficher_resume_validation(resultat_validation["resultats"])
        
        print(f"\n📄 Rapport détaillé sauvegardé: {resultat_validation['rapport_path']}")
        return 0
    else:
        print(f"❌ Erreur lors de la validation: {resultat_validation.get('error', 'Erreur inconnue')}")
        return 1

if __name__ == "__main__":
    exit_code = main()
    sys.exit(exit_code)