#!/usr/bin/env python3
"""
Validation finale de la documentation de la mission ComfyUI-Login
Vérifie la complétude, la cohérence et les liens croisés de toute la documentation
"""

import os
import re
import json
from pathlib import Path
from typing import Dict, List, Tuple, Optional
from datetime import datetime

class DocumentationValidator:
    """Validateur complet de la documentation de mission"""
    
    def __init__(self):
        self.base_dir = Path(__file__).parent.parent.parent
        self.docs_dir = self.base_dir / "docs" / "suivis" / "genai-image"
        self.scripts_dir = self.base_dir / "scripts" / "genai-auth"
        
        # Documents attendus
        self.expected_docs = {
            "RAPPORT-FINAL-MISSION-COMFYUI-LOGIN-20251125.md": {
                "title": "Rapport Final de Mission",
                "min_lines": 300,
                "required_sections": ["## Contexte", "## Problèmes Identifiés", "## Solution Finale"]
            },
            "ARCHITECTURE-FINALE-COMFYUI-QWEN-20251125.md": {
                "title": "Architecture Finale",
                "min_lines": 400,
                "required_sections": ["## Vue d'Ensemble", "## Scripts Consolidés", "## Docker Configurations"]
            },
            "GUIDE-UTILISATION-COMFYUI-QWEN-20251125.md": {
                "title": "Guide d'Utilisation",
                "min_lines": 500,
                "required_sections": ["## Installation", "## Configuration", "## Utilisation"]
            },
            "README-ECOSYSTEME-COMFYUI-QWEN-20251125.md": {
                "title": "Index de l'Écosystème",
                "min_lines": 250,
                "required_sections": ["## Documentation", "## Scripts", "## Configuration"]
            },
            "RESUME-EXECUTIF-MISSION-COMFYUI-LOGIN-20251125.md": {
                "title": "Résumé Exécutif",
                "min_lines": 200,
                "required_sections": ["## Objectifs et Résultats", "## Réalisations Principales"]
            },
            "RAPPORT-RESOLUTION-UNIFICATION-TOKENS-COMFYUI-20251125.md": {
                "title": "Résolution Tokens",
                "min_lines": 150,
                "required_sections": ["## Problème", "## Analyse", "## Solution"]
            }
        }
        
        self.validation_results = {
            "documents": {},
            "liens": {},
            "coherence": {},
            "completude": {},
            "erreurs": [],
            "avertissements": []
        }
    
    def validate_document_existence(self) -> Dict[str, bool]:
        """Vérifie que tous les documents attendus existent"""
        existence = {}
        for doc_name, doc_info in self.expected_docs.items():
            doc_path = self.docs_dir / doc_name
            exists = doc_path.exists()
            existence[doc_name] = exists
            
            if not exists:
                self.validation_results["erreurs"].append(
                    f"Document manquant: {doc_name}"
                )
            else:
                self.validation_results["documents"][doc_name] = {
                    "path": str(doc_path),
                    "title": doc_info["title"],
                    "exists": True
                }
        
        return existence
    
    def validate_document_content(self, doc_name: str, doc_path: Path) -> Dict:
        """Valide le contenu d'un document spécifique"""
        doc_info = self.expected_docs[doc_name]
        
        try:
            with open(doc_path, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            self.validation_results["erreurs"].append(
                f"Erreur lecture {doc_name}: {str(e)}"
            )
            return {"valid": False, "error": str(e)}
        
        # Vérifier le nombre de lignes
        lines = content.split('\n')
        line_count = len(lines)
        
        # Vérifier les sections requises
        missing_sections = []
        for section in doc_info["required_sections"]:
            if section not in content:
                missing_sections.append(section)
        
        # Vérifier la présence de code blocks
        code_blocks = len(re.findall(r'```', content))
        code_blocks_count = code_blocks // 2
        
        # Vérifier la présence de liens
        links = len(re.findall(r'\[.*?\]\(.*?\)', content))
        
        # Vérifier la présence de tableaux
        tables = len(re.findall(r'\|.*\|', content))
        
        # Vérifier les images/diagrammes
        images = len(re.findall(r'!\[.*?\]\(.*?\)', content))
        
        validation = {
            "valid": True,
            "line_count": line_count,
            "min_lines_required": doc_info["min_lines"],
            "line_count_ok": line_count >= doc_info["min_lines"],
            "missing_sections": missing_sections,
            "sections_ok": len(missing_sections) == 0,
            "code_blocks": code_blocks_count,
            "links": links,
            "tables": tables,
            "images": images
        }
        
        if not validation["line_count_ok"]:
            self.validation_results["avertissements"].append(
                f"{doc_name}: {line_count} lignes (minimum: {doc_info['min_lines']})"
            )
        
        if not validation["sections_ok"]:
            self.validation_results["avertissements"].append(
                f"{doc_name}: sections manquantes - {', '.join(missing_sections)}"
            )
        
        validation["valid"] = validation["line_count_ok"] and validation["sections_ok"]
        
        return validation
    
    def validate_cross_references(self) -> Dict:
        """Valide les références croisées entre documents"""
        cross_refs = {}
        
        # Lire tous les documents pour extraire les liens
        all_docs_content = {}
        for doc_name in self.expected_docs.keys():
            doc_path = self.docs_dir / doc_name
            if doc_path.exists():
                try:
                    with open(doc_path, 'r', encoding='utf-8') as f:
                        all_docs_content[doc_name] = f.read()
                except Exception:
                    all_docs_content[doc_name] = ""
        
        # Vérifier les références entre documents
        for doc_name, content in all_docs_content.items():
            refs_to_other_docs = []
            for other_doc in self.expected_docs.keys():
                if other_doc != doc_name and other_doc in content:
                    refs_to_other_docs.append(other_doc)
            
            cross_refs[doc_name] = {
                "references": refs_to_other_docs,
                "ref_count": len(refs_to_other_docs)
            }
        
        # Vérifier que l'index référence tous les autres documents
        index_doc = "README-ECOSYSTEME-COMFYUI-QWEN-20251125.md"
        if index_doc in all_docs_content:
            index_content = all_docs_content[index_doc]
            missing_refs = []
            for doc_name in self.expected_docs.keys():
                if doc_name != index_doc and doc_name not in index_content:
                    missing_refs.append(doc_name)
            
            if missing_refs:
                self.validation_results["avertissements"].append(
                    f"Index ne référence pas: {', '.join(missing_refs)}"
                )
        
        self.validation_results["liens"] = cross_refs
        return cross_refs
    
    def validate_scripts_documentation(self) -> Dict:
        """Valide que les scripts sont bien documentés"""
        scripts_validation = {}
        
        # Vérifier le README principal des scripts
        scripts_readme = self.scripts_dir / "README.md"
        if scripts_readme.exists():
            try:
                with open(scripts_readme, 'r', encoding='utf-8') as f:
                    readme_content = f.read()
                
                # Vérifier les sections principales
                required_sections = [
                    "## Scripts Principaux",
                    "## Utilitaires",
                    "## Scripts de Test"
                ]
                
                missing_sections = []
                for section in required_sections:
                    if section not in readme_content:
                        missing_sections.append(section)
                
                scripts_validation["readme"] = {
                    "exists": True,
                    "sections_ok": len(missing_sections) == 0,
                    "missing_sections": missing_sections
                }
                
            except Exception as e:
                scripts_validation["readme"] = {
                    "exists": True,
                    "error": str(e)
                }
        else:
            scripts_validation["readme"] = {"exists": False}
            self.validation_results["erreurs"].append("README.md des scripts manquant")
        
        # Vérifier la documentation des scripts principaux
        core_scripts = [
            "setup_complete_qwen.py",
            "validate_genai_ecosystem.py",
            "diagnose_comfyui_auth.py"
        ]
        
        for script in core_scripts:
            script_path = self.scripts_dir / "core" / script
            if script_path.exists():
                try:
                    with open(script_path, 'r', encoding='utf-8') as f:
                        script_content = f.read()
                    
                    # Vérifier la présence de docstring principale
                    has_docstring = '"""' in script_content and script_content.count('"""') >= 2
                    
                    scripts_validation[f"core_{script}"] = {
                        "exists": True,
                        "has_docstring": has_docstring
                    }
                    
                    if not has_docstring:
                        self.validation_results["avertissements"].append(
                            f"Script core/{script} sans docstring principale"
                        )
                        
                except Exception as e:
                    scripts_validation[f"core_{script}"] = {
                        "exists": True,
                        "error": str(e)
                    }
            else:
                scripts_validation[f"core_{script}"] = {"exists": False}
        
        self.validation_results["scripts"] = scripts_validation
        return scripts_validation
    
    def validate_docker_configuration(self) -> Dict:
        """Valide la documentation Docker"""
        docker_validation = {}
        
        docker_dir = self.base_dir / "docker-configurations" / "comfyui-qwen"
        
        # Vérifier docker-compose.yml
        compose_file = docker_dir / "docker-compose.yml"
        if compose_file.exists():
            try:
                with open(compose_file, 'r', encoding='utf-8') as f:
                    compose_content = f.read()
                
                docker_validation["compose"] = {
                    "exists": True,
                    "has_services": "services:" in compose_content,
                    "has_volumes": "volumes:" in compose_content,
                    "has_environment": "environment:" in compose_content
                }
                
            except Exception as e:
                docker_validation["compose"] = {
                    "exists": True,
                    "error": str(e)
                }
        else:
            docker_validation["compose"] = {"exists": False}
            self.validation_results["erreurs"].append("docker-compose.yml manquant")
        
        # Vérifier .env
        env_file = docker_dir / ".env"
        if env_file.exists():
            try:
                with open(env_file, 'r', encoding='utf-8') as f:
                    env_content = f.read()
                
                # Compter les variables d'environnement
                env_vars = len(re.findall(r'^[A-Z_]+=', env_content, re.MULTILINE))
                
                docker_validation["env"] = {
                    "exists": True,
                    "env_vars_count": env_vars,
                    "has_auth_vars": "COMFYUI_AUTH_TOKEN" in env_content
                }
                
            except Exception as e:
                docker_validation["env"] = {
                    "exists": True,
                    "error": str(e)
                }
        else:
            docker_validation["env"] = {"exists": False}
            self.validation_results["erreurs"].append(".env manquant")
        
        self.validation_results["docker"] = docker_validation
        return docker_validation
    
    def calculate_completeness_score(self) -> float:
        """Calcule un score de complétude global"""
        total_checks = 0
        passed_checks = 0
        
        # Documents existants
        total_checks += len(self.expected_docs)
        passed_checks += sum(1 for doc in self.validation_results["documents"].values() 
                          if doc.get("exists", False))
        
        # Contenu des documents
        for doc_name, validation in self.validation_results.get("documents_content", {}).items():
            total_checks += 1
            if validation.get("valid", False):
                passed_checks += 1
        
        # Références croisées
        if self.validation_results.get("liens"):
            total_checks += 1
            # Vérifier que l'index référence les autres documents
            index_refs = self.validation_results["liens"].get(
                "README-ECOSYSTEME-COMFYUI-QWEN-20251125.md", {}
            ).get("ref_count", 0)
            if index_refs >= 4:  # Au moins 4 autres documents
                passed_checks += 1
        
        # Scripts
        if self.validation_results.get("scripts", {}).get("readme", {}).get("exists"):
            total_checks += 1
            if self.validation_results["scripts"]["readme"].get("sections_ok", False):
                passed_checks += 1
        
        # Docker
        if self.validation_results.get("docker", {}).get("compose", {}).get("exists"):
            total_checks += 1
            compose_ok = all([
                self.validation_results["docker"]["compose"].get("has_services", False),
                self.validation_results["docker"]["compose"].get("has_volumes", False)
            ])
            if compose_ok:
                passed_checks += 1
        
        return (passed_checks / total_checks * 100) if total_checks > 0 else 0
    
    def generate_validation_report(self) -> str:
        """Génère le rapport de validation"""
        score = self.calculate_completeness_score()
        
        report = f"""# Rapport de Validation - Documentation ComfyUI-Login

**Date de validation** : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
**Score de complétude** : {score:.1f}%
**Statut** : {"✅ VALIDÉ" if score >= 90 else "⚠️ COMPLÉTION REQUISE" if score >= 70 else "❌ VALIDATION ÉCHOUÉE"}

---

## 📋 Résultats de Validation

### Documents Principaux
"""
        
        for doc_name, doc_info in self.expected_docs.items():
            doc_path = self.docs_dir / doc_name
            status = "✅" if doc_path.exists() else "❌"
            report += f"{status} **{doc_info['title']}**\n"
            
            if doc_path.exists() and doc_name in self.validation_results.get("documents_content", {}):
                content_val = self.validation_results["documents_content"][doc_name]
                lines = content_val.get("line_count", 0)
                sections_ok = "✅" if content_val.get("sections_ok", False) else "❌"
                report += f"   - Lignes : {lines} (min: {content_val.get('min_lines_required', 'N/A')})\n"
                report += f"   - Sections : {sections_ok}\n"
            report += "\n"
        
        report += f"""### Références Croisées
"""
        
        if self.validation_results.get("liens"):
            for doc_name, refs in self.validation_results["liens"].items():
                doc_title = self.expected_docs.get(doc_name, {}).get("title", doc_name)
                ref_count = refs.get("ref_count", 0)
                report += f"- **{doc_title}** : {ref_count} référence(s) croisée(s)\n"
        
        report += f"""
### Documentation Scripts
"""
        
        if self.validation_results.get("scripts", {}).get("readme"):
            scripts_readme = self.validation_results["scripts"]["readme"]
            status = "✅" if scripts_readme.get("exists", False) else "❌"
            report += f"{status} README.md scripts principaux\n"
            
            if scripts_readme.get("sections_ok", False):
                report += "   - Sections complètes ✅\n"
        
        report += f"""
### Configuration Docker
"""
        
        if self.validation_results.get("docker"):
            docker_val = self.validation_results["docker"]
            
            if docker_val.get("compose", {}).get("exists"):
                compose = docker_val["compose"]
                report += "✅ docker-compose.yml\n"
                report += f"   - Services : {'✅' if compose.get('has_services') else '❌'}\n"
                report += f"   - Volumes : {'✅' if compose.get('has_volumes') else '❌'}\n"
            
            if docker_val.get("env", {}).get("exists"):
                env = docker_val["env"]
                report += "✅ .env\n"
                report += f"   - Variables : {env.get('env_vars_count', 0)}\n"
                report += f"   - Auth : {'✅' if env.get('has_auth_vars') else '❌'}\n"
        
        report += f"""
---

## ⚠️ Avertissements
"""
        
        if self.validation_results["avertissements"]:
            for warning in self.validation_results["avertissements"]:
                report += f"- {warning}\n"
        else:
            report += "Aucun avertissement\n"
        
        report += f"""
## ❌ Erreurs
"""
        
        if self.validation_results["erreurs"]:
            for error in self.validation_results["erreurs"]:
                report += f"- {error}\n"
        else:
            report += "Aucune erreur\n"
        
        report += f"""
---

## 📊 Statistiques Détaillées

### Métriques de Documentation
- **Documents attendus** : {len(self.expected_docs)}
- **Documents créés** : {len(self.validation_results.get("documents", {}))}
- **Lignes totales** : {sum(val.get("line_count", 0) for val in self.validation_results.get("documents_content", {}).values())}
- **Sections couvertes** : {sum(1 for val in self.validation_results.get("documents_content", {}).values() if val.get("sections_ok", False))}

### Qualité Technique
- **Code blocks** : {sum(val.get("code_blocks", 0) for val in self.validation_results.get("documents_content", {}).values())}
- **Liens hypertextes** : {sum(val.get("links", 0) for val in self.validation_results.get("documents_content", {}).values())}
- **Tableaux** : {sum(val.get("tables", 0) for val in self.validation_results.get("documents_content", {}).values())}
- **Images/Diagrammes** : {sum(val.get("images", 0) for val in self.validation_results.get("documents_content", {}).values())}

---

## 🎯 Recommandations

"""
        
        if score >= 90:
            report += """✅ **Documentation EXCELLENTE**

La documentation est complète, cohérente et prête pour la production.

Actions recommandées :
1. Créer le tag Git de version stable
2. Communiquer la documentation à l'équipe
3. Mettre en place les processus de maintenance
"""
        elif score >= 70:
            report += """⚠️ **Documentation BONNE - Améliorations mineures requises**

La documentation est globalement complète mais nécessite quelques ajustements.

Actions recommandées :
1. Corriger les avertissements identifiés
2. Compléter les sections manquantes
3. Valider à nouveau avant release
"""
        else:
            report += """❌ **DOCUMENTATION INCOMPLÈTE**

La documentation nécessite un travail important avant d'être utilisable.

Actions requises :
1. Corriger toutes les erreurs identifiées
2. Compléter les documents manquants
3. Revalider complètement
"""
        
        report += f"""
---

**Rapport généré par** : DocumentationValidator  
**Date de génération** : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}  
**Version** : 1.0  
**Score final** : {score:.1f}%
"""
        
        return report
    
    def run_validation(self) -> bool:
        """Exécute la validation complète"""
        print("🔍 Validation de la documentation ComfyUI-Login")
        print("=" * 50)
        
        # 1. Vérifier l'existence des documents
        print("📋 Vérification des documents...")
        existence = self.validate_document_existence()
        
        # 2. Valider le contenu des documents
        print("📝 Validation du contenu...")
        self.validation_results["documents_content"] = {}
        for doc_name in self.expected_docs.keys():
            doc_path = self.docs_dir / doc_name
            if doc_path.exists():
                content_val = self.validate_document_content(doc_name, doc_path)
                self.validation_results["documents_content"][doc_name] = content_val
        
        # 3. Valider les références croisées
        print("🔗 Validation des références croisées...")
        self.validate_cross_references()
        
        # 4. Valider la documentation des scripts
        print("🐍 Validation documentation scripts...")
        self.validate_scripts_documentation()
        
        # 5. Valider la configuration Docker
        print("🐳 Validation configuration Docker...")
        self.validate_docker_configuration()
        
        # 6. Calculer le score et générer le rapport
        print("📊 Génération du rapport...")
        score = self.calculate_completeness_score()
        
        print(f"\n📈 Score de complétude : {score:.1f}%")
        
        if score >= 90:
            print("✅ Documentation VALIDÉE et complète")
            success = True
        elif score >= 70:
            print("⚠️ Documentation BONNE - Améliorations mineures requises")
            success = True
        else:
            print("❌ Documentation INCOMPLÈTE")
            success = False
        
        # Générer le rapport
        report = self.generate_validation_report()
        
        # Sauvegarder le rapport
        report_path = self.docs_dir / "RAPPORT-VALIDATION-DOCUMENTATION-20251125.md"
        with open(report_path, 'w', encoding='utf-8') as f:
            f.write(report)
        
        print(f"\n📝 Rapport sauvegardé : {report_path}")
        
        # Afficher le résumé
        print("\n📋 Résumé de la validation :")
        print(f"- Documents : {len([v for v in existence.values() if v])}/{len(existence)}")
        print(f"- Erreurs : {len(self.validation_results['erreurs'])}")
        print(f"- Avertissements : {len(self.validation_results['avertissements'])}")
        
        if self.validation_results["erreurs"]:
            print("\n❌ Erreurs à corriger :")
            for error in self.validation_results["erreurs"]:
                print(f"  - {error}")
        
        if self.validation_results["avertissements"]:
            print("\n⚠️ Avertissements :")
            for warning in self.validation_results["avertissements"]:
                print(f"  - {warning}")
        
        return success

def main():
    """Point d'entrée principal"""
    validator = DocumentationValidator()
    success = validator.run_validation()
    
    if success:
        print("\n🎉 Validation terminée avec succès !")
        print("La documentation est prête pour la production.")
    else:
        print("\n❌ Validation échouée")
        print("Veuillez corriger les problèmes identifiés avant de continuer.")
    
    return 0 if success else 1

if __name__ == "__main__":
    exit(main())