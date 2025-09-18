#!/usr/bin/env python3
"""
Papermill-CoursIA CLI - Interface Ligne de Commande Éducative
===========================================================

Entry point principal pour exécution notebooks avec monitoring éducatif.
Compatibilité avec workflows CoursIA existants.
"""

import argparse
import asyncio
import json
import logging
import sys
from pathlib import Path
from typing import Dict, Any, List

# Import des modules core
sys.path.append(str(Path(__file__).parent.parent))

from core.executor import (
    PapermillExecutor, 
    create_educational_executor, 
    create_production_executor,
    NotebookSpec
)


def setup_logging(verbose: bool = False, quiet: bool = False) -> None:
    """Configuration logging adapté CLI éducatif"""
    if quiet:
        level = logging.ERROR
        format_str = '❌ %(message)s'
    elif verbose:
        level = logging.DEBUG
        format_str = '[%(asctime)s] %(levelname)-8s | %(name)s | %(message)s'
    else:
        level = logging.INFO
        format_str = '%(message)s'
    
    logging.basicConfig(
        level=level,
        format=format_str,
        datefmt='%H:%M:%S'
    )
    
    # Suppression logs externes en mode normal
    if not verbose:
        logging.getLogger("papermill").setLevel(logging.WARNING)
        logging.getLogger("nbformat").setLevel(logging.WARNING)


def parse_parameters(param_strings: List[str]) -> Dict[str, Any]:
    """Parse paramètres CLI au format -p key value ou -p key=value"""
    parameters = {}
    
    i = 0
    while i < len(param_strings):
        if i + 1 < len(param_strings) and '=' not in param_strings[i]:
            # Format: -p key value
            key = param_strings[i]
            value_str = param_strings[i + 1]
            i += 2
        else:
            # Format: -p key=value
            key, value_str = param_strings[i].split('=', 1)
            i += 1
        
        # Conversion automatique types pour contexte éducatif
        try:
            # Tentative conversion numérique
            if '.' in value_str:
                value = float(value_str)
            else:
                value = int(value_str)
        except ValueError:
            # Tentative boolean
            if value_str.lower() in ('true', 'false'):
                value = value_str.lower() == 'true'
            else:
                # String par défaut
                value = value_str
        
        parameters[key] = value
    
    return parameters


async def execute_single_notebook(args) -> int:
    """Exécution notebook unique avec reporting éducatif"""
    
    # Configuration executor selon profil
    if args.production_mode:
        executor = create_production_executor(
            conda_env=args.conda_env,
            timeout_default=args.timeout,
            max_workers=args.max_workers
        )
    else:
        executor = create_educational_executor(
            conda_env=args.conda_env,
            timeout_default=args.timeout,
            max_workers=args.max_workers
        )
    
    try:
        # Parse paramètres si fournis
        parameters = {}
        if args.parameters:
            parameters = parse_parameters(args.parameters)
            if not args.quiet:
                param_str = ', '.join([f"{k}={v}" for k, v in parameters.items()])
                print(f"🔧 Paramètres: {param_str}")
        
        # Exécution avec monitoring
        if not args.quiet:
            notebook_name = Path(args.input_notebook).name
            print(f"🚀 Démarrage exécution: {notebook_name}")
            if args.kernel:
                print(f"📋 Kernel spécifié: {args.kernel}")
        
        result = await executor.execute_notebook(
            input_path=args.input_notebook,
            output_path=args.output_notebook,
            parameters=parameters,
            kernel=args.kernel,
            timeout=args.timeout
        )
        
        # Reporting résultats
        if result.success:
            if not args.quiet:
                print(f"✅ Succès! Notebook exécuté en {result.metrics.execution_time_seconds:.2f}s")
                print(f"📊 Performance: {result.metrics.cells_per_second:.2f} cell/s")
                print(f"📁 Sortie: {result.output_path}")
                
                # Rapport éducatif si disponible
                if result.educational_report:
                    report = result.educational_report
                    print(f"🎓 Grade: {report.get('performance_grade', 'N/A')}")
                    
                    if 'learning_insights' in report:
                        print("💡 Insights:")
                        for insight in report['learning_insights']:
                            print(f"   {insight}")
            
            # Export métriques JSON si demandé
            if args.export_metrics:
                metrics_path = args.export_metrics
                with open(metrics_path, 'w', encoding='utf-8') as f:
                    json.dump(result.to_dict(), f, indent=2, ensure_ascii=False)
                if not args.quiet:
                    print(f"📊 Métriques exportées: {metrics_path}")
            
            return 0
            
        else:
            # Gestion échecs avec contexte éducatif
            print(f"❌ Échec d'exécution")
            print(f"📁 Notebook source: {result.input_path}")
            
            if result.errors:
                print("🔍 Détails des erreurs:")
                for error in result.errors:
                    print(f"   • {error}")
            
            # Rapport éducatif même en cas d'échec
            if result.educational_report and 'recommendations' in result.educational_report:
                print("💡 Recommandations:")
                for rec in result.educational_report['recommendations']:
                    print(f"   {rec}")
            
            return 1
            
    except Exception as e:
        logging.error(f"Erreur critique: {e}")
        return 2
        
    finally:
        executor.close()


async def execute_batch_notebooks(args) -> int:
    """Exécution batch pour TP/cours multiples"""
    
    # Lecture configuration batch
    if not Path(args.batch_config).exists():
        logging.error(f"Fichier batch introuvable: {args.batch_config}")
        return 1
    
    try:
        with open(args.batch_config, 'r', encoding='utf-8') as f:
            batch_config = json.load(f)
    except Exception as e:
        logging.error(f"Erreur lecture configuration batch: {e}")
        return 1
    
    # Construction spécifications notebooks
    notebook_specs = []
    for spec_data in batch_config.get('notebooks', []):
        spec = NotebookSpec(
            input_path=spec_data['input_path'],
            output_path=spec_data.get('output_path'),
            parameters=spec_data.get('parameters', {}),
            kernel=spec_data.get('kernel'),
            timeout=spec_data.get('timeout'),
            priority=spec_data.get('priority', 1)
        )
        notebook_specs.append(spec)
    
    if not notebook_specs:
        logging.error("Aucun notebook spécifié dans la configuration batch")
        return 1
    
    # Configuration executor batch
    executor_config = batch_config.get('executor_config', {})
    if args.production_mode:
        executor = create_production_executor(**executor_config)
    else:
        executor = create_educational_executor(**executor_config)
    
    try:
        if not args.quiet:
            print(f"🎓 Démarrage batch: {len(notebook_specs)} notebooks")
        
        # Exécution batch avec monitoring
        results = await executor.batch_execute(notebook_specs)
        
        # Analyse résultats batch
        success_count = sum(1 for r in results if r.success)
        total_time = sum(r.metrics.execution_time_seconds for r in results)
        
        if not args.quiet:
            print(f"📊 Batch terminé: {success_count}/{len(results)} succès")
            print(f"⏱️ Temps total: {total_time:.2f}s")
        
        # Export rapport batch si demandé
        if args.export_metrics:
            batch_report = {
                'batch_summary': {
                    'total_notebooks': len(results),
                    'successful': success_count,
                    'failed': len(results) - success_count,
                    'total_time_seconds': total_time,
                    'average_performance': sum(r.metrics.cells_per_second for r in results) / len(results)
                },
                'individual_results': [r.to_dict() for r in results]
            }
            
            with open(args.export_metrics, 'w', encoding='utf-8') as f:
                json.dump(batch_report, f, indent=2, ensure_ascii=False)
            
            if not args.quiet:
                print(f"📊 Rapport batch exporté: {args.export_metrics}")
        
        return 0 if success_count == len(results) else 1
        
    except Exception as e:
        logging.error(f"Erreur batch: {e}")
        return 2
        
    finally:
        executor.close()


def main():
    """Point d'entrée principal CLI"""
    
    parser = argparse.ArgumentParser(
        prog='papermill-coursia',
        description='🎓 Exécution robuste notebooks Jupyter pour CoursIA',
        epilog="""
Exemples:
  # Exécution simple avec monitoring éducatif
  papermill-coursia notebook.ipynb output.ipynb
  
  # Avec paramètres et kernel spécifique  
  papermill-coursia input.ipynb output.ipynb -k .net-csharp -p param1 value1
  
  # Mode batch pour TP classe entière
  papermill-coursia --batch batch_config.json --export-metrics rapport.json
  
  # Mode production (moins verbeux, plus rapide)
  papermill-coursia input.ipynb output.ipynb --production-mode
        """,
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    
    # Arguments principaux
    parser.add_argument('input_notebook', nargs='?',
                       help='Notebook source (.ipynb)')
    parser.add_argument('output_notebook', nargs='?',
                       help='Notebook sortie (auto-généré si omis)')
    
    # Configuration exécution
    parser.add_argument('-k', '--kernel', 
                       help='Kernel Jupyter (auto-détection si omis)')
    parser.add_argument('-t', '--timeout', type=int, default=300,
                       help='Timeout en secondes (défaut: 300s)')
    parser.add_argument('-p', '--parameters', nargs='*',
                       help='Paramètres notebook: -p key value ou -p key=value')
    
    # Configuration environnement
    parser.add_argument('--conda-env', default='mcp-jupyter',
                       help='Environnement Conda (défaut: mcp-jupyter)')
    parser.add_argument('--max-workers', type=int, default=2,
                       help='Workers parallèles (défaut: 2)')
    
    # Modes opérationnels
    parser.add_argument('--batch', 
                       help='Mode batch avec fichier config JSON')
    parser.add_argument('--production-mode', action='store_true',
                       help='Mode production (moins verbeux, plus rapide)')
    parser.add_argument('--educational-mode', action='store_true', default=True,
                       help='Mode éducatif avec rapports détaillés (défaut)')
    
    # Logging et export
    parser.add_argument('-v', '--verbose', action='store_true',
                       help='Logging détaillé')
    parser.add_argument('-q', '--quiet', action='store_true',
                       help='Mode silencieux (erreurs seules)')
    parser.add_argument('--export-metrics',
                       help='Export métriques vers fichier JSON')
    
    # Version
    parser.add_argument('--version', action='version', version='papermill-coursia 1.0.0-sddd')
    
    args = parser.parse_args()
    
    # Configuration logging
    setup_logging(args.verbose, args.quiet)
    
    # Validation arguments
    if not args.batch and not args.input_notebook:
        parser.error("Notebook source requis (ou --batch pour mode batch)")
    
    if args.batch and args.input_notebook:
        parser.error("Mode batch incompatible avec notebook source individuel")
    
    # Exécution selon mode
    try:
        if args.batch:
            return_code = asyncio.run(execute_batch_notebooks(args))
        else:
            return_code = asyncio.run(execute_single_notebook(args))
        
        sys.exit(return_code)
        
    except KeyboardInterrupt:
        logging.warning("Exécution interrompue par utilisateur")
        sys.exit(130)
    except Exception as e:
        logging.error(f"Erreur fatale: {e}")
        if args.verbose:
            import traceback
            logging.error(traceback.format_exc())
        sys.exit(1)


if __name__ == '__main__':
    main()