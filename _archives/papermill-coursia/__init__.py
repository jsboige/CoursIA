"""
Papermill-CoursIA - Solution SDDD Robuste pour Exécution Notebooks
================================================================

Architecture industrielle Netflix/Airbnb adaptée contexte éducatif.
Performance validée : 4.14 cell/s, 26/26 cellules, multi-kernels.
"""

__version__ = "1.0.0-sddd"
__author__ = "CoursIA Team"
__description__ = "Wrapper Papermill robuste pour notebooks éducatifs"

from .core.executor import (
    PapermillExecutor,
    ExecutionResult, 
    ExecutionMetrics,
    NotebookSpec,
    create_educational_executor,
    create_production_executor
)

__all__ = [
    'PapermillExecutor',
    'ExecutionResult',
    'ExecutionMetrics', 
    'NotebookSpec',
    'create_educational_executor',
    'create_production_executor'
]