"""Strip d'un bloc ``metadata.papermill`` perime, partage par executeurs (#12722).

Le raisonnement ne doit rien a .NET : il vaut pour TOUT executeur non-Papermill
qui reecrit un notebook. Papermill reecrit son propre bloc a chaque passage ; un
executeur de kernel (nbclient, jupyter-client, websocket QC) reecrit les sorties
mais laisse le bloc de la passe Papermill ANTERIEURE — qui date alors les sorties
fraises au mauvais run. C'est le defaut STALE_BLOCK du ratchet (#11155) : 11 PRs
bloquees au 2026-08-24 pour cette ligne manquante.

Historique : fonction introduite dans ``dotnet_executor.py`` (#11146), extraite
ici pour etre cablee dans chaque executeur qui reecrit un notebook sans passer
par Papermill (cf #12722). Ne pas retirer le bloc dans les PRs a la main comme
politique : le correctif durable est ce cablage, afin que le bloc perime ne
revienne pas a l'execution suivante.
"""

from __future__ import annotations


def strip_stale_papermill_metadata(nb):
    """Remove a pre-existing Papermill block from a notebook the executor is
    about to rewrite.

    The outputs and ``execution_count`` just written describe THIS run; a
    ``metadata.papermill`` left over from an earlier Papermill pass would still
    describe that pass (old dates, old duration) and would let a reviewer date
    the fresh outputs to the wrong run. An absent metadata is missing
    information; a stale one is misleading information (#11146).

    The same rationale applies per cell (#18305, suite #11146) : un executeur
    qui reecrit un carnet touche les sorties de chaque cellule code mais laisse
    les blocs ``cells[i].metadata.execution`` (``iopub.status.busy``/``iopub.
    execute_input``) et ``cells[i].metadata.papermill`` (``start_time``,
    ``duration``) dater des executions precedentes. On les retire aussi.
    """
    metadata = nb.get("metadata")
    if metadata:
        metadata.pop("papermill", None)
        execution = metadata.get("execution")
        if isinstance(execution, dict):
            execution.pop("papermill", None)
            if not execution:
                metadata.pop("execution", None)
    for cell in nb.get("cells", []) or []:
        cell_meta = cell.get("metadata")
        if not cell_meta:
            continue
        cell_meta.pop("papermill", None)
        execution = cell_meta.get("execution")
        if isinstance(execution, dict):
            execution.pop("papermill", None)
            if not execution:
                cell_meta.pop("execution", None)
