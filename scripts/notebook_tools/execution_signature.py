"""Signature d'execution d'un carnet -- equivalent du tampon papermill cote .NET Interactive.

Le tampon `metadata.papermill` (cote Python) porte, pour chaque execution, la trace
rejouable de l'execution : noyau, horodatage, versions d'outillage, chemin d'entree.
Un carnet `.NET Interactive` n'a pas d'equivalent : ses cellules portent un
`execution_count`, mais rien ne dit *avec quel outillage* elles ont ete executees, ni
*si leur source a ete editee depuis*.

Ce module introduit une signature portable, stockee sous
`metadata.execution_signature`, qui repond a ces deux questions :

- **quelle outillage a produit les sorties committees** (noyau, versions mesurees,
  horodatage UTC) ;
- **la source executee est-elle toujours celle qui est commitee** (empreinte SHA-256
  des cellules code executees, recalculee a chaque verification).

La signature est **opt-in** : seuls les carnets qui en portent une sont verifies par
la ligne de garde. Aucun carnet existant n'est donc rendu rouge par l'introduction
de l'organe.

La signature est un **temoignage d'execution**, pas une sortie de cellule : elle vit
dans les metadonnees du carnet, comme `metadata.papermill`, et n'altere aucune sortie.
"""

from __future__ import annotations

import hashlib
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

SIGNATURE_KEY = "execution_signature"
SCHEMA_VERSION = 1

#: Codes de constat produits par :func:`verify`.
SIGNATURE_ABSENTE = "SIGNATURE_ABSENTE"
SIGNATURE_PERIMEE = "SIGNATURE_PERIMEE"
CELLULE_NON_EXECUTEE = "CELLULE_NON_EXECUTEE"
COMPTES_INCOHERENTS = "COMPTES_INCOHERENTS"
KERNEL_INCOHERENT = "KERNEL_INCOHERENT"
SIGNATURE_ILLISIBLE = "SIGNATURE_ILLISIBLE"


def code_cells(notebook: dict) -> list[dict]:
    """Renvoie les cellules de code du carnet, dans l'ordre du fichier."""
    return [c for c in notebook.get("cells", []) if c.get("cell_type") == "code"]


def executed_code_cells(notebook: dict) -> list[dict]:
    """Renvoie les cellules de code portees par une execution (`execution_count` non nul)."""
    return [c for c in code_cells(notebook) if c.get("execution_count") is not None]


def source_digest(notebook: dict) -> str:
    """Empreinte SHA-256 des cellules code executees (source + rang).

    Le rang de la cellule est inclus : deplacer une cellule sans modifier son source
    change l'ordre d'execution, donc le resultat.
    """
    h = hashlib.sha256()
    for index, cell in enumerate(executed_code_cells(notebook)):
        source = cell.get("source")
        text = "".join(source) if isinstance(source, list) else str(source or "")
        h.update(str(index).encode("utf-8"))
        h.update(b"\x00")
        h.update(text.encode("utf-8"))
        h.update(b"\x00")
    return "sha256:" + h.hexdigest()


def kernel_of(notebook: dict) -> dict:
    """Nom et libelle du noyau demande par le carnet."""
    spec = (notebook.get("metadata") or {}).get("kernelspec") or {}
    return {
        "name": spec.get("name") or "",
        "display_name": spec.get("display_name") or "",
    }


def measure_tool_versions() -> dict:
    """Mesure les versions d'outillage disponibles sur la machine.

    La mesure est **best effort** : un outillage absent donne `None` plutot qu'une
    erreur -- la signature reste valide, elle porte simplement moins d'information.
    """
    versions: dict[str, Any] = {}

    def _run(argv: list[str]) -> str | None:
        try:
            out = subprocess.run(
                argv,
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
                timeout=60,
            )
        except (OSError, subprocess.SubprocessError):
            return None
        if out.returncode != 0:
            return None
        return out.stdout.strip() or None

    versions["dotnet_sdk"] = _run(["dotnet", "--version"])
    tools = _run(["dotnet", "tool", "list", "--global"]) or ""
    for line in tools.splitlines():
        parts = line.split()
        if len(parts) >= 2 and parts[0] == "microsoft.dotnet-interactive":
            versions["dotnet_interactive"] = parts[1]
            break
    versions.setdefault("dotnet_interactive", None)
    return versions


def compute_signature(
    notebook: dict,
    tool_versions: dict | None = None,
    executed_at: str | None = None,
) -> dict:
    """Calcule la signature d'execution du carnet fourni.

    La signature ne depend que de l'etat **execute** du carnet : cellules code
    executees, noyau demande, et empreinte de leur source. Les versions d'outillage
    sont mesurees par l'appelant (voir :func:`measure_tool_versions`).

    `executed_at` permet de porter l'instant **reel** de l'execution attestee --
    celui du run qui a produit les sorties committees -- plutot que l'heure du
    tampon. Format attendu : `YYYY-MM-DDTHH:MM:SSZ` (UTC).
    """
    executed = executed_code_cells(notebook)
    return {
        "schema": SCHEMA_VERSION,
        "kernel": kernel_of(notebook),
        "executed_at": executed_at or datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "tool_versions": dict(tool_versions or {}),
        "executed_cells": len(executed),
        "source_digest": source_digest(notebook),
    }


def stamp(
    notebook: dict,
    tool_versions: dict | None = None,
    executed_at: str | None = None,
) -> dict:
    """Ecrit la signature dans les metadonnees du carnet et la renvoie."""
    metadata = notebook.setdefault("metadata", {})
    signature = compute_signature(notebook, tool_versions, executed_at)
    metadata[SIGNATURE_KEY] = signature
    return signature


def read_signature(notebook: dict) -> dict | None:
    """Lit la signature portee par le carnet, ou ``None``."""
    signature = (notebook.get("metadata") or {}).get(SIGNATURE_KEY)
    return signature if isinstance(signature, dict) else None


def verify(notebook: dict, require_signature: bool = True) -> list[dict]:
    """Verifie la signature d'un carnet et renvoie la liste des constats.

    Constats produits :

    - ``SIGNATURE_ABSENTE`` : le carnet ne porte aucune signature et l'exigence est
      posee ;
    - ``SIGNATURE_ILLISIBLE`` : la signature est presente mais mal formee ;
    - ``SIGNATURE_PERIMEE`` : la source des cellules executees a change depuis
      l'execution atteste (le temoin negatif de l'organe) ;
    - ``CELLULE_NON_EXECUTEE`` : une cellule code n'a pas ete executee ;
    - ``COMPTES_INCOHERENTS`` : le nombre de cellules executees ne correspond plus ;
    - ``KERNEL_INCOHERENT`` : le noyau demande a change depuis l'execution atteste.
    """
    findings: list[dict] = []
    signature = read_signature(notebook)

    if signature is None:
        if require_signature:
            findings.append({"code": SIGNATURE_ABSENTE, "detail": "aucune signature dans metadata"})
        return findings

    if signature.get("schema") != SCHEMA_VERSION:
        findings.append({
            "code": SIGNATURE_ILLISIBLE,
            "detail": f"schema {signature.get('schema')!r} inconnu (attendu {SCHEMA_VERSION})",
        })
        return findings

    expected_digest = source_digest(notebook)
    if signature.get("source_digest") != expected_digest:
        findings.append({
            "code": SIGNATURE_PERIMEE,
            "detail": f"source executee {signature.get('source_digest')} != source actuelle {expected_digest}",
        })

    executed = executed_code_cells(notebook)
    if signature.get("executed_cells") != len(executed):
        findings.append({
            "code": COMPTES_INCOHERENTS,
            "detail": f"signature {signature.get('executed_cells')} cellules executees, carnet {len(executed)}",
        })

    unexecuted = [
        index for index, cell in enumerate(code_cells(notebook))
        if cell.get("execution_count") is None
    ]
    if unexecuted:
        findings.append({
            "code": CELLULE_NON_EXECUTEE,
            "detail": f"cellules code sans execution_count : {unexecuted}",
        })

    if signature.get("kernel") != kernel_of(notebook):
        findings.append({
            "code": KERNEL_INCOHERENT,
            "detail": f"signature {signature.get('kernel')} != carnet {kernel_of(notebook)}",
        })

    return findings


def load_notebook(path: str | Path) -> dict:
    """Charge un carnet depuis le disque."""
    with open(path, "r", encoding="utf-8") as handle:
        return json.load(handle)


def save_notebook(path: str | Path, notebook: dict) -> None:
    """Ecrit un carnet sur le disque, en preservant l'indentation du depot (1 espace)."""
    with open(path, "w", encoding="utf-8", newline="\n") as handle:
        json.dump(notebook, handle, ensure_ascii=False, indent=1)
        handle.write("\n")
