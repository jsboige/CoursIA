#!/usr/bin/env python
# -*- coding: utf-8 -*-


# Verbatim copy of `argumentation_analysis/core/utils/file_loaders.py` from
# the 2025-Epita-Intelligence-Symbolique project
# (https://github.com/jsboigeEpita/2025-Epita-Intelligence-Symbolique),
# Copyright (c) 2025 jsboigeEpita, MIT License.
# Source commit: a8025f60 (2026-07-02) "feat(conv-c): de-templatised PM prompt +
# designation backfill + pipeline cap (#1334 phase 3/3) (#1345)".
# Verbatim import rationale: see NOTICE-EPITA at the root of this directory.
#
# Verbatim integrity: file content below this header is byte-for-byte identical
# to the upstream source at the cited commit. No CoursIA modification.
#
# RUNTIME WIRING (#23633, Volet B etape 4) : ce module est enregistre sous son
# nom amont par `_epita_vendor_shim.install_informal_runtime_shim()` pour que
# les imports litteraux de `_informal_definitions.py` (verbatim, non modifiable)
# resolvent au runtime.

# -*- coding: utf-8 -*-
"""
Utilitaires pour le chargement de fichiers de différents formats.
"""

import json
from pathlib import Path
from typing import List, Dict, Any, Optional, Union
import logging

# Logger spécifique pour ce module
loaders_logger = logging.getLogger("App.ProjectCore.FileLoaders")
if not loaders_logger.handlers and not loaders_logger.propagate:
    handler = logging.StreamHandler()
    formatter = logging.Formatter(
        "%(asctime)s [%(levelname)s] [%(name)s] %(message)s", datefmt="%H:%M:%S"
    )
    handler.setFormatter(formatter)
    loaders_logger.addHandler(handler)
    loaders_logger.setLevel(logging.INFO)


def load_json_file(
    file_path: Path,
) -> Optional[Union[List[Dict[str, Any]], Dict[str, Any]]]:
    """
    Charge des données depuis un fichier JSON.
    Gère les listes ou dictionnaires à la racine du JSON.
    Tente également de parser le contenu si le JSON initial est une chaîne (double encodage).
    """
    loaders_logger.info(f"Chargement des données JSON depuis {file_path}")
    try:
        with open(file_path, "r", encoding="utf-8") as f:
            loaded_initial_data = json.load(f)

        if isinstance(loaded_initial_data, str):
            loaders_logger.info(
                f"Contenu de {file_path} est une chaîne, tentative de re-parse JSON."
            )
            try:
                data = json.loads(loaded_initial_data)
            except json.JSONDecodeError as e_inner:
                loaders_logger.error(
                    f"❌ Erreur lors du re-parse de la chaîne JSON depuis {file_path}: {e_inner}"
                )
                loaders_logger.debug(
                    f"Contenu de la chaîne (premiers 500 caractères): {loaded_initial_data[:500]}"
                )
                return None
        else:
            data = loaded_initial_data

        if isinstance(data, list):
            loaders_logger.info(
                f"[OK] {len(data)} éléments (liste) chargés avec succès depuis {file_path}"
            )
        elif isinstance(data, dict):
            loaders_logger.info(
                f"[OK] Dictionnaire chargé avec succès depuis {file_path}"
            )
        else:
            loaders_logger.error(
                f"Type de données inattendu ({type(data)}) après chargement de {file_path}. Attendu List ou Dict. Retour de None."
            )
            return None
        return data
    except FileNotFoundError:
        loaders_logger.error(f"❌ Fichier non trouvé: {file_path}")
        return None
    except json.JSONDecodeError as e:
        loaders_logger.error(f"❌ Erreur de décodage JSON dans {file_path}: {e}")
        return None
    except Exception as e:
        loaders_logger.error(
            f"❌ Erreur inattendue lors du chargement du fichier JSON {file_path}: {e}"
        )
        return None


def load_extracts(file_path: Path) -> List[Dict[str, Any]]:
    """
    Charge les extraits déchiffrés depuis un fichier JSON. Wrapper autour de load_json_file.
    """
    data = load_json_file(file_path)
    if isinstance(data, list):
        return data
    elif data is None:
        return []
    else:
        loaders_logger.warning(
            f"Les données chargées depuis {file_path} ne sont pas une liste comme attendu pour des extraits. Type: {type(data)}. Retour d'une liste vide."
        )
        return []


def load_base_analysis_results(file_path: Path) -> List[Dict[str, Any]]:
    """
    Charge les résultats de l'analyse rhétorique de base depuis un fichier JSON. Wrapper.
    """
    data = load_json_file(file_path)
    if isinstance(data, list):
        loaders_logger.info(
            f"Données de type liste chargées pour les résultats d'analyse de base depuis {file_path}"
        )
        return data
    elif data is None:
        return []
    else:
        loaders_logger.warning(
            f"Les données chargées depuis {file_path} pour les résultats d'analyse de base ne sont pas une liste. Type: {type(data)}. Retour d'une liste vide."
        )
        return []


def load_text_file(file_path: Path, encoding: str = "utf-8") -> Optional[str]:
    """
    Charge le contenu d'un fichier texte.
    """
    loaders_logger.info(
        f"Chargement du fichier texte {file_path} avec l'encodage {encoding}"
    )
    try:
        with open(file_path, "r", encoding=encoding) as f:
            content = f.read()
        loaders_logger.info(f"[OK] Fichier texte {file_path} chargé avec succès")
        return content
    except FileNotFoundError:
        loaders_logger.error(f"❌ Fichier non trouvé: {file_path}")
        return None
    except UnicodeDecodeError as e:
        loaders_logger.error(
            f"❌ Erreur de décodage Unicode lors du chargement du fichier {file_path} avec l'encodage {encoding}: {e}",
            exc_info=True,
        )
        return None
    except IOError as e:
        loaders_logger.error(
            f"❌ Erreur d'E/S lors du chargement du fichier {file_path}: {e}",
            exc_info=True,
        )
        return None
    except Exception as e:
        loaders_logger.error(
            f"❌ Erreur inattendue lors du chargement du fichier texte {file_path}: {e}",
            exc_info=True,
        )
        return None


def load_csv_file(file_path: Path) -> Optional[Any]:
    """
    Charge des données depuis un fichier CSV en utilisant la bibliothèque pandas.
    """
    try:
        import pandas as pd
    except ImportError:
        loaders_logger.error(
            "Le package 'pandas' est requis pour charger les fichiers CSV mais n'est pas installé."
        )
        loaders_logger.error("Veuillez installer pandas: pip install pandas")
        return None

    loaders_logger.info(f"Chargement des données CSV depuis {file_path}")
    try:
        df = pd.read_csv(file_path, encoding="utf-8")
        loaders_logger.info(
            f"[OK] Fichier CSV chargé avec succès ({len(df)} lignes) depuis {file_path}"
        )
        return df
    except FileNotFoundError:
        loaders_logger.error(f"❌ Fichier CSV non trouvé: {file_path}")
        return None
    except pd.errors.EmptyDataError:  # type: ignore
        loaders_logger.warning(
            f"⚠️ Fichier CSV vide: {file_path}. Retour d'un DataFrame vide."
        )
        return pd.DataFrame()
    except Exception as e:
        loaders_logger.error(
            f"❌ Erreur inattendue lors du chargement du fichier CSV {file_path}: {e}",
            exc_info=True,
        )
        return None


def load_document_content(file_path: Path) -> Optional[str]:
    """
    Charge le contenu textuel d'un fichier document (.txt, .md).
    """
    loaders_logger.info(
        f"Tentative de chargement du contenu du document depuis {file_path}"
    )
    if not file_path.is_file():
        loaders_logger.error(
            f"❌ Le chemin spécifié n'est pas un fichier : {file_path}"
        )
        return None

    file_extension = file_path.suffix.lower()

    if file_extension in [".txt", ".md"]:
        loaders_logger.debug(
            f"Chargement du fichier {file_extension} : {file_path} via load_text_file."
        )
        return load_text_file(file_path)
    else:
        loaders_logger.warning(
            f"Type de fichier non supporté '{file_extension}' pour le chargement direct de document : {file_path}. Seuls .txt et .md sont gérés par cette fonction."
        )
        return None


loaders_logger.info("Utilitaires de chargement de fichiers (FileLoaders) définis.")
