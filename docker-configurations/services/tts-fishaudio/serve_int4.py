#!/usr/bin/env python
"""Lance l'API server de l'image avec le correctif de chargement int4.

Defaut amont (mesure dans l'image, torch 2.8) : la branche int4 du chargeur
(`fish_speech/models/text2semantic/llama.py`) lit le groupsize via
`path.name.split("-")`, donc exige un `pathlib.Path`. Or l'API server passe
le chemin du checkpoint en **str** (`init_model` -> `from_pretrained`) :
sans correctif, le chargement d'un checkpoint int4 s'arrete sur
`AttributeError: 'str' object has no attribute 'name'` apres le message
"Using int4 quantization!". Le quantificateur amont ne voit jamais ce defaut
-- click lui fournit deja un `Path` (`path_type=Path`).

Correctif : convertir `checkpoint_path` en `Path` avant l'appel, puis
executer `tools/api_server.py` avec les arguments recus, inchanges.

Usage (variable du compose, voir docker-compose.yml) :

    FISHAUDIO_SERVE_SCRIPT=/app/serve_int4.py

Le fichier est monte en lecture seule par le compose et n'ecrit rien :
il ne modifie que l'objet module en memoire, dans le processus du serveur.
"""
from __future__ import annotations

import runpy
import sys
from pathlib import Path

import fish_speech.models.text2semantic.inference as _inference

_init_model_orig = _inference.init_model


def _init_model_path_safe(checkpoint_path, *args, **kwargs):
    if isinstance(checkpoint_path, str):
        checkpoint_path = Path(checkpoint_path)
    return _init_model_orig(checkpoint_path, *args, **kwargs)


_inference.init_model = _init_model_path_safe

# L'API server relit ses arguments dans sys.argv[1:] ; on les lui transmit
# tels quels, en ne remplacant que le nom du script (argv[0]).
sys.argv = ["tools/api_server.py"] + sys.argv[1:]
runpy.run_path("tools/api_server.py", run_name="__main__")
