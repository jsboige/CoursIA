#!/usr/bin/env python
"""Lance l'API server de l'image avec les correctifs de chargement int4.

Deux correctifs, tous deux mesures sur la bench po-2023 :

1. Path (correctif original) : la branche int4 du chargeur
   (`fish_speech/models/text2semantic/llama.py`) lit le groupsize via
   `path.name.split("-")`, donc exige un `pathlib.Path`. Or l'API server
   passe le chemin du checkpoint en **str** (`init_model` ->
   `from_pretrained`) : sans correctif, le chargement d'un checkpoint int4
   s'arrete sur `AttributeError: 'str' object has no attribute 'name'`
   apres le message "Using int4 quantization!". Le quantificateur amont ne
   voit jamais ce defaut -- click lui fournit deja un `Path`.

2. bf16 (repair du crash-loop, 2026-11-10) : `from_pretrained` instancie le
   modele FULL-SIZE en RAM sous le dtype fp32 par defaut AVANT la conversion
   int4, si bien que le pic de chargement atteint ~14 GiB (mesure : 14 120
   MiB sous une probe 14g ; OOM sous chaque borne 6g/8g/12g/14g). Le
   `load_state_dict(assign=True)` final remplace ensuite tous les tenseurs
   par ceux du checkpoint : le dtype d'init n'affecte que le pic de
   chargement, pas le modele servi. `torch.set_default_dtype(bfloat16)`
   autour de `init_model` divise ce pic (mesure apres correctif : 10 536
   MiB sous borne 12g, poids "All keys matched", /v1/health 200).

Usage (variable du compose, voir docker-compose.int4.yml) :

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
    # Correctif 1 : l'API server passe le checkpoint en str ; le loader int4
    # exige un pathlib.Path.
    if isinstance(checkpoint_path, str):
        checkpoint_path = Path(checkpoint_path)
    # Correctif 2 : init sous bf16 autour de init_model. from_pretrained
    # instancie le modele full-size en fp32 AVANT la conversion int4 (pic
    # ~14 GiB mesure), ce qu'aucune borne memoire raisonnable ne survit. Le
    # load_state_dict(assign=True) final remplace les tenseurs par ceux du
    # checkpoint : le dtype d'init ne change que le pic, pas le modele servi.
    import torch

    _orig_dtype = torch.get_default_dtype()
    torch.set_default_dtype(torch.bfloat16)
    try:
        return _init_model_orig(checkpoint_path, *args, **kwargs)
    finally:
        torch.set_default_dtype(_orig_dtype)


_inference.init_model = _init_model_path_safe

# L'API server relit ses arguments dans sys.argv[1:] ; on les lui transmit
# tels quels, en ne remplacant que le nom du script (argv[0]).
sys.argv = ["tools/api_server.py"] + sys.argv[1:]
runpy.run_path("tools/api_server.py", run_name="__main__")
