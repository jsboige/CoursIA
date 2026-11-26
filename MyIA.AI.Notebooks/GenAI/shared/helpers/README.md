# shared/helpers — bibliothèque partagée GenAI

Helpers Python transverses de la série GenAI, importés par les notebooks via `sys.path` ou directement.

- `genai_helpers.py`, `genai_service.py` — appels services GenAI (réseau, retries, formats).
- `comfyui_client.py` — client ComfyUI (workflows, polling, récupération d'assets).
- `audio_helpers.py`, helpers vidéo — encode/décodage et montage des sorties Audio/Video.
- `audio_v4.py` — résolution du paquet `v4` de la série Audio (`Audio/04-Applications/v4`), point unique du bootstrap d'import des carnets de la série.
- `test_genai_helpers.py`, `test_video_helpers.py`, `test_audio_v4.py` — tests unitaires (`pytest shared/helpers/`).

Règles : pas de secret en dur (`.env` + `os.getenv`), pas d'emoji, type hints Python 3.10+.
