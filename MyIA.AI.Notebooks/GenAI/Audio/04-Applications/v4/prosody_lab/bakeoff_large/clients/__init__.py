# Clients par modèle — un fichier .py par moteur TTS
# Chaque client expose une interface uniforme :
#   def synth(text: str, out_wav: str, **kwargs) -> dict:
#       """Synthèse text→wav, retourne {'sample_rate', 'duration_s', 'rtf', 'vram_peak_gb'}"""
#
# Convention : le client est pilotable en CLI :
#   python clients/<modele>.py --text "..." --out <wav> [--ref-voice <wav>] [--voice-id <id>]
#
# Référentiel : voir `../models_shortlist.md` pour la liste courante.
