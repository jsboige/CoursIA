# Bakeoff Large — Phase A0 EPIC #1028 / Issue #17586

Périmètre `myia-po-2023:CoursIA-2` : RTX 3090 24 GB + RTX 3080 16 GB, modèles TTS au-delà de 8 GB de VRAM, visant la production audiobook français pour l'Association Bibliothèques Sonores.

Disjoint de `bakeoff_small/` (`myia-po-2027:CoursIA-2`, RTX 4060 8 GB).

## Convention

- Chaque modèle candidat = 1 client dans `clients/<modele>.py`
- Chaque banc = 1 appel `python prosody_lab/ab_engine_test.py --model <modele> --extract <A|B> --out runs/<run-id>/A0-bakeoff/<modele>/`
- Verdict plancher : `python scripts/tts_verification/verify_prosody.py --single <wav>` + WER Whisper
- Aucun binaire audio dans le dépôt — dépôt GDrive `G:\Mon Drive\MyIA\Projets\BibliothequesSonores\<run-id>\A0-bakeoff\`

## Run-id courant

`run-20260924-143012` (à confirmer en début de Phase A)

## Modèles candidats (veille c.815, sous-agent haiku)

Tableau mis à jour dynamiquement dans `models_shortlist.md`.
