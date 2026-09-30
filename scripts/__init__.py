"""Scripts CoursIA (boite a outils admin, tests, pipelines).

Ce paquet rend les modules sous ``scripts/`` importables via
``scripts.<module>`` sans manipulation du ``sys.path``. Le CI lance
pytest avec ``--import-mode importlib`` (cf workflow
``windows-self-hosted-tests.yml``) ; sans cette racine, l'import
``scripts.livecoding_video_pipeline`` echoue avec
``ModuleNotFoundError: No module named 'scripts.livecoding_video_pipeline'``.

Les modules sous ``scripts/`` sont des outils admin / pipelines ;
ils ne sont **pas** distribues comme bibliotheque Python : le present
paquet sert de **namespace d'import** pour les tests pytest
uniquement, pas de surface d'API publique.
"""
