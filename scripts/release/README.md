# scripts/release/

Outils lies au cycle de release semestriel (`v<annee>.S<semestre>`). Source de
la decision de design : issue **#9856** (« 0 tag / 0 release pour ~95 forks
etudiants -- poser v2026.S2 et generer les notes »). Le depot a ete
historiquement sans tag et sans release GitHub ; ce repertoire introduit la
plomberie minimale pour les ajouter.

## Pourquoi ces notes sont generees (et pas tapees a la main)

L'acceptance **#9856** est explicite : « les notes citent des comptes **lus
dans le catalogue**, jamais recopies a la main ». Taper les comptes a la
main derive inevitablement avec le catalogue (cron quotidien) -- une release
deja publiee devient obsolète des qu'une entree est ajoutee. Le script
[`generate_release_notes.py`](generate_release_notes.py) re-calcule tout a
chaque execution ; les notes sont donc byte-deterministes en fonction du
catalogue seul (le seul element qui change entre deux executions est
l'horodatage UTC injecte dans l'en-tete).

## Scripts

| Fichier | Role |
|---|---|
| [`generate_release_notes.py`](generate_release_notes.py) | Lit `COURSE_CATALOG.generated.json` et emet les notes markdown d'une release |

## Tests

`scripts/tests/test_generate_release_notes.py` -- 22 tests unitaires sur le
module (load / count / render / CLI / determinism).

## Utilisation type

```bash
# Notes v2026.S2 sur stdout (le catalogue est sur main par defaut)
python scripts/release/generate_release_notes.py --tag v2026.S2

# Notes dans un fichier, prete a etre injectees dans gh release create
python scripts/release/generate_release_notes.py --tag v2026.S2 \
    --out RELEASE_NOTES_v2026.S2.md

# Section "ajouts depuis rentree" optionnelle
python scripts/release/generate_release_notes.py --tag v2026.S2 \
    --out RELEASE_NOTES_v2026.S2.md --since 2026-09-01
```

Aucune dependance hors stdlib Python 3.10+.