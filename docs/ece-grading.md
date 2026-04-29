# ECE - Evaluation etudiants et compilation notes

## ECE Student Repos

ECE students submit work in a **separate GitHub org**, NOT in CoursIA.

- **Org** : `jsboigeECE` on GitHub
- **Repos pattern** : `2026-ECE-Ing4-Fin-IA-Projet{1,2,3}-Gr{01,02,03}`

| Repo | Description |
| ------ | ------------- |
| `2026-ECE-Ing4-Fin-IA-Projet1-Gr01` | Projet 1 - Groupe 01 |
| `2026-ECE-Ing4-Fin-IA-Projet1-Gr02` | Projet 1 - Groupe 02 |
| `2026-ECE-Ing4-Fin-IA-Projet1-Gr03` | Projet 1 - Groupe 03 |
| `2026-ECE-Ing4-Fin-IA-Projet2-Gr01` | Projet 2 - Groupe 01 |
| `2026-ECE-Ing4-Fin-IA-Projet2-Gr02` | Projet 2 - Groupe 02 |
| `2026-ECE-Ing4-Fin-IA-Projet2-Gr03` | Projet 2 - Groupe 03 |

**For any ECE student grading or rattrapage investigation** : search `jsboigeECE/` repos, NOT CoursIA.

```bash
# List student PRs
gh pr list --repo jsboigeECE/2026-ECE-Ing4-Fin-IA-Projet2-Gr02 --state all --limit 30

# View a specific PR
gh pr view 12 --repo jsboigeECE/2026-ECE-Ing4-Fin-IA-Projet2-Gr02
```

## Compilation finale

- **Excel grading** : `G:/Mon Drive/MyIA/Formation/ECE/2026/Notes_Finales_ECE_2026_Compilation.xlsq`
- **Pipeline Python** : `python GradeBookApp/gradebook.py`

## Autres ecoles (rappel)

- **EPITA** : depot dedie `jsboigeEpita/2026-Epita-Programmation-par-Contraintes`
- **EPF** : projets soumis sur `jsboigeEPF/2025-MSBNS3IN03-GenAI`
- **ESGF** : org QuantConnect `Trading Firm ESGF`
