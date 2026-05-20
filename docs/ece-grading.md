# ECE - Evaluation etudiants et compilation notes

Pipeline GradeBookApp + repos GitHub etudiants. Pour le **calendrier toutes ecoles, scope EPITA-IS, agents par ecole** : cf [docs/teaching-context.md](teaching-context.md). Pour les **regles de review PR etudiantes** (anti-fuite questions soutenance) : cf [.claude/rules/student-pr-reviews.md](../.claude/rules/student-pr-reviews.md).

## Repos GitHub etudiants

Les rendus etudiants sont dans des **orgs/comptes GitHub dedies, jamais dans CoursIA**.

| Ecole | Compte | Pattern repo |
|-------|--------|--------------|
| ECE Finance Ing4 IA | `jsboigeECE` | `2026-ECE-Ing4-Fin-IA-Projet{1,2,3}-Gr{01,02,03}` |
| EPITA Programmation par Contraintes | `jsboigeEpita` | `2026-Epita-Programmation-par-Contraintes` (mono-repo, sujets numerotes) |
| EPITA IA Symbolique | `jsboigeEpita` | `2026-Epita-Intelligence-Symbolique` (sujets) **+ forks `jsboige/CoursIA`** (TPs notebooks) |
| EPF GenAI | `jsboigeEPF` | `2025-MSBNS3IN03-GenAI` |
| ESGF Algo Trading | (QC org Trading Firm ESGF) | code QC Cloud, pas de repo GitHub commun |

Pour toute investigation rattrapage/notation, lister les PRs etudiants :

```bash
gh pr list --repo jsboigeECE/2026-ECE-Ing4-Fin-IA-Projet2-Gr02 --state all --limit 30
gh pr view 12 --repo jsboigeECE/2026-ECE-Ing4-Fin-IA-Projet2-Gr02
```

**Specificite EPITA-IS** : les TPs sont des PRs sur `jsboige/CoursIA` (workflow type PrCon : fork + PR sur notebooks). Le repo `jsboigeEpita/2026-Epita-Intelligence-Symbolique` contient les sujets/projets de soutenance, **distinct** des TPs notebooks.

## GradeBookApp - Engine de notation collegiale

Pipeline Python pour notation **collegiale** (note prof + moyenne notes etudiants evaluateurs) avec redressement statistique et bonus taille de groupe.

### Localisation

| Fichier | Role |
|---------|------|
| `GradeBookApp/gradebook.py` | Engine principal (note collegiale + redressement) |
| `GradeBookApp/compile_ece_2026.py` | Compilation finale (bonus CC + Excel multi-feuilles) |
| `GradeBookApp/configs/ece_2026_gr{01,02,03}_multi.py` | Configs multi-epreuves par groupe (P1+P2, poids 50/50) |
| `GradeBookApp/configs/ece_2026_compilation.py` | Config compilation (bonus types, plafond, fichiers) |

Configs runtime hors repo sur `G:\Mon Drive\MyIA\Formation\ECE\2026\grading\` (resolution `COURSIA_ROOT` env var, fallback `D:\CoursIA`).

### Ponderation note prof / note etudiants

Notation collegiale : la note finale = moyenne ponderee de la note prof et de la moyenne des notes etudiants evaluateurs.

```python
TEACHER_WEIGHT = 1.0   # gradebook.py:17 - "1.0 = 50% du total"
note = (student_avg + teacher_avg * TEACHER_WEIGHT) / (1 + TEACHER_WEIGHT)
```

`TEACHER_WEIGHT = 1.0` -> **50% prof / 50% moyenne etudiants**, independamment du nombre d'evaluateurs etudiants. Cas degeneres :
- Pas d'evaluation etudiante -> note = note prof seule
- Pas d'evaluation prof -> note = moyenne etudiants seule

### Etape A - Redressement statistique (centrage-reduction par groupe)

Apres calcul de la note collegiale brute, on centre-reduit dans chaque groupe pour stabiliser la distribution. Configs identiques Gr01/02/03 P1/P2 :

| Parametre | Valeur 2026 |
|-----------|-------------|
| `target_mean` | **13.0** |
| `target_std` | **2.5** |

Formule (`gradebook.py:301-306`) :
```
ajustee = ((brute - moyenne_groupe) / std_groupe) * target_std + target_mean
```
Resultat clip dans `[0, 20]`.

### Etape B - Bonus/malus taille de groupe

Apres redressement, ajustement selon la taille du groupe projet (table `group_size_adjustments`, `gradebook.py:309`) :

| Taille groupe | Ajustement |
|---------------|------------|
| 1 (solo) | +3.0 |
| 2 | +1.0 |
| 3 | 0.0 (reference) |
| 4 | -1.0 |
| 5+ | -2.0 |

Justification : un groupe solo doit produire 100% du contenu seul ; un groupe de 5+ benefice d'une mutualisation forte.

### Etape C - Ponderation inter-projets (compilation finale)

`ece_2026_compilation.py:18` :
```python
PROJECT_WEIGHTS = {'projet_1': 0.5, 'projet_2': 0.5}
```

Note finale = `(P1_ajustee + P2_ajustee) / 2`. Les bonus CC (cf section suivante) sont appliques **sur P2** avant cette moyenne, pas apres.

## Pipeline 2 couches (multi-epreuve + compilation)

| # | Couche | Script | Sortie |
|---|--------|--------|--------|
| 1 | Notes brutes par groupe | `python ece_2026_gr0{1,2,3}_multi.py` | `Notes_Finales_ECE_Gr0X.xlsx` (P1+P2) |
| 2 | Compilation + bonus | `python compile_ece_2026.py` | `Notes_Finales_ECE_2026_Compilation.xlsx` (source-of-truth multi-feuilles) |

**Fix architecturaux applies 2026-04-05** :
- `process_epreuve` recoit un `group_match_threshold` par epreuve (seuils fuzzy distincts P1 vs P2)
- `load_all_grades_from_multi_epreuve()` remplace `load_project_grades()` pour la compilation
- Seuils fuzzy par epreuve : Gr01 P2=94%, Gr03 P2=95%, autres=90% defaut

## Systeme de bonus CC

Bonus continus (Controle Continu) appliques sur P2 **avant** la moyenne P1/P2. Entres manuellement dans `BONUS_ENTRIES` de `ece_2026_compilation.py`.

| Type | Ajustement |
|------|------------|
| `pr_merged` | +0.5 |
| `pr_quality` | +1.0 |
| `qc_participation` | +0.5 |
| `participation_cours` | +0.5 |
| `aide_pairs` | +0.5 |
| `retard_rattrapage` | -1.0 |
| `retard_grave` | -2.0 |

**Plafond** : +3.0 / -3.0 par etudiant cumule. Au-dela : ignore avec warning.

## Regles d'evaluation

Regles user 2026-04-30 (HARD pour toute generation de notes) :

- **Note de groupe** : tous les membres du groupe recoivent la meme note, peu importe les commiters individuels. La contribution individuelle n'est pas evaluee dans la note de projet (sauf cas explicite de rattrapage ou litige).
- **Absence = 0** : un projet manquant compte 0 dans la moyenne brute `(P1+P2)/2`, pas un mix tronque sur un seul projet.
- **Pas de plafonnement affiche** : les notes brutes calculees sont attribuees telles quelles, pas de cap artificiel masque sur la feuille resultats.

## Compilation finale

- Excel source-of-truth : `G:/Mon Drive/MyIA/Formation/ECE/2026/Notes_Finales_ECE_2026_Compilation.xlsx`
- Format etabli 2026-04-05 ; bonus appliques 2026-04-22 ; notes finales rendues **2026-05-05**
- Pour cas particuliers (rattrapage, format heritier 2025) : script `regen_2026_groups.py` (lit la compilation, applique overrides manuels, produit format 3 feuilles avec colonne Bonus CC)

## Reviews PR etudiantes - rappel CRITIQUE

Sur tout repo etudiant, les commentaires de PR sont **visibles par les etudiants concernes**. Avant toute soutenance, ne JAMAIS poster en commentaire public :
- Sections "Questions pour la soutenance" / "A clarifier au jury" / "Points methodologiques"
- Grilles d'evaluation detaillees / criteres de notation
- Briefings jury

Le briefing jury / les questions / la grille restent **internes** (G drive `Notation/`, dashboard RooSync, rapport markdown local non-committe).

Voir [.claude/rules/student-pr-reviews.md](../.claude/rules/student-pr-reviews.md) pour le protocole complet (incident 2026-05-17 documente).
