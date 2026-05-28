# ESGF - Evaluation etudiants et compilation notes

Pipeline d'evaluation cohorte ESGF (5ESGF-5BD1) sur module Trading Algorithmique. Pour le **calendrier toutes ecoles, scope par cohorte, agents par ecole** : cf [docs/teaching-context.md](teaching-context.md). Pour les **regles de review PR etudiantes** (anti-fuite questions soutenance) : cf [.claude/rules/student-pr-reviews.md](../.claude/rules/student-pr-reviews.md). Pour le **pattern ECE** dont ce pipeline est le miroir : cf [docs/ece-grading.md](ece-grading.md).

## Contexte

ESG Finance 5e annee, parcours BD (Big Data) et HL (Haute Liaison). Module Trading Algorithmique, evaluation unique par soutenance + projet QuantConnect Cloud.

- **Cohorte** : 5ESGF-5BD1 (~30 etudiants)
- **Projets soumis** : 10 (8 BD + 2 HL : s_kadid, f_gueye11)
- **Evaluation** : 1 soutenance / projet + 1 baseline ESGF a battre par projet
- **Soutenance** : 2026-05-19 (10 projets, fenetre 1 cession)
- **Compilation** : notes finales 2026-05-28 -> ingestion ESGF intervenant 2026-06-01

## Localisation des artefacts

**Regle (MEMORY.md) : NO grading data in repo - all on G-drive.** Le repo CoursIA contient le **moteur** generique ; le **runtime per-cohorte** vit sur G-drive.

| Element | Localisation |
|---------|--------------|
| Moteur de notation collegiale | [GradeBookApp/gradebook.py](../GradeBookApp/gradebook.py) (repo) |
| Runner generique | [GradeBookApp/run_grading.py](../GradeBookApp/run_grading.py) (repo) |
| Configs runtime ESGF | `G:\Mon Drive\MyIA\Formation\ESGF\2026\grading\` (G-drive) |
| Reponses peer eval (GForm CSV) | `G:\Mon Drive\MyIA\Formation\ESGF\2026\ESG - 2026 - 5ESGF-5BD1 - Trading Algorithmique - Evaluations (reponses) - Reponses au formulaire 1.csv` (G-drive) |
| Compilation finale | `G:\Mon Drive\MyIA\Formation\ESGF\2026\Notes_Finales_ESGF_2026_Compilation.xlsx` (G-drive) |
| Review forks vs baselines | `G:\Mon Drive\MyIA\Formation\ESGF\2026\REVIEW_FORKS_AGAINST_BASELINES.md` (G-drive) |
| Briefing soutenance | `G:\Mon Drive\MyIA\Formation\ESGF\2026\SOUTENANCE_2026-05-19_REVIEW.md` (G-drive) |

Les scripts de compilation per-cohorte (`compile_esgf_2026.py` + `esgf_2026_compilation.py`) vivent dans `G:\Mon Drive\MyIA\Formation\ESGF\2026\grading\`, parallele du pattern ECE.

## Structure du peer eval Google Form

Le formulaire ESGF est rempli par les etudiants apres chaque soutenance, evaluant le projet d'un camarade. Colonnes CSV :

| Colonne | Description |
|---------|-------------|
| `Horodateur` | Timestamp soumission |
| `Adresse e-mail` | Email evaluateur (pour deduplication, drop self-eval) |
| `Votre nom`, `Votre prenom` | Identite evaluateur |
| `Groupe a evaluer` | Cle projet evalue (sujet ou nom etudiant ; alignment manuel si flou) |
| `Sujet de la presentation` | Libelle algo / strategie |
| `Qualite de la presentation (communication, la forme)` | Note /10 |
| `Qualite theorique (principes, classe d'algos, contexte, perfs, problemes, histoire)` | Note /10 |
| `Qualite technique (livrables, commits, code, demos, resultats, perspectives)` | Note /10 |
| `Points positifs`, `Points negatifs`, `Recommandations` | Texte libre |

Format different ECE : ECE evalue **2 projets** (P1+P2) sur 3 groupes ; ESGF evalue **1 projet** sur 10 sujets dans une **seule cohorte**.

## Pipeline en 3 etapes

### Etape 1 - Note collegiale brute

Pour chaque projet :
1. Charger les peer evals depuis le CSV GForm
2. Filtrer les self-evals (Adresse e-mail = email du sujet evalue, mapping manuel via liste participants)
3. Aggreger les 3 notes /10 -> note /30 -> /20 (division par 1.5)
4. Moyenne pondéree note prof / moyenne etudiants : `TEACHER_WEIGHT = 1.0` (50/50)

Formule (mirror [gradebook.py:17](../GradeBookApp/gradebook.py)) :
```
note_brute = (student_avg + teacher_avg * TEACHER_WEIGHT) / (1 + TEACHER_WEIGHT)
```

### Etape 2 - Redressement statistique (centrage-reduction cohorte)

Calibrage cible cohorte ESGF 2026 :

| Parametre | Valeur 2026 |
|-----------|-------------|
| `target_mean` | **13.0** |
| `target_std` | **2.5** |
| `floor` | **10.0** |

Formule :
```
ajustee = ((brute - moyenne_cohorte) / std_cohorte) * target_std + target_mean
ajustee = max(ajustee, floor)   # plancher 10/20 ESGF (regle 2026-05-28)
```

Resultat clip dans `[floor, 20]` (vs `[0, 20]` ECE). Le plancher 10 reflete la decision : aucun projet soumis et soutenu ne descend sous la moyenne, sauf cas extreme documente.

### Etape 3 - Calibration Option C HL + arbitrage Wheel

Apres redressement, ajustement individuel pour les sujets HL (Haute Liaison) selon validation user 2026-05-28 :

| Sujet | Verdict (review forks) | Note finale validée |
|-------|------------------------|---------------------|
| `SectorMomentum-ETF-Rotation` (f_gueye11) | EXTENSION_MINIME | **12.8** |
| `ZScore`-based strategy | (cf review) | **12.8** |
| `RiskParity` / AllWeather variant | AMELIORATION_REELLE | **13.5** |
| `Wheel-Tech-Simple` (s_kadid) | EXTENSION_MINIME (arbitrage user) | **(cf user)** |

L'arbitrage HL Wheel reste a confirmer explicitement par le user avant generation finale du XLSX v2 (tag `[ASK USER]` actif).

## Verdicts review forks vs baselines (rappel)

Source : [REVIEW_FORKS_AGAINST_BASELINES.md](file:///G:/Mon%20Drive/MyIA/Formation/ESGF/2026/REVIEW_FORKS_AGAINST_BASELINES.md). 10 verdicts qualitatifs informent l'evaluation **technique** (deja capturee dans le peer eval) :

| Verdict | Effet sur note technique |
|---------|--------------------------|
| `PLAGIAT_BRUT` | Note technique tres basse (cf G1 EMA-Cross, G6 SectorMom, G4 Ekouebla clone) |
| `EXTENSION_MINIME` | Note technique moyenne (cf G5 DualMomentum, HL s_kadid, HL f_gueye11) |
| `AMELIORATION_REELLE` | Note technique bonne (cf G3 El Hajji LLMNews, G2 Morel MarkovRegime, G4 Bayiha AdaptiveAssetAllocation) |
| `RECONSTRUCTION_AUTONOME` | Note technique tres bonne (cf G2 Dzolevo MTF Trend) |

Les peer evals etudiants ne **distinguent pas toujours** plagiat brut vs amelioration reelle (manque d'expertise technique pour auditer le code QC). La note prof corrige cela via le verdict baseline-relative.

## Note de groupe

Comme ECE : **tous les membres d'un sous-groupe projet recoivent la meme note**, sauf cas explicite de rattrapage individuel (cf [docs/ece-grading.md](ece-grading.md#regles-d-evaluation)).

## Absence

Absence = 0 sur la cohorte. Pas de plafonnement cache. Sous-groupes solo (1 etudiant) recoivent l'ajustement +3 du bareme `group_size_adjustments` ([gradebook.py:309](../GradeBookApp/gradebook.py)).

## Bonus CC ESGF

Pas de bonus CC pour la cohorte ESGF 2026 : evaluation unique sur le projet final, pas d'integration aux TPs CoursIA contrairement a ECE. Une futur extension possible (bonus PR sur depot commun) reste a discuter avec le user.

## Pipeline scripts G-drive (parallele ECE)

Les scripts vivent dans `G:\Mon Drive\MyIA\Formation\ESGF\2026\grading\` (a creer si absent) :

| Script | Role | Mirror ECE |
|--------|------|------------|
| `esgf_2026_compilation.py` | Config compilation (cohort, calibration, HL adjustments, output path) | `ece_2026_compilation.py` |
| `compile_esgf_2026.py` | Engine compilation peer eval CSV -> XLSX final | `compile_ece_2026.py` |
| `Notes_Finales_ESGF_2026_Compilation.xlsx` | Sortie source-of-truth multi-feuilles | `Notes_Finales_ECE_2026_Compilation.xlsx` |

Difference cle : ESGF prend directement le CSV GForm en entree (pas de fichiers intermediaires multi-epreuves comme ECE Gr01/02/03), car cohorte unique avec 1 projet evalue.

## Etat actuel et reste a faire

| Item | Etat | Owner |
|------|------|-------|
| Peer eval CSV (84 reponses) | RECU 2026-05-27 | (etudiants) |
| Review forks vs baselines (10 verdicts) | COMPLETE 2026-05-19 | po-2024 |
| Calibration Option C (Mean 13.0 / Std 2.5 / Floor 10) | VALIDEE 2026-05-28 | user |
| HL Option C ajustements (SectorMom/ZScore 12.8, RiskParity 13.5) | VALIDEE 2026-05-28 | user |
| HL Wheel (s_kadid) arbitrage final | `[ASK USER]` | user |
| Gr02 Markov 9.90 -> 10.00 (floor policy) | A appliquer dans v2 | po-2024 |
| Generation v2 XLSX validee | TODO | po-2024 |
| Ingestion ESGF intervenant (UI) | TODO | po-2024 / ai-01 |

## Reviews PR etudiantes - rappel CRITIQUE

Comme pour ECE et EPITA-IS, les comments sur PR / commits dans `Trading-Firm-ESGF` QuantConnect Cloud sont **visibles par les etudiants concernes**. Ne JAMAIS poster en commentaire public :
- Sections "Questions pour la soutenance" / "A clarifier au jury" / "Points methodologiques"
- Grilles d'evaluation detaillees / criteres de notation chiffres
- Briefings jury

Le briefing jury / les questions / la grille restent **internes** (G-drive `SOUTENANCE_*_REVIEW.md`, dashboard RooSync, rapport markdown local non-committe).

Voir [.claude/rules/student-pr-reviews.md](../.claude/rules/student-pr-reviews.md) pour le protocole complet (incident 2026-05-17 documente).

## Voir aussi

- [docs/ece-grading.md](ece-grading.md) - Pattern ECE Finance Ing4 (3 groupes, 2 projets, bonus CC)
- [docs/teaching-context.md](teaching-context.md) - Calendrier toutes ecoles, scope par cohorte
- [docs/quantconnect.md](quantconnect.md) - Org QC Trading-Firm-ESGF, MCP qc-mcp, baselines
- [GradeBookApp/README.md](../GradeBookApp/README.md) - Moteur generique
- [.claude/rules/student-pr-reviews.md](../.claude/rules/student-pr-reviews.md) - Anti-fuite jury (HARD)
