# Reviews PR etudiantes — anti-fuite questions soutenance

S'applique a **toute review humaine ou bot sur depots etudiants** : `jsboigeECE/*`, `jsboigeEpita/*`, `jsboigeEPF/*`, et `jsboige/CoursIA` quand la PR vient d'un etudiant (cas EPITA-IS qui forke). Scope + format + workflow detaille : [docs/student-pr-reviews-detail.md](../../docs/reference/student-pr-reviews-detail.md).

## Regle HARD — pas de fuite jury

**JAMAIS** poster comme commentaire de PR ou de commit sur depot etudiant, avant l'epreuve :

- Sections "### Questions pour la soutenance" / "Pour le jury" / "A clarifier au jury"
- Grilles d'evaluation detaillees / criteres de notation chiffres
- "Points methodologiques a verifier" / "Manques a justifier"
- Briefing jury sous forme de checklist
- Toute formulation qui donne a l'etudiant un **avantage indu** en lisant le comment avant l'oral

**Test avant `gh pr comment`** : "un etudiant qui lit ce commentaire avant l'epreuve, y gagne-t-il un avantage indu sur ses camarades ?" Si oui, ne pas poster.

## Regle HARD — review bienveillante (mandat 2026-05-20)

Sur PR etudiante : review **breve et bienveillante**, points forts uniquement. NE PAS appliquer les criteres CHANGES_REQUESTED A-G de [pr-review-discipline.md](pr-review-discipline.md) (ils visent les contributeurs internes). CHANGES_REQUESTED reserve aux VRAIS problemes (code qui ne tourne pas du tout, TP hors-sujet, fichier essentiel manquant). Template vide + CI rouges = OK. Merge admin via `gh auth switch -u jsboige`. Format public + bypass + workflow : cf [detail](../../docs/reference/student-pr-reviews-detail.md).

## Regle HARD — un seul reviewer public

`@clusterManager-Myia` (reviewer principal) et `@jsboige self-bot` coordonnent via dashboard workspace CoursIA. Une seule review publique breve par PR. Pas de double review redondante ni contradictoire (incident 2026-05-17).

## Incident reference

2026-05-17 22:30Z, veille soutenance EPITA-PrCon. 6 reviews avec "### Questions pour la soutenance" postees sur PRs etudiantes — fuite directe des questions d'oral.

## Voir aussi

- [docs/student-pr-reviews-detail.md](../../docs/reference/student-pr-reviews-detail.md) — incident, format public, briefings internes, cooperation reviewers, bypass CI, anti-patterns, precedents
- [exercise-example-labeling.md](exercise-example-labeling.md) — workflow exercices → exemples
- [pr-review-discipline.md](pr-review-discipline.md) — NE PAS appliquer criteres A-G a PR etudiante
- [GradeBookApp/configs/README.md](../../GradeBookApp/configs/README.md) — moteur de notation (pipelines par cohorte prives sur GDrive)
