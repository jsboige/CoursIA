# Reviews PR etudiantes — detail

Detail de [.claude/rules/student-pr-reviews.md](../../.claude/rules/student-pr-reviews.md). Voir aussi [exercise-example-labeling.md](../../.claude/rules/exercise-example-labeling.md), [pr-review-discipline.md](../../.claude/rules/pr-review-discipline.md).

## Incident fondateur (2026-05-17)

Veille soutenance EPITA-PrCon (18 mai matin). 6 reviews detaillees postees sur PRs #26, #27, #29, #30, #31, #32 avec section "### Questions pour la soutenance" — fuite directe des questions d'oral aux etudiants. Suppression immediate apres alerte user.

## Scope — identifier une PR de TP etudiante

- Depots : `jsboigeECE/*`, `jsboigeEpita/*`, `jsboigeEPF/*`, **`jsboige/CoursIA`** quand auteur etudiant (cas EPITA-IS qui forke).
- Auteur != agent cluster (`myia-*`) ET != staff (jsboige). Branche hors convention `feature/`/`fix/`. Touche TP/exercices.

## Format public autorise

```
Points forts :
- <3 a 5 bullets concrets sur ce qui marche>

Bonne chance pour la soutenance.
```

Signaler factuellement un manque (sans question) : "Le notebook 03 n'est pas finalise." OK. "Comment justifierez-vous le choix X ?" INTERDIT.

## Briefings internes — ou poser

| Format | Usage |
|--------|-------|
| Markdown local non-committe | Brainstorm questions |
| Dashboard RooSync workspace CoursIA | Coordination ai-01 <-> agents notation |
| G drive `Mon Drive\MyIA\Formation\<ecole>\<promo>\Notation\` | Brief jury, grille, questions pre-validees |
| Issue GitHub privee | Suivi process notation |

**Jamais** : commentaire PR sur depot etudiant, issue publique, dashboard partage etudiants, fichier dans depot CoursIA public.

## Cooperation reviewers (HARD)

- Une **seule** review publique breve par PR. Pas de double review (incident 2026-05-17).
- `@clusterManager-Myia` : reviewer principal, review bienveillante uniquement, ne PAS appliquer criteres A-G de [pr-review-discipline.md](../../.claude/rules/pr-review-discipline.md).
- `@jsboige self-bot` : COMMENTED, ne duplique pas.
- Coordination dashboard workspace CoursIA **avant** de commenter en cas de doute.

## Bypass template/CI sur PR etudiante (mandat 2026-05-20)

- Template PR peut rester vide / non coche.
- Checks CI rouges OK (`notebook-execution-required`, `catalog-drift` visent les contributeurs internes).
- Merge ai-01 : `gh auth switch -u jsboige` + `gh pr merge <N> --admin --squash` (admin override bypasse required checks rouges).
- Corriger soi-meme les petits defauts (typo, output manquant) plutot que renvoyer l'etudiant.
- CHANGES_REQUESTED reserve : code qui ne tourne pas du tout, TP hors-sujet, fichier essentiel manquant.

## Reparation d'une fuite deja postee

`gh api -X DELETE repos/<owner>/<repo>/issues/comments/<id>` immediatement. **Le contenu a pu etre lu/notifie par email** — fuite reparee != effacee.

## Anti-patterns observes

- Review detaillee la veille de soutenance "pour aider l'etudiant" → fuite des questions
- "j'ai vu que vous n'avez pas X, le jury pourrait demander..." → briefing jury reformule
- "ce point vaut 3 points" → fuite grille
- Repondre publiquement a question etudiant en livrant la grille

## Precedents (memory feedbacks)

- **2026-04-20** `feedback_commits_solutions_discrets` : titres commits/PRs ne mentionnent PAS "solutions"/"answer"/"leak".
- **2026-04-28** `feedback_public_repo_naming` : noms etudiants + sponsors externes OK, staff ecoles partenaires JAMAIS.
- **2026-04-30** notation par groupe : meme note pour tous, aucun comment public individualise (sauf rattrapage explicite).
