# Reviews PR etudiantes - anti-fuite questions soutenance

S'applique a **toute review humaine ou bot sur les depots etudiants** : `jsboigeECE/*`, `jsboigeEpita/*`, `jsboigeEPF/*`, et **`jsboige/CoursIA`** quand la PR vient d'un etudiant (cas EPITA-IS qui forke CoursIA).

**Source incident** : 2026-05-17 22:30Z, veille soutenance EPITA-PrCon (18 mai matin). 6 reviews detaillees postees sur PRs #26, #27, #29, #30, #31, #32 avec section "### Questions pour la soutenance" - visibles par les etudiants, fuite directe des questions d'oral. Suppression effectuee immediatement apres alerte user.

## Regle HARD

**JAMAIS** poster comme commentaire de PR ou de commit sur depot etudiant, avant l'epreuve :
- Sections "### Questions pour la soutenance" / "Pour le jury" / "A clarifier au jury"
- Grilles d'evaluation detaillees / criteres de notation chiffres
- "Points methodologiques a verifier" / "Manques a justifier"
- Briefing jury sous forme de checklist
- Toute formulation qui donne a l'etudiant un **avantage indu** en lisant le comment avant l'oral

Test avant `gh pr comment` sur depot etudiant : **"un etudiant qui lit ce commentaire avant l'epreuve, est-ce qu'il y gagne un avantage indu sur ses camarades ?"** Si oui, ne pas poster.

## Reviews publiques autorisees (format)

Sur depot etudiant, les reviews publiques restent **breves et bienveillantes** :

```
Points forts :
- <3 a 5 bullets concrets sur ce qui marche>

Bonne chance pour la soutenance.
```

Pas de "Questions", pas de "A clarifier", pas de "Points methodologiques". Juste les points forts. Si la PR est incomplete, la review peut signaler **factuellement** qu'un point manque sans poser de question (e.g. "Le notebook 03 n'est pas finalise.") - mais sans pose de question qui pourrait servir au jury.

## Briefings internes (formats autorises)

| Format | Usage |
|--------|-------|
| Fichier markdown local non-committe | Brainstorm initial des questions |
| Dashboard RooSync workspace CoursIA | Coordination ai-01 <-> agents de notation |
| G drive `Mon Drive\MyIA\Formation\<ecole>\<promo>\Notation\` | Brief jury, grille, questions pre-validees |
| Issue GitHub privee (jamais sur depot etudiant) | Suivi process notation |

**Jamais** : commentaire PR sur depot etudiant, issue GitHub publique, dashboard partage avec etudiants, fichier dans le depot CoursIA public.

## Coordination plusieurs reviewers sur la meme PR

Si plusieurs agents commentent un meme PR etudiant (ex: `jsboigeEpita` bot breve + ai-01 detaillee) :

1. **Se coordonner avant** via dashboard RooSync workspace CoursIA - decider qui poste quoi
2. **Par defaut** : seul l'agent qui merge poste publiquement (review breve). L'audit/grille ai-01 reste interne
3. Si decouverte d'un comment problematique deja poste : `gh api -X DELETE repos/<owner>/<repo>/issues/comments/<id>` immediatement. **Mais le contenu peut avoir ete deja lu/notifie par email** - une fuite reparee n'est pas effacee, juste rendue non-recuperable au futur lecteur.

## Workflow recommande pre-soutenance

1. ai-01 (ou agent enseignant) prepare grille + questions dans `G:\Mon Drive\...\Notation\`
2. Bot `jsboigeEpita` / `jsboigeECE` poste review breve publique (points forts uniquement)
3. ai-01 garde le brief jury sur dashboard RooSync workspace CoursIA (visibilite agents, pas etudiants)
4. Apres soutenance : compilation des resultats sur G drive + GradeBookApp pipeline (cf [docs/ece-grading.md](../../docs/ece-grading.md))

## Anti-patterns observes

- Poster une review detaillee la veille de la soutenance "pour aider l'etudiant a preparer" -> en pratique, fuite des questions
- Commenter "j'ai vu que vous n'avez pas X, le jury pourrait demander..." -> reformulation du briefing jury
- Mentionner un critere chiffre ("ce point vaut 3 points") -> fuite de la grille
- Repondre publiquement a une question etudiant en livrant la grille ("pour la soutenance, regardez bien tel critere")

## Precedents associes

- **2026-04-20** (`feedback_commits_solutions_discrets`) : les titres de commits/PRs ne doivent PAS mentionner "solutions" / "answer" / "leak". Cette regle etend la prudence aux comments PR.
- **2026-04-28** (`feedback_public_repo_naming`) : sur depot public, OK pour les noms etudiants + sponsors externes (Jared Broad), JAMAIS de mention de staff ecoles partenaires dans issues/PRs/commits. Etend a : etudiants peuvent lire les comments -> rien ne doit leur donner d'avantage premature.
- **2026-04-30** (notation par groupe) : tous les membres du groupe recoivent la meme note. Aucun comment public ne doit individualiser une evaluation (sauf cas rattrapage explicite).
