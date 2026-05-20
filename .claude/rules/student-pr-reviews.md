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

## PRs de TP etudiantes — review bienveillante + bypass CI/template (mandat user 2026-05-20)

Quand les etudiants soumettent leurs PRs de TP (forks de `jsboige/CoursIA` ou comptes etudiants), le standard de review **change** par rapport aux PRs internes du cluster. Source : mandat user 2026-05-20 (afflux PRs TP EPITA-IS).

**Identifier une PR de TP etudiante** : auteur != agent cluster (`myia-*`) ET != staff (jsboige). Branche ne suit pas la convention `feature/`/`fix/`. Touche des notebooks de TP / exercices.

### 1. Reviews bienveillantes (HARD)

- **Corriger soi-meme les petits defauts** (typo, cellule oubliee, output manquant, petit bug) plutot que renvoyer l'etudiant.
- **CHANGES_REQUESTED reserve aux VRAIS problemes** : code qui ne tourne pas du tout, TP hors-sujet, fichier essentiel manquant. **Pas de relance** pour : template incomplet, CI rouge, style, `execution_count` manquant, formatage, scaffolding.
- Format = points forts + signalement **factuel** des manques (cf "Reviews publiques autorisees"). Toujours : **pas de fuite questions soutenance** (regle HARD ci-dessus reste valable).

### 2. Bypass modele de PR + CI (mandat user)

Les etudiants sont freines par le template PR (checklist 5 points) et les checks CI (`notebook-execution-required`, `catalog-drift`). Pour une PR de TP etudiante :

- Le **template peut rester vide / non coche** — ne pas exiger qu'il soit rempli.
- Les **checks CI peuvent etre rouges** — `notebook-execution-required` (exec_count/outputs/C.1) et `catalog-drift` ciblent la discipline des contributeurs internes, **pas les etudiants**.
- **Merge** : ai-01 (coordinateur) merge via `gh auth switch -u jsboige` + `gh pr merge <N> --admin --squash` (l'admin override bypasse les required checks rouges), apres une review bienveillante. Ne pas bloquer un TP correct sur un CI rouge de scaffolding.

### 3. Workflow exercices -> exemples (inchange)

Le workflow pedagogique reste : un exercice resolu/soumis **devient un exemple**, et de **nouveaux exercices sont ajoutes a la suite**. Classification par contenu (cf [exercise-example-labeling.md](exercise-example-labeling.md)). Ne jamais stubber une solution etudiante soumise ni purger les exemples existants.

### 4. Cooperation des 2 bots reviewers (HARD)

Sur une PR etudiante, **@clusterManager-Myia** (reviewer principal) et **@jsboige self-bot** doivent coordonner :

- **Une seule review publique breve** par PR (points forts). Pas de double review redondante ni contradictoire (incident 2026-05-17).
- **clusterManager-Myia** : NE PAS appliquer les criteres CHANGES_REQUESTED A-G de [pr-review-discipline.md](pr-review-discipline.md) aux PRs etudiantes (ils visent les PRs internes/contributeurs). Sur PR etudiante : review bienveillante uniquement.
- **jsboige self-bot** : reste en COMMENTED, ne duplique pas la review de clusterManager-Myia.
- En cas de doute sur qui poste : coordination dashboard workspace CoursIA **avant** de commenter.

## Precedents associes

- **2026-04-20** (`feedback_commits_solutions_discrets`) : les titres de commits/PRs ne doivent PAS mentionner "solutions" / "answer" / "leak". Cette regle etend la prudence aux comments PR.
- **2026-04-28** (`feedback_public_repo_naming`) : sur depot public, OK pour les noms etudiants + sponsors externes (Jared Broad), JAMAIS de mention de staff ecoles partenaires dans issues/PRs/commits. Etend a : etudiants peuvent lire les comments -> rien ne doit leur donner d'avantage premature.
- **2026-04-30** (notation par groupe) : tous les membres du groupe recoivent la meme note. Aucun comment public ne doit individualiser une evaluation (sauf cas rattrapage explicite).
