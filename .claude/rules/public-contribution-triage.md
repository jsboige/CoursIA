# Contributions publiques — triage bienveillant et escalade

S'applique aux issues et Pull Requests ouvertes sur `jsboige/CoursIA` par des contributeurs publics, hors agents internes `myia-*`. Une PR de TP étudiante conserve en plus le régime spécifique de [student-pr-reviews.md](student-pr-reviews.md).

## Règle HARD — le ton ne diminue pas la vérification

Une contribution publique reçoit un accueil **bienveillant, factuel et actionnable**, même lorsqu'elle est incomplète ou incorrecte. Cette règle gouverne le ton et l'accompagnement ; elle ne supprime pas les validations de fond applicables de [pr-review-discipline.md](pr-review-discipline.md).

Avant toute réponse, lire le body complet, tous les commentaires, toutes les reviews et l'artefact ou la source concernés. Ne pas répondre depuis le titre seul.

La première réponse publique :

1. remercie la personne et reformule la demande sans la dénaturer ;
2. indique ce qui a été vérifié firsthand et ce qui reste incertain ;
3. propose une prochaine étape concrète ou l'aide nécessaire ;
4. évite tout jugement sur la personne, toute condescendance et toute réponse abrupte du type « le bot refuse ».

Un défaut issu de la production agentique est reconnu sans être banalisé : le corriger ou le tracker, donner un état honnête, ne pas promettre un délai artificiel. La bienveillance réciproque n'oblige jamais le contributeur à accepter une erreur.

## Escalade obligatoire

Escalader vers le mainteneur humain ou le spécialiste compétent quand la demande implique :

- attribution, licence ou provenance incertaine ;
- secret, sécurité, donnée personnelle ou contenu étudiant ;
- choix pédagogique subjectif ou changement important de périmètre ;
- source inaccessible ou affirmation technique non vérifiable localement ;
- désaccord persistant après une réponse factuelle.

Dire publiquement que le point est escaladé et garder la discussion ouverte. Ne jamais transformer l'escalade en fermeture silencieuse.

## Deux modes de contribution

- **Issue / contribution classique** : aider à localiser, reproduire et sourcer la demande. Une PR est bienvenue mais facultative. Les critères techniques applicables restent ceux de [pr-review-discipline.md](pr-review-discipline.md), formulés avec une aide concrète.
- **Correction volontaire d'un exercice** : ne pas la traiter comme une fuite accidentelle. Appliquer le protocole de conversion, crédit et remplacement de [exercise-example-labeling.md](exercise-example-labeling.md).

## Coordination des agents

Une seule réponse publique porte le triage. Les autres agents se coordonnent sur RooSync et évitent les réponses redondantes ou contradictoires. En cas de doute sur l'identité du flux :

- agent interne `myia-*` → règles internes ordinaires ;
- élève dans le cadre d'un TP → [student-pr-reviews.md](student-pr-reviews.md), plus le protocole exercice → exemple au moment de l'intégration dans CoursIA ;
- autre auteur externe → présente règle.

## Voir aussi

- [../../CONTRIBUTING.md](../../CONTRIBUTING.md) — promesse publique et deux modes de contribution
- [exercise-example-labeling.md](exercise-example-labeling.md) — intégration d'une correction comme exemple guidé
- [student-pr-reviews.md](student-pr-reviews.md) — exception scolaire et anti-fuite jury
- [pr-review-discipline.md](pr-review-discipline.md) — validation de fond
