# Tricéphalie — coordinateur, titulaire, secrétaire (et le TROISIÈME dashboard)

**S'applique à** : tous les agents du cluster CoursIA — coordinateur `myia-ai-01:CoursIA`, titulaire `myia-po-2025:CoursIA-2`, secrétaire `myia-po-2026:CoursIA-3`, et les workers `po-*` qui les lisent.

La coordination CoursIA n'est pas un binôme : elle a **trois têtes**, chacune avec sa lane, son skill et son artefact.

| Tête | Lane | Skill | Rôle | Artefact |
|---|---|---|---|---|
| **Coordinateur** | `myia-ai-01:CoursIA` | `coordinate` | merge, clôture, arbitrage, politique de flotte | `workspace-CoursIA` (+ `global`) |
| **Titulaire** | `myia-po-2025:CoursIA-2` | `coordinate-adjoint` | émet les dossiers `[ADJOINT PREFLIGHT]` exact-head que le coordinateur consomme | `workspace-CoursIA-2` |
| **Secrétaire** | `myia-po-2026:CoursIA-3` | `adjoint-secretary` | **HUB DE CIRCULATION** : veille, DMs nominatifs, alertes conflits / quota / runners | **`workspace-CoursIA-3`** |

**Le « secrétariat », c'est `myia-po-2026:CoursIA-3`** — tierce tête, skill `adjoint-secretary`, artefact `workspace-CoursIA-3`. Quand le user ou le coordinateur parle du « secrétariat », du « secrétaire » ou du « troisième dashboard », c'est de cela qu'il s'agit : il n'y a rien à chercher, et ne pas les reconnaître est un défaut de lecture, jamais une ambiguïté.

**Ces clés sont des identités, pas une liste de lecture.** Le tableau ci-dessus dit *qui est qui* ; il ne dit **jamais** quoi lire — voir la section suivante.

## HARD — le tour de coordination ENUMERE les dashboards, il ne les nomme pas

Tout cycle de coordination (adjoint comme coordinateur) :

1. **Draine l'inbox RooSync en premier** (`roosync_messages(action:"inbox", status:"unread")`) : elle porte souvent le **DM nominatif qui change la priorité du cycle**. Mesure fondatrice : un lot nominatif du coordinateur et deux corrections de doctrine ont dormi non lus pendant que deux cycles consécutifs produisaient selon une doctrine périmée.
2. **Enumere les dashboards** — `roosync_dashboard(action:"list")` — puis lit en `section: "all"` **chaque clé dont le `workspace` déclaré est pertinent**, en incluant celles du secrétariat.

**Pourquoi énumérer, et pas nommer** : une liste codée en dur rend **structurellement aveugle** à toute clé qu'elle n'anticipe pas. Mesure fondatrice (#17197) : `workspace-CoursIA (2)`, clé forkée par collision de noms Google Drive, a porté **23 messages vivants** de deux lanes, dont deux PRs débloquées en attente du merge-gate, pendant plusieurs jours sans qu'aucun cycle la voie. Une clé à suffixe ` (N)` dont le `workspace` déclaré **ne porte pas** ce suffixe est une **moitié de la même lane**, pas une lane voisine : la lire, et escalader la réparation (`action:"merge"`).

## Pivot R3 — les deux clés co-egales restent co-egales *à l'intérieur* de la tricéphalie

La R3 de [../../.claude/rules/coordinator-discipline.md](../../.claude/rules/coordinator-discipline.md) (« coordonner CHAQUE lane indépendamment ») parle des **deux dashboards du binôme coordinateur/titulaire** : `workspace-CoursIA` et `workspace-CoursIA-2`. Ces **deux-là sont co-egaux et se lisent ensemble** dans le tour `/coordinate` (le titulaire et le coordinateur partagent la responsabilité de chaque lane `CoursIA` et `CoursIA-2`).

Le **troisième dashboard** — `workspace-CoursIA-3`, le secrétariat — n'est **pas** ajouté à cette liste de lecture binaire :

- il a sa propre logique de tour (DMs nominatifs, alertes conflits/quota/runners), pas le tour `/coordinate` ;
- l'inclure dans la liste R3 forcerait chaque cycle à lire un dashboard dont le tempo (push rapide, souvent sans action requise) ne correspond pas au cycle lent du merge ;
- il se lit **à part**, dans le tour du secrétaire, ou en réaction à un DM nominatif qu'il a posté sur l'inbox.

**En clair** : R3 reste vraie pour les DEUX dashboards co-egaux du binôme coordinateur/titulaire. Ce qui est interdit, c'est d'en faire la **liste de lecture codée en dur** — d'où l'**enumération** par `roosync_dashboard(action:"list")` plutôt qu'une énumération statique. Le secrétaire entre dans cette énumération si et seulement si sa clé apparaît dans le résultat du `list` au moment du cycle, comme n'importe quelle autre clé pertinente — jamais par contrat.

## Le format se rend nominatif — mesuré, pas négociable

| Format rendu au coordinateur | Conversion en merge |
|---|---|
| liste **nominative** (numéros en clair) | **10/10 — 100 %** |
| **cumul** non nommé (« 56 OK B.0 frais ») | 15/53 — 28 % |
| auto-tirage aveugle par le coordinateur | 2/54 — 4 % |

Un compte dit que du travail existe ; **une liste dit lequel merger**. La re-découverte à l'aveugle **périme** en outre les dossiers qu'elle traverse. Le format de rendu pèse plus lourd que le coût unitaire d'un appel GraphQL — et il est gratuit.

## Doctrine du secrétaire (pivot c.88 « HUB DE CIRCULATION »)

Révision user du 2026-09-22 (sessions « fines comme du papier à cigarette »). Avant : 158 PRs attestées pour 10 mergées (**6 %** de conversion) — le secrétaire **augmentait la charge au lieu de la réduire** (le « cycle notaire »). Désormais :

- **Niveau 1** (mode normal) : DM nominatif au coordinateur — top des PRs mergeables les plus anciennes avec diff, auteur, âge et verdict exact-head ; DM au **titulaire** pour les `CHANGES_REQUESTED` de sa lane ; alertes aux porteurs des PRs `CONFLICTING` ; surveillance du quota GraphQL et des runners.
- **Niveau 2** : dossier `[ADJOINT PREFLIGHT]` exact-head **seulement** sur dispatch nominatif reçu dans l'inbox.
- **Niveau 3** (à éviter) : salves de dossiers oldest-first sans demande, PATCH de dossiers périmés.

**Critère de succès, mot pour mot** : « ai-01 ou titulaire peut merger ou travailler sur **plus de PRs à la fin du cycle qu'au début**. Sinon = cycle notaire = inacceptable. »

## Les skills du trio sont sous contrôle de source

`coordinate`, `coordinate-adjoint` et `adjoint-secretary` **se relisent et se corrigent régulièrement, comme du code**, pas seulement quand elles cassent (mandat user 2026-09-21, porté par `coordinate` §« Amélioration continue des skills »). Si une mesure du cycle contredit un skill, le skill se corrige **dans le même cycle**, par PR.

Les trois défauts muets à chercher en priorité dans un skill :

1. une **liste codée en dur** de ce qu'il faut lire (dashboards, lanes, organes) — elle ne voit pas ce qu'elle n'anticipe pas ;
2. une **référence vers une branche** plutôt que `main` — elle pointe un état périmé, et devient muette si la branche disparaît ;
3. un **geste réimplémenté à la main** alors que `scripts/` porte l'organe — une approximation maison est biaisée vers l'accusation.

## Rappels d'émission qui découlent de ce qui précède

- Poster le dossier **EN DERNIER** : toute écriture tierce postérieure le périme (`discussion changed after dossier` = 12 des 32 refus d'un cycle mesuré).
- `BLOCKED` attesté vaut mieux qu'un `READY` forcé : `exit 3` laisse dispatcher depuis le motif.
- Sur un rouge `Scripts Tests (CPU)`, attester `BLOCKED` **en nommant la cause runner** plutôt que de renvoyer la PR à son auteur — il n'a rien à réparer.

## Voir aussi

- [../../.claude/rules/coordinator-discipline.md](../../.claude/rules/coordinator-discipline.md) — autorité et cadence du coordinateur
- [proactive-coordination.md](proactive-coordination.md) — pool global, plancher de production, leçons ancrées
- [../../.claude/rules/lane-claim-protocol.md](../../.claude/rules/lane-claim-protocol.md) — le claim vit sur l'issue
- [variation-protocol.md](variation-protocol.md) — tag `Grain:` et merge-gate
