# Politique d'accès GitHub — comptes, Apps et quotas

**Source :** #27124 (conception, arbitrage user 17/11) · parent #17315 (saturation du quota GraphQL, incident du 21/09).
**Statut :** PROPOSITION. Ce document conçoit la politique ; il n'accomplit aucun geste d'administration. Les points qui engagent le mainteneur sont listés en §6 et restent au registre des questions user jusqu'à tranchage.

## 1. État mesuré — les identités qui existent aujourd'hui

| Identité | Nature | Usage réel mesuré |
|---|---|---|
| `jsboige` | compte partagé | **toute l'écriture courante des workers** (PR, commentaires, push) — toutes les lanes, toutes les machines ; **exception mesurée** : reviews et fusions du coordinateur sous son identité propre `myia-ai-01`, et levées de réserves de bot par l'adjoint via l'App `coursia-lane-po-2025[bot]` (Q185) |
| comptes par machine (ex. `myia-po-2023`) | comptes distribués aux sièges | lecture/navigation locale ; écriture sur les dépôts où le siège a une identité propre ; recommandation registre en cours = rester sur `jsboige` pour CoursIA (option (a), plus courte) |
| GitHub Apps du dépôt | apps (dependabot, clusterManager-Myia, lane-bots tel `coursia-lane-po-2025[bot]`) | CI/workflows, bots reviewers, levées de réserves de bot (Q185) |

Le constat fondateur (#27124) : **on a les deux** — comptes par machine distribués **et** Apps désignées comme le « vrai bon geste » par le coordinateur. L'enjeu n'est pas d'empiler, mais de décider **qui utilise quoi, dans quel but, avec quelle conséquence sur le quota partagé**.

## 2. Coût d'appel par organe — le raisonnement de quota

Faits mesurés (source #17315, sauf mention) :

| Organe | Coût par appel | Surface |
|---|---|---|
| Gate de prévalidation (`check_adjoint_prevalidation.py`) | **3+ opérations** (`_pr_metadata` ×2 + `reviewThreads` paginé) | GraphQL → REST partiellement migré par #19966 ; `reviewThreads` reste GraphQL sans équivalent REST |
| Organe B.0 (`check_unaddressed_nits.py`) | reviews + comments + **threads inline paginés** (3e surface) | `reviewThreads` GraphQL sans équivalent REST (`scripts/check_unaddressed_nits.py:5141`) |
| Tapis rapide (`tapis_rapide.py`) | **13 appels** par tirage | REST (mesuré 17/11 16:22Z, affiché par l'organe) |
| Folds légers (`check_run_state.py`) | 1–2 appels par PR | REST |

**L'incident qui fait foi** (21/09) : une passe de 200 appels de gate a rendu **110 `rc=2` consécutifs** — organe injoignable une heure **pour toute la flotte**, PR #17206 perdue au passage. Et la mesure clé : ce jour-là, **469 dossiers produits pour 24 consommés** — c'est la **péremption** qui brûle le quota, pas le coût unitaire du gate. Deux correctifs déjà livrés réduisent le risque à la source : #19966 (gate 100 % REST côté `_pr_metadata`, threads batchés) et le passage au **dossier à la demande** (05/11) qui supprime la production en masse de dossiers.

Piège d'instrument (rappel #17315) : `gh api rate_limit` rendait 5000/5000 **au moment du rejet** — le compteur REST n'est jamais une preuve d'autorisation ; seul l'appel qui passe en est une. Les quotas GitHub Apps sont **par installation** et donc structurellement séparés de ceux des comptes (documenté GitHub) : c'est la propriété que la politique exploite ci-dessous.

## 3. L'arbre des usages (décision recommandée par branche)

| Usage | Aujourd'hui | **Cible recommandée** | Raison de quota |
|---|---|---|---|
| Lecture / navigation (tapis, folds, `gh issue view`) | compte du siège | **compte du siège** — inchangé | coût unitaire 1 appel REST ; 13 appels/tirage très en dessous du plafond ; aucune écriture → aucun risque d'attribution |
| Écriture courante (PR, commentaires, reviews, push) | **état observé** : `jsboige` partagé pour l'écriture des workers ; le coordinateur review et fusionne sous `myia-ai-01` | **`jsboige` partagé** — inchangé (arbitrage (a) du registre) ; l'exception coordinateur reste : reviews et fusions sous identité propre | les gardes d'auteur (B.0, dossiers, mémoire `gh-auth-race-pin-token`) épingle `jsboige` ; une bascule fabrique des mésattributions (un artefact écrit sous un compte que les gardes n'attendent pas = dossier refusé sans cause visible) ; le quota d'écriture n'est **pas** le goulot mesuré |
| **Passes de masse** (sweeps de PRs, census, audits 100+ issues) | `jsboige` partagé pour les lectures unitaires ; le **mode lecture** existe (§3.1) et alimente la couche de lecture partagée | **GitHub App lecture-seule dédiée** | la seule classe d'usage **mesurée** ayant tué le gate flotte-entière (110 `rc=2`) ; une App = quota installation **séparé** + permissions bornées lecture ; un second compte humain ajouterait une identité d'écriture à gouverner pour un usage qui n'écrit pas |
| CI / workflows | Apps bots existantes | **inchangé** | quotas par App déjà séparés ; rien à gagner à y toucher |
| Gates (B.0, prévalidation) | `jsboige` | **`jsboige` + plafond organisationnel** | le goulot mesuré = péremption (469/24), pas l'identité ; #19966 a réduit le coût unitaire, le dossier-à-la-demande a supprimé la production en masse ; changer d'identité ici déplacerait le problème sans le réduire |
| Attribution (qui a fait quoi) | tag `lane <machine:workspace>` (bodies/claims) | **inchangé + trailer de commit optionnel** (§5) | seul canal fiable sous login partagé |

### 3.1 Le mode lecture — une App par lane, portée par `gh_identity`

Le point d'entrée est **unique** : `scripts/ci/gh_identity.py`.

- `lecture_token()` — forge le jeton d'installation de l'App **de la lane** (le slug est dérivé du nom de la machine ; la clé privée vient du trousseau partagé, jamais d'un fichier versionné ni de l'environnement). Le jeton vit en mémoire : il n'est **jamais affiché** et **jamais écrit**. L'absence d'App est mémorisée — l'organe ne rouvre pas le coffre à chaque appel.
- `read_env()` — copie de l'environnement dans laquelle `GH_TOKEN` porte le jeton App : la forme qui convient à un sous-processus (un appel `gh` ponctuel).
- `lecture()` — contexte qui pose `GH_TOKEN` pendant un bloc et **restaure** l'environnement à la sortie : la forme qui convient à une séquence d'appels.

`scripts/coordination/gh_bulk.py` est la **couche de lecture partagée** : ses appels `gh` sortent désormais sous le jeton App quand il existe. C'est par elle que le tapis rapide et la couverture de visite consomment le seau d'installation.

**L'écriture n'est pas concernée.** La résolution du jeton d'écriture (`post_dossier.resolve_write_token()`) isole `jsboige` en **retirant** `GH_TOKEN` de l'environnement qu'elle construit : un jeton App ne peut donc pas se substituer à l'écriture par accident. C'est pourquoi le jeton App est posé **par appel** ou **par bloc**, jamais dans l'environnement global d'un processus qui écrit aussi.

**Mesure** (24/11, `myia-ai-01`) : une passe de lecture faite à travers la couche partagée fait baisser **le compteur de l'App d'exactement une unité** (`core` 4998 → 4997) et laisse le seau `jsboige` inchangé par cette passe. La lecture est donc bien facturée à l'installation, et non au compte partagé.

**Limite connue** : un jeton d'installation ne peut pas appeler `/user` (GitHub répond `Resource not accessible by integration`). Un organe qui a besoin de l'identité du porteur **ne doit pas** tourner en mode lecture.

## 4. Qui révoque quoi

| Identité | Qui révoque | Temps mesurable | Portée de la révocation |
|---|---|---|---|
| Compte du siège (token local) | mainteneur, sur le siège | **minutes** (retrait du token local — confinement du siège, **pas** une révocation : voir ci-dessous) | 1 siège |
| GitHub App (passe de masse) | owner du dépôt, Settings > Developer settings | **minutes** | l'usage entier de l'App, sans toucher aucun siège |
| `jsboige` partagé | mainteneur, GitHub | **heures** (rotation + re-provision des N sièges, gel des merges pendant l'opération) | **toute la flotte** — dernier recours uniquement |

**Retrait local ≠ révocation ≠ vérification.** Sortir le jeton du poste est un **confinement** : ce siège cesse de le servir, mais le jeton **reste valide chez GitHub** — toute copie déjà exfiltrée resterait utilisable. La **révocation côté émetteur** (rotation ou suppression du jeton sur GitHub) est la seule qui invalide toutes les copies ; pour un compte de siège, elle se fait **en sus** du retrait local, sans toucher les autres sièges. La **vérification** qu'un retrait est effectif passe par un appel authentifié qui doit **échouer** (§2 : l'appel qui passe fait foi) — sans jamais publier de valeur de jeton pour la vérifier.

**Corollaire de coût de révocation :** les pouvoirs étendus (admin du dépôt, accès aux secrets, force-push) ne vivent **jamais** sur le compte partagé — une révocation flotte-entière est le scénario le plus cher, il ne doit exister que pour l'identité la moins dangereuse (écriture courante sous protection de branche, déjà `allow_force_pushes: false`).

## 5. Attribution — la signature `machine:workspace`

Sous login partagé, l'attribution ne peut pas venir du compte GitHub : elle vient des **marqueurs de lane**.

- **Canal existant et obligatoire** : le tag `Grain: <TIER>/<GENRE> — lane <machine:workspace> — prev: …` en première ligne de tout `[CLAIMED]` et de tout body de PR ([variation-protocol.md](../../.claude/rules/variation-protocol.md)), et la clause `lane <machine:workspace>` des marqueurs de claim ([lane-claim-protocol.md](../../.claude/rules/lane-claim-protocol.md)). **Ce document les désigne comme le canal d'attribution canonique de la flotte.**
- **Option proposée (à trancher, §6)** : trailer git `Lane: <machine:workspace>` dans chaque commit, posé par hook — rend l'attribution lisible dans `git log` sans ouvrir les bodies. Changement normatif (nouvelle obligation) → PR de gouvernance + sign-off user si GO.

## 6. Points à trancher par le mainteneur

1. **App lecture-seule pour les passes de masse** : GO / NO-GO. Si GO, issue fille = création de l'App + branchement des sweeps existants (`check_unaddressed_nits.py --audit`, census) sur son token via le trousseau partagé. — **GO technique posé par le coordinateur** (dispatch du 24/11) : les Apps par lane existent déjà (`coursia-lane-<lane>`) et le mode lecture est en service (§3.1) ; le basculement des derniers organes reste à faire, et reste réversible — il suffit de ne pas installer le jeton App.
2. **Trailer `Lane:` dans les commits** : GO / NO-GO (normatif → sign-off).
3. **Écriture courante** : ce document recommande le statu quo (`jsboige`) — valide ou infirmé en une ligne, ce qui clôt aussi l'entrée (a)/(b) ouverte au registre.

## 7. Plan de migration mesuré

| Phase | Contenu | Prérequis | Ce qui change concrètement |
|---|---|---|---|
| P0 | **ce document** | — | rien : la politique est écrite, les arbitrages sont posés |
| P1 | App lecture-seule (passe de masse) | GO §6.1 — **posé** (dispatch du 24/11) | **en cours** : le mode lecture existe (`gh_identity`, §3.1) et la couche de lecture partagée (`gh_bulk`) est branchée — le tapis rapide et la couverture de visite consomment le seau d'installation ; **restent à brancher** les organes qui appellent `gh` en propre (`belt_queues`, `check_lane_claim` en lot, `approved_without_dossier`, sweep B.0). Objectif inchangé : les sweeps basculent sur un quota installation séparé ; `jsboige` ne paie plus les fan-out |
| P2 | trailer `Lane:` | GO §6.2 | hook commit-msg + une ligne au §E du CLAUDE.md (PR gouvernance) |
| — | **Ce qui reste sur `jsboige`** : toute l'écriture courante des workers et les gates par PR (le coordinateur review et fusionne sous `myia-ai-01`, §1) | — | inchangé — mesuré non-goulot après #19966 et le dossier-à-la-demande |

Aucun secret ne transite par ce document ni par ses issues filles : toute identité de service vit dans le trousseau partagé (`MyIA-Keys`) ou dans une App, jamais dans un fichier versionné ([secrets-hygiene.md](../../.claude/rules/secrets-hygiene.md)).

## Voir aussi

- #17315 — le parent : saturation GraphQL, tableau des coûts fichier:ligne, census des dossiers
- #19966 — correctif de coût livré (gate 100 % REST côté `_pr_metadata`, threads batchés)
- [lane-claim-protocol.md](../../.claude/rules/lane-claim-protocol.md) — la prémisse « une lane = un agent actif » que la révocation §4 préserve
- [secrets-hygiene.md](../../.claude/rules/secrets-hygiene.md) — trousseau partagé, jamais de fichier versionné
