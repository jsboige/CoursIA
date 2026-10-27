# Transport git du ledger `gpu-reservation`

Ce document décrit une capacité technique : le transport des observations du ledger, sa cible paramétrable et les garde-fous qui l'entourent. Le [protocole de réservation GPU](gpu-reservation.md) décrit le registre, son utilisation et les gestes manuels ; il n'est pas repris ici.

## Publication sur une branche dédiée

La sous-commande `publish --git` de `scripts/coordination/debt_ledger.py` publie les observations du spool local sur la branche `ops/gpu-ledger`, nom porté par `GIT_LEDGER_BRANCH`. L'écriture effective demande `--emit` ; sans cette option, la commande est un dry-run.

Le transport est en ajout seul : chaque machine publie dans `gpu-reservation/<machine>.jsonl`, avec une ligne par observation. Les lignes existantes sont conservées et les nouvelles enveloppes sont ajoutées ; les observations déjà présentes sont dédupliquées par `observation_id`. Une machine ne peut publier que dans son propre fichier, et le commit est refusé avant poussée s'il touche un autre chemin.

Plusieurs lanes d'une même machine écrivent dans le même fichier. Chaque tentative de publication épingle la tête de la branche une seule fois après son `fetch` : le contenu déjà publié, l'arbre du commit et son parent viennent de ce même commit. Si la branche a avancé entre-temps, la poussée n'est pas un fast-forward ; elle est rejetée, et la tentative suivante repart d'un arbre relu. Avant la poussée, le commit est refusé (`GIT_PUBLISH_LOSS`) s'il retire un identifiant présent dans le fichier de son parent ou s'il ne porte pas toutes les observations à publier. Après la poussée, le spool n'est vidé que des identifiants retrouvés dans le commit poussé.

La cible de publication est un paramètre, non une décision attachée au dépôt du projet. L'option `--remote` de l'organe choisit le remote lu et poussé ; la garde de lancement expose le même choix par `--gpu-ledger-remote`. L'option `--repo` identifie le checkout utilisé pour les opérations git, tandis que le remote désigne la destination de la branche. Rien ne déduit cette destination de l'URL du dépôt du projet.

Le **défaut** de ce paramètre désigne le dépôt **privé et dédié** `jsboige/coursia-gpu-ledger` (remote nommé `gpu-ledger`), et non le remote du dépôt de travail — arbitrage du mainteneur du 2026-10-27, rendu sur [#22456](https://github.com/jsboige/CoursIA/issues/22456). L'état GPU de la flotte ne se publie pas dans un dépôt public.

Deux gardes fail-closed encadrent cette cible, et elles vivent dans le code, pas dans une convention de saisie :

- **remote non configuré** → refus nommé `GIT_LEDGER_REMOTE_UNKNOWN`, porteur du geste exact (`git remote add gpu-ledger https://github.com/jsboige/coursia-gpu-ledger.git`). L'organe ne crée pas le remote lui-même : écrire dans un dépôt partagé ne doit pas dépendre d'un effet de bord d'une commande de lecture ou de test. L'authentification passe par le helper `gh` du siège — jamais par un jeton dans une URL git ;
- **cible interdite** → si le remote configuré désigne le dépôt de travail (`jsboige/CoursIA`, public), la publication est refusée par `GIT_LEDGER_FORBIDDEN_TARGET`, et le gate rend `UNREADABLE` sans se replier sur le cache local. Un device ne se libère pas parce que la cible de référence est mal configurée.

Le remote est donc un **prérequis de siège**, à poser une fois : chaque machine qui publie ou lit le registre configure `gpu-ledger` vers le dépôt privé. Tant qu'il n'est pas configuré, l'organe refuse en nommant le geste, au lieu de publier ailleurs.

## Admission et libération par la garde de lancement

`scripts/ci/run_guarded.py` active la séquence GPU avec `--gpu-entity`. Les options `--gpu-holder` et `--gpu-workload` sont alors requises ; `--gpu-expected-end` borne la réservation, avec une borne par défaut si l'option est absente, et `--gpu-issue` rattache facultativement le hold à une issue. `--gpu-ledger-remote` sélectionne le remote pour la consultation comme pour les publications.

À l'admission, la garde consulte `check_pending`, écrit l'observation `held` avant de lancer l'enfant, puis la publie immédiatement. Elle refuse le lancement si le gate n'autorise pas le device, si l'observation ne peut pas être écrite ou si elle ne peut pas être publiée. Si la publication échoue après l'écriture du `held`, la garde tente de clore cette réservation par un `released`.

Au teardown, la garde écrit l'observation `released` et la publie. Ce chemin couvre la sortie normale, l'arrêt par une garde, l'interruption et les échecs de démarrage après réservation.

## Sources du gate et comportement fail-closed

`debt_ledger.py check_pending` accepte `--source auto`, `--source git` et `--source local`. Le mode `git` lit la branche dédiée ; le mode `local` lit explicitement le snapshot local ; le mode `auto`, utilisé par défaut, tente la lecture git avant d'envisager le cache. Chaque verdict nomme sa source, dans le champ `source` de la sortie JSON et sur la ligne `source=` de la sortie texte.

Une branche distante qui existe mais ne peut pas être lue produit `UNREADABLE` : le gate ne rend pas l'entité libre à partir d'un cache périmé. Un remote dont l'état est inconnu mène au même refus. En mode `auto`, le repli vers le cache local n'a lieu que si `git ls-remote` confirme que la branche n'existe pas sur le remote ; la sortie nomme alors ce repli et sa raison. La décision repose sur le code de retour et la sortie de `ls-remote`, jamais sur l'interprétation du texte d'une erreur.

Si le `fetch` échoue alors que le ref de suivi local de la branche reste lisible, le gate rend `UNREADABLE` : ce ref n'est que le dernier état connu de la branche, et un `held` publié depuis par une autre lane n'y figure pas. Le verdict que ce ref porterait est lu pour le diagnostic seulement, nommé dans la raison et dans le champ `stale_ref` de la sortie JSON ; il n'autorise aucun lancement. Par ailleurs, une observation encore en attente dans le spool local produit `UNPOSTED` avant tout verdict sur l'état du device.

La garde de lancement transmet au gate la lane qui demande le device (`--gpu-holder`, passée en `--my-lane`) : seul le tenant d'un `held` reçoit `OK_TO_RUN` dans sa fenêtre, toute autre lane reçoit `HOLD`. Sans lane appelante, un `held` rend toujours `HOLD`. La garde applique aussi une restriction supplémentaire : un verdict `OK_TO_RUN` ou `RELEASED` qui ne provient pas d'une lecture fraîche de la branche (`source` exactement `git`) devient `NON_AUTORITAIRE` et refuse le lancement. Le constat d'absence `NO_OBS` conserve son traitement distinct.

## Capacité technique et autorité déclarée

La question de savoir quelle source fait autorité, et où vit l'état vivant publié, a été **arbitrée** : option (a), le registre des réservations GPU devient la référence d'un dépôt git **privé et dédié** (`jsboige/coursia-gpu-ledger`, branche `ops/gpu-ledger`), le dashboard RooSync n'en étant plus que la copie. L'arbitrage du mainteneur du 2026-10-27 est consigné sur [#22456](https://github.com/jsboige/CoursIA/issues/22456).

La déclaration d'autorité elle-même est celle de [gpu-reservation.md](gpu-reservation.md) ; le transport en est le **moyen**, pas l'arbitrage. Ce que cette livraison change est technique : la cible par défaut de publication, et les deux gardes qui refusent une cible non configurée ou le dépôt de travail public.

Quand le canal de messagerie est indisponible, la branche est la seule copie partagée des observations encore lisible entre les machines. C'est la raison d'être du transport, et la raison pour laquelle son autorité a demandé un arbitrage humain plutôt qu'une déduction depuis son fonctionnement technique — arbitrage rendu.

## Lancement sans la garde

Une lane qui n'utilise pas `run_guarded.py` conserve le geste manuel décrit dans [gpu-reservation.md](gpu-reservation.md) : observation `held` avant le lancement, puis observation `released` à la fin. Le transport ne remplace ni ce protocole ni les autres gardes de lancement qu'il prescrit.
