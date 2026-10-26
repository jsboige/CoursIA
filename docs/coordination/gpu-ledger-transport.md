# Transport git du ledger `gpu-reservation`

Ce document décrit une capacité technique : le transport des observations du ledger, sa cible paramétrable et les garde-fous qui l'entourent. Le [protocole de réservation GPU](gpu-reservation.md) décrit le registre, son utilisation et les gestes manuels ; il n'est pas repris ici.

## Publication sur une branche dédiée

La sous-commande `publish --git` de `scripts/coordination/debt_ledger.py` publie les observations du spool local sur la branche `ops/gpu-ledger`, nom porté par `GIT_LEDGER_BRANCH`. L'écriture effective demande `--emit` ; sans cette option, la commande est un dry-run.

Le transport est en ajout seul : chaque machine publie dans `gpu-reservation/<machine>.jsonl`, avec une ligne par observation. Les lignes existantes sont conservées et les nouvelles enveloppes sont ajoutées ; les observations déjà présentes sont dédupliquées par `observation_id`. Une machine ne peut publier que dans son propre fichier, et le commit est refusé avant poussée s'il touche un autre chemin.

La cible de publication est un paramètre, non une décision attachée au dépôt du projet. L'option `--remote` de l'organe choisit le remote lu et poussé, avec `origin` par défaut ; la garde de lancement expose le même choix par `--gpu-ledger-remote`. L'option `--repo` identifie le checkout utilisé pour les opérations git, tandis que le remote désigne la destination de la branche. Rien ne déduit cette destination de l'URL du dépôt du projet.

## Admission et libération par la garde de lancement

`scripts/ci/run_guarded.py` active la séquence GPU avec `--gpu-entity`. Les options `--gpu-holder` et `--gpu-workload` sont alors requises ; `--gpu-expected-end` borne la réservation, avec une borne par défaut si l'option est absente, et `--gpu-issue` rattache facultativement le hold à une issue. `--gpu-ledger-remote` sélectionne le remote pour la consultation comme pour les publications.

À l'admission, la garde consulte `check_pending`, écrit l'observation `held` avant de lancer l'enfant, puis la publie immédiatement. Elle refuse le lancement si le gate n'autorise pas le device, si l'observation ne peut pas être écrite ou si elle ne peut pas être publiée. Si la publication échoue après l'écriture du `held`, la garde tente de clore cette réservation par un `released`.

Au teardown, la garde écrit l'observation `released` et la publie. Ce chemin couvre la sortie normale, l'arrêt par une garde, l'interruption et les échecs de démarrage après réservation.

## Sources du gate et comportement fail-closed

`debt_ledger.py check_pending` accepte `--source auto`, `--source git` et `--source local`. Le mode `git` lit la branche dédiée ; le mode `local` lit explicitement le snapshot local ; le mode `auto`, utilisé par défaut, tente la lecture git avant d'envisager le cache. Chaque verdict nomme sa source, dans le champ `source` de la sortie JSON et sur la ligne `source=` de la sortie texte.

Une branche distante qui existe mais ne peut pas être lue produit `UNREADABLE` : le gate ne rend pas l'entité libre à partir d'un cache périmé. Un remote dont l'état est inconnu mène au même refus. En mode `auto`, le repli vers le cache local n'a lieu que si `git ls-remote` confirme que la branche n'existe pas sur le remote ; la sortie nomme alors ce repli et sa raison. La décision repose sur le code de retour et la sortie de `ls-remote`, jamais sur l'interprétation du texte d'une erreur.

Si le `fetch` échoue alors que le ref de suivi local de la branche reste lisible, le gate lit ce ref et signale dans `source` que la lecture est potentiellement ancienne. Il ne remplace pas cette lecture git par le cache du snapshot. Par ailleurs, une observation encore en attente dans le spool local produit `UNPOSTED` avant tout verdict sur l'état du device.

La garde de lancement applique une restriction supplémentaire : un verdict `OK_TO_RUN` ou `RELEASED` provenant d'une source non git devient `NON_AUTORITAIRE` et refuse le lancement. Le constat d'absence `NO_OBS` conserve son traitement distinct.

## Capacité technique et autorité déclarée

La déclaration d'autorité reste celle de [gpu-reservation.md](gpu-reservation.md), que cette livraison ne modifie pas : le dashboard reste la référence déclarée de l'usage GPU de la flotte. Le transport, ses paramètres et la provenance explicite des verdicts ajoutent une capacité, pas un changement d'autorité. Le choix technique d'une source de lecture par le gate ne vaut pas arbitrage de gouvernance.

La question de savoir quelle source fait autorité, et où vit l'état vivant publié, reste en attente du sign-off user porté par l'issue [#22456](https://github.com/jsboige/CoursIA/issues/22456).

Quand le canal de messagerie est indisponible, la branche est la seule copie partagée des observations encore lisible entre les machines. C'est la raison d'être du transport, et précisément pourquoi sa déclaration comme source d'autorité demande un arbitrage humain plutôt qu'une déduction depuis son fonctionnement technique.

## Lancement sans la garde

Une lane qui n'utilise pas `run_guarded.py` conserve le geste manuel décrit dans [gpu-reservation.md](gpu-reservation.md) : observation `held` avant le lancement, puis observation `released` à la fin. Le transport ne remplace ni ce protocole ni les autres gardes de lancement qu'il prescrit.
