# Session cloud d'agnosticisme — rôle et circulation

Mandat du mainteneur (2026-09-26) : officialiser le rôle de la session Claude Code qu'il ouvre dans son environnement cloud pour rendre le dépôt **agnostique du type de visiteur**.

## Qui

Une session Claude Code ouverte par le mainteneur dans son environnement cloud : conteneur Linux éphémère, clone vierge du dépôt, sans GPU. Elle **ne fait pas partie de la flotte** : pas de RooSync, pas de dashboard, pas d'inbox, pas de `[CLAIMED]`, pas de tag `Grain:` (CLAUDE.md, « À qui ce fichier s'adresse »).

## Mission

Garantir qu'un visiteur quelconque — étudiant sous Linux, macOS ou Windows sans l'environnement de la flotte, contributeur externe, lecteur qui clone pour la première fois — peut installer l'environnement documenté et exécuter les notebooks sans adapter un script à la main. C'est le premier critère d'acceptation de l'EPIC [#10643](https://github.com/jsboige/CoursIA/issues/10643).

La flotte travaille sur des machines dont l'environnement a été réparé au fil du temps : les défauts qu'un clone vierge révèle — dépendance non déclarée, commande d'installation qui n'existe plus, chemin ou bibliothèque native propre à Windows, sous-module non initialisé — lui sont structurellement invisibles. La valeur de cette session tient à la fraîcheur de son environnement.

## Méthode

1. Rejouer **à la lettre** le parcours documenté : README (« Installation rapide »), [setup-linux-macos.md](setup-linux-macos.md), scripts de `scripts/environment/`, `requirements.txt` de la série, sous-modules et leurs scripts de build.
2. Exécuter les notebooks par l'outil du dépôt (`python scripts/notebook_tools/notebook_tools.py execute <nb> --json`), dans un **worktree jetable** : aucune sortie d'audit n'est committée.
3. Requalifier chaque échec à la main (cellule fautive, sortie committée, relance isolée) avant de le classer : défaut, non reproduit, ou non conclu.
4. Corriger ce qui relève de CoursIA ou de ses sous-modules, avec la mesure avant/après dans le body de la PR ; un notebook n'est committé que si sa source est modifiée (C.3), et alors ré-exécuté (C.2).
5. Tracer le reste — défauts ouverts, décisions à prendre, portée non mesurée — dans l'issue de suivi [#17654](https://github.com/jsboige/CoursIA/issues/17654).

Les sous-modules se modifient depuis le dépôt principal ([submodule-maintenance.md](../../.claude/rules/submodule-maintenance.md), R2 et R7) : commit **dans** le sous-module, push, PR sur son dépôt, puis bump du pointeur dans CoursIA.

## Identification des PRs

Le compte GitHub est partagé avec la flotte : une PR de cette session se reconnaît à **deux marques conjointes**, une branche `claude/*` et la mention `Hors flotte` dans le body. À cette double condition, le garde bloquant du tag `Grain:` l'exempte (#17713, `scripts/ci/variation_tag_required.py`). Une PR = un sujet ; la session repart de `main` après chaque merge.

## Circulation

Pour économiser les tokens de la session, **la flotte porte ses PRs jusqu'au merge**, comme les siennes :

- l'adjoint prévalide (`[ADJOINT PREFLIGHT]`), ai-01 merge ; `scripts/coordination/merge_ready.py` s'applique aux PRs hors harnais ;
- une lane peut rafraîchir la branche (`update-branch`) ou y pousser une correction mécanique, en nommant le script et le commit (règle 0 de [proactive-coordination.md](../../.claude/rules/proactive-coordination.md)) ;
- la session ne surveille pas ses PRs en continu : elle relit leur état au tour suivant, intègre ce qui a changé — corrections de la flotte, décisions, remède meilleur que le sien — puis enchaîne sur la PR suivante.

## Ce que la session ne fait pas

Merger, fermer une issue, trancher une décision de politique (elle la pose au mainteneur), régénérer le catalogue.
