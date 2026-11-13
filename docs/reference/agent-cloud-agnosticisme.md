# Session cloud d'agnosticisme — rôle, circulation et protocole des contributions cloud

> REFERENCE — vivante — dernière révision 2026-11-13

Mandat du mainteneur (2026-09-26) : officialiser le rôle de la session Claude Code qu'il ouvre dans son environnement cloud pour rendre le dépôt **agnostique du type de visiteur**.

Mandat du mainteneur (2026-11-13) : écrire ici le protocole commun à **toutes** les contributions cloud hors flotte — lots, une classe par lot, coût CI, relecture. Il fait l'objet de la dernière section, [Protocole des contributions cloud](#protocole-des-contributions-cloud).

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

Le compte GitHub est partagé avec la flotte : une PR de cette session se reconnaît à **deux marques conjointes**, une branche `claude/*` et la mention `Hors flotte` dans le body. À cette double condition, le garde bloquant du tag `Grain:` l'exempte (#17713, `scripts/ci/variation_tag_required.py`). Une PR = un sujet, livré en lot (voir le [protocole](#protocole-des-contributions-cloud)) ; chaque lot part de `main` à jour.

## Circulation

La session **produit** les PRs ; **la flotte les porte jusqu'au merge**, comme les siennes (mandat du mainteneur : économie de tokens, charge mentale retirée au mainteneur) :

- la session **s'abonne aux événements** de ses PRs (CI, reviews, commentaires) : le suivi ne repose plus sur le mainteneur ;
- l'adjoint prévalide (`[ADJOINT PREFLIGHT]`), ai-01 lit et merge ; `scripts/coordination/merge_ready.py` merge les PRs hors harnais qu'ai-01 a approuvées ;
- **réparation déléguée** : sur un check rouge ou une réserve, la session poste le diagnostic sur la PR (ce qui échoue, pourquoi, correctif proposé) puis ouvre une **issue de réparation** qui renvoie à la PR — le pool d'issues est le canal où les lanes tirent leur travail. Elle ne corrige elle-même que lorsque le correctif est plus court que l'issue ;
- une lane peut rafraîchir la branche (`update-branch`) ou y pousser la correction, en nommant le script et le commit (règle 0 de [proactive-coordination.md](../../.claude/rules/proactive-coordination.md)) ; dès qu'elle y a poussé, elle est la seule à y pousser (voir [Relecture et merge](#relecture-et-merge)) ;
- à chaque tour, la session intègre ce qui a changé — corrections de la flotte, décisions, remède meilleur que le sien — puis enchaîne sur la PR suivante.

## Ce que la session ne fait pas

Merger, fermer une issue, trancher une décision de politique (elle la pose au mainteneur), régénérer le catalogue.

## Protocole des contributions cloud

Ce protocole s'applique à **toute session cloud hors flotte** qui ouvre des PRs sur ce dépôt : la session d'agnosticisme décrite plus haut, le marathon de parité (création en série de jumeaux Python et C# de carnets existants) et les sessions d'audit (relecture critique d'une série, avec constats et corrections courtes). Il dit comment livrer sans engorger la CI de la flotte, et ce que la flotte refait avant le merge. Une session qui arrive sans contexte peut l'appliquer sans lire autre chose ; les liens donnent le détail.

Ce qui est écrit au présent est une règle du dépôt, appliquée aux sessions cloud. Ce qui est marqué **recommandation, en attente d'arbitrage (Q184)** n'est pas encore tranché par le mainteneur : la session peut le suivre, et la flotte ne le lui oppose pas en review.

Les renvois §A et §A bis visent [pr-review-discipline.md](../../.claude/rules/pr-review-discipline.md) ; les renvois §B.0, §C et §F visent le `CLAUDE.md` racine.

### Mesure fondatrice

Le 2026-11-12, chaque PR du marathon de parité déclenchait environ 33 workflows, et le marathon ouvrait une PR toutes les cinq minutes environ. Vers 14:30Z, environ 700 runs en file venaient de 21 branches `claude/marathon2-*`, et une PR de la flotte poussée depuis une heure n'avait démarré aucun check. À 21:15Z, 50 PRs du marathon étaient ouvertes, une seule avait été mergée en 24 h, et le dernier `PR gate` de 37 d'entre elles avait été annulé. La CI s'est engorgée pour toute la flotte. Mesures et suite : #25510.

### Lots

**Le coût d'une PR se paie par PR, pas par ligne** (§A bis de [pr-review-discipline.md](../../.claude/rules/pr-review-discipline.md)) : chaque PR déclenche la CI, une lecture du coordinateur et un merge. Une session cloud livre donc par **lots**, et non carnet par carnet.

- **Un lot tient dans une série ou une sous-série**, dans une seule PR. C'est le plafond de la fournée homogène (§A).
- **Une PR trop fine ne s'ouvre pas seule** (seuil de §A bis), sauf urgence CI ou correctif bloquant : elle attend son lot. Un constat petit et local s'écrit en une ligne dans l'issue de la série, pas dans une issue neuve.
- **Corrections mécaniques** (un fixer déterministe, un organe qui mesure la classe) : le lot peut couvrir la série entière, sans seuil de taille (§A, fournée homogène).
- **Créations et réécritures** (jumeau, section neuve, carnet neuf) : elles ne sortent pas d'un fixer déterministe, donc les seuils de taille de §A s'appliquent (fichiers, lignes hors carnets, fonctionnalités annoncées, domaines) : au-delà, la PR se scinde. Une PR de jumeau du marathon touchait au moins cinq fichiers (deux carnets, le README de la série, le descripteur de paire, une ou plusieurs attestations de parité) : un lot de jumeaux atteint donc vite le seuil de fichiers de §A.
- **Un README de série par lot.** Sur #26279, l'organe de collision de chemins a relevé six PRs ouvertes qui modifiaient le même `README.md` de série : chaque merge exposait les cinq autres à un conflit. Grouper les carnets d'une série dans un lot, c'est éditer ce README une seule fois.

**Recommandation, en attente d'arbitrage (Q184)** :

- regrouper les créations d'une même série en un lot, sous les seuils de §A, plutôt que d'ouvrir une PR par carnet ;
- traiter un lot de créations d'une même classe (par exemple, les jumeaux d'une série) comme une fournée homogène, avec une série pour plafond, le body nommant la méthode à la place du fixer. Aujourd'hui, §A réserve cette exemption aux fixers déterministes ;
- n'ouvrir le lot suivant que lorsque les checks du lot précédent sont agrégés, c'est-à-dire quand son `PR gate` a rendu un verdict. Le mainteneur a aussi demandé, le 2026-11-12, que la CI soit rendue capable d'encaisser les arrivées : la cadence ne se règle pas seulement côté session.

### Une classe par lot

- Un lot porte **une seule classe** : une seule correction mécanique, ou un seul type de création.
- Pour une correction mécanique, le body nomme le **fixer**, l'**organe** qui vérifie la classe, et la **sortie de l'organe avant et après** (§A).
- Une seconde classe, ou une retouche à la main dans un lot mécanique, fait tomber l'exemption : les seuils de §A s'appliquent de nouveau.
- Un défaut d'une autre classe, vu en passant, ne s'ajoute pas au lot. Il va dans le lot de sa classe, ou en une ligne dans l'issue de la série.

### Coût CI

Tant que la bascule de #25510 (phase P4) n'est pas faite, les suites lourdes tournent **à chaque push** de chaque PR. Le lot quotidien de #25510, qui passe quatre fois par jour sur l'arbre fusionné avec `main`, tourne pour l'instant en ombre, à côté ([slow-lane.md](../ci/slow-lane.md)). Après la bascule, les suites lourdes passeront au lot, mais les gardes légers resteront à chaque push : le coût restera par PR et par push.

| Geste sur une PR ouverte | CI | Plancher DWELL (120 min) | Approbation du coordinateur |
|---|---|---|---|
| Pousser un commit de contenu | tous les workflows, de nouveau | ré-armé | périmée : relecture à refaire |
| Rebase puis force-push | tous les workflows, de nouveau | ré-armé | périmée |
| Fusion de `main` avec un conflit résolu | tous les workflows, de nouveau | ré-armé | périmée |
| `update-branch` sans conflit | tous les workflows, de nouveau | inchangé | conservée |
| Rejouer une jambe (`gh run rerun <run> --job <job>`) | une seule jambe | inchangé | conservée |

Sources : [git-workflow.md](../../.claude/rules/git-workflow.md) et [git-workflow-detail.md §4](git-workflow-detail.md#4-dwell--pourquoi-update-branch-ne-re-arme-plus-le-plancher-16962) pour le plancher ; `scripts/coordination/merge_ready.py` pour l'approbation, qui couvre la tête lue ou une tête qui n'en diffère que par des rafraîchissements de base prouvés sans contenu. Un `update-branch` est donc gratuit pour le plancher, pas pour la CI.

D'où la forme qui coûte le moins :

- **Le lot est fini avant le premier push** : exécution, vérifications locales, body. Le premier push ouvre la facture.
- **Un seul push par lot, puis un par réponse.** Les retouches se regroupent en local, puis partent ensemble ; une réponse à une réserve regroupe tout ce qui est connu à cet instant. Une rafale de petits commits paie la CI à chaque push et ré-arme le plancher à chaque fois.
- **Une PR ouverte ne se rebase pas.** La fusion de `main` revient à la flotte (`update-branch`, ou résolution de conflit).
- **Un rouge se lit avant de se corriger.** `python scripts/check_run_state.py --pr <N>` lit l'état à la source. Un rouge d'infrastructure, ou un rouge déjà présent sur `main`, ne se corrige pas par un push : la jambe se rejoue, ou la flotte rafraîchit la branche une fois `main` réparé.
- **Une branche par lot.** Le checkout complet (`fetch-depth: 0`) tire toutes les branches du dépôt : chaque branche de plus alourdit le checkout des jambes qui l'emploient encore (#25510).

### Identité et chevauchement

- **Branche `claude/<sujet>`** et chaîne exacte **`Hors flotte`** dans le body : les deux ensemble exemptent la PR du tag `Grain:` (#17713). L'une sans l'autre ne suffit pas.
- **Jamais de push sur `main`** : toute contribution passe par une PR.
- **Pas de `[CLAIMED]`, pas de tag `Grain:`, pas de dashboard** (CLAUDE.md, « À qui ce fichier s'adresse »).
- **Avant de commencer un lot**, vérifier que personne n'y travaille déjà :

```bash
gh issue view <N> --comments                                                    # l'issue en entier : body, puis tous les commentaires
python scripts/check_lane_claim.py <N> --lane hors-flotte:cloud                 # exit 1 : une lane de la flotte tient l'issue
python scripts/check_lane_claim.py --lane hors-flotte:cloud --open-prs-on '<dossier de la série>/**'   # PRs ouvertes sur les mêmes fichiers
```

Si une lane de la flotte tient l'issue, ou si une PR ouverte touche les mêmes fichiers, la session prend une autre issue ou une autre série. Les claims de plus de 48 h sont signalés comme périmés et ne bloquent pas ([lane-claim-protocol.md](../../.claude/rules/lane-claim-protocol.md)).

### Ce que la flotte reprend avant le merge

La session ne dispose ni de l'environnement canonique de la flotte, ni de ses ressources. La flotte fait donc, avant tout merge :

- **Ré-exécuter les carnets dans l'environnement canonique** : les versions de la flotte (Python et ses bibliothèques, .NET), la culture fr-FR de ses machines, les noyaux Lean, le GPU et les clés d'API (§C.2, §F). Les sorties d'une cellule dont la source n'a pas changé doivent rester celles de `main` : `python scripts/notebook_tools/check_kernel_drift.py origin/main` le vérifie.
- **Attester la parité des jumeaux** à la tête, après cette ré-exécution : `python scripts/notebook_tools/check_twin_parity.py --pair "<paire>"`.
- **Archiver les publications citées** dans la bibliographie partagée, qui n'est pas accessible depuis le cloud ([bibliography-hygiene.md](../../.claude/rules/bibliography-hygiene.md)). La session cite dans le body chaque publication utilisée, avec un identifiant stable (DOI, arXiv, ISBN). Elle n'attribue à une publication que ce qu'elle a lu dans le texte, jamais un souvenir.
- **Fusionner `main`** dans la branche, et aligner la prose sur les sorties ré-exécutées.

Le body dit **sans détour ce qui n'a pas été exécuté, et pourquoi**. C'est une information pour la reprise, jamais un état accepté au merge (§C.2, §F). Une sortie de repli (clé, outil ou GPU absent) ne remplace pas une sortie réelle : la session laisse alors les sorties de `main` en place et le dit.

Exemple de reprise (#26274, jumeau C# d'un carnet de comparaison de modèles) : la flotte a fusionné `main`, ré-exécuté les deux carnets sous l'environnement canonique, et fixé la culture du C# pour tous les threads (`DefaultThreadCurrentCulture`, et pas seulement `CurrentCulture`) — sous une machine fr-FR, les sorties prenaient la virgule décimale à partir de la cinquième cellule. Elle a aussi aligné la prose sur les sorties, corrigé deux références, archivé les publications et refait l'attestation de parité. Chacun de ces gestes, fait par la session avant le premier push, est un aller-retour de moins.

### Relecture et merge

La flotte porte la PR jusqu'au merge (voir [Circulation](#circulation)), dans cet ordre :

1. l'adjoint (le titulaire `myia-po-2025:CoursIA-2`) peut pré-lire la PR et poster un dossier, que le coordinateur consulte ;
2. le coordinateur (`myia-ai-01`) lit le diff et **approuve à la tête exacte** ;
3. l'organe B.0 (`python scripts/check_unaddressed_nits.py <N>`) rend 0 : aucune réserve marquée ne reste sans levée ;
4. les tests d'intégrité tournent sur l'arbre fusionné avec `main`, et la PR est `mergeable_state: clean` ;
5. `scripts/coordination/merge_ready.py` merge une PR hors harnais approuvée ; une PR de harnais (`.claude/`, `CLAUDE.md`, `.github/`) est mergée à la main par le coordinateur.

Ce que la session en retient :

- **Une réserve qui tient le merge porte un marqueur reconnu** : préfixe de verdict ou glyphe de sévérité ([pr-review-discipline.md](../../.claude/rules/pr-review-discipline.md)). La session lit chaque réserve marquée et y répond par une phrase sur la PR, qui la nomme et dit ce qui a été fait (avec le commit) ou pourquoi elle est refusée. Pour citer un marqueur sans recréer une réserve, elle l'encage entre backticks (#17071).
- **Cette phrase ne lève pas la réserve d'un tiers.** La session écrit sous le login partagé, et sous ce login seul le coordinateur lève une réserve par une phrase (CLAUDE.md §B.0).
- **Un commentaire de diagnostic** porte en première ligne `[ACTION]`, `[DIAG]` ou `[ASK]` ([pr-review-discipline.md](../../.claude/rules/pr-review-discipline.md)). Un diagnostic sans action attachée va de préférence dans l'issue de réparation (voir [Circulation](#circulation)).
- **Dès qu'une lane de la flotte a poussé sur une branche `claude/*`, elle en est la seule manipulatrice : la session n'y pousse plus.** Ce qu'elle voudrait changer, elle l'écrit sur la PR. Une réécriture de sa part (rebase, force-push) effacerait les commits de la flotte, et [git-workflow.md](../../.claude/rules/git-workflow.md) interdit le force-push sur une branche que deux agents manipulent.

### Body d'un lot

Le body minimal d'un lot porte, dans cet ordre :

```markdown
Hors flotte — <session : agnosticisme, marathon de parité, audit>.

Classe : <la classe unique du lot>. Fixer ou méthode : <commande ou description>.
Organe : <commande> — avant : <sortie>, après : <sortie>.

Carnets :
- `<chemin>` : <ce qui change>

Environnement d'exécution : <OS, versions de Python et de .NET, culture>.
Exécutés : <liste>. Non exécutés : <liste, et pourquoi>.

Reste à la flotte : <ré-exécution canonique, attestation de parité, publications à archiver (avec DOI ou arXiv), fusion de main>.

See #<issue servie>
Closes #<issue>
```

`Closes #N` s'écrit sur sa propre ligne, et seulement si **tous** les critères de l'issue sont remplis ; une livraison partielle s'écrit `See #N` ([git-workflow.md](../../.claude/rules/git-workflow.md)).

### Avant d'ouvrir un lot

- [ ] L'issue servie est lue en entier ; aucune lane de la flotte ne la tient ; aucune PR ouverte ne touche les mêmes fichiers.
- [ ] Le lot tient dans une série ou une sous-série, et porte une seule classe.
- [ ] Correction mécanique : fixer et organe nommés, sortie de l'organe avant et après dans le body. Création : sous les seuils de taille de §A.
- [ ] Le diff n'est pas sous le seuil de §A bis, sinon il rejoint un lot.
- [ ] Chaque carnet dont la source a changé est ré-exécuté ; aucun autre carnet n'est committé (§C.2, §C.3).
- [ ] Aucune erreur volontaire dans un stub (§C.1), aucun secret, aucun emoji ; aucune sortie de repli à la place d'une sortie réelle.
- [ ] Les publications citées sont lues dans leur texte et listées dans le body avec leur identifiant.
- [ ] Le body porte `Hors flotte`, la classe, les carnets, l'environnement, ce qui n'a pas été exécuté et pourquoi, ce qui reste à la flotte, et `See #N` (`Closes #N` seulement si tous les critères sont tenus).
- [ ] La branche est `claude/<sujet>`, partie de `main` à jour (jamais de la branche du lot précédent), et le lot part en un seul push.
- [ ] Recommandation, en attente d'arbitrage (Q184) : le `PR gate` du lot précédent a rendu son verdict.
