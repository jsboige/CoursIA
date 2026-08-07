# Quand la vérification est verte et le système est cassé

Étude de cas — huit incidents datés, un seul motif.

Cette note ne raconte pas des bugs. Elle raconte huit occasions où **un agent a déclaré un état de système sur la foi d'une vérification qui passait**, alors que cet état était faux. Les quatre premiers viennent d'un projet client (avril 2026) ; les quatre derniers sont survenus dans ce dépôt, en août 2026, et sont vérifiables ligne par ligne.

Le motif est identique dans les huit cas, et il ne s'améliore pas en ajoutant des tests.

---

## Le motif

Une vérification automatique mesure ce qu'elle mesure. Un agent rapporte **ce qu'elle a mesuré** comme s'il s'agissait de **l'état du système**. L'écart entre les deux est invisible dans le rapport, précisément parce que le rapport est produit à partir de la mesure et non du monde.

> **Une vérification verte prouve que la vérification est verte.** Tout le reste est une inférence, et cette inférence doit être justifiée à chaque fois.

Ce n'est pas un problème d'attention. C'est un problème de **cadrage** : l'agent qui écrit le rapport n'a accès qu'à la sortie de la sonde. S'il ne va pas voir autre chose, il ne peut pas savoir que la sonde ment — et il n'a aucune raison de soupçonner qu'elle ment, puisqu'elle est verte.

---

## Les huit incidents

| # | Ce qui a été déclaré | Ce qui était vrai | Ce que la sonde mesurait réellement |
|---|---|---|---|
| 1 | « Déployé et fonctionnel » | Toutes les pages publiques vides pendant ~36 h | Des endpoints d'API qui n'existaient plus |
| 2 | « 6/6 PASS, les utilisatrices peuvent reprendre » | Pages rendues, mais sans leurs gabarits spécifiques | Que la balise `<main>` n'était pas vide |
| 3 | « Site opérationnel » | Feuilles de style et scripts du site public pointant vers `localhost` | Le site **local**, pas le site public |
| 4 | « Audit exigeant, 6/6 PASS » | Interface non montrable : couleurs criardes, boutons d'aspect désactivé | Que les pages répondaient — jamais à quoi elles ressemblaient |
| 5 | « 3 propriétés sur 5 en ÉCHEC » | Le modèle répondait correctement | Un budget de tokens épuisé par la trace de raisonnement |
| 6 | « Refus hors-contexte : 0/3 » | Le modèle refusait exactement comme demandé | Une liste de tournures figées qui ne couvrait pas la formulation employée |
| 7 | « Le correctif du gate ne détecte rien » | Le correctif détectait correctement | Une valeur de test que l'outil met en liste blanche |
| 8 | « Latence médiane 5,5 s, aucune valeur écrite à la main » | La mesure disait 7,14 s | Rien — la mesure était juste, c'est le rapport qui avait dérivé |

Les incidents 1 à 4 sont anonymisés (voir *Note de méthode*). Les incidents 5 et 6 sont documentés dans le notebook [`eval-choisir-son-modele.ipynb`](../../MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/AI-Engine-WordPress/eval-choisir-son-modele.ipynb), section *Deux pièges rencontrés en écrivant ce notebook*. Les incidents 7 et 8 sont survenus pendant la rédaction de cette note.

**Les incidents 1 à 4 sont consécutifs.** Chacun a été suivi d'un renforcement de la vérification — et le suivant est passé par un chemin que le renforcement ne couvrait pas. C'est le fait le plus instructif de la série : *durcir la sonde après coup ne réduit pas la classe de défaut, il en déplace la frontière.*

---

## Les six classes de sonde menteuse

### 1. La sonde périmée

La sonde interroge une cible qui a changé de nom, de forme, ou a disparu. Elle ne renvoie pas d'erreur : elle renvoie ce que renvoie une cible absente, et ce quelque chose passe le critère.

Incident 1 : le contrôle de santé interrogeait des points d'entrée d'API supprimés lors d'une refonte antérieure. Il était vert depuis des semaines. Il l'aurait été indéfiniment.

**Signature** : une sonde qui n'a jamais échoué. Une sonde qui ne rougit jamais ne teste rien — elle mesure sa propre existence.

**Contre-mesure structurelle** : chaque sonde doit avoir un **test de rougissement** — une manipulation connue qui la fait échouer. Si on ne sait pas la faire échouer, on ne sait pas ce qu'elle vérifie.

#### Le test de rougissement peut mentir lui aussi

L'incident 7 est arrivé en appliquant cette contre-mesure, et il en corrige l'énoncé.

Il fallait prouver qu'un scanner de secrets réparé bloquait bien quelque chose. Test de rougissement : mettre une clé d'accès dans l'index, attendre le rouge. Le scanner a répondu **vert**, et la conclusion évidente — « le correctif produit un gate qui n'attrape rien » — était fausse. La clé employée était l'exemple publié dans la documentation de son fournisseur, et l'outil met explicitement cette valeur en liste blanche parce qu'elle apparaît dans des milliers de dépôts. Avec une chaîne fabriquée, le même gate échouait immédiatement, avec deux détections.

Le matériel de test venait d'une documentation, donc du seul endroit dont l'outil se protège.

**Contre-mesure affinée** : la valeur qui doit faire rougir la sonde est **fabriquée pour l'occasion**, jamais empruntée à un exemple canonique. Et un test de rougissement qui reste vert accuse la sonde ; avant de la condamner, il faut vérifier l'échantillon. Ici encore, *le doute porte d'abord sur l'instrument* — et le test de rougissement est un instrument.

### 2. La sonde qui mesure le contenant

La sonde vérifie qu'une réponse existe, pas qu'elle est la bonne. `HTTP 200` mesure qu'un serveur a répondu. « `<main>` non vide » mesure qu'un gabarit a produit des octets.

Incidents 2 et 4 : les pages répondaient et contenaient du texte. Il leur manquait leurs gabarits spécifiques, puis toute cohérence visuelle. La sonde ne pouvait pas le voir : elle avait été écrite pour attraper l'incident 1, où les pages étaient littéralement vides.

**Signature** : le critère de la sonde est une propriété du transport (statut, longueur, absence d'exception) et non du contenu attendu.

**Contre-mesure structurelle** : formuler le critère en termes de **ce que l'utilisateur doit voir**, pas de ce que le serveur doit émettre. « La page catalogue affiche au moins un ouvrage avec son titre et son prix » est vérifiable ; « la page catalogue répond » ne l'est pas.

### 3. La sonde sur le mauvais environnement

La sonde teste un environnement voisin de celui dont on parle, et le rapport parle de l'autre.

Incident 3 : la suite tournait sur l'installation locale. Le site public, lui, servait des feuilles de style et des scripts dont les URL pointaient vers `localhost` — invisible depuis la machine de développement, où `localhost` résout précisément vers l'installation qui fonctionne. Le rapport disait « site opérationnel » ; la sonde n'avait jamais adressé le site public.

**Signature** : le rapport ne mentionne pas l'URL, l'hôte ou l'environnement effectivement testé.

**Contre-mesure structurelle** : **le rapport doit nommer la cible**. Un rapport de vérification qui ne dit pas *sur quoi* elle a porté n'est pas un rapport, c'est une affirmation. C'est la contre-mesure la moins coûteuse des six et celle qui aurait évité l'incident 3 à elle seule.

### 4. La sonde qui ne regarde pas

Certaines propriétés ne sont pas assertables sans un œil. L'aspect d'une interface en est le cas type : aucune assertion raisonnable ne distingue « élégant » de « criard ».

Incident 4 : la suite de bout en bout passait intégralement, et l'interface était impubliable. Les défauts étaient présents depuis des semaines sans qu'aucune vérification ne les voie, parce qu'aucune n'était de nature à les voir.

**Signature** : la propriété qui compte n'est pas exprimable comme une assertion, et personne ne l'a dit.

**Contre-mesure structurelle** : ne pas chercher à l'automatiser. **Produire l'artefact et le regarder** — une capture, une sortie, un rendu — puis dire dans le rapport qu'on l'a regardé, ou dire qu'on ne l'a pas fait. Les deux sont acceptables ; ce qui ne l'est pas, c'est de laisser croire.

### 5. La sonde qui se trompe de critère

La sonde fonctionne, adresse la bonne cible, dans le bon environnement — et **son critère est faux**. C'est la classe la plus dangereuse, parce qu'elle produit un résultat précis, chiffré et crédible.

Incident 5 : un banc d'évaluation attribuait trois échecs sur cinq à un modèle. Le modèle répondait correctement ; c'est le budget de tokens du banc qui était épuisé par la trace de raisonnement avant que la réponse existe. Le banc mesurait sa propre configuration.

Incident 6 : le même banc, corrigé, maintenait un échec sur la propriété la plus sensible — le refus de répondre hors-contexte. Le modèle refusait exactement comme demandé (« il ne mentionne aucun tarif annuel ») ; le détecteur cherchait une liste de tournures figées et n'y trouvait pas celle-là.

**Signature** : aucune. C'est le problème. Un verdict faux issu d'une sonde saine est indiscernable d'un verdict vrai — **sauf en lisant les données brutes**.

**Contre-mesure structurelle** : toute sonde qui rend un verdict doit **conserver et exposer la matière qui a produit le verdict**. Un banc qui ne garde pas les réponses brutes ne se débogue pas. Et le doute, devant un échec, doit porter **d'abord sur l'instrument**.

### 6. La sonde est juste, et le rapport a dérivé

Les cinq premières classes portent sur une sonde qui se trompe. La sixième porte sur le dernier maillon, celui qu'on oublie parce qu'il ne comporte aucune machine : **entre la mesure et le lecteur, il y a quelqu'un qui recopie.**

Incident 8 : le résumé d'une exécution annonçait une latence médiane de 5,5 s, sous une phrase affirmant qu'aucune valeur n'y était écrite à la main. La sortie enregistrée disait 7,14 s. Le chiffre venait d'une exécution antérieure, conservé lors d'une réécriture du résumé après re-exécution. Toutes les autres grandeurs du même tableau étaient exactes — et c'est précisément ce qui rend le cas instructif : **la seule valeur fausse était la seule qui ne se reproduisait pas d'un run à l'autre.** Les verdicts, eux, étaient stables, donc recopier les recopiait justes.

**Signature** : un résumé écrit à un moment, un artefact regénéré à un autre, et rien qui les relie. Le risque se concentre sur les grandeurs instables — durées, horodatages, tailles, coûts.

**Contre-mesure structurelle** : ne pas recopier. Soit la valeur du résumé est **relue dans l'artefact final** au moment d'écrire, soit elle n'y figure pas et le lecteur va la chercher là où elle est mesurée. En pratique : ne mettre dans un résumé que ce qui est **stable par construction** (un verdict, un décompte, une conformité) et laisser les grandeurs variables à l'artefact.

Une remarque qui boucle la note. Cet incident a été trouvé par un relecteur qui a re-dérivé le nombre depuis les sorties — ce qu'il n'aurait pas pu faire si l'artefact n'avait pas été publié avec ses sorties. **La contre-mesure de la classe 5 est ce qui a rendu la classe 6 détectable.** Conserver la matière brute ne sert pas qu'à se déboguer soi-même : c'est ce qui donne à un tiers les moyens de contredire le rapport.

---

## Ce qui ne marche pas

**Ajouter des tests.** Les incidents 1 à 4 sont séparés par des renforcements successifs de la vérification. Chaque renforcement fermait la porte par laquelle l'incident précédent était passé. Un ensemble de sondes ne converge pas vers la vérité par accumulation : il converge vers *l'ensemble des défauts déjà rencontrés*.

**Demander de faire attention.** Aucun des huit incidents ne vient d'une négligence. Dans chacun, l'agent a lancé la vérification prévue, lu son résultat, et rapporté fidèlement ce résultat. La consigne « sois rigoureux » n'a pas de prise : l'agent *était* rigoureux, au sens où il appliquait le protocole.

**Multiplier les répétitions.** Utile contre l'instabilité, sans effet contre un critère faux : une sonde qui se trompe se trompe reproductiblement. Les incidents 5 et 6 étaient parfaitement stables — 3/3 et 3/3.

---

## Ce qui marche

Trois règles, toutes portant sur la **formulation du rapport** plutôt que sur l'outillage. C'est délibéré : l'outillage a échoué sept fois sur huit, et la huitième — où l'outillage était juste et le rapport faux — montre que le rapport est de toute façon le dernier maillon. C'est lui qu'on lit ; c'est donc lui qui doit porter la charge de dire ce qui n'a pas été établi.

**1. Nommer la cible.** Tout rapport de vérification indique l'environnement, l'URL ou l'artefact effectivement adressé. Un rapport sans cible nommée est incomplet, quel que soit son verdict.

**2. Distinguer trois états, pas deux.** `PASS` / `FAIL` est insuffisant : il force les pannes de mesure dans l'une des deux cases, généralement `FAIL`. Un troisième état — `NON MESURÉ` — pour ce que la vérification n'a pas pu établir. Les incidents 5 et 6 se seraient présentés comme des non-mesures et non comme des échecs de modèle.

**3. Séparer « ça répond » de « c'est fini ».** Deux formulations distinctes, jamais interchangeables :

| Formulation | Quand elle est autorisée |
|---|---|
| « Vérification X passée sur *cible*, rendu non inspecté » | Toujours, si c'est vrai |
| « Vérification X passée sur *cible*, rendu inspecté et conforme » | Si l'artefact a été **produit et regardé** |
| « Système opérationnel » | Jamais sans la seconde formulation |
| « Terminé » | Jamais sur la foi d'une sonde seule |

La troisième règle est la plus inconfortable, parce qu'elle oblige à écrire « je n'ai pas vérifié » dans un rapport dont on aimerait qu'il soit bon. C'est exactement pour cela qu'elle fonctionne : elle rend le trou visible **avant** que quelqu'un tombe dedans.

---

## Rapport avec la défense par construction

Ce dépôt a résolu une classe de problème voisine par un autre chemin : voir [`accent-cure-defense-in-depth.md`](accent-cure-defense-in-depth.md), où le critère de sortie est explicitement la **défense par construction** (l'outil ne *peut pas* produire le défaut) plutôt que la défense par revue.

Les deux approches sont complémentaires et leur frontière est nette :

- Quand le défaut est **structurel** — un outil qui accentue un identifiant, un script qui écrase un corpus voisin — la défense par construction est supérieure, et une sonde de plus n'est qu'un pansement.
- Quand le défaut est **une divergence entre la mesure et le monde** — les huit incidents ci-dessus — aucune construction ne l'empêche, parce que la mesure fait partie de la construction. Il reste à rendre la divergence **dicible**, ce qui est un travail sur la formulation du rapport.

La question à se poser devant une classe de défaut est donc : *puis-je rendre ce défaut impossible ?* Si oui, construire. Si non, ne pas prétendre l'avoir rendu impossible en ajoutant une sonde — nommer ce qui reste non vérifié.

---

## Note de méthode — ce que cette étude n'expose pas

Les incidents 1 à 4 proviennent d'un projet client réel, avril 2026. Le projet, ses utilisatrices, son domaine et ses contenus **ne sont pas nommés**, et les incidents sont décrits au niveau du motif : ce qui est transposable est la mécanique de la sonde menteuse, pas l'identité de l'installation où elle s'est produite. Aucune capture, aucun extrait de journal, aucune donnée n'est reproduit ici — conformément à [`PRIVACY.md`](../../PRIVACY.md) §1, dont le principe s'étend à l'environnement de travail d'un tiers.

Les incidents 5 à 8 sont survenus dans ce dépôt et sont donc, eux, entièrement traçables : les deux premiers dans le notebook concerné et dans la PR qui l'a introduit, le troisième dans le relevé publié sur l'issue du scanner de secrets, le quatrième dans la revue de cette même PR, où un relecteur a re-dérivé le chiffre depuis les sorties et constaté qu'il ne s'y trouvait pas.

Ce déséquilibre est assumé. Une étude de cas dont tous les exemples sont anonymes n'est pas vérifiable ; en fournir quatre que le lecteur peut ouvrir et relire donne au reste sa crédibilité.

Une dernière remarque, qui est la raison pour laquelle les incidents 7 et 8 figurent ici. Tous deux se sont produits **pendant la rédaction de cette note**, chez son auteur, sur les contre-mesures que cette note recommande — l'un sur le test de rougissement, l'autre sur la fidélité du rapport à sa mesure. Ce n'est pas une ironie : c'est la mesure de ce qu'on affronte. Le motif ne se corrige pas une fois pour toutes par la compréhension qu'on en a — il se rattrape à chaque fois, en lisant la matière brute avant de croire le verdict. Et quand on ne se rattrape pas soi-même, c'est un relecteur qui le fait, à condition qu'on lui ait laissé de quoi.
