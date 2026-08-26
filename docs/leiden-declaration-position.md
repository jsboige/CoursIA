# CoursIA face à la Déclaration de Leiden

## Statut de ce texte

La [Déclaration de Leiden sur l’intelligence artificielle et les mathématiques](https://leidendeclaration.ai/) a été publiée le 2 juin 2026, déposée sous le DOI [`10.5281/zenodo.20302944`](https://doi.org/10.5281/zenodo.20302944) et endossée par l’[International Mathematical Union](https://www.mathunion.org/fileadmin/documents/2026-06/IMU_AO_CL_8_2026.pdf). Elle est issue d’un groupe de travail réuni au Lorentz Center en septembre 2025.

Ce document n’est ni une paraphrase de la Déclaration, ni une déclaration d’adhésion sans réserve. Il situe CoursIA face à ses valeurs, confronte ces valeurs à des artefacts vérifiables du dépôt et nomme les écarts qui restent ouverts. Il suit en cela deux précédents du projet : le [dialogue avec *Magnifica Humanitas*](magnifica-humanitas-dialogue.md), qui répond à un texte externe par des objets concrets, et la [clé de lecture grothendieckienne](grothendieckian-lens.md), qui conserve les changements de cadre, les échecs et les niveaux de certification.

Le texte est daté. Un workflow, un registre ou un notebook cité ici peut évoluer ; le lien vers l’artefact prime sur la déclaration de conformité.

## Notre lecture de Leiden

Leiden protège cinq choses que l’usage de l’IA rend plus faciles à dissocier :

1. la pluralité des motivations mathématiques, avec la preuve comme niveau élevé de certitude ;
2. l’attribution à des auteurs identifiables, responsables de leurs résultats ;
3. la transparence des arguments et leur vérification indépendante ;
4. l’évaluation partagée de la profondeur, de la difficulté et de l’importance ;
5. la compréhension, le jugement et l’autonomie dans le choix des questions.

La Déclaration alerte symétriquement sur cinq menaces : arguments plausibles mais faux, exploitation du corpus et défaut d’attribution, distorsion des incitations, communication contournant la revue communautaire, et dépendance industrielle susceptible de déplacer les priorités de recherche.

CoursIA partage ce diagnostic, avec une précision issue de son expérience : **la validité technique et la valeur pédagogique sont deux axes distincts**. Un notebook peut s’exécuter de bout en bout et mal expliquer son objet. Une preuve Lean peut être acceptée par le noyau et rester opaque, mal attribuée ou dépendante d’axiomes non discutés. À l’inverse, un récit limpide ne compense jamais un résultat non reproduit.

Cette distinction motive l’[Epic de digestion et canonicalisation](https://github.com/jsboige/CoursIA/issues/13105), inspiré de la chaîne proposée par Terry Tao dans *Mathematics in the Age of AI* : génération, vérification, exposition, publication, puis digestion dans un corpus humainement cohérent.

## Principes, pratiques, preuves et engagements

| Principe de Leiden | Pratique CoursIA actuelle | Preuve consultable | Lacune reconnue | Engagement |
|---|---|---|---|---|
| La preuve vise certitude **et** compréhension | Les notebooks combinent exécution, narration, exemples et exercices ; les preuves Lean sont relues au-delà du simple build | [Règles de validation H.1–H.7](reference/regles-validation-detail.md), [discipline de review Lean](../.claude/rules/pr-review-discipline.md), série [Lean](../MyIA.AI.Notebooks/SymbolicAI/Lean/README.md) | Un build vert ne mesure ni la lisibilité ni la digestion | Appliquer la grille de l’Epic #13105 aux résultats qui dépassent la capacité d’exposition actuelle |
| Attribution et responsabilité humaines | Les sources, auteurs et artefacts amont doivent être nommés ; une attribution douteuse bloque une conclusion | [Verify Before Claiming](../.claude/rules/verify-before-claiming.md), [registre d’attribution MBML](reference/mbml-source-attribution.md), [anti-régression](../.claude/rules/anti-regression.md) | La provenance n’est pas encore uniforme dans tous les notebooks historiques | Traiter chaque lacune actionnable par une issue dédiée, avec source primaire et correction vérifiable |
| Transparence et vérification indépendante | Outputs réels committés, exécution end-to-end, comptage des axiomes et validation après modification | [Règles notebooks](../CLAUDE.md#c-notebooks-3-règles-user-2026-04-26), [couverture proof-integrity](reference/lean-axiom-coverage.md), [PARCOURS](PARCOURS.md) | La couverture `proof-integrity` n’atteint pas encore tous les lakes | Étendre la couverture sans présenter les lakes non câblés comme déjà certifiés |
| Standards partagés d’évaluation | Les axes éditorial, reproductibilité et revue scientifique sont séparés ; les reviews substantielles sont enregistrées | [PARCOURS](PARCOURS.md), [registre de revues éditoriales](notebook-metadata/editorial-review-registry.md), [carte de revue](notebook-metadata/EDITORIAL_REVIEW_CARD.md) | Les registres restent partiels et la qualité pédagogique garde une part de jugement humain | Nommer la portée de chaque review et refuser l’auto-promotion par métrique unique |
| Compréhension, jugement et autonomie | Le dépôt privilégie les outils ouverts, locaux ou reproductibles lorsque c’est possible ; les limites des services externes sont documentées | [Services GenAI](genai/genai-services.md), [matrice de coût](notebook-metadata/cost-matrix.md), [politique de taille et reproductibilité](reference/repo-size-policy.md) | Modèles, GPU, APIs et plateformes cloud créent encore des dépendances réelles | Rendre chaque dépendance visible et distinguer `RECOVERABLE-*` d’une impossibilité intrinsèque |
| Ouverture et partage | Notebooks, scripts, preuves et sorties pédagogiques sont versionnés dans le dépôt ; les données et licences sont inventoriées | [Registre datasets](notebook-metadata/DATASET_REGISTRY.md), [THIRD_PARTY_NOTICES](../THIRD_PARTY_NOTICES.md), [politique SOTA](../.claude/rules/sota-not-workaround.md) | Ouverture du code ne signifie pas gratuité énergétique, accès universel aux modèles ou licence uniforme des sources | Publier les coûts, licences et prérequis au même niveau que les résultats |

## Ce que nos artefacts démontrent — et ce qu’ils ne démontrent pas

### 1. Exécution authentique

CoursIA exige que les notebooks committés conservent leurs sorties et que toute cellule de code modifiée soit ré-exécutée. Cette règle combat une forme directe de plausible-but-false : un récit qui affirme un résultat que le livrable ne produit pas. Elle interdit aussi de maquiller manuellement une sortie ; la cause doit être corrigée puis l’exécution rejouée.

Cette discipline démontre qu’une sortie a été produite dans un environnement donné. Elle ne démontre pas, à elle seule, que l’expérience répond à la bonne question, que le problème n’est pas dégénéré ou que l’interprétation est juste. Les critères de [validation réelle](reference/regles-validation-detail.md) et de [vrai outil SOTA](../.claude/rules/sota-not-workaround.md) existent précisément pour éviter ce glissement.

### 2. Vérification formelle

Les lakes Lean permettent d’interroger les axiomes, de construire les modules et, lorsque le workflow est câblé sur la cible, de contrôler l’intégrité des preuves. CoursIA distingue explicitement `sorryAx`, `native_decide.*` et `Classical.choice` plutôt que de réduire la confiance à l’absence textuelle de `sorry`.

Cette précision reste incomplète : la [carte de couverture](reference/lean-axiom-coverage.md) montre que tous les lakes ne sont pas atteints par le même gate. Un succès hors cible n’est donc jamais présenté comme une preuve sur cible.

### 3. Exposition et digestion

Lean-19 Sendov, Lean-20 Analysis I et Lean-21 PFR illustrent trois formes de digestion : exposer un grand résultat, étudier un workflow de formalisation et relier une méthode entropique à un lake réel. Ces notebooks sont des points de départ, pas des certificats de canonicalisation définitive.

L’[inventaire Palomar](https://github.com/jsboige/CoursIA/issues/13107) rend cette prudence opérationnelle. Au snapshot du 26 août 2026, le registre comptait 68 résultats actifs et 76 versions. Un seul résultat, Sendov, avait un chevauchement direct avec une digestion CoursIA existante. La plupart des autres reçoivent `VEILLE` ou `AUCUNE ACTION` : être vérifié dans Palomar ne suffit pas à justifier un import, un notebook ou une place dans le curriculum.

### 4. Revue humaine

Le [registre de revues éditoriales](notebook-metadata/editorial-review-registry.md) refuse qu’un notebook soit promu par simple ancienneté ou auto-évaluation. La portée de la review — typographie, faits, pédagogie, substance ou revue complète — est nommée.

Le registre ne prétend pas couvrir tout le dépôt. Il constitue un mécanisme de responsabilité, non une preuve que tout artefact absent serait mauvais ou que tout artefact présent serait définitif.

## Cinq menaces confrontées au dépôt

### Arguments plausibles mais faux

La réponse ne peut pas être seulement stylistique. CoursIA combine exécution, sorties réelles, contrôles de régression, tests, revue du diff et, pour Lean, inspection des axiomes. Les règles [Verify Before Claiming](../.claude/rules/verify-before-claiming.md) et [Audit Reassessment](../.claude/rules/audit-reassessment.md) imposent de confronter les verdicts automatisés au code réel, car un audit peut lui-même produire un faux positif.

**Risque résiduel :** un check peut être vert tout en mesurant le mauvais objet. Le dépôt conserve plusieurs études de cas de ce phénomène dans [Quand la vérification est verte et le système est cassé](reference/verification-verte-systeme-casse.md).

### Exploitation du corpus et mauvaise attribution

Les datasets, sources pédagogiques, lakes et logiciels tiers doivent être reliés à leur provenance et à leur licence. L’usage d’un modèle n’efface pas les auteurs des données ou des preuves dont il dépend.

**Risque résiduel :** les notebooks historiques n’ont pas tous le même niveau de détail bibliographique. L’engagement est de corriger les manques vérifiés, sans inventer une priorité ou conclure à l’absence d’antériorité depuis une recherche négative rapide.

### Distorsion des incitations

Un nombre de preuves, de PRs, de cellules ou de notebooks n’est pas une mesure suffisante du progrès. Le [protocole de variation](../.claude/rules/variation-protocol.md) sépare contenu et méta-outillage et exige qu’un cycle ajoute quelque chose qu’un lecteur ou un étudiant puisse utiliser.

**Risque résiduel :** toute métrique peut devenir une cible. Les tags `DEEP/MED/LIGHT`, les densités et les gates restent des instruments de triage ; la décision se relit contre le livrable.

### Communication qui contourne la revue

CoursIA ne traite pas une annonce de blog, une fiche de registre ou un résultat de modèle comme un substitut à la source et à la revue. Pour une PR ou une issue, le body complet, les commentaires, les reviews et le diff sont lus avant décision.

**Risque résiduel :** la vitesse de production peut dépasser la capacité de revue. L’Epic #13105 nomme cette situation « indigestion de preuve » et privilégie l’exposition, l’attribution et l’intégration au corpus plutôt que l’accumulation de certificats.

### Dépendance industrielle et perte d’autonomie

Le dépôt utilise des services commerciaux, des modèles propriétaires et des plateformes cloud, mais maintient aussi des environnements locaux, des scripts reproductibles et des alternatives ouvertes. L’autonomie est évaluée capacité par capacité, jamais proclamée globalement.

**Risque résiduel :** le matériel, les licences, les tokens, les modèles gated et les coûts énergétiques limitent encore l’accès. Un fallback dégradé n’est pas consacré comme résultat SOTA lorsqu’un chemin de réparation existe.

## Tensions que nous refusons de lisser

### Vitesse contre revue

L’IA réduit le coût de génération. Elle ne réduit pas automatiquement le coût de vérification sémantique, d’attribution, d’exposition ou de maintenance. Lorsque le flux dépasse la revue, ralentir la publication peut constituer le progrès responsable.

### Formalisation contre compréhension

La formalisation rend des hypothèses et des dépendances inspectables. Elle peut aussi déplacer l’opacité vers les bibliothèques, les tactiques, les ponts de langage ou la sélection même de l’énoncé. Une preuve noyau-correcte n’est pas encore un cours.

### Ouverture contre coût

Versionner les sorties et les dépendances améliore la reproductibilité, mais augmente la taille du dépôt, le temps de CI et l’empreinte de calcul. La [politique de taille](reference/repo-size-policy.md) assume ce compromis et demande de mesurer le coût plutôt que de l’effacer.

### Infrastructure locale contre dépendances

L’auto-hébergement augmente le contrôle et la réparabilité, sans supprimer les dépendances aux fabricants, aux modèles et aux communautés open source. Le verdict honnête se formule par composant.

### Reconstruction claire contre chemin de découverte

Une exposition finale doit être lisible. Mais supprimer tous les essais ratés, pivots et choix intermédiaires rend la difficulté invisible et l’apprentissage plus pauvre. La digestion conserve une sélection d’échecs instructifs, sans transformer le notebook en journal brut.

## Engagements CoursIA

1. **Disclosure situé.** Nommer l’usage d’IA lorsqu’il affecte la génération, la vérification, l’exposition ou la décision scientifique ; ne pas réduire ce disclosure à une signature générique.
2. **Responsabilité humaine finale.** Une sortie de modèle, un verdict de bot ou un build vert ne décide jamais seul de la justesse d’un claim.
3. **Attribution active.** Chercher et citer les sources primaires, les auteurs, les dépôts substantifs et les licences ; distinguer un wrapper du travail qu’il enveloppe.
4. **Preuve inspectable.** Publier, lorsque le domaine le permet, toolchain, dépendances, axiomes, seeds, paramètres, sorties et limites.
5. **Outputs authentiques.** Corriger la cause puis ré-exécuter ; ne jamais hand-éditer une sortie pour la rendre plus propre ou conforme au récit.
6. **Revue nommée.** Documenter qui a relu quoi, avec quelle portée ; éviter que « reviewed » devienne un label sans contenu.
7. **Résultats négatifs conservés.** Garder les non-reproductions, réfutations et plafonds lorsqu’ils changent la décision scientifique.
8. **Digestion avant accumulation.** Pour les résultats formels ou IA à fort débit, investir dans l’exposition, la littérature, les exercices et le raccord au curriculum.
9. **Autonomie mesurée.** Favoriser les outils ouverts et locaux sans masquer les dépendances restantes.
10. **Coûts visibles.** Documenter les coûts de calcul, d’accès et d’énergie lorsqu’ils conditionnent la reproductibilité ou l’équité d’accès.

## Ce que nous ne revendiquons pas

- Un build Lean ne certifie ni la nouveauté, ni l’importance, ni la pédagogie d’un résultat.
- Une exécution Papermill ne certifie pas que l’expérience est non triviale ou que son interprétation est correcte.
- Une entrée Palomar ne valide pas un lake entier et n’impose pas son import.
- Un modèle local ne rend pas l’infrastructure indépendante de toute industrie.
- Un dépôt public ne résout pas les barrières de matériel, de licence ou d’énergie.
- Une grille de review ne remplace pas le jugement mathématique et pédagogique.
- Ce document ne constitue pas une canonicalisation achevée ; il énonce des engagements vérifiables et des lacunes ouvertes.

## Dialogue avec les recommandations de Leiden

Aux **mathématiciens**, Leiden demande disclosure, attribution, revue, responsabilité et formation continue. CoursIA répond par des règles d’exécution et de review, mais doit encore homogénéiser la provenance historique.

Aux **organisations et financeurs**, Leiden demande des standards de publication, la protection des auteurs, des infrastructures publiques et le maintien de la rigueur. CoursIA peut documenter des pratiques et fournir des artefacts ouverts ; il ne possède ni l’autorité d’un journal ni celle d’un financeur.

Aux **pouvoirs publics**, Leiden recommande de protéger les auteurs, de résister au battage promotionnel, de réguler l’industrie et d’investir dans des infrastructures publiques. CoursIA peut rendre visibles les dépendances et les coûts, non se substituer à cette politique.

À **l’industrie**, Leiden demande le respect des standards communautaires, de l’autonomie et des préoccupations éthiques. CoursIA évalue les outils par leurs résultats et leurs conditions d’usage, et refuse de transformer l’accès à un service en preuve de neutralité ou de légitimité.

## Sources principales

- [Leiden Declaration on Artificial Intelligence and Mathematics](https://leidendeclaration.ai/), 2 juin 2026.
- [Version archivée et DOI](https://doi.org/10.5281/zenodo.20302944).
- [Lettre d’endossement de l’International Mathematical Union](https://www.mathunion.org/fileadmin/documents/2026-06/IMU_AO_CL_8_2026.pdf).
- [Mechanization and Mathematical Research](https://www.lorentzcenter.nl/mechanization-and-mathematical-research.html), Lorentz Center, septembre 2025.
- Terence Tao, [*Mathematics in the Age of AI*](https://arxiv.org/abs/2608.16753), ICM 2026.
- [UNESCO Recommendation on Open Science](https://unesdoc.unesco.org/ark:/48223/pf0000379949).
- [FAIR Guiding Principles](https://www.nature.com/articles/sdata201618).
- [San Francisco Declaration on Research Assessment](https://sfdora.org/read/).
- [Uppsala Code of Ethics for Scientists](https://phsj.org/wp-content/uploads/2007/10/Uppsala-Code-of-Ethics-for-Scientists.pdf).
- [Universal Ethical Code for Scientists](https://www.gov.uk/government/publications/universal-ethical-code-for-scientists).
- [SIAM AI Task Force Report](https://www.siam.org/media/b03hwuwe/siam-report-ai-task-force.pdf).
- [AMS AI Summary](https://www.ams.org/about-us/ai-summary).
