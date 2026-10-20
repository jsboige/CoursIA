# Argument_Analysis_Observatoire-2-Initiation-Regional_PreRegistration

**Statut** : document de pré-inscription pour le Cas 2 de l'Observatoire des formes relationnelles (#13303), suite du Cas 1 (#16410 — Bumble Opening Moves global, DiD temporel). Ce document **n'effectue aucune mesure** ; il engage le protocole décrit dans [`Argument_Analysis_RelationalForms_Protocol.md`](Argument_Analysis_RelationalForms_Protocol.md) §3 (pré-inscription datée, asymétrie des hypothèses, réfutation explicite).

**Barreau déclaré** : quasi-expérimental (DiD imparfait), avec passage obligatoire par les trois réserves DiD décrites en §3.1 ci-dessous.

**Conformité** : respecte les cinq exigences de §3 du protocole (date du changement, fenêtre pré/post, quantité, direction attendue, réfutation). Le branchement sur l'outillage est [`../../Probas/DecisionTheory/Causal-Bridges/CausalBridges-07-Quasi-Experimental.ipynb`](../../Probas/DecisionTheory/Causal-Bridges/CausalBridges-07-Quasi-Experimental.ipynb) (livré, MERGED, lien vérifiable) — **aucune réimplémentation locale**.

**Hors périmètre de ce document** :
- collecte des données (grain séparé, à ouvrir après pré-inscription acceptée) ;
- analyse et verdict final (grain séparé) ;
- sélection des 2-3 cas datables parmi les candidats (grain séparé, citera celui-ci) ;
- **aucun nom d'entreprise n'est engagé dans ce document** : la candidate retenue est désignée par son type de rupture régionale, pas par un opérateur identifié (cf. §2.2 et §4.2).

---

## 1. Le Cas 2, par contraste avec le Cas 1

Le Cas 1 a montré qu'une **plateforme unique, à une date unique**, modifie ses règles et que l'écart se lit dans les métriques de `Dated_Graphs` (axe structurel : `d_noeuds`, `d_att` ; axe sémantique : `d_sem` au sens de l'instrument #13310), à condition que l'écart inter-dates dépasse le **plancher de bruit** mesuré par split chronologique (cf. #18873 — le plancher publié est le minimum de la distribution, et l'Exercice 2 qui en donnerait la distribution n'a pas été exécuté ; cette fragilité est héritée).

Le Cas 2 transpose la question sur un autre axe : **la même plateforme applique-t-elle des règles différentes selon la région à des dates différentes ?** Si oui, le Cas 2 n'est plus un DiD temporel (pré/post global), mais un **DiD régional** (régions affectées vs régions non affectées, dans une même fenêtre temporelle). La rupture n'est plus datée par l'opérateur mondial mais par l'**hétérogénéité** de la mise en application.

L'intérêt du Cas 2 :
1. **Varier le type de DiD** (régional vs temporel) teste si la conclusion du Cas 1 dépend du seul fait que la rupture est mondiale. Si oui, le Cas 2 sera sans signal ; si non, le Cas 1 n'était pas un artefact de la temporalité.
2. **Renforcer le barreau quasi-expérimental** : un DiD régional bien construit (avec contrôle des populations différentes, assignation non aléatoire et changements concomitants) **renforce** la plausibilité causale de l'effet mesuré au Cas 1.
3. **Tester la robustesse du plancher** : si le Cas 2 est construit sur un sous-corpus où la structure argumentative est moins dense, le plancher de bruit `#18873` (split chronologique première/seconde moitié) pourrait être mécaniquement plus haut ; le Cas 2 devient alors un test de la **stabilité** du seuil.

## 2. Le candidat retenu (sans nom d'entreprise)

### 2.1 Type de rupture

Le Cas 2 vise une plateforme de mise en relation (catégorie « app ») qui a **publié un changement de règle de mise en relation** (l'algorithme de suggestion, le mécanisme d'ouverture, le wording de la première interaction, ou la tarification) **à des dates différentes selon la région** dans une fenêtre temporelle d'observation qui inclut les deux.

Pourquoi cette signature : la régionalisation est **publique et datable** (communiqués, release notes localisées, journalism tech, comparaisons marché par marché), donc la date du changement par région n'est pas postulée — elle est consultable. Cette accessibilité est ce qui rend le Cas 2 falsifiable par un lecteur externe, sans qu'on ait à ouvrir les données des utilisateurs.

### 2.2 Anonymisation du candidat

Conformément à la consigne de l'observatoire (aucun nom d'entreprise dans le grain de pré-inscription), le candidat est désigné par sa **signature de rupture** :

- Plateforme (catégorie « app de mise en relation ») ;
- Mécanisme modifié (axe : ouverture de conversation OU suggestion algorithmique OU tarification différenciée) ;
- Hétérogénéité régionale (≥ 2 régions affectées à des dates séparées, ≥ 1 région contrôle non affectée dans la fenêtre d'observation) ;
- Fenêtre temporelle d'observation : 18 mois (9 mois pré / 9 mois post, autour de la première date de changement).

**Le nom de la plateforme et de la fonctionnalité modifiée seront publiés dans le grain de collecte de données**, après vérification que (a) la signature énoncée ci-dessus est satisfaite, (b) la fenêtre temporelle est couverte par le corpus, (c) le contrôle régional est bien non affecté. Si l'un de ces trois points échoue, le Cas 2 est **refusé à la pré-inscription** (cf. §3.4 — l'asymétrie est ce qui rend la pré-inscription honnête).

### 2.3 Pourquoi pas une alternative

Trois alternatives ont été écartées **avant** l'écriture de la pré-inscription :

1. **Bumble Opening Moves (régional)** : le Cas 1 a déjà utilisé la plateforme en mode global, et le Cas 1 n'a pas formellement séparé les régions (le split chronologique est temporel, pas régional). Le Cas 2 sur la même plateforme mais avec un split régional apporterait de l'information, mais la dépendance au Cas 1 affaiblit la portée du barreau quasi-expérimental : les deux cas partageraient la même plateforme, et un critique pourrait arguer que les deux effets sont colinéaires. **Rejeté pour diversification**.
2. **Modification d'API d'un réseau social (régional)** : la signature « régional » existe (règles de contenu par juridiction), mais l'effet sur les **formes relationnelles** est médiat (le réseau social n'est pas une plateforme de mise en relation, son design n'engage pas la relation d'entrée). Le Cas 2 doit porter sur les **formes relationnelles** (humour / désir / attachement, cf. sister issues #12680/#12682/#12683), pas sur les formes éditoriales. **Rejeté pour distance au protocole**.
3. **Pricing différencié (régional)** : la signature existe, et la modification est datable, mais le mécanisme modifié (tarification) n'a pas de signature dans `Dated_Graphs` (l'instrument mesure des relations argumentatives, pas des paiements). **Rejeté pour absence de mesure dans l'outillage**.

Le Cas 2 retenu est donc : **plateforme de mise en relation, modification datée d'un mécanisme d'ouverture de conversation (ou équivalent), hétérogénéité régionale documentée, ≥ 1 région contrôle**.

## 3. Pré-inscription datée (cinq champs §3 du protocole)

> **Pré-inscription datée 2026-10-15 (publication).**
>
> **Cas** : plateforme de mise en relation (cf. §2.1), mécanisme d'ouverture modifié à des dates différentes selon la région. Nom de la plateforme et du mécanisme publié au grain de collecte, après vérification de la signature §2.1.

### 3.1 Date du changement

- **Mécanisme modifié** : la modification est événementielle (release datée) ou rolling (fenêtre de déploiement) ; dans les deux cas, **la date pivot est la date de release publique par région**, fixée **sans connaître les données post**.
- **Fenêtre de release** : attendue **≤ 6 mois** entre la première région affectée et la dernière. Au-delà, la fenêtre de split DiD temporel est dominée par l'effet « déploiement » plutôt que par l'effet « modification » et le Cas 2 perd son contraste régional.
- **Source de la date** : release notes officielles de l'opérateur + journalism tech spécialisé. **Pas** une reconstruction post hoc depuis les données.

### 3.2 Fenêtre pré/post

- **Pré** : 9 mois avant la date pivot de **chaque** région (fenêtre alignée régionalement, pas mondialement) ;
- **Post** : 9 mois après la date pivot de **chaque** région ;
- **Granularité** : hebdomadaire, pour préserver la mesure `Dated_Graphs` (`#13310`) et la structure de split chronologique (`#18873`).
- **Total** : 18 mois par région, ce qui donne au moins 78 observations hebdomadaires par moitié de split (39 semaines × 2) — la distribution du plancher de bruit sous split chronologique (cf. `12f608aa` cellule de l'instrument, reproduit dans #18873) reste mesurable.

### 3.3 Quantité mesurée

- **Variables** : `d_noeuds`, `d_att`, `d_sem` (cf. instrument #13310). Ce sont les **trois composantes** publiées par `Dated_Graphs` ; le Cas 2 les utilise toutes, et le verdict exige que l'écart inter-dates dépasse le plancher sur **au moins deux** des trois (cf. §3.4).
- **Source des corpus** : à ouvrir dans le grain de collecte — la pré-inscription **n'engage pas la source**, elle engage la **quantité** (métrique) et sa **définition opérationnelle** (distance entre graphes d'argumentation datés). La pré-inscription refuse un livrable qui s'engagerait sur la source avant que les trois conditions §2.2 (a)/(b)/(c) soient vérifiées.

### 3.4 Direction attendue et réfutation

| Composante | H₀ (null) | H₁ (effet attendu, signé) | Réfutation (observation qui invalide H₁) |
|---|---|---|---|
| `d_noeuds` | pas de changement de structure nodale | **+** (la modification ajoute un type de nœud dans le graphe d'argumentation des conversations) | `d_noeuds` ≤ plancher de bruit régional, **OU** signe contraire |
| `d_att` | pas de changement du pattern d'attaques | **+** (la modification augmente la variété des attaques argumentatives, par densification des schémas) | `d_att` ≤ plancher de bruit régional, **OU** signe contraire |
| `d_sem` | pas de changement d'extensions de Dung | **+** (la modification change l'ensemble des extensions acceptées au sens de Dung) | `d_sem` ≤ plancher de bruit régional, **OU** signe contraire |

**Règle de décision** : H₁ (effet signé) est validée **si et seulement si** au moins deux des trois composantes dépassent leur plancher respectif ET gardent le signe attendu. Sinon, **H₀ tient** et le Cas 2 est **non concluant** (verdict `INCONCLUSIVE` au sens de #10961, CE1 — pas de fallback sur la jambe `linear`).

**Asymétrie** : la pré-inscription risque H₁ sur les trois composantes simultanément. Si une seule des trois bouge, le Cas 2 est **non concluant** ; le plancher régional, plus sévère que le plancher mondial (cf. §1.3), est conçu pour cela.

### 3.5 Le plancher de bruit à dépasser

- **Plancher mondial** (instrument #13310, mesure #18873) : split chronologique première/seconde moitié, **sur 20 tirages seedés `random.Random(42)`** ; les trois composantes publient respectivement 0,077 / 0,111 / 0,125 (les **minima** de la distribution ; la distribution complète, l'Exercice 2 du carnet, n'a pas été exécutée — c'est précisément la fragilité héritée, documentée).
- **Plancher régional (Cas 2)** : réplication du même split, mais sur les **fenêtres régionales** (date pivot alignée par région) plutôt que sur la fenêtre mondiale. Attendu : **plus haut** que le plancher mondial, parce que la fenêtre régionale est plus petite et la variance d'échantillonnage plus grande. Mesure à publier en §1 du grain d'analyse.
- **Honnêteté du seuil** : la pré-inscription **ne reproduit pas** l'omission de l'Exercice 2. Le grain d'analyse **doit** publier la distribution complète du plancher régional (20 tirages seedés, comme prescrit) **avant** de déclarer un écart inter-dates `DEPASSE`. Si l'Exercice 2 n'est pas exécuté, le verdict du Cas 2 est **non déposable**, quelle que soit la magnitude apparente de l'écart inter-dates.

## 4. Réserves DiD (assignation non aléatoire, populations différentes, changements concomitants)

Le Cas 2 vise le barreau **quasi-expérimental** (cf. protocole §1). Trois réserves DiD sont à écrire **avant** la collecte, pas après.

### 4.1 Assignation non aléatoire des régions

L'assignation (qui est affecté, qui ne l'est pas) **n'est pas aléatoire** : l'opérateur choisit la séquence de déploiement, généralement par marché adressable, par pression réglementaire ou par alignement marketing. Le DiD régional ne peut donc pas s'appuyer sur une hypothèse de tendance parallèle **stricte** ; il s'appuie sur une hypothèse de tendance parallèle **conditionnelle** aux variables observables (taille du marché, langue principale, indice de pénétration mobile, prévalence d'autres plateformes de mise en relation).

**Contrôle** : apparier chaque région affectée à sa plus proche région non affectée sur ces observables ; reporter la balance de l'appariement (écart-type des écarts sur chaque observable) en §2 du grain d'analyse. Si l'appariement est mauvais (écart-type > 1 σ), le Cas 2 plafonne au barreau **associatif**.

### 4.2 Populations différentes

Les utilisateurs de la région affectée et de la région contrôle **ne sont pas les mêmes personnes**. L'écart mesuré est **agrégé** ; il mélange l'effet de la modification et l'effet de la population (composition par âge, langue, usage, niveau socio-économique, alphabétisation numérique). Sans contrôle de la composition, l'écart n'est pas attribuable à la modification.

**Contrôle** : utiliser les variables observables disponibles dans le corpus (profil public, langue de la conversation, fuseau horaire) pour estimer la **balance de composition** entre régions ; reporter l'écart en §2.2. Si les compositions sont déséquilibrées (plus de 1 σ sur l'un des observables), le Cas 2 plafonne au barreau **associatif**.

### 4.3 Changements concomitants

D'autres modifications datées peuvent survenir dans la fenêtre de 18 mois : campagnes marketing, mise à jour de l'app concurrente, modification réglementaire (RGPD-local, DMA, AI Act), événement culturel (élections, crise sanitaire). Si l'un de ces événements concomitants est daté dans la fenêtre post, **il est candidat à expliquer l'écart** au même titre que la modification visée.

**Contrôle** : énumérer les événements concomitants **avant** la mesure ; pour chaque événement concomitant, soit le contrôler (s'il existe une variable observable), soit déclarer que l'événement concomitant **plafonne le Cas 2 au barreau associatif** sur la fenêtre où il se produit. Le Cas 2 **n'élimine pas** les changements concomitants par randomisation ; il les **documente** et les **borner**.

## 5. Ce que ce document refuse

- **Aucun nom d'entreprise n'est publié.** La candidate est désignée par sa signature (§2.1), et la levée de l'anonymisation est conditionnée à la vérification de §2.2 (a)/(b)/(c) dans le grain de collecte.
- **Aucune métrique n'est calculée ici.** Le Cas 2 ouvre un grain de collecte puis un grain d'analyse ; il ne mesure pas.
- **Aucun corpus réel n'est engagé.** La pré-inscription refuse les engagements de source ; le grain de collecte le fera, après vérification.
- **Aucune conclusion sur les formes relationnelles** n'est tirée. Le Cas 2 est un test du DiD régional sur l'instrument `Dated_Graphs`, pas une affirmation sur le désir, l'humour ou l'attachement. Cette dernière étape appartient à un grain ultérieur qui reprendra les trois sister issues #12680 / #12682 / #12683, **et pas avant**.

## 6. Critères d'acceptation (à vérifier à la review)

1. [ ] Le document existe et porte les **cinq champs** de §3 (date, fenêtre, quantité, direction, réfutation).
2. [ ] Le candidat est décrit par sa **signature de rupture** (§2.1), sans nom d'entreprise, et la levée de l'anonymisation est conditionnée.
3. [ ] Les **trois réserves DiD** (§4.1, §4.2, §4.3) sont écrites **avant** la collecte, avec contrôle proposé.
4. [ ] Le **plancher de bruit régional** est défini et son mode de calcul (split chronologique seedé, distribution complète — pas seulement le minimum) est explicité.
5. [ ] La **règle de décision** est asymétrique : `H₁` validée **seulement** si ≥ 2/3 composantes dépassent leur plancher régional ET gardent le signe attendu ; sinon `H₀` tient, et le verdict est `INCONCLUSIVE` au sens de #10961 CE1.
6. [ ] Le **barreau** est déclaré (quasi-expérimental) et les **conditions de plafonnement** (associatif) sont écrites.
7. [ ] Aucune mesure n'est produite. Aucune source de données n'est engagée.

## 7. See also

- [`Argument_Analysis_RelationalForms_Protocol.md`](Argument_Analysis_RelationalForms_Protocol.md) — protocole de l'EPIC #13303, dont ce document applique §3.
- [`../../Probas/DecisionTheory/Causal-Bridges/CausalBridges-07-Quasi-Experimental.ipynb`](../../Probas/DecisionTheory/Causal-Bridges/CausalBridges-07-Quasi-Experimental.ipynb) — outillage DiD livré, MERGED, lien vérifiable.
- #13303 (EPIC parent Observatoire), #12680/#12682/#12683 (sister issues humour / désir / attachement).
- #16410 — Cas 1, Bumble Opening Moves, DiD temporel.
- #13310 — instrument `Dated_Graphs`.
- #18873 — fragilité héritée du plancher de bruit (minimum de la distribution, Exercice 2 non exécuté) — **le Cas 2 refuse explicitement de reproduire cette omission**.
- #10961 CE1 — référence du verdict `INCONCLUSIVE` (pas de fallback `linear`).
- #20764 — issue de pré-inscription, source de ce grain.
