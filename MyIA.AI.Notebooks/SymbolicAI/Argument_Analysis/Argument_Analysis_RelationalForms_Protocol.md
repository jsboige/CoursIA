# Argument_Analysis_RelationalForms_Protocol

**Statut** : protocole bloquant pour l'EPIC #13303 (Observatoire des formes relationnelles — témoins externes pour humour, désir, attachement). Ce grain **ne mesure rien**. Il écrit le contrat que toute mesure ultérieure sous #13303 doit respecter pour être réfutable.

**Outillage de référence** (livré, ne pas reconstruire) : [`Quasi-Experimental.ipynb`](../../Probas/DecisionTheory/Causal-Bridges/Quasi-Experimental.ipynb) — différence-en-différences, contrôle synthétique, régression sur discontinuité, variables instrumentales.

**Sister issues** : #13303 (EPIC parent), #12680 (humour), #12682 (désir), #12683 (attachement).

---

## 1. L'échelle de preuve, à trois barreaux

Chaque affirmation produite sous #13303 se **range explicitement** sur un barreau, et le barreau est écrit **à côté de l'affirmation**, pas dans une annexe. Un barreau non déclaré vaut **« descriptif »**. Une affirmation qui monte d'un barreau sans le dire est le défaut que ce protocole existe pour attraper.

| Barreau | Ce qu'il autorise à dire | Ce qu'il n'autorise PAS |
|---|---|---|
| **Descriptif** | « le corpus C, collecté ainsi, présente telle distribution D » | rien sur la population dont C est issu |
| **Associatif** | « dans C, X co-varie avec Y, sous tel contrôle K » | rien sur la cause ; une co-variation sous K reste une co-variation sous K |
| **Quasi-expérimental** | « le changement daté D est suivi d'un écart Δ, sous hypothèse de tendances parallèles vérifiée sur la pré-période » | rien hors du périmètre de D ; un autre changement concomitant peut aussi expliquer Δ |

### 1.1 Pourquoi trois, et pas deux

Le barreau « descriptif » seul est trop laxiste : il laisse dire « les gens font X » sans qu'on sache ce que « les gens » signifie dans C. Le barreau « causal » seul est trop strict : il exige une expérience randomisée qu'on n'aura jamais sur des formes relationnelles historiques. Le barreau intermédiaire **« associatif sous contrôle K »** est ce que les sciences sociales font la plupart du temps ; le protocole l'élève au rang de barreau en nommant **K** (ce qui se contrôle, et ce qui reste).

### 1.2 Exemple travaillé — humour (#12680)

| Affirmation | Barreau | Contrôle K (si associatif) | Référence datée |
|---|---|---|---|
| « le corpus Stand-Up transcripts (2010-2024) présente une distribution de sujets stable autour de 7 catégories » | descriptif | — | snapshot mensuel, sans hypothèse causale |
| « dans ce corpus, la fréquence des sujets 'politique' co-varie avec le cycle électoral US, sous contrôle des saisons de tournée » | associatif | saison de tournée (oct-mars / avr-sep), disponibilité des Specials Netflix | comparaison 2012 vs 2016 vs 2020 vs 2024 |
| « la modification de l'algorithme de recommandation de YouTube au T2 2019 est suivie d'un écart Δ dans la fréquence de 'politique' » | quasi-expérimental | tendances parallèles vérifiées 2017-2019 sur les autres catégories | date de l'algorithme = T2 2019 |

### 1.3 Exemple de **refus**

Une affirmation qui dirait « la plateforme X a **provoqué** un changement d'humour moyen » sans barreau déclaré, ou avec un barreau quasi-expérimental sans date vérifiable du changement algorithmique, est **refusée à l'écriture**. Ce refus est un livrable du protocole, pas une absence de livrable.

---

## 2. La contrainte de biais de sélection, écrite comme une inégalité

Toute source de témoignage en ligne obéit à :

```
P(récit | l'auteur a choisi de publier)  ≠  P(récit | population)
```

Le protocole exige, **pour chaque corpus utilisé**, que soit écrit :

1. **qui publie** (et donc qui manque) ;
2. **ce que le manque déforme** dans la direction attendue — **signé**, pas seulement « il y a un biais » ;
3. si un **contrôle** est disponible (population comparable non exposée au changement daté) ou si son absence plafonne l'affirmation au barreau associatif.

Ce point n'est pas une précaution rhétorique : **il décide du barreau atteignable**. Un corpus auto-sélectionné sans contrôle ne peut pas atteindre le barreau quasi-expérimental, quel que soit le volume.

### 2.1 Exemple travaillé — désir (#12682)

| Source de témoignage | Qui publie | Qui manque | Direction signée du biais | Contrôle disponible |
|---|---|---|---|---|
| Tweets publics « I want X » | utilisateurs Twitter actifs, anglophones, 18-35 ans, politiquement engagés | population offline, >35 ans, non-anglophone, abstentionnistes | sur-représentation des désirs exprimés publiquement ; sous-représentation des désirs tus | comparaison intra-plateforme par cohorte d'âge (si la plateforme ventile) |
| Forums Reddit r/relationship_advice | posters qui ont **choisi** de demander conseil public | posters qui ont résolu en privé, ou qui n'ont pas ressenti le besoin de poster | sur-représentation des cas **non résolus** ; sous-représentation des résolutions paisibles | panel représentatif (ex. NORC AmeriSpeak) si accessible |
| Bumble Opening Moves (variantes 2024+) | femmes 18-30 ans qui utilisent l'app quotidiennement | app-light users, populations rurales, hors-app | sur-représentation des désir exprimés dans un contexte de **sélection explicite** | difficile — la plateforme n'expose pas les non-clics |

### 2.2 Pourquoi signé

« Il y a un biais » n'est pas falsifiable. « Le biais pousse vers la sur-représentation des cas non résolus » l'est : si on observe une distribution symétrique entre résolu/non-résolu, c'est que la mesure ne lit pas vraiment ce qu'on croit. Le signe est ce qui rend le constat réfutable.

---

## 3. La pré-inscription du cas

**Avant** de regarder les données d'un cas, sont écrits, dans un document de pré-inscription daté :

- la **date du changement** (événement, release, modification algorithmique) — fixée sans connaître les données post ;
- la **fenêtre pré/post** — durée, granularité ;
- la **quantité mesurée** — définie opérationnellement, pas par ses variations ;
- la **direction attendue** — hypothèse H₀ : « pas d'effet » vs H₁ : « effet de signe σ » ;
- **ce qui constituerait une réfutation** — l'observation qui, si elle sort, invalide l'hypothèse.

Un cas dont **aucune observation ne pourrait décevoir l'hypothèse** ne rentre pas. C'est le filtre d'asymétrie : la pré-inscription refuse les hypothèses qui ne risquent rien.

### 3.1 Exemple travaillé — attachement (#12683)

> **Pré-inscription datée 2026-09-XX.**
>
> **Cas** : modification de l'algorithme de matching de Hinge (release T1 2025).
>
> **Date du changement** : 2025-03-15 (release publique annoncée par Hinge Engineering).
>
> **Fenêtre pré/post** : 2024-03 → 2025-03 (pré, 12 mois) ; 2025-03 → 2026-03 (post, 12 mois).
>
> **Quantité** : taux de « conversations > 5 messages » par match réussi (proxy d'engagement).
>
> **Hypothèse** : H₀ = pas de changement ; H₁ = changement positif de signe +, magnitude ≥ 5 %.
>
> **Réfutation** : observation d'un changement de signe − OU magnitude < 5 % dans la fenêtre post. Toute autre observation (bruit, saison) est neutre.

### 3.2 Pourquoi cette étape est le cœur du protocole

Sans pré-inscription, **toute mesure post hoc peut être racontée**. Le cas suggère la mesure ; la mesure confirme le cas. C'est la séquence que ce grain refuse. La pré-inscription est ce qui rend la séquence **cas → mesure** impossible à renverser en **mesure → cas**.

---

## 4. Renvoi vers l'outillage existant

L'outillage méthodologique est déjà livré dans :

[`../../Probas/DecisionTheory/Causal-Bridges/Quasi-Experimental.ipynb`](../../Probas/DecisionTheory/Causal-Bridges/Quasi-Experimental.ipynb)

Ce notebook porte : différence-en-différences, contrôle synthétique (SyntheticDiD), régression sur discontinuité (RDD), variables instrumentales (IV/2SLS). **Le protocole y renvoie ; il ne réimplémente rien.** Si une méthode manque pour un cas ultérieur, c'est une issue sur ce notebook, pas ici.

---

## 5. Critères d'acceptation (à vérifier à la review)

1. [ ] Les trois pièces ci-dessus existent (échelle 3 barreaux, biais signé, pré-inscription) avec un exemple travaillé **chacune**.
2. [ ] Au moins un exemple de **refus** (un cas qui ne passe pas la pré-inscription, et pourquoi) est documenté.
3. [ ] Le document nomme au moins un cas candidat **et le laisse non mesuré** : la sélection des 2-3 cas datables est un grain séparé, qui citera celui-ci.
4. [ ] **Aucune donnée n'est collectée dans ce grain.** Un livrable contenant des mesures est hors scope, même s'il est bon.
5. [ ] Le renvoi vers `Quasi-Experimental.ipynb` est un **lien vérifiable** (chemin correct, fichier présent), pas une mention.

---

## 6. Ce que ce protocole refuse délibérément

- **Ne pas créer trois notebooks ICT** (humour / désir / attachement) : la recommandation retenue sous #13303 est un observatoire transversal, pas une famille de plus.
- **Ne pas trancher** le choix du cas Bumble Opening Moves ni d'un autre : ce serait pré-choisir le résultat que le protocole doit pouvoir refuser.
- **Ne pas produire de mesure** : la production de mesures est un grain séparé, qui devra citer ce protocole et passer ses trois pièces.

---

## See also

- #13303 — EPIC parent (Observatoire des formes relationnelles)
- #12680 — humour (cas 1)
- #12682 — désir (cas 2)
- #12683 — attachement (cas 3)
- #12445 — livraison de l'outillage (Quasi-Experimental.ipynb, MERGED)
