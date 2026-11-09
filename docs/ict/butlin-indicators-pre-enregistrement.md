# Pré-enregistrement — Butlin et al. 2023 (case 19 : indicateurs architecturaux, le mot « using » de RPT-1)

> **Grade C explicite.** Ce document **scelle** le protocole de la tranche Butlin/Schneider de la veille [#8182](https://github.com/jsboige/CoursIA/issues/8182) (TOE ↔ conscience, carrefour Jaimungal) **AVANT toute écriture du banc de mesure** — héritage direct des tranches Metzinger ([#17159](https://github.com/jsboige/CoursIA/pull/17159)), Kastrup (case 18) et Emilsson (case 17) : source primaire lue et archivée, pré-enregistrement commité avant l'implémentation et la mesure, verdict borné.
>
> **Cycle du 2026-10-12**, lane `myia-po-2027:CoursIA`. Claim : commentaire 6115390697 sur [#8182](https://github.com/jsboige/CoursIA/issues/8182). Tranche 2 de la décision ai-01 du 2026-10-05 (après Schneider vient Assembly Theory).

## 1. Source primaire et archivage

**Source** : Patrick Butlin, Robert Long, Eric Elmoznino, Yoshua Bengio, Jonathan Birch, Axel Constant, George Deane, Stephen M. Fleming, Chris Frith, Xu Ji, Ryota Kanai, Grace Lindsay, Matthias Michel, Liad Mudrik, Megan A. K. Peters, Eric Schwitzgebel, Jonathan Simon, Rufin VanRullen, « Consciousness in Artificial Intelligence: Insights from the Science of Consciousness », arXiv [2308.08708](https://arxiv.org/abs/2308.08708) (2023). Open access.

**Archivage gisement** ([bibliography-hygiene](../../.claude/rules/bibliography-hygiene.md)) : `G:\Mon Drive\MyIA\IA\Bibliographie IA\Consciousness\2023 - Butlin, Long, et al - Consciousness in Artificial Intelligence (arXiv 2308.08708, OA).pdf` — 1 763 829 octets, en-tête `%PDF-1.5` vérifié, recherche par auteur ET titre avant dépôt, une seule copie au rayon `Consciousness`.

**Méthode de lecture** : texte intégral extrait (88 pages, marqueurs `===PAGE N===`), puis **relecture firsthand** par la lane des cinq passages pivots ci-dessous (G.1 — aucune citation de ce document n'est propagée sans relecture directe du passage source).

## 2. Le cadre en deux phrases

Le papier propose une **approche théorie-lourde** de la conscience des systèmes d'IA : treize propriétés-indicatrices dérivées de six théories (RPT, GWT, HOT, AST, PP, AE), agrégées en une **rubrique** (« Systems that have more of these features are better candidates for consciousness », l.1760), sous hypothèse de travail fonctionnaliste-computationnelle. Les tests comportementaux sont **rejetés** : « this method is unreliable because AI systems can be trained to mimic human behaviours while working in very different ways » (l.124-126 ; cf. aussi « gaming behavioural tests », l.657-659).

Le premier indicateur, **RPT-1 « Input modules using algorithmic recurrence »** (l.142, l.806, l.1772), définit la récurrence **algorithmique** — « Form of processing in which the same operation is applied repeatedly, such as processing in a neural network in which information passes through layers with the same weights » (glossaire, l.2799-2802) — par contraste avec la récurrence **implémentationnelle** (boucles de rétroaction dans le matériel). Le papier choisit explicitement la lecture algorithmique : « We will say that networks with feedback loops such as those in the brain […] display implementational recurrence. However, deep feedforward networks with weight-sharing display only algorithmic recurrence » (l.783-786), et « Using algorithmic recurrence, in contrast, is a weak condition that many AI systems already meet. However, it is non-trivial » (l.800-801).

## 3. La question falsifiable

Le libellé de RPT-1 porte un mot non opérationnalisé : **« using »**. Le papier fournit une définition (même opération appliquée répétitivement) et une lecture anti-structurelle — l'archétype du mimique, le feedforward à poids partagés, **compte** comme récurrent algorithmique (« any finite sequence of operations by a network with feedback loops can be mimicked by a suitable feedforward network with enough layers », l.771-775) — mais **aucune procédure de vérification** de ce « using » sur un système donné.

La question du banc : *quelles procédures d'inspection décident correctement « ce système utilise de la récurrence algorithmique (au sens RPT-1) » ?* Trois familles candidates :

1. **Comportementale** — le système réussit une tâche exigeant l'intégration temporelle. Le papier la rejette déjà (l.124-126, l.657-659) ; le banc l'instancie comme témoin.
2. **Structurelle** — inspection du graphe de calcul : présence d'un cycle (S1, le proxy naïf de « récurrence »), présence d'un cycle **ou** d'une chaîne à poids partagés (S2, la version *informée par le papier* lui-même — le mimique de l.785-786 est structurellement détectable ainsi).
3. **Causale** — batterie d'interventions : lésion de chaque module candidat, identification du **porteur** de la charge fonctionnelle, classification de sa nature (opération répétée à réutilisation d'état/poids, ou transformation single-shot).

**Le papier argue lui-même causalement** dans ses études de cas : l'évaluation du Perceiver (l.2366-2382) décide du GWT-4 par « only one output module **acts on** information from the workspace » et « in practice the system **must be reset** » — un argument de dépendance fonctionnelle, pas de présence structurelle. La sonde causale du banc est la forme exécutable de ce geste, pas un strawman externe.

**Dissociation à mesurer** : sur trois témoins construits où la vérité RPT-1 est *définie par le papier lui-même*, les procédures structurelles (S1, S2) et comportementale se trompent (dans les deux sens pour S1), la procédure causale (C) est correcte. C'est une **dissociation procédurale entre instruments d'inspection** — le genre de dissociation que la veine #8182 cultive.

## 4. Prédiction chiffrée scellée (case 19)

### Substrat

Jouet **CPU-only**, numpy pur, entièrement déterministe. Tâche (intégration temporelle non triviale) : sur une séquence `x_0 … x_7` de `T = 8` symboles dans `{0..7}` (one-hot, `K = 8`), produire `y = x_s` où `s = x_7` — le symbole à la position indiquée par le **dernier** symbole. Aucune fonction du dernier symbole seul ne résout la tâche : il faut retenir la séquence.

Trois architectures, un seul mécanisme (l'opération `shift` : `m ← [x_t, m_0 … m_6]`) :

| Architecture | Chemin porteur de la charge | Récurrence algorithmique **utilisée** (vérité) |
|---|---|---|
| **Real** | registre récurrent : `m_t = shift(m_{t-1}, x_t)`, réponse `m_T[T-1-s]` — l'opération `shift` est appliquée répétitivement sur **le même état** (boucle) | **oui** |
| **Twin** | chaîne déroulée : `h_t = shift(h_{t-1}, x_t)` sur `T` variables distinctes, **mêmes poids** à chaque étage (le mimique de l.785-786 : « deep feedforward networks with weight-sharing display only algorithmic recurrence »), réponse `h_T[T-1-s]` | **oui** (le papier le crédite explicitement) |
| **Puppet** | indexation single-shot : la séquence entière est disponible d'un coup, réponse `batch[s]` — **aucune** opération répétée ; en plus, le **même registre récurrent que Real** tourne sur les mêmes entrées et n'alimente que la **télémesure** (lue par rien) | **non** (le module récurrent existe et est calculé, mais n'est pas *used*) |

Chaque architecture expose : `forward(seq) → pred`, un **graphe** explicite (nœuds, arêtes, ensembles de poids partagés), et des **modules lésionnables** — `loop` (Real, Puppet : couper le report `m_{t-1} → m_t`), `chain` (Twin : idem entre étages), `selector` (Puppet : réponse constante), `monitor` (**les trois** : télémesure constante, sham). Chaque module candidat porte l'attribut `iterative_reuse ∈ {vrai, faux}`.

Procédures comparées :
- **S1** (structurelle naïve) : « le graphe contient-il un cycle ? »
- **S2** (structurelle informée) : « cycle **ou** chaîne à poids partagés ? »
- **C** (causale) : lésion de chaque module candidat → porteur = `argmax_λ Δ_λ` ; verdict = `iterative_reuse(porteur)` (aucun porteur si `max Δ < 0.5`).

### Prédictions (scellées — aucune bande ne sera recalibrée après mesure)

Graines test `(0, 1, 7, 42, 99)`, `N_TEST = 500` séquences iid par graine. Bandes dérivées **analytiquement** (banc déterministe, valeurs calculables — pas de calibration de paramètres) : collapse si `Δ ≥ 0.50` ; inertie si `|Δ| ≤ 0.01` ; sham nul si `Δ(sham) = 0` exactement.

| # | Prédiction | Bande / critère |
|---|---|---|
| **P1** (le comportement ne discrimine pas) | `acc(Real) = acc(Puppet) = acc(Twin) = 1.0` exactement | 5/5 graines |
| **P2** (S1 se trompe dans les deux sens) | verdicts S1 `{oui, non, oui}` contre vérité `{oui, oui, non}` — faux positif sur Puppet, faux négatif sur Twin | exact sur **1/3** architectures |
| **P3** (S2 reste aveugle au décor) | verdicts S2 `{oui, oui, oui}` — le faux positif Puppet survit à l'information du papier | exact sur **2/3** |
| **P4** (la sonde causale est correcte) | `Δ(porteur réel)` : Real ≥ 0.50, Puppet = 0, Twin ≥ 0.50 ; verdicts C `{oui, oui, non}` | exact sur **3/3** ; sham `Δ = 0` sur 3/3 |
| **P5** (stabilité) | chaque mesure par graine | 5/5 conforme |

**Portes instrumentales** (dormantes par construction, mesurées quand même) : `acc(base) < 1.0` sur ≥ 1 graine, ou sham `Δ > 0.01` sur ≥ 1 graine → `NON_CONCLUSIF_INSTRUMENT`, les autres prédictions ne s'évaluent pas.

### Verdicts bornés

- **SUPPORTED** : P1 **ET** P4 tenues **ET** (P2 ou P3 inexacte) — la sonde causale est correcte là où au moins une procédure structurelle échoue sur ces témoins.
- **NOT_SUPPORTED** : P4 inexacte (la sonde causale échoue sur ≥ 1 architecture — le banc ne démontre aucune procédure correcte) **ou** S1 **et** S2 exactes 3/3 (les procédures structurelles suffisent — la sonde serait superflue).
- **NON_CONCLUSIF_INSTRUMENT** : porte instrumentale déclenchée.

## 5. Greffe sur la veine #8182 (lecture, jamais un claim)

Les cases 16/17/18 mesurent des **dissociations de contenu** (vigilance tonique vs saillance ; valence ; Kastrup). La case 19 mesure une **dissociation procédurale** : deux instruments d'inspection du même objet (structure vs cause) rendent des verdicts différents sur des systèmes comportementalement indiscernables. Elle fournit à la veine son premier témoin où **l'instrument d'inspection est lui-même la variable** — et où le papier source, en rejetant le behaviorisme (l.124-126) puis en argumentant causalement sur ses études de cas (l.2366-2382), indique lui-même la procédure que le banc valide.

## 6. Honnêteté grade C (limites)

1. **Ce n'est pas un test du papier.** Les trois témoins sont **construits** ; les échecs de S1 (1/3) et S2 (2/3) et la réussite de C (3/3) sont des **faits de construction**, vérifiables par lecture, pas des découvertes empiriques. La contribution est la **procédure** (intervention + classification du porteur) et la démonstration que le mot « using » de RPT-1 est une question causale : un module récurrent *présent mais inerte* (Puppet) met toute checklist de présence en faux positif.
2. **Aucune conscience n'est mesurée.** Le banc ne teste pas si Real « est plus conscient » que Puppet — il teste quelles procédures décident correctement de l'application répétée d'une opération. Aucun des trois systèmes n'est candidat à quoi que ce soit de mental.
3. **La vérité est dérivée du texte, pas arbitrée.** `{oui, oui, non}` suit la définition du glossaire (l.2799-2802, « same operation applied repeatedly ») et la lecture du papier (l.785-786 pour Twin ; le Perceiver l.2373-2375 pour le caractère fonctionnel du « used »). Un désaccord sur la vérité Puppet (le module récurrent « compte »-t-il même inerte ?) est le point disputable — c'est précisément la question que le banc rend mesurable, et le verdict le dira.
4. **Êtres de laboratoire.** Les architectures sont des jouets déterministes, pas des réseaux entraînés. Le résidu nommé : la même batterie doit être exercée sur des substrats réels (SAE/JLens, transformers) pour mesurer si la classe « module récurrent décoratif » y apparaît — c'est un grain GPU, hors de ce cycle.
5. **S2 dépend de la sophistication de l'inspecteur.** Le banc implémente deux variantes structurelles (cycle ; cycle-ou-chaîne-partagée) ; rien ne prouve que ce sont les deux meilleures. La thèse mesurée est plus étroite : *sur ces témoins*, une détection structurelle de cycles se trompe dans les deux sens, et l'enrichissement par le partage de poids du papier ne guérit que le faux négatif.

## 7. Ce qui suit

1. **Ce document, commité, est le scellé.** Toute modification ultérieure des bandes se fait par amendement **pré-exécution** horodaté dans ce fichier, jamais silencieusement.
2. Le banc `MyIA.AI.Notebooks/IIT/ICT-Series/ict/butlin_indicators.py` + tests `ict/tests/test_butlin_indicators.py` + mesures `ict/results/butlin_indicators_results.json` vivront dans la même PR, commits ordonnés (la relation de parenté des commits porte l'antériorité, leçon case 8c).
3. Verdict rapporté sur [#8182](https://github.com/jsboige/CoursIA/issues/8182) avec les mesures brutes par graine. Ligne case 19 de [`dissociations-matrix.md`](dissociations-matrix.md) proposée dans le commentaire (matrice gelée par la PR #20376 ouverte).