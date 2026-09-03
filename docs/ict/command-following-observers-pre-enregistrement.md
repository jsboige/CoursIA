# Pré-enregistrement — observateurs du suivi de commande covert

> **Statut.** Grade **T-pré-enregistrement** : protocole verrouillé avant implémentation et avant mesure. Ce document ne rapporte aucun résultat du jouet. Il distille la première étape P0 de [#8182](https://github.com/jsboige/CoursIA/issues/8182), sans simuler ni mesurer la conscience.
>
> **Objet formel.** Un état latent binaire `C` (« capacité de suivre volontairement une commande dans le paradigme ») est observé par plusieurs canaux imparfaits : comportement moteur, imagerie EEG et imagerie fMRI. Le banc quantifie l'asymétrie diagnostique : un résultat neuronal positif est informatif si sa spécificité est haute ; un résultat négatif n'établit pas l'absence de capacité quand la sensibilité est imparfaite.

## Sources primaires lues intégralement

1. Adrian M. Owen et al., « Detecting Awareness in the Vegetative State », *Science* 313 (2006), 1402, DOI [`10.1126/science.1130197`](https://doi.org/10.1126/science.1130197). Cas unique : imagerie tennis/navigation reproductible et spécifique de la commande. Les auteurs signalent explicitement que les résultats négatifs ne prouvent pas l'absence d'awareness, les faux négatifs fMRI étant courants même chez les contrôles sains.
2. Damian Cruse et al., « Bedside detection of awareness in the vegetative state: a cohort study », *The Lancet* 378 (2011), 2088–2094, DOI [`10.1016/S0140-6736(11)61224-5`](https://doi.org/10.1016/S0140-6736(11)61224-5). Cohorte : 16 patients diagnostiqués VS et 12 contrôles sains. Trois patients ont produit un signal EEG discriminable (`61–78 %`) ; 9/12 contrôles ont été positifs en suivi de commande ; 0/12 l'ont été dans la condition « écouter sans suivre ». Les 3/12 contrôles conscients négatifs interdisent de lire un résultat nul comme absence de capacité.
3. Aaron Schurger, Jacobo D. Sitt et Stanislas Dehaene, « An accumulator model for spontaneous neural activity prior to self-initiated movement », *PNAS* 109 (2012), E2904–E2913, DOI [`10.1073/pnas.1210467109`](https://doi.org/10.1073/pnas.1210467109). Lecture de contrôle : sa dissociation `readiness potential moyen ≠ décision préalable` relève d'un biais d'alignement sur franchissement de seuil, pas d'une erreur d'observation d'un état latent. Elle formera un grain séparé ; aucune synthèse Owen×Schurger n'est revendiquée ici.

## Claim, contre-claim et périmètre

- **Claim testé.** Une absence de manifestation comportementale ne permet pas d'inférer l'absence de suivi volontaire de commande ; un observateur neuronal peut rendre visible une capacité latente.
- **Contre-claim adversarial.** Le signal neuronal classifié pourrait provenir d'une réponse automatique aux instructions plutôt que d'un suivi volontaire. Dans le modèle, ce contre-claim est représenté par un taux de faux positifs neuronal non négligeable.
- **Non-claim.** `C` n'est ni la conscience phénoménale, ni l'agentivité générale, ni un diagnostic clinique. Le jouet ne transforme pas un classifieur en « détecteur de conscience » ; il borne ce qui est inférable à propos de la capacité opérationnelle testée.

## Modèle verrouillé

Chaque observateur `j` possède une sensibilité `Se_j = P(+ | C)` et une spécificité `Sp_j = P(- | ¬C)`. Les données de contrôle Cruse alimentent deux postérieurs indépendants avec un prior uniforme `Beta(1, 1)` :

- suivi volontaire : `Se_EEG ~ Beta(10, 4)` à partir de 9 positifs et 3 négatifs ;
- null « écouter sans suivre » : `Sp_EEG ~ Beta(13, 1)` à partir de 0 positif et 12 négatifs.

Pour une prévalence hypothétique `p = P(C)`, les valeurs prédictives sont :

```text
PPV = p·Se / (p·Se + (1-p)·(1-Sp))
NPV = (1-p)·Sp / ((1-p)·Sp + p·(1-Se))
P(C | résultat négatif) = 1 - NPV
```

Le banc tire `50 000` couples `(Se, Sp)` par graine pour les graines `(0, 1, 7, 42, 99)`. Il balaie `p ∈ {0.05, 0.10, 0.20, 0.40}`. Les quantiles inter-tirages, et non les moyennes seules, portent le verdict.

### Observateurs comparés

1. **Comportement seul.** Sensibilité fixée à `0` dans la classe précisément étudiée (patient sans manifestation comportementale), spécificité `1`. Ce bras illustre une non-identifiabilité par construction ; il n'est pas présenté comme une estimation de la sensibilité du CRS-R en population générale.
2. **EEG calibré.** Postérieurs `Beta(10,4)` et `Beta(13,1)` ci-dessus.
3. **EEG adversarial automatique.** Même sensibilité, mais `Sp_auto ~ Beta(9,5)`, centré vers `0,64` : le null n'exclut plus suffisamment une réponse automatique. Ce scénario n'est pas une mesure Cruse ; c'est le stress test explicite du contre-claim.
4. **Fusion comportement + EEG.** Règle OR (« positif si l'un des canaux est positif »), avec indépendance conditionnelle déclarée. Dans la sous-population sans comportement, cette fusion doit se réduire exactement à l'EEG ; elle ne peut fabriquer de gain.

## Prédictions falsifiables

Les seuils ci-dessous sont verrouillés avant implémentation.

| ID | Prédiction | Critère sur 5 graines | Lecture si échec |
|---|---|---|---|
| **P1 — positif informatif** | Sous calibration Cruse et `p=0,20`, un positif EEG doit relever substantiellement la probabilité de capacité. | médiane du `PPV` médian ≥ **0,55** et quantile 5 % du PPV ≥ **0,25**, dans ≥4/5 graines | Les données de contrôle sont trop faibles pour soutenir un positif informatif à cette prévalence. |
| **P2 — négatif non conclusif** | Sous calibration Cruse et `p=0,20`, un négatif doit laisser une masse postérieure non triviale sur `C`. | médiane de `P(C | -)` ≥ **0,04**, dans 5/5 graines | Le banc aurait artificiellement transformé une sensibilité imparfaite en exclusion. |
| **P3 — observateurs non interchangeables** | Dans la sous-population comportementalement nulle, fusion OR et EEG seul sont identiques. | différence absolue PPV et `P(C|- )` < **1e-12** pour chaque tirage agrégé | Le modèle fabrique de l'information à partir d'un canal constant. |
| **P4 — null adversarial** | Relâcher la spécificité doit faire chuter la force du positif. | à `p=0,20`, ratio des médianes `PPV_auto / PPV_calibré` ≤ **0,60**, dans ≥4/5 graines | Le banc est insensible au contre-claim automatique et surinterprète le signal. |
| **P5 — dépendance à la prévalence** | Un positif n'a pas une signification universelle : son PPV doit augmenter avec `p`. | médianes strictement croissantes pour `p={0,05,0,10,0,20,0,40}`, dans 5/5 graines | Le calcul prédictif ignore le taux de base. |

### Verdict

- `SUPPORTED` si P1–P5 passent.
- `INCONCLUSIVE` si P2, P3 et P5 passent mais P1 ou P4 échoue : l'asymétrie logique tient, mais la calibration est trop faible.
- `FALSIFIED_MODEL` si P2, P3 ou P5 échoue : le banc ne représente pas correctement l'asymétrie diagnostique revendiquée.

Un échec est conservé et rapporté ; aucun seuil ne sera recalibré après mesure dans la PR d'exécution.

## Contrôles instrumentaux

- Formules fermées : `PPV=1` lorsque `Sp=1` et `Se>0`; `PPV=p` lorsque `Se=1-Sp` (observateur non informatif).
- Monotonicité : à `Se, Sp` fixés, PPV croît avec la prévalence et avec la spécificité.
- Déterminisme : même graine, mêmes tirages et mêmes agrégats.
- Domaines : rejet des probabilités hors `[0,1]` et des tailles d'échantillon non positives.

## Livrables d'exécution

La tranche suivante, dans un commit distinct, portera :

- `MyIA.AI.Notebooks/IIT/ICT-Series/ict/command_following_observers.py` ;
- `MyIA.AI.Notebooks/IIT/ICT-Series/ict/tests/test_command_following_observers.py` ;
- `MyIA.AI.Notebooks/IIT/ICT-Series/ict/results/command_following_observers_results.json`.

Aucun notebook ni sortie de cellule n'est modifié. Le registre [`dissociations-matrix.md`](dissociations-matrix.md) reste hors scope pour éviter les claims périmés qui le couvrent encore ; le résultat pourra y être relié par une tranche ultérieure de sa lane propriétaire.
