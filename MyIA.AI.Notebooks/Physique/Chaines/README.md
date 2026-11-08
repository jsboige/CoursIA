# Chaînes — la physique comme réseaux de paires intriquées

Sous-série Physique de la collection [MyIA.AI.Notebooks](../../README.md), ouverte par
l'issue de distillation #25005. Le fil « chaînes » distille des programmes récents de
physique-de-l'information — un axiome informationnel unique dont on tire une conséquence
physique calculable — avec un patron strict : **Mesuré / Cité / Ouvert**. Ce que le carnet
rejoue lui-même (énumérations, écarts numériques) est Mesuré ; toute la chaîne dérivative
de la source est Cité ; et ce que la source ne prouve pas est listé ligne à ligne, jamais
maquillé en résultat établi. Les sources sont des preprints archivés au gisement avant
écriture, cités avec attribution, jamais recopiées en masse.

| Carnet | Ce qu'il démontre | Outils |
|---|---|---|
| [Chaînes-01 — L'axiome d'intrication et la constante de structure fine](Chaines-01-Axiome-Intrication-Constante-Structure-Fine-Python.ipynb) | Le programme Chain Theory (Wissner-Gross, 2026, preprint non relu) suivi de bout en bout : l'état maximalement intriqué vérifié, le plafond de lisibilité qui ne laisse que deux types de liens, la charge centrale identifiée à l'hypercharge ($Q = 6iY$ vérifié numériquement), l'objet qutrit–3 qubits, puis **notre propre énumération** des 172 enregistrements qui reconstruit les secteurs 79/48/42/3, la forme fermée $(79 + 48\sqrt2 + 42\sqrt3 + 3\sqrt6)/31\,104$ et son inverse à 60 chiffres — identique au script amont ; les écarts en $\sigma$ aux quatre déterminations expérimentales recalculés ($+0{,}6\,\sigma$ de CODATA 2022), la conjecture du photon tenue pour ce qu'elle est : non prouvée | numpy, matplotlib, decimal |

La sous-série se distingue du canon vérification-contre-solution-exacte du reste de la
série Physique : ici, la vérité indépendante du code est double — le calcul combinatoire
de la source, rejoué indépendamment, et les déterminations expérimentales citées. Une
conséquence de théorie (comme $\alpha_{\text{cand}}$) n'est jamais présentée comme une
prédiction validée : le statut épistémique de chaque affirmation est posé avant le calcul.
