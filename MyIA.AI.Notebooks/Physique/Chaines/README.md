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
| [Chaînes-02 — La règle de Born, l'unitarité et la relation d'incertitude](Chaines-02-Born-Unitarite-Incertitude-Python.ipynb) | Les chapitres 40-41 du compendium (Wissner-Gross, 2026, preprint non relu) : les trois noms que la littérature appelle règle de Born, unitarité et incertitude, **tous les trois théorèmes conditionnels** à la source. L'équivalence du pli plat (éq. 51) vérifiée dans les deux sens, l'envariance $(U \otimes \bar U)\lvert\omega\rangle = \lvert\omega\rangle$ mesurée sur unitaires aléatoires, le canon $\mathrm{Tr}(\rho P)$ (éq. 56), le join de la figure 15 unitaire sur son support, la relation de Weyl aux dimensions 2-3-4, **nos recensements indépendants** des paires de lettres non commutantes (3/24/84) et des paires de bases distinctes (3/6/21) — les comptes du census de la source retrouvés par énumération — et la borne de Robertson (éq. 57) aux sept registres : saturée aux six purs, écart de $1/16$ au registre plein ; les prémices ouvertes (2.4-2.8, 18.5-18.6, monogamie, valence) listées ligne à ligne | numpy |
| [Chaînes-03 — La mesure : le lavage à un acte et la POVM](Chaines-03-Mesure-Lavage-POVM-Python.ipynb) | Le chapitre 42 du compendium (Wissner-Gross, 2026, preprint non relu) : la lecture collective de la toile jointe, l'objet que la littérature classe sous la POVM — un **théorème conditionnel**. L'arithmétique exacte que la source invite à reprendre : le corps à neuf sites et dix liens, $S_1 = 1350$, les quatre comptes de paires 863298 / $-863298$ / 94608 / 1296 refermés par $1350^2$ ; le **swap d'intrication** rejoué aux quatre issues (une par lettre de Weyl, fidélité exacte, sous-produit = la lettre) ; la **trine** complète $\sum_i E_i = I$ comme référentiel du gloss — contre les **dix-sept effets** de l'électron dont la somme part du registre debout : la relation de complétude, frontière exacte du chapitre, listée ligne à ligne avec les prémices ouvertes | numpy |

La sous-série se distingue du canon vérification-contre-solution-exacte du reste de la
série Physique : ici, la vérité indépendante du code est double — le calcul combinatoire
de la source, rejoué indépendamment, et les déterminations expérimentales citées. Une
conséquence de théorie (comme $\alpha_{\text{cand}}$) n'est jamais présentée comme une
prédiction validée : le statut épistémique de chaque affirmation est posé avant le calcul.
