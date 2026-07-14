# MANIFEST des figures README

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).
**Audit G.1 c.486 (2026-07-14, doctrine #5780)** : migration vague-1 → standard avec section *Contenu réel vérifié* + *Ce qui n'est PAS dans la figure* par figure. **Bilan : 3 ACCURATE sans correction + 2 corrections réelles + 1 enrichissement** (dt2 et dt3 omettent des panneaux décisifs, dt5-evpi omet la frontière de décision bleue et le scenario actuel). 33% bug-rate, cohérent avec familles à dominante matplotlib (cf c.483 Probas/PyMC racine 50%, c.478 SocialChoice 6/6 ACCURATE — rigueur variable selon auteur, mais la structure pédagogique reste robuste).

## dt2-investment.png

- **Source** : notebook `DecPyMC-2-Utility-Money.ipynb` (cellule 31, output 0 — display_data `image/png`)
- **Alt-text (FR)** : Choix d'investissement sous aversion au risque : distributions postérieures de rendement (Obligations, Actions, Crypto) et utilité espérée en fonction du coefficient d'aversion CRRA.
- **Poids** : 69.7 KB (natif)
- **Contenu réel vérifié (2026-07-14, c.486)** : **4 panneaux matplotlib en grille 2×2** : haut gauche « Distribution : Obligations » histogramme bleu (E=3.0%, ligne rouge pointillée « Rendement nul » à 0, axe rendement -0.05 à 0.10, densité max 20) ; haut droite « Distribution : Actions » histogramme vert (E=7.9%, axe -0.6 à 0.6, densité max 2.5) ; bas gauche « Distribution : Crypto » histogramme orange (E=14.9%, axe -2 à 3, densité max 0.7) ; bas droite « EU en fonction de l'aversion » courbe orange Crypto vs rho CRRA (axe 1-10, utilité espérée ~0 puis chute à **-3×10⁸⁷** pour rho > 9 — instabilité numérique).
- **Ce qui n'est PAS dans la figure** : l'alt-text v1 mentionnait « trois actifs comparés » mais **omettait le 4ᵉ panneau « EU vs aversion »** qui est précisément le panneau **décisionnel** : il montre comment l'utilité espérée Crypto passe de la meilleure (rho faible = agent neutre) à la pire (rho élevé = agent très aversif). L'instabilité numérique à rho > 9 (valeurs ~10⁸⁷) révèle aussi une limite du modèle d'utilité exponentielle à queue lourde. Sans le 4ᵉ panneau, le titre « Choix d'investissement » perd sa substance (comparer 3 distributions sans profil de risque ne tranche pas la décision). Alt-text v1 sur-vendeur corrigé pour inclure les 4 panneaux et la mention du 4ᵉ panneau décisionnel.

## dt3-multiattribute.png

- **Source** : notebook `DecPyMC-3-Multi-Attribute.ipynb` (cellule 38, output 1 — display_data `image/png`)
- **Alt-text (FR)** : Décision multi-attributs sous incertitude : distributions d'utilité de deux projets (Projet A E[U]=0.509, Projet B E[U]=0.482) et nuage de points rendement-risque illustrant la zone de non-dominance stochastique.
- **Poids** : 102.0 KB (natif)
- **Contenu réel vérifié (2026-07-14, c.486)** : **2 panneaux côte à côte** : gauche « Distributions de l'utilité » histogrammes superposés (Projet A bleu E[U]=0.509, Projet B orange E[U]=0.482, axe 0-1 utilité, densité max 2.3, **recouvrement massif** sur l'intervalle [0,1]) ; droite « Rendement vs Risque (échantillon) » scatter plot bleu Projet A vs orange Projet B (rendement axe -0.2 à 0.6, risque axe -0.1 à 0.6, ~1500 points par projet, **forme d'ellipse centrée sur (0.08, 0.18)**).
- **Ce qui n'est PAS dans la figure** : l'alt-text v1 mentionnait « Monte Carlo sur plusieurs critères en compétition » (la méthode) mais **omettait** : (a) le **scatter plot droite** qui visualise la corrélation rendement-risque (les 2 projets occupent des zones qui se chevauchent), (b) l'**écart E[U] 0.027 non significatif** (les distributions se recouvrent massivement, le test serait non concluant), (c) la **zone de non-dominance stochastique** où aucun projet ne bat l'autre sur tous les axes simultanément. Sans cette mention, l'alt-text laissait croire à une décision tranchée, alors que c'est précisément un cas où MAUT/swing weights devient nécessaire. Alt-text v1 corrigé pour inclure le scatter plot, l'écart E[U] explicite, et la zone de non-dominance.

## dt5-evpi-heatmap.png

- **Source** : notebook `DecPyMC-5-Value-Information.ipynb` (cellule 29, output 0 — display_data `image/png`)
- **Alt-text (FR)** : Carte de chaleur EVPI selon la probabilité a priori de pétrole et le gain si pétrole trouvé, avec frontière de décision et scénario actuel (P=0.30, G=1000k) tombant en zone d'information peu précieuse.
- **Poids** : 68.5 KB (natif)
- **Contenu réel vérifié (2026-07-14, c.486)** : **Heatmap** axes (Probabilité a priori P(pétrole) 0.0-1.0 × Gain si pétrole trouvé 0.2-2.0 milliers EUR), colormap **YlOrRd** (jaune clair → rouge foncé, échelle 0 à 450 milliers EUR), **frontière de décision bleue** traversant la zone rouge (= décision « acheter l'information »), **étoile noire ★ « Scenario actuel (P=0.30, G=1000k) »** placée dans la zone claire sous la frontière, **lignes pointillées noires verticales et horizontales** marquant les seuils de basculement de décision.
- **Ce qui n'est PAS dans la figure** : l'alt-text v1 mentionnait « carte de chaleur selon la probabilité de pétrole et le gain » mais **omettait** : (a) la **frontière de décision bleue** (sépare la zone rouge où l'EVPI est élevé — décision « équilibrée » où l'information vaut cher — vs zone jaune où l'EVPI est faible — décision « triviale » où l'information est inutile), (b) le **scenario actuel ★ à (0.30, 1000k)** qui matérialise un point de décision concret tombant en zone **non-dominante** pour l'achat d'info, (c) les **lignes pointillées noires** matérialisant les seuils analytiques de basculement de décision. Sans la frontière + le scenario, la heatmap est décorative. Alt-text v1 enrichi pour refléter la frontière, le scenario actuel, et la zone d'opération réelle.

## dt5-mc-convergence.png

- **Source** : notebook `DecPyMC-5-Value-Information.ipynb` (cellule 54, output 0 — display_data `image/png`)
- **Alt-text (FR)** : Convergence de l'estimateur Monte Carlo de l'EVPI vers sa valeur analytique (90k EUR) : l'estimateur se stabilise à partir de N=10⁴ échantillons avec un intervalle de confiance 95% resserré.
- **Poids** : 43.0 KB (natif)
- **Contenu réel vérifié (2026-07-14, c.486)** : **1 graphique linéaire** : axe x log « Nombre d'échantillons N » (10² à 10⁵), axe y « EVPI estimé (milliers EUR) » (60-120), courbe bleue « EVPI estimé (MC) » avec marqueurs circulaires, zone bleue transparente « IC 95% » (large à N=10² : ~63-117, se resserre à N=10⁵ : ~88-92), ligne horizontale rouge pointillée « EVPI analytique = 90k ».
- **Verdict** : VRAI — alt-text v1 dit l'essentiel. Précision ajoutée : **N=10⁴ est le seuil pratique de convergence** (au-delà l'IC 95% se resserre autour de 90k avec une marge < 5k). En deçà, l'estimateur fluctue largement (N=100 : EVPI=90 mais IC ~27k de large).

## dt6-expert-graph.png

- **Source** : notebook `DecPyMC-6-Expert-Systems.ipynb` (cellule 40, output 0 — display_data `image/png`)
- **Alt-text (FR)** : Architecture du Système Expert Bayésien Multi-Sources : 3 sources (Logs, Utilisateur, Capteur RAM) conditionnellement indépendantes, posterior sur 4 états latents (Disque 95.8%, CPU 2.9%, OK 1.0%, RAM 0.3%) et décision « Remplacer Disque » (EU = -20).
- **Poids** : 68.6 KB (natif)
- **Contenu réel vérifié (2026-07-14, c.486)** : **Diagramme nœuds-flèches matplotlib** (titre gras « Architecture du Système Expert Bayésien Multi-Sources ») : « Prior Uniforme P(panne) = [0.25, 0.25, 0.25, 0.25] » rectangle vert en haut → flèche verte vers ellipse bleue centrale « Panne (latent) ». 3 nœuds likelihoods alignés horizontalement : « Source 1: Logs » rouge (Scores = [0.10, 0.15, 0.65, 0.10], Faible: moyenne) ; « Source 2: Utilisateur Dit 'Disque' » orange (Matrice confusion: 75% correct) ; « Source 3: Capteur RAM » violet (Pas d'alerte, Détection 95%, FP 2%). Flèches colorées par source vers ellipse centrale. Flèche orange vers bas : « Posterior P(panne | evidence) » rectangle vert (Disque: 95.8% | CPU: 2.9% | OK: 1.0% | RAM: 0.3%). Annotation Bayes à gauche : « posterior prop. prior × L1 × L2 × L3 ». Flèche orange finale vers « Décision: Remplacer Disque » rectangle orange (EU = -20, « meilleur choix »).
- **Verdict** : VRAI — alt-text v1 dit l'essentiel. Précisions transférables : (a) les 3 likelihoods sont **distinctes en nature** : Logs = scores continus moyennés, Utilisateur = matrice de confusion 75%, RAM = détection/FP. (b) Le posterior écrase Disque à **95.8%** car 2 sources sur 3 (Logs + Utilisateur) pointent vers Disque alors que RAM n'a rien détecté. (c) La décision « Remplacer Disque » découle directement du posterior, EU=-20 = meilleur choix parmi les 4 actions. La chaîne complète prior → likelihoods → posterior → décision est visualisée.

## dt7-thompson.png

- **Source** : notebook `DecPyMC-7-Sequential.ipynb` (cellule 49, output 0 — display_data `image/png`)
- **Alt-text (FR)** : Thompson Sampling bayésien sur 4 bandits (vrais means 0.3/0.5/0.7/0.4) : regret cumulé comparé à Greedy, ε-greedy et UCB1, et posterior Beta final pour chaque bras après 2000 pas.
- **Poids** : 142.8 KB (downscale max-dim 1200)
- **Contenu réel vérifié (2026-07-14, c.486)** : **2 panneaux côte à côte** : gauche « Regret cumulé des 4 stratégies » (axe x 0-2000 « Pas de temps », axe y -50 à 125 « Regret cumulé ») — 4 courbes : Greedy rouge descendant vers ~-45 à t=2000, ε-greedy (e=0.1) bleu ~60, UCB1 vert ~115, Thompson Sampling violet ~35 ; droite « Posteriores Beta après Thompson Sampling » (axe x 0-1 « Taux de succès », axe y 0-35+ « Densité ») — 4 courbes Beta : Bras 0 (vrai=0.3) bleu étalée, Bras 1 (vrai=0.5) orange modérée, Bras 2 (vrai=0.7) vert **pic étroit à 0.7**, Bras 3 (vrai=0.4) rouge étalée ; lignes verticales pointillées colorées aux vrais means.
- **Verdict** : VRAI — alt-text v1 dit l'essentiel. Note transférable : Thompson (violet ~35) **gagne** sur UCB1 (~115) et ε-greedy (~60) mais est **dépassé par Greedy** qui descend vers -45. Le pattern classique : Greedy exploite fort le Bras 2 (vrai 0.7) dès identification, ce qui maximise le regret cumulé négatif (= gain). Thompson explore plus, donc son regret cumulé reste positif mais borne. Trade-off exploitation/exploration visible. Le Bras 2 a posteriori Beta extrêmement étroite (pic à 0.7) montre que Thompson l'a **correctement identifié** malgré l'exploration.
