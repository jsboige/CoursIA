# MANIFEST des figures README

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).

**Note d'audit c.488 (2026-07-14)** : migration vague-1 → format standard (sections *Contenu réel vérifié* + *Ce qui n'est PAS dans la figure* par figure). Audit vision **G.1 firsthand** par lecture directe des 6 PNG via `Read` tool. Méthode 4-pass formalisée c.481b-L1 : (1) lecture G.1 PNG + (2) croisement alt-text + (3) croisement MANIFEST + (4) `sha256sum` (ici : 6 SHA distincts — pas de permutation). Bilan : **5 ACCURATE sans correction** (ml21, ml22, ml24, ml25, ml26) + **1 correction réelle** (ml23 — l'alt-text v1 sur-vendait « OLS vs MLE » alors que la figure ne contient que la sigmoïde seule, sans droite OLS superposée).

## ml21-overfitting.png

- **Source** : notebook `2.1-Workflow-ML.ipynb` (cellule 11, output 0, `display_data` `image/png`)
- **SHA** : `40f2e98a9d17a56f` (taille 33 087 octets)
- **Alt-text (FR)** : Surapprentissage rendu visible : la courbe de score (train vs test) diverge quand la profondeur de l'arbre croît.
- **Poids** : 32.3 KB (natif)
- **Contenu réel vérifié (2026-07-14, c.488)** : **Single panel** matplotlib sans barre d'erreur. Axe x « profondeur de l'arbre (max_depth) » de 1 à 25 (25 points marqués) ; axe y « accuracy » de 0.70 à 1.00. Courbe **bleue « accuracy train »** monte rapidement de ~0.74 (profondeur=1) à 1.00 (profondeur=8) et reste à 1.00 (mémorisation). Courbe **orange « accuracy test »** monte de ~0.705 (profondeur=1) à un pic ~0.825 vers profondeur=4 puis redescend à ~0.77 (profondeur=8+) et reste stable (surapprentissage). Ligne pointillée verticale **grise « max test (profondeur=4) »** matérialise le compromis biais-variance optimal. Title « Surapprentissage visible : train vs test selon la complexité ». Légende en bas à droite.
- **Verdict** : **VRAI** — l'alt-text capture l'enseignement pédagogique (divergence train vs test avec la profondeur). Précision transférable : le pic test = 0.825 à profondeur=4 = compromis biais-variance optimal ; train sature à 1.0 (mémorisation du bruit).
- **Ce qui n'est PAS dans la figure** : pas de barre d'erreur ni IC 95% sur les courbes (un seul `train_test_split`) ; pas de courbe de validation croisée k-fold ; pas d'annotation du score AUC (la métrique est accuracy seulement).

## ml22-learning-rate.png

- **Source** : notebook `2.2-Descente-de-gradient.ipynb` (cellule 13, output 0, `display_data` `image/png`)
- **SHA** : `de5b8cbc136b2e58` (taille 31 297 octets)
- **Alt-text (FR)** : Effet du learning rate : trois régimes (trop lent, bon, divergent) sur la même fonction de coût.
- **Poids** : 30.6 KB (natif)
- **Contenu réel vérifié (2026-07-14, c.488)** : **Single panel** matplotlib **échelle log-y**. Axe x « iteration » 0→100 ; axe y « MSE » en log 10⁶ à 10⁷¹ (60 ordres de grandeur). Trois courbes : **« trop petit (0.001) »** bleu (quasi-plat à ~10⁶, descend très lentement), **« bon (0.05) »** orange (descend rapidement et se stabilise en <20 itérations), **« trop grand (1.5) »** vert (explose linéairement en log → de 10⁶ à ~10⁶² sur 100 itérations). Title « Effet du learning rate sur la convergence ». Légende en haut à gauche.
- **Verdict** : **VRAI** — alt-text capture l'enseignement (3 régimes divergent).
- **Ce qui n'est PAS dans la figure** : pas de visualisation du paysage de perte (loss surface) ni des trajectoires dans le plan des paramètres ; pas d'annotation de l'itération où la divergence devient irréversible ; pas de comparaison à un optimizer adaptatif (Adam, RMSProp).

## ml23-sigmoid.png

- **Source** : notebook `2.3-Regression-lineaire-logistique.ipynb` (cellule 13, output 0, `display_data` `image/png`)
- **SHA** : `2c8b33f802054e90` (taille 26 530 octets)
- **Alt-text (FR)** : Fonction sigmoïde : le score linéaire est écrasé en probabilité dans [0, 1] par la fonction de lien logistique (MLE).
- **Poids** : 25.9 KB (natif)
- **Contenu réel vérifié (2026-07-14, c.488)** : **Single panel** matplotlib **uniquement la fonction sigmoïde**. Axe x « score z = w.x + b » de -6 à 6 ; axe y « sigmoid(z) = probabilite » de 0.0 à 1.0. Courbe **bleue** lisse passant par (0, 0.5). Deux annotations verticales : **dashed gris « seuil 0.5 »** à z=0 et **dotted gris « z = 0 »** (axe de symétrie de la sigmoïde). Title « La fonction sigmoid ». Légende en haut à gauche avec les deux annotations.
- **Verdict** : **CORRIGÉ** (2026-07-14, c.488) — alt-text v1 affirmait « OLS vs MLE : droite vs sigmoïde », sous-entendant une superposition OLS droite dans la même figure. **La cellule ne contient que la sigmoïde seule, sans droite OLS** (la comparaison OLS droite est probablement dans une cellule antérieure ou postérieure du même notebook, ou dans une autre figure). Alt-text corrigé pour ne décrire que ce qui est réellement visible (la fonction sigmoïde seule et son seuil 0.5).
- **Ce qui n'est PAS dans la figure** : pas de droite OLS superposée ; pas de points de données observés (synthetic `make_classification`) ; pas de marqueurs sur le seuil (le seul annoté « 0.5 » est l'asymptote horizontale, pas un point expérimental) ; pas de MLE fitting (c'est la fonction de lien canonique, pas le résultat d'un ajustement).

## ml24-frontiere.png

- **Source** : notebook `2.4-Arbres-Forets-Ensembles.ipynb` (cellule 13, output 0, `display_data` `image/png`)
- **SHA** : `e2f86181761686d8` (taille 180 300 octets)
- **Alt-text (FR)** : Forêt aléatoire : la frontière de décision, escalier d'un arbre seul vs lissage par l'ensemble (réduction de variance géométrique, jeu de cancer du sein `mean radius` × `mean texture`).
- **Poids** : 176.1 KB (natif)
- **Contenu réel vérifié (2026-07-14, c.488)** : **2 panneaux côte à côte** sur le dataset `load_breast_cancer` réel, projection 2D des deux features `mean radius` (axe x 7.5→27.5) × `mean texture` (axe y 10→40). Points **rouges** (classe maligne) et **bleus** (classe bénigne) entremêlés. **Gauche : « Arbre seul (forte variance) »** — frontière en marche d'escalier avec rectangles rigides, ~5-6 paliers verticaux/horizontaux. **Droite : « Foret aleatoire (variance reduite) »** — frontière plus lisse (moins de paliers anguleux) mais pas radicalement différente visuellement ; l'enseignement est dans la **réduction du bruit** (les rectangles rouges/bleus de fond sont mieux alignés sur les classes). Légende implicite (rouge=maligne, bleu=bénigne via `ListedColormap`).
- **Verdict** : **VRAI** — alt-text capture l'enseignement (escalier vs lissage, réduction de variance).
- **Ce qui n'est PAS dans la figure** : pas de score/AUC affiché par panneau (la visualisation est géométrique, pas métrique) ; pas de frontière d'un troisième modèle (ex: SVM linéaire) pour comparaison supplémentaire ; pas d'indication du nombre d'arbres dans la forêt ; les deux features choisies ne sont pas les plus discriminantes du dataset (le panel retient 2 features sur 30 pour la lisibilité visuelle, le modèle complet en utilise davantage).

## ml25-roc.png

- **Source** : notebook `2.5-Biais-Variance-CV-ROC.ipynb` (cellule 15, output 1, `display_data` `image/png`)
- **SHA** : `a0a81cae1ece87bc` (taille 33 556 octets)
- **Alt-text (FR)** : Courbe ROC et AUC : le coût du seuil, arbitrage entre faux positifs et faux négatifs (régression logistique sur cancer du sein, AUC = 0.988).
- **Poids** : 32.8 KB (natif)
- **Contenu réel vérifié (2026-07-14, c.488)** : **Single panel** matplotlib. Axe x « Taux de faux positifs (FPR) » 0.0→1.0 ; axe y « Taux de vrais positifs (TPR = rappel) » 0.0→1.0. **Courbe bleue « Regression logistique (AUC = 0.988) »** qui monte quasi-verticalement dans le coin supérieur gauche (TPR ~0.95 à FPR ~0.05), puis s'aplatit progressivement vers (1.0, 1.0). **Diagonale pointillée noire « Hasard (AUC = 0.5) »** du coin (0,0) au coin (1,1). Title « Courbe ROC - Diagnostic cancer du sein ». Légende en bas à droite avec les deux labels et leurs AUC.
- **Verdict** : **VRAI** — alt-text capture l'enseignement (compromis FN/FP via le seuil).
- **Ce qui n'est PAS dans la figure** : pas de courbe ROC comparative d'un deuxième modèle (ex: arbre, SVM) — un seul modèle visualisé ; pas de marqueurs des seuils optimaux selon différents coûts métier (le coût asymétrique FN vs FP est mentionné dans le README mais pas annoté sur la courbe) ; pas d'intervalle de confiance bootstrap sur l'AUC ; pas de matrice de confusion annexée.

## ml26-pca.png

- **Source** : notebook `2.6-Clustering-KMeans-PCA.ipynb` (cellule 11, output 1, `display_data` `image/png`)
- **SHA** : `852911045e527679` (taille 168 736 octets)
- **Alt-text (FR)** : Réduction de dimension (ACP) : structure latente des chiffres manuscrits retrouvée sans étiquettes sur les deux premières composantes principales (colorisation a posteriori par vrai chiffre, colorbar 0-9).
- **Poids** : 164.8 KB (natif)
- **Contenu réel vérifié (2026-07-14, c.488)** : **Single panel** scatter matplotlib sur le dataset `load_digits` (1 797 images 8×8 = 1 797 points). Axe x « Composante principale 1 » -35→35 ; axe y « Composante principale 2 » -30→30. Points colorés selon le **vrai chiffre** (colorbar discrète à droite avec labels 0/1/2/3/4/5/6/7/8/9 et label « chiffre (vrai label, pour verification) »). Amas relativement distincts mais avec recouvrement significatif entre chiffres visuellement proches (4/5/6, 3/5/8). Title « Projection PCA (2 composants) - couleur = vrai chiffre ».
- **Verdict** : **VRAI** — alt-text capture l'enseignement (structure retrouvée sans étiquettes via PCA).
- **Ce qui n'est PAS dans la figure** : pas d'annotation du pourcentage de variance expliquée par chaque composante (information essentielle pour interpréter la projection 2D) ; pas de marqueurs des centres KMeans si le notebook enchaîne clustering après PCA (le titre précise « couleur = vrai chiffre » = usage a posteriori, pas clustering) ; pas de graphe de la variance expliquée cumulée (scree plot) ; la colorbar explicite « pour vérification » rappelle que les étiquettes n'ont pas servi à l'ajustement.
