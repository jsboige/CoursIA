# MANIFEST des figures README

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).
**Audit G.1 c.483 (2026-07-14, doctrine #5780)** : migration vague-1 → standard avec section *Contenu réel vérifié* + *Ce qui n'est PAS dans la figure* par figure. **Bilan : 3 ACCURATE sans correction + 3 corrections réelles** (pymc2, pymc5, pymc15). 50% bug-rate, cohérent avec familles à dominante matplotlib (L478-L1 — rigueur variable selon auteur).

## pymc2-gaussian-mixtures.png

- **Source** : notebook `PyMC-2-Gaussian-Mixtures.ipynb` (cellule 4, output 6)
- **Alt-text (FR)** : Inférence bayésienne sur les temps de trajet : postérieures de la moyenne (μ) et de la précision (τ) du modèle Normal simple.
- **Poids** : 44.4 KB (PIL optimisé)
- **Contenu réel vérifié (2026-07-14, c.483)** : **2 panneaux de densité postérieure ArviZ** : gauche `mu` mean=16, 94% HDI [14, 18], axe 10-22 ; droite `tau` mean=0.081, 94% HDI [0.025, 0.14], axe 0-0.25. Title « Posterior : moyenne et precision du temps de trajet ». KDE posteriors ArviZ authentiques, avec barres HDI noires.
- **Ce qui n'est PAS dans la figure** : aucun mélange de gaussiennes n'est visible (le « Gaussian Mixtures » du nom de fichier et de l'alt-text v1 fait référence au *notebook source*, pas au *contenu de cette cellule précise* — le notebook PyMC-2 illustre le modèle Normal simple sur les temps de trajet AVANT d'aborder le modèle de mélange dans les cellules ultérieures, ex. cell[16] `sigma_components`). Alt-text v1 sur-vendeur corrigé.

## pymc5-irt-curves.png

- **Source** : notebook `PyMC-7-Skills-IRT.ipynb` (cellule 15, output 3)
- **Alt-text (FR)** : Évaluation IRT : courbe ROC du modèle sur la prédiction de réussite aux items, AUC=0.788 au-dessus du hasard.
- **Poids** : 29.3 KB (PIL optimisé)
- **Contenu réel vérifié (2026-07-14, c.483)** : **Courbe ROC sklearn-style** : axe x « Taux de faux positifs » 0-1, axe y « Taux de vrais positifs » 0-1, courbe bleue IRT (AUC=0.788) + diagonale pointillée noire « Aleatoire ». Title « Courbe ROC - Modele IRT ».
- **Ce qui n'est PAS dans la figure** : aucune « courbe de réponse aux items » au sens IRT canonique (probabilité de bonne réponse vs compétence latente) n'est tracée — il s'agit d'une **évaluation** (discrimination binaire items réussis/échoués), pas des courbes ICC/IFT du modèle. Alt-text v1 confondait l'objet IRT avec son évaluation ; corrigé pour décrire ce que la figure MONTRE.

## pymc11-sequences.png

- **Source** : notebook `PyMC-14-Sequences.ipynb` (cellule 14, output 0)
- **Alt-text (FR)** : Inférence sur séquences : comparatif HMM Forward-Backward vs classification indépendante, où les transitions lissent les états ambigus.
- **Poids** : 30.2 KB (PIL optimisé)
- **Contenu réel vérifié (2026-07-14, c.483)** : **2 panneaux empilés** : haut « Classification independante (sans transitions) » — barres verticales P(haut)/P(bas) avec labels rouges « ambigu » sur temps 2 et 5 ; bas « Forward-Backward (avec transitions) » — même structure mais labels verts « lisse » sur les mêmes temps (probabilités moins tranchées sur 2 et 5, transitions propageant l'incertitude). Axe x « Temps » 0-7.
- **Verdict** : VRAI — la figure illustre précisément le bénéfice du HMM (transitions → lissage) face à la classification i.i.d.

## pymc12-recommenders.png

- **Source** : notebook `PyMC-15-Recommenders.ipynb` (cellule 48, output 0)
- **Alt-text (FR)** : Système de recommandation bayésien : facteurs latents par document (estimations ponctuelles vs distributions postérieures d'incertitude).
- **Poids** : 58.4 KB (PIL optimisé, downscale manuel 1389→1200 px — voir note PR)
- **Contenu réel vérifié (2026-07-14, c.483)** : **2 panneaux côte à côte** : gauche « Sources vs Score latent » — barplot grouped par Document (0-5) avec 3 barres (Jugements bleu, Score latent orange, Clics rescaled vert), score 0-5 ; droite « Distributions posterieures des scores » — histogrammes ArviZ par Doc 0-5 (6 couleurs), axe x « Score latent » 1-6, axe y « Frequence » 0-500.
- **Verdict** : VRAI — la structure pédagogique est exactement « facteurs latents estimés » : le barplot de gauche compare trois sources observées au score latent inféré, les histogrammes de droite montrent l'incertitude postérieure sur ce score par document.

## pymc13-mcmc-diagnostics.png

- **Source** : notebook `PyMC-6-Debugging.ipynb` (cellule 21, output 6)
- **Alt-text (FR)** : Diagnostics MCMC : vérification visuelle du mélange des chaînes via KDE postérieure et trace plot pour les hyperparamètres.
- **Poids** : 142.1 KB (PIL optimisé)
- **Contenu réel vérifié (2026-07-14, c.483)** : **4 panneaux ArviZ en grille 2×2** : ligne 1 « hyper_mean » (densité KDE à gauche + trace plot 0-2000 samples à droite) ; ligne 2 « hyper_sigma » (densité KDE + trace). Title général « Trace plots : verifier le melange des chaines ».
- **Ce qui n'est PAS dans la figure** : aucun R-hat ni ESS n'est affiché directement (pas de panneau numérique) — le diagnostic est **purement visuel** (KDE + trace), conformément au title. Alt-text v1 mentionnait R-hat et ESS comme « vérifient la convergence » mais la figure montre seulement le mélange des chaînes via KDE et trace. Alt-text corrigé pour refléter ce qui est réellement visible.

## pymc15-sparse-gp.png

- **Source** : notebook `PyMC-16-Sparse-Gaussian-Process.ipynb` (cellule 14, output 2)
- **Alt-text (FR)** : Classification par Processus Gaussien sur un problème jouet en « donut » : probabilité prédite de la classe 1 et incertitude associée (écart-type de f*), sans inducer points (illustration dense classique).
- **Poids** : 60.1 KB (PIL optimisé)
- **Contenu réel vérifié (2026-07-14, c.483)** : **2 panneaux côte à côte** : gauche « Probabilite predite P(classe 1) » — contour plot x1∈[-2,2], x2∈[-2,2], colormap bleu→rouge (échelle 0-1), points bleus (classe 0) au centre + carrés rouges (classe 1) en couronne, frontière de décision en noir ; droite « Incertitude (ecart-type de f*) » — contour plot colormap jaune→orange (échelle 0.725-1.025), mêmes axes et points (carrés noirs cette fois). Title « Classification GP probit sur le donut ».
- **Ce qui n'est PAS dans la figure** : aucun **inducing point** (le « sparse » de l'alt-text v1) n'est visible — il s'agit d'un **GP classification 2D dense classique** sur un problème jouet en donut, PAS d'un sparse GP avec inducteurs. Le notebook `PyMC-16-Sparse-Gaussian-Process.ipynb` introduit probablement les inducteurs dans des cellules ultérieures ; la cellule 14 output 2 illustre le pré-requis (GP dense jouet). Alt-text v1 sur-vendeur corrigé pour refléter ce qui est réellement affiché.
