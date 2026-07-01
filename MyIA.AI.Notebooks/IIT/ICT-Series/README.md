# ICT — Integrated Causal Trajectories

<!-- CATALOG-STATUS
series: ICT
pedagogical_count: 0
breakdown: 
maturity: 
-->

[← IIT](../README.md) | [↑ Notebooks](../../README.md) | [→ Probas](../../Probas/README.md)

La série [IIT](../README.md) étudie des structures causales **à un instant donné** : on photographie un système et on calcule combien d'information il intègre ($\Phi$). **ICT** (Integrated Causal Trajectories, Epic #4588) prolonge ce regard vers les **trajectoires** de structures causales : comment une organisation se maintient, se transforme, se répare, change d'échelle et traverse un espace de possibles ($C_0 \rightarrow C_1 \rightarrow \dots \rightarrow C_n$). C'est la photographie IIT mise en mouvement.

ICT s'appuie sur un package léger `ict/` posé à côté de PyPhi (autonome pour les simulations et mesures, PyPhi pour les calculs IIT stricts), et s'ouvre sur deux articles fondateurs : le tri vu comme morphogenèse minimale (Zhang, Goldstein & Levin, 2025) et l'ingénierie de l'émergence multi-échelle (Jansma & Hoel, 2025).

La série progresse en **deux strates**. La **strate 1** (ICT-0 à ICT-7) prend le **tri auto-organisé** comme banc d'essai entièrement transparent : trajectoires enregistrables, compétences inattendues réelles, pont vers la causal emergence. Elle bute toutefois sur trois limites — un **attracteur global unique**, un **but imposé de l'extérieur**, une **hiérarchie non générative**. La **strate 2** (ICT-8+) ouvre la *morphogenèse dynamique* sur des systèmes dont le paysage d'attracteurs est **engendré par la dynamique** (bifurcation, réaction-diffusion), levant ces limites une à une.

> **Caractère expérimental.** ICT est une série de recherche en construction (statut ALPHA). Elle pose des mesures *sans complaisance* : chaque notebook confronte une intuition séduisante (émergence, agence, criticalité) à une mesure qui peut la **réfuter**, et signale explicitement les fantômes statistiques (signal apparent issu de degrés de liberté cachés).

## Prérequis & environnement

ICT partage l'environnement Python de la série IIT (PyPhi 1.2.0, Python 3.9). Le setup et les dépendances sont mutualisés au niveau du répertoire parent :

```bash
# Depuis MyIA.AI.Notebooks/IIT/
powershell -File scripts/setup_pyphi_env.ps1     # conda env pyphi + kernel
pip install -r requirements.txt                  # dépendances ICT additionnelles (numpy, scipy, networkx…)
```

Le package `ict/` est importé en relatif depuis le répertoire `ICT-Series/` : chaque notebook insère le dossier courant dans `sys.path` puis `from ict import …`. Lancer les notebooks **depuis `ICT-Series/`** (cwd) pour que les imports résolvent.

| Élément | Emplacement | Rôle |
|---------|-------------|------|
| Package `ict/` | `ICT-Series/ict/` | Simulations (tri, bistable, réaction-diffusion), mesures (Φ-trajectoires, EWS, émergence causale, scale-free) |
| Tests | `ICT-Series/tests/` | Suite pytest de validation des modules `ict/` (`python -m pytest tests/`) |
| Setup PyPhi | `../scripts/setup_pyphi_env.ps1` | Mutualisé avec IIT |
| Dépendances | `../requirements.txt` | Mutualisé avec IIT |

## Notebooks

### Strate 1 — le tri auto-organisé (transparent et calculable)

| Document | Contenu |
|----------|---------|
| [ICT-0-Framing](ICT-0-Framing.md) | Cadrage de la série : de l'état à la trajectoire, articles fondateurs, feuille de route |
| [ICT-1-PhiTrajectories](ICT-1-PhiTrajectories.ipynb) | Trajectoires de $\Phi$ : paysage de $\Phi$, suivi de $\Phi$ le long d'un attracteur (pulsations) et robustesse aux perturbations — la photographie IIT mise en mouvement, avec le vrai PyPhi |
| [ICT-2-SelfSortingMorphogenesis](ICT-2-SelfSortingMorphogenesis.ipynb) | Le tri auto-organisé comme morphogenèse : trajectoire dans le morphospace, robustesse aux cellules défectueuses, délai de gratification, auto-réparation, impasses chimériques |
| [ICT-3-RobustnessDelayedGratification](ICT-3-RobustnessDelayedGratification.ipynb) | Robustesse & délai de gratification, étude quantitative : dégradation gracieuse face aux cellules défectueuses, distributions de récupération, comptage du délai de gratification |
| [ICT-4-ChimericArraysKinAggregation](ICT-4-ChimericArraysKinAggregation.ipynb) | Tableaux chimériques & agrégation émergente : réparation bidirectionnelle (guérit l'impasse d'ICT-2) puis affinité « kin », mesurée honnêtement (sans degrés de liberté, pas d'agrégation) |
| [ICT-5-CausalEmergence](ICT-5-CausalEmergence.ipynb) | Émergence causale : $\Phi$ et information effective aux échelles micro/macro, recherche systématique du coarse-graining (vrai `pyphi.macro`), émergence discriminante (Jansma & Hoel, 2025) |
| [ICT-6-SortingToTPM-CausalEmergence](ICT-6-SortingToTPM-CausalEmergence.ipynb) | Pont tri → TPM : chaîne de Markov estimée depuis les trajectoires de tri d'ICT-2, puis émergence causale multi-échelles avec l'outillage *Causal Emergence 2.0* (Hoel, 2025) au-delà de la borne de taille de PyPhi |
| [ICT-7-ScaleFreeSignatures](ICT-7-ScaleFreeSignatures.ipynb) | Signatures scale-free & criticalité : détecter une loi de puissance *sans se faire avoir* (MLE de Hill, choix de $x_{\min}$, KS, à la Clauset et al.) ; étalon critique (branchement, exposant $3/2$) vs tri qui *paraît* sans échelle mais possède une taille caractéristique |

### Strate 2 — morphogenèse dynamique (paysages d'attracteurs)

| Document | Contenu |
|----------|---------|
| [ICT-8-AttractorLandscapesEWS](ICT-8-AttractorLandscapesEWS.ipynb) | Paysages d'attracteurs & signaux précurseurs — *les deux tressées*. Modèle de pâturage de May (1977), système canonique des *early-warning signals* (Scheffer 2009). Bistabilité entre deux états positifs alternatifs, bifurcation pli, catastrophe = changement de régime. Chaque image (vallée qui s'aplatit, mémoire du danger, alerte) adossée à une mesure réelle (potentiel effectif, valeur propre → 0, variance ↑, autocorrélation ↑, τ de Kendall). Lève l'attracteur unique + ouvre une hiérarchie générative |
| [ICT-9-AgencyRegeneration](ICT-9-AgencyRegeneration.ipynb) | Agence & régénération — *réparer sa forme, ou seulement dériver ?* Morphogenèse réaction-diffusion de Gray-Scott (Pearson 1993) : le système engendre un motif auto-entretenu (point de consigne **intrinsèque**), on l'ablate via une intervention `do(·)`, puis on contraste **deux mondes contrefactuels** (Pearl) — réaction-diffusion qui régénère vs diffusion pure qui dissout. L'agence n'est jamais déclarée, elle est **mesurée** comme *gain de réparation* (recouvrement RD − recouvrement diffusion). *Sans complaisance* : les mesures naïves de ressemblance (pixel-à-pixel, cosinus spectral) fabriquent un signal fantôme ; seule la structure restaurée contrastée au contrôle passif tient. Lève le **but extrinsèque** : un point de consigne que le système maintient de lui-même |
| [ICT-10-CatastropheGrammar](ICT-10-CatastropheGrammar.ipynb) | Grammaire des catastrophes — *l'obstacle qui engendre les formes, le verbe qui les fait basculer*. **Charnière strate 2→3**, prélude sémiophysique de R. Thom (*Esquisse d'une sémiophysique*, 1991). Sur la catastrophe canonique (la **fronce**), deux fils tressés et **mesurés** : le **métathéorème** (le comptage d'équilibres ne change qu'aux **plis** — exactement 2 transitions le long d'un chemin générique ; *l'obstacle comme source de l'ontologie*, clôt la strate 2) et le **lacet de prédation** (cycle d'hystérésis à 2 catastrophes — perception J, capture K — d'aire signée non nulle = irréversibilité ; un **représentant interne** `p̂` dont le contenu anticipateur est *mesuré* : pic de corrélation au futur, battant la persistance ; ouvre la strate 3). La correspondance linguistique du **Ch.2 « Le Langage »** de Thom est *nommée* (pivots ↔ transitions de comptage ; verbe transitif SVO ↔ lacet ; anticipation ↔ `p̂`), avec son caveat explicite de **non-prédictivité** et les barreaux du pont basse-dim → haute-dim (séries neurosymbolique, Lean ; veille EML #4653). *Sans complaisance* : hors régime non dégénéré ($a<0$), zéro saut, aire nulle — un *fantôme* |

Reste sur la feuille de route de [ICT-0-Framing](ICT-0-Framing.md) : **ICT-11/12** (profils d'agence causale micro/méso/macro ; renormalisation causale & invariance multi-échelle) et **ICT-Synthèse**.

## Lien avec la causalité du dépôt

ICT-5 est l'un des quatre points d'ancrage du **fil rouge causalité** du dépôt (do-calculus de Pearl à travers les paradigmes : symbolique Tweety, bayésien Infer.NET / PyMC, information-théorique ICT). L'essai complet — l'échelle de la causalité L1/L2/L3 et les quatre instanciations de l'opérateur `do(·)` — vit dans le README parent : voir [Ponts causaux : le do-calculus de Pearl](../README.md#ponts-causaux--le-do-calculus-de-pearl-à-travers-les-paradigmes).

## Validation

```bash
# Depuis MyIA.AI.Notebooks/IIT/ICT-Series/
python -m pytest tests/        # suite de validation des modules ict/
```

## Licence

Voir la licence du repository principal.

---

*Série expérimentale — Epic #4588. Voir aussi #4208 (surfaçage des différenciants du dépôt).*
