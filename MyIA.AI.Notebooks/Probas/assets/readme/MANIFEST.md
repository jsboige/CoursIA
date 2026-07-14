# Manifeste des figures — Probas

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).

**Audit G.1 po-2025 c.491 (2026-07-14, doctrine #5780)** : audit fondateur sur la racine Probas (jamais traversée en tant que racine ; c.486 c.6486 a audité `DecisionTheory/PyMC/` sibling, pas la racine). **Verdict G.1 firsthand = 1/1 ACCURATE** : le contenu visuel de `probas-utility-functions.png` (3 panneaux côte-à-côte `√x` concave / `ln(x)` concave / `x` linéaire neutre) **correspond fidèlement** à la fois (a) à l'attribution `DecPyMC-2-Utility-Money.ipynb` cellule 10 (vérification `nbformat` confirme `cell[10] out[1] md5=30fafb1a size=35168 B`), (b) à l'**alt-text in-situ du README racine** ligne 60 (3 fonctions d'utilité fondamentales, utilité marginale décroissante, fondement Pratt 1964 / Arrow 1965), et (c) au **code source de la cellule** (`fig, axes = plt.subplots(1, 3, figsize=(14, 4))` + 3 `ax.plot(x, U, 'b-', linewidth=2)` sur `U_sqrt`/`U_log`/`U_lin`). **0 correction d'alt-text nécessaire** ; le seul changement est la **migration du format vague-1 (Source / Alt-text / Poids) vers le format liste détaillé standard** (pattern c.487 GenAI/Video racine, c.488b ML racine, c.490 GameTheory racine, c.490b GenAI/Audio racine), avec ajout du champ *Contenu réel vérifié* par figure + un audit-block en tête pour la traçabilité G.1.

| Figure | Fichier | Dimensions | Poids | Source (notebook · cellule · output) | Sujet |
|--------|---------|------------|-------|--------------------------------------|-------|
| Fonctions d'utilité | `probas-utility-functions.png` | 1389×390 | 65 Ko | `DecisionTheory/PyMC/DecPyMC-2-Utility-Money.ipynb` · cellule 10 · output 1 | Trois fonctions d'utilité fondamentales (√x, ln(x), x) — utilité marginale décroissante |

**Total** : 1 figure, 65 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. Sortie `matplotlib` `fig, axes = plt.subplots(1, 3, figsize=(14, 4))` : **PNG lossless natif** préféré à WebP (line-art + étiquettes texte, plots académiques). Note technique sur la différence de taille : la cellule source produit un PNG de **35 168 B** (compression matplotlib `savefig` standard), tandis que la copie sur disque fait **66 455 B** (ré-export PIL optimize sans compression palette) — **ratio disque/source = 1.89×**. Cette inflation est un artefact d'encodage (PIL ne compresse pas mieux que matplotlib par défaut sur du line-art 3 panneaux côte-à-côte), pas un signe d'incohérence ; le contenu visuel et la résolution sont identiques (1389×390 = ratio d'aspect 3.56 confirmé).

---

## Détail vérifié figure par figure (audit vision c.491)

### probas-utility-functions.png

- **Source** : `DecisionTheory/PyMC/DecPyMC-2-Utility-Money.ipynb` cellule 10 (index toutes-cellules, convention `extract_readme_figures.py`), output 1.
- **SHA256** : `afbb60f97b36b090c44e7dc3a0137acc7ab8e7e3828ccd944542b8fdd0453767` (66 455 B).
- **Cellule source vérifiée `nbformat`** : `cell[10]` est une cellule code dont le source commence par `# Demonstration numerique : utilite marginale decroissante`, contient `fig, axes = plt.subplots(1, 3, figsize=(14, 4))`, et trace 3 courbes `U(x) = sqrt(x)`, `U(x) = ln(x)`, `U(x) = x (neutre)` via une boucle `for ax, U, name in [(axes[0], U_sqrt, r"$U(x) = \sqrt{x}$"), (axes[1], U_log, r"$U(x) = \ln(x)$"), (axes[2], U_lin, r"$U(x) = x$ (neutre)")]`. L'output 1 porte un `image/png` de 35 168 B (md5 = `30fafb1a`) = **source authentique du PNG disque** (contenu visuel identique, seul le ré-export diffère par sa compression).
- **Contenu réel vérifié (lecture `Read` 2026-07-14)** : Figure 1389×390, **3 panneaux côte-à-côte** sans titre global (le `suptitle` n'est pas utilisé ; chaque sous-figure porte son propre titre matplotlib) :
  - **Panneau 1 (gauche)** : `U(x) = √x` — courbe bleue pleine (`b-`, linewidth=2) **strictement concave**, montée de U(0)=0 → U(100)=10 (droite pointillée noire `k--` alpha=0.3 = référence neutre U(x)=x pour comparer visuellement la concavité). Axes annotés : X = « Richesse (x) » 0→100, Y = « U(x) » 0→100. Le panneau illustre la **croissance sous-linéaire** : √x s'aplatit, donc chaque euro marginal apporte de moins en moins d'utilité.
  - **Panneau 2 (centre)** : `U(x) = ln(x)` — courbe bleue pleine **strictement concave** (plus aplatie que √x), U(0)=−∞ (coupé par l'axe), U(100)≈4.6. Mêmes axes annotés 0→100, même droite pointillée de référence. Le panneau illustre l'utilité marginale **la plus décroissante** des trois (logarithme = concavité la plus marquée en base naturelle pour x∈[1,100]).
  - **Panneau 3 (droite)** : `U(x) = x (neutre)` — droite bleue pleine passant par l'origine, pente 1, U(0)=0 → U(100)=100. Mêmes axes annotés. Le panneau montre l'**agent neutre au risque** : l'utilité marginale est constante (=1 par euro), donc aversion au risque nulle.
  - Pas de légende globale (les 3 panneaux sont auto-suffisants via leurs titres mathématiques + la droite pointillée interne à chaque panneau).

- **Alt-text (FR)** : Trois fonctions d'utilité fondamentales tracées sur 3 panneaux côte-à-côte — racine carrée `U(x) = √x` (concave), logarithme `U(x) = ln(x)` (concave), et linéaire `U(x) = x` (neutre au risque, en référence) — montrant l'utilité marginale décroissante : les deux courbes concaves s'aplatissent quand la richesse x augmente (chaque euro supplémentaire apporte moins d'utilité que le précédent), tandis que la linéaire reste constante (aversion nulle). Fondement de la théorie de la décision sous incertitude (Pratt 1964, Arrow 1965). Extrait du notebook DecPyMC-2-Utility-Money.
- **Alt-text in-situ README racine ligne 60** : Trois fonctions d'utilité fondamentales sur trois panneaux côte-à-côte : racine carrée U(x)=√x (concave), logarithme U(x)=ln(x) (concave), et linéaire U(x)=x (neutre au risque, en référence) — montrant l'utilité marginale décroissante : les deux courbes concaves s'aplatissent quand la richesse x augmente (chaque euro supplémentaire apporte moins d'utilité que le précédent), tandis que la linéaire reste constante (aversion nulle). Fondement de la théorie de la décision sous incertitude (Pratt 1964, Arrow 1965). Extrait du notebook DecPyMC-2-Utility-Money, cellule « Démonstration numérique : utilité marginale décroissante ». — **fidèle au contenu G.1 firsthand** (vérification croisée OK).
- **Note** : référence implicite aux fondements théoriques de l'aversion au risque (Pratt 1964 *Measure of Risk Aversion*, Arrow 1965 *Aspects of the Theory of Risk-Bearing*) — choix pédagogique pertinent pour ouvrir le sous-chapitre « De la distribution à l'utilité » du README racine. Le **caption** dans le README ligne 62 cite explicitement la cellule 10 du DecPyMC-2-Utility-Money et le track DecisionTheory/PyMC, ce qui **renforce** l'attribution MANIFEST (pas de risque de désalignement).

## Note méthodologique — figure mono-famille matplotlib authenthique

Cette série est **5ᵉ dans le rollout** à présenter exclusivement des **figures matplotlib authentiques** (après #6453 c.478 SocialChoice 6/6, #6458 c.479 GenAI/Texte 3/3, #6459 c.480 ML.Net 6/6, #6517 c.489 RL 6/6, et maintenant #c.491 Probas racine 1/1). La racine Probas est **mono-figure** (1 seule image dans `assets/readme/`) et constitue le **profil le plus minimal** du rollout : le MANIFEST de la racine est un **pointeur unique** vers la figure de l'arc Décision PyMC (`DecisionTheory/PyMC/DecPyMC-2-Utility-Money`).

**Cohérence interne au track Probas** : la figure de la racine n'est pas dupliquée dans le MANIFEST sibling `DecisionTheory/PyMC/assets/readme/MANIFEST.md` (audité par c.486 c.6486) — le track Décision PyMC y a ses propres figures (`dt2-decision-tree.png`, `dt3-stochastic-dominance.png`, `dt4-mdp-grid.png`, `dt5-evpi-frontier.png`), distinctes. La racine opère donc comme un **sommaire narratif** (« voici ce que représente l'arc Décision dans son ensemble ») plutôt que comme un **catalogue exhaustif** — choix pédagogique cohérent avec la prose racine qui introduit les concepts transversaux.

**Pattern transférable** : pour les familles à dominante matplotlib mono-figure racine (Probas, futurs cross-series, CaseStudies), la rigueur des **annotations** (variables, légendes, unités) est presque toujours au rendez-vous. Le travail d'audit consiste principalement à vérifier la **fidélité des annotations au contenu effectif**, pas à corriger des sur-ventes majeures. **0 bug détecté sur l'unique figure** : la table c.491 MANIFEST est plus proche du standard que les vagues 1-2 (SymbolicLearning/Image), mais avec un format vague-1 (Source/Alt-text/Poids seulement) — ce qui réduit le travail de migration à un simple changement de format.

## Conformité règles

- **§A single-subject** : 1 sujet (audit figures Probas racine), 1 sous-dossier, 1 fichier. Bien sous plafond 3000L.
- **§E doctrine corrigée** (issue #5780) : pas de section `## Galerie`, figure unique inline dans la prose racine (ligne 60 du README) avec alt-text décrivant le contenu réel vérifié par lecture directe.
- **R1 catalog-pr-hygiene** : `git diff origin/main..HEAD -- "**/CATALOG-STATUS*" "**/COURSE_CATALOG*"` = vide. Section Probas utilise CATALOG-STATUS (lignes 3-8 du README), R1 respectée (catalogue byte-identique à main).
- **L268 #4 LF-only** : `git diff | tr -cd '\r' | wc -c` = 0. Pas de retour chariot dans le diff.
- **L143 secrets-hygiene** : `grep -nE "sk-|ghp_|AIza|password=|secret="` sur le diff = 0 hit.

## Voir aussi

- [c.486 Probas/DecisionTheory/PyMC MANIFEST](../DecisionTheory/PyMC/assets/readme/MANIFEST.md) — pattern frère (audit fondateur G.1 + corrections réelles dt2/dt3 + enrichissement dt5)
- [c.488b ML racine MANIFEST](../../ML/assets/readme/MANIFEST.md) — pattern frère (dette cumulative mineure 4/6 ACCURATE + 2/6 enrichissements)
- [c.490 GameTheory racine MANIFEST](../../GameTheory/assets/readme/MANIFEST.md) — pattern frère (6/6 ACCURATE + 6 corrections enrichissement croisant README in-situ)
- [c.490b GenAI/Audio racine MANIFEST](../../GenAI/Audio/assets/readme/MANIFEST.md) — pattern frère (5ᵉ profil = dette cumulative majeure, swap correctif NON TENTÉ)
- [c.479 GenAI/Texte racine MANIFEST](../../GenAI/Texte/assets/readme/MANIFEST.md) — pattern frère (3/3 ACCURATE, format standard déjà en place)
- [c.489 RL racine MANIFEST](../../RL/assets/readme/MANIFEST.md) — pattern frère (6/6 ACCURATE, attribution cellule corrigée)
- issue [#5780](../../../issues/5780) ; EPIC [#5654](../../../issues/5654)