# ICT-12 — Valence Fields & Animats (champs de valence et animats)

Sous-série **strate 3** de la série ICT : les **trajectoires intégrées** régime-dépendantes vues du côté de l'animat. La scène actantielle de Thom cesse d'être une correspondance nommée : les rôles (capture, évasion, prégnance, inhibition) deviennent des **grandeurs mesurées**, puis **apprises**, puis **incarnées**, puis **valorisées par l'information**.

> [↑ Index ICT-Series](../README.md) · [Cadrage ICT-0](../ICT-0-Framing.md) · [Matrice des dissociations](../../../../docs/ict/dissociations-matrix.md) · Epic [#4588](https://github.com/jsboige/CoursIA/issues/4588) · File d'origine : #7740

## Ce que chaque carnet démontre

| Carnet | Ce qu'il démontre |
|---|---|
| [ICT-12 — Champs de valence et animats](ICT-12-ValenceFieldsAndAnimats-Python.ipynb) | Premier toy model **actantiel spatial** : des animats évoluent dans un champ de valence (source attractive + obstacles répulsifs). Le **réactif** suit le gradient instantané ; l'**anticipateur `p̂`** extrapole le point d'interception. Verdict *sans complaisance* : le modèle interne est **régime-dépendant** — capture ×4 en balistique rapide, défaite en erratique. Ni universellement avantageux, ni ruineux. |
| [ICT-12b — Valence apprise, transférable, réversible](ICT-12b-LearnedValence-Python.ipynb) | L'envers exact d'ICT-12 : la valence n'est plus programmée dans le champ, elle est **acquise** par conditionnement Pavlovien (Rescorla-Wagner) sur banc désincarné. Trois verdicts falsifiables : **transfert** (un neutre co-occurrent devient attractif par lui-même), **distinction de la prédiction `p̂`**, **réversibilité** (acquisition et extinction partagent la même règle). |
| [ICT-12c — Animat prégnance/valence incarné](ICT-12c-PregnanceAnimat-Python.ipynb) | La jambe **C1** de la tresse transverse : ICT-12b quitte son banc désincarné pour un animat qui se déplace, a faim et choisit. La porte scientifique est une **matrice de dissociation** — le régime erratique détruit `p̂` mais laisse intact le conditionnement : prégnance et représentation sont **deux grandeurs dissociables**, même incarnées. |
| [ICT-12d — Animat inhibé (Laborit)](ICT-12d-InhibitedActionAnimat-Python.ipynb) | La jambe **C2** : l'inhibition porte sur l'**action** d'un animat individuel (à distinguer d'ICT-30, inhibition de l'innovation, strate collective). L'animat inhibé **rigidifie** son action sous perte de contrôle, et la **dette d'irréversibilité `I(R)`** échappe à l'action — consomme le module [`ict.inhibited_action`](../ict/inhibited_action.py). |
| [ICT-12e — Valeur de l'information : EVPI / EVSI](ICT-12e-Value-of-Information-Animat-Python.ipynb) | La greffe décisionnelle : ICT *pose* un problème de décision, la théorie de la valeur de l'information le résout — observer avant d'agir, et le **coût** de cette observation (EVPI/EVSI) pour l'animat incarné. |

## Place dans l'escalier

La strate 3 (ICT-11 → ICT-13) mesure des trajectoires intégrées **régime-dépendantes** : profils d'agence (ICT-11), champs de valence (cette sous-série), morphodynamique stratégique (ICT-13, racine). Elle prépare la **strate 4** (ICT-14 → ICT-20), qui ajoute la jambe **représentationnelle** — énergie libre, surprise, inférence active — dont ICT-12c pose déjà les trois lecteurs orthogonaux de l'état interne (`p̂`, `π`, `q̂`).

## Instruments

Organes : `valence`, `learned_valence`, `pregnance_animat`, `inhibited_action`, `voi` — voir la table des organes de l'[index de série](../README.md) et le paquet [`ict/`](../ict/). L'état scientifique de chaque claim se lit dans la [matrice des dissociations](../../../../docs/ict/dissociations-matrix.md).
