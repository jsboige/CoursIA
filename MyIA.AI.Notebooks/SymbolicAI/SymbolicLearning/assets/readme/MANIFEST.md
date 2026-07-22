# MANIFEST des figures README

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).

**Audit visuel juillet 2026** : chaque PNG a été rouvert via l'outil Read et son **contenu réel** documenté ci-dessous. Les légendes dans `README.md` ont été ré-auditées pour refléter exactement ce qui est visible (et signaler honnêtement ce qui ne l'est pas).

**Audit juillet 2026 (PR #5780, doctrine corrigée)** : conformément à la doctrine « pas de Galerie, légende = ce que l'image MONTRE, choisir figure distinctive ou renoncer », trois figures ont été retirées du README :

- `sl6-modernilp.png` (cellule 18 de SL-6) ne montrait qu'une seule courbe dILP alors que le contexte du README parle de quatre moteurs ILP comparés. Légende factuellement fausse → figure retirée (doctrine « renoncer »).
- `sl10-angluin-lstar.png` (cellule 39 de SL-10) montrait l'agrégation bayésienne de preuves, pas l'automate minimal de Myhill-Nerode. Légende misleading → figure remplacée par le rendu mermaid de l'automate cible à 4 états (voir ci-dessous).
- `sl12-difflogic.png` (cellule 11 de SL-12) montrait des courbes d'entraînement MNIST génériques, pas le circuit booléen discrétisé. Légende misleading → figure retirée (doctrine « renoncer », le circuit exact nécessite la ré-exécution de l'environnement difflogic).

## sl10-dfa-target.png

- **Source** : notebook `SL-10-ActiveAutomataLearning.ipynb` (cellule 4, bloc `mermaid stateDiagram-v2`), rendu manuel via mermaid.ink en juillet 2026.
- **Description visuelle** : Diagramme d'automate fini déterministe à 4 états disposés horizontalement de gauche à droite. L'état `ee` est mis en évidence par un fond vert clair et une bordure vert foncé épaisse (état acceptant, code couleur `classDef accept fill:#d1e7dd,stroke:#0f5132`). Les 3 états `oe`, `oo`, `eo` ont un fond violet/lavande clair avec bordure violette (non acceptants). Une petite flèche noire (point d'entrée `[*]`) à gauche pointe vers l'état initial `ee`. Chaque état porte son label textuel sur deux lignes (sigle `ee`/`oe`/`oo`/`eo` puis description entre parenthèses `(pair a, pair b)` / `(impair a, pair b)` / etc., police monospace). Les transitions sont des flèches noires courbes portant des étiquettes `a` ou `b` en minuscules au-dessus — 8 transitions au total, deux paires symétriques `ee↔oe` (label `a`) et `oo↔eo` (label `a`) plus deux paires symétriques `ee↔oo` (label `b`) et `oe↔eo` (label `b`) qui s'enroulent au-dessus et en-dessous de la chaîne linéaire. Aucun axe, aucune légende textuelle secondaire, aucune graduation.
- **Alt-text (FR)** : Automate fini déterministe à 4 états (ee/oe/oo/eo) cible de l'algorithme L* d'Angluin : chaque état code une classe de parité (mod 2 × mod 2) sur la suite de symboles `a`/`b` lue.
- **Contenu réel vérifié** : diagramme d'automate fini déterministe à 4 états étiquetés par la parité du nombre de `a` et du nombre de `b` lus — `ee` (état initial + acceptant, en vert), `oe`, `oo`, `eo`. Transitions étiquetées `a` ou `b` flipant la parité correspondante. C'est l'automate cible de la tâche `parity2(a,b)` que L* d'Angluin reconstruit par requêtes d'appartenance et d'équivalence.
- **Poids** : 60.1 KB (PNG optimisé via PIL depuis JPEG mermaid.ink)
- **Justification du choix** : c'est l'objet conceptuel central du notebook — la minimalité de l'automate (Myhill-Nerode) est la garantie théorique de L*. La cellule 4 contient le bloc mermaid source ; le rendu PNG est conservé comme livrable durable pour le README.