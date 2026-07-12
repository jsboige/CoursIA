# MANIFEST des figures README

Provenance des images de `assets/readme/` (EPIC #5654, source 1 = extraction d'outputs de notebooks).

**Audit visuel juillet 2026** : chaque PNG a été rouvert via l'outil Read et son **contenu réel** documenté ci-dessous. Les légendes dans `README.md` ont été ré-auditées pour refléter exactement ce qui est visible (et signaler honnêtement ce qui ne l'est pas).

**Audit juillet 2026 (PR #5780, doctrine corrigée)** : conformément à la doctrine « pas de Galerie, légende = ce que l'image MONTRE, choisir figure distinctive ou renoncer », trois figures ont été retirées du README :

- `sl6-modernilp.png` (cellule 18 de SL-6) ne montrait qu'une seule courbe dILP alors que le contexte du README parle de quatre moteurs ILP comparés. Légende factuellement fausse → figure retirée (doctrine « renoncer »).
- `sl10-angluin-lstar.png` (cellule 39 de SL-10) montrait l'agrégation bayésienne de preuves, pas l'automate minimal de Myhill-Nerode. Légende misleading → figure remplacée par le rendu mermaid de l'automate cible à 4 états (voir ci-dessous).
- `sl12-difflogic.png` (cellule 11 de SL-12) montrait des courbes d'entraînement MNIST génériques, pas le circuit booléen discrétisé. Légende misleading → figure retirée (doctrine « renoncer », le circuit exact nécessite la ré-exécution de l'environnement difflogic).

## sl10-dfa-target.png

- **Source** : notebook `SL-10-ActiveAutomataLearning.ipynb` (cellule 4, bloc `mermaid stateDiagram-v2`), rendu manuel via mermaid.ink en juillet 2026.
- **Contenu réel vérifié** : diagramme d'automate fini déterministe à 4 états étiquetés par la parité du nombre de `a` et du nombre de `b` lus — `ee` (état initial + acceptant, en vert), `oe`, `oo`, `eo`. Transitions étiquetées `a` ou `b` flipant la parité correspondante. C'est l'automate cible de la tâche `parity2(a,b)` que L* d'Angluin reconstruit par requêtes d'appartenance et d'équivalence.
- **Alt-text (FR)** : Automate fini déterministe à 4 états (ee/oe/oo/eo) cible de l'algorithme L* d'Angluin : chaque état code une classe de parité (mod 2 × mod 2) sur la suite de symboles `a`/`b` lue.
- **Poids** : 60.1 KB (PNG optimisé via PIL depuis JPEG mermaid.ink)
- **Justification du choix** : c'est l'objet conceptuel central du notebook — la minimalité de l'automate (Myhill-Nerode) est la garantie théorique de L*. La cellule 4 contient le bloc mermaid source ; le rendu PNG est conservé comme livrable durable pour le README.