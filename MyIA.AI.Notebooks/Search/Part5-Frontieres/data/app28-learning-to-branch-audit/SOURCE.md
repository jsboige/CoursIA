# Provenance `app28-learning-to-branch-audit`

Ce répertoire accompagne App-28, distillation du geste du groupe G4 sur
l'apprentissage d'heuristiques de branchement pour CSP.

| Champ | Valeur |
|---|---|
| **Travail original** | *Apprentissage d'heuristiques pour solveurs CP* — groupe G4, Programmation par Contraintes, EPITA SCIA 2026 |
| **Auteurs** | **Simon Naulet** et **Matis Codjia** |
| **PR source** | [jsboigeEpita/2026-Epita-Programmation-par-Contraintes#46](https://github.com/jsboigeEpita/2026-Epita-Programmation-par-Contraintes/pull/46) |
| **Répertoire source** | [`matis.codjia_simon.naulet`](https://github.com/jsboigeEpita/2026-Epita-Programmation-par-Contraintes/tree/main/matis.codjia_simon.naulet) |
| **Commit d'intégration** | `9f91222f537a54147c9532f1c1cc5090fa58109b` |
| **Tip source audité** | `b5f3f0351dbd41f3a76f047cf02e9c93e81192f3` |
| **Licence du dépôt source** | MIT, voir [`LICENSE`](LICENSE) |

## Ce qui est attribué

Le geste intellectuel conservé est la chaîne : mini-solveur CSP avec AC-3,
features locales des variables, imitation de `dom/wdeg`, puis intégration d'une
politique apprise dans le choix de branchement. Le notebook étudiant emploie
XGBoost et trois familles synthétiques (N-reines, coloration, carrés latins).

Aucune cellule, fonction, donnée, figure ou prose étudiante n'est copiée dans
App-28. Les générateurs, le solveur, le validateur et l'expérience sont une
réécriture indépendante CoursIA.

## Maturation CoursIA

L'audit initial a montré qu'un split aléatoire par lignes mélangeait des
candidats issus des mêmes instances entre train et test. App-28 répare le
protocole :

1. 36 CSP déterministes et identifiés (12 par famille) ;
2. split groupé par instance, plus trois validations leave-one-family-out ;
3. baseline choisie sur le train uniquement ;
4. cinq graines de `HistGradientBoostingClassifier` ;
5. comparaison intégrée sur les mêmes CSP : top-1 par nœud, nœuds, temps mur,
   part d'inférence ;
6. validation indépendante de chaque affectation retournée.

Les fichiers générés par l'exécution du notebook sont :

- `baseline_runs.csv` — 36 instances × 4 heuristiques classiques ;
- `oracle_trace.csv` — candidats rencontrés par `dom/wdeg`, groupés par nœud et
  instance ;
- `evaluation_runs.csv` — politique apprise et baseline sélectionnée pour les
  quatre splits et cinq graines ;
- `maturation_report.json` — contrat expérimental et agrégats par split/graine.

## Limites

Le banc porte sur de petits CSP binaires synthétiques et la recherche d'une
première solution. Les variantes `dom/wdeg` et activity sont pédagogiques ; les
temps absolus dépendent de la machine. L'absence de gain observée ne démontre
pas que le learning-to-branch échoue en général : elle démontre seulement que
l'accuracy locale ne suffit pas à établir une réduction d'arbre, un gain de
temps ou un transfert entre ces familles.
