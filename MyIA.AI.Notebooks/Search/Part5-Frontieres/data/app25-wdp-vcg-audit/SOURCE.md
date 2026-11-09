# Source des données `app25-wdp-vcg-audit`

Ce répertoire porte la distillation App-25 du projet de groupe J2 (enchères
combinatoires et Winner Determination). Il contient :

- `cats_snapshot.json` — snapshot **compact** produit par CoursIA (28 août 2026) :
  pour chacune des 18 instances CATS, les valeurs **committées par les étudiants**
  (outputs du notebook source) et la **re-résolution indépendante CoursIA**
  (CP-SAT, prix entiers milli-unités bout-en-bout), plus l'audit VCG, le
  contre-exemple de manipulation matérialisé et les mesures du mur de la force
  brute ;
- `cats/{regions,paths,matching}_g*_b*_s10000.txt` — 3 instances CATS copiées
  **sans modification** depuis le dépôt source, pour l'exercice live de parsing
  dans le notebook ;
- `LICENSE` — licence MIT du dépôt source, copiée à l'identique.

| Champ | Valeur |
|---|---|
| **Travail original** | *« Enchères combinatoires et Winner Determination »* — sujet **J2**, cours *Programmation par Contraintes*, EPITA SCIA 2026 |
| **Auteurs** | **Lucas Majerczyk** ([Sosolalt](https://github.com/Sosolalt)), **Nabil Chartouni** ([NCH04](https://github.com/NCH04)), **Wilfrid Wangon-Zekou** ([56Nights](https://github.com/56Nights)) |
| **Dépôt source** | [jsboigeEpita/2026-Epita-Programmation-par-Contraintes](https://github.com/jsboigeEpita/2026-Epita-Programmation-par-Contraintes) |
| **Répertoire source** | [`Groupe-J2-Enchere_combinatoire_et_Winner_Determination`](https://github.com/jsboigeEpita/2026-Epita-Programmation-par-Contraintes/tree/main/Groupe-J2-Enchere_combinatoire_et_Winner_Determination) |
| **Commit source** | `b5f3f0351dbd41f3a76f047cf02e9c93e81192f3` (tip de `main` à la distillation) |
| **Chemins d'origine** | `data/cats/*.txt` (18 fichiers, générateur CATS v2.1, Leyton-Brown 2000) ; outputs étudiants = cellules exécutées de `J2-CombinatorialAuctions.ipynb` |
| **Licence** | MIT — copyright 2026 « EPITA SCIA - Programmation par Contraintes (students and teaching staff) » (voir [`LICENSE`](LICENSE)) |

## Provenance et bon usage

- Les instances CATS sont la **propriété intellectuelle des auteurs** (MIT),
  redistribuées ici avec copyright et mention de licence conservés.
- **Aucun code de solveur étudiant n'est recopié** dans le notebook App-25 :
  le package `wdp/` (CP-SAT, PLNE, greedy, VCG, parser CATS) reste dans le
  dépôt source, référencé et testé (44/44 tests pytest passants au commit
  source, re-vérifiés à la distillation).
- Le notebook App-25 **ré-écrit** l'expérience de façon autonome (modèle
  CP-SAT indépendant, prix entiers milli-unités) et **sépare** explicitement
  les valeurs étudiants (`student_reported`) des vérifications CoursIA
  (`revenue_int`, deltas en milli-unités).

## Expérience dérivée CoursIA (28 août 2026)

`cats_snapshot.json` a été produit depuis le dépôt source au commit
`b5f3f035`, en trois volets :

1. **Tests source** — `python -m pytest tests/` au commit source :
   44/44 passants (~3,4 s), Windows/Python 3.13/ortools 9.15.
2. **Re-résolution indépendante** — les 18 instances CATS re-résolues par
   l'implémentation CoursIA du notebook (CP-SAT, milli-entiers, sans import
   de `wdp/`). Accord exact avec les outputs PLNE committés (18/18 modulo
   l'affichage à 2 décimales) ; écart de 10 instances avec les outputs
   CP-SAT committés (voir volet 3).
3. **Forensics `PRICE_SCALE`** — les outputs CP-SAT committés du notebook
   source sont reproduits à 18/18 en re-exécutant le solveur étudiant avec
   `PRICE_SCALE = 100` (valeur héritée, docstring « centimes ») ; la valeur
   du code au commit (`1000`) ne les reproduit qu'à 8/18. Conclusion :
   le notebook committé a été exécuté **avant** l'alignement
   `PRICE_SCALE = bid_alpha = 1000` (corroboré par la prose du notebook qui
   annonce « 39 tests » alors que la suite au même commit en compte 44).
   Reproduction : `import wdp.solver_cpsat as sc; sc.PRICE_SCALE = 100` puis
   `sc.solve_wdp_cpsat(parse_cats_file(path))` sur les fichiers du dépôt source.

Le contre-exemple de manipulation sous budget (surplus 7 contre 0) est
**documenté** dans `research/04_vcg_budget_non_truthful.md` du dépôt source —
qui annonce aussi un test `test_vcg_budget_admits_strict_manipulation`
**absent** de `tests/` au commit source. Le snapshot en porte l'exécution
matérialisée (régime budgété, `strict_manipulation: true`).

## Contenu du snapshot

- `meta` — provenance, unités (CATS : entiers bruts du flag `-int_prices` ;
  unités de valeur = brut / `bid_alpha`, défaut CATS 1000, **non consigné
  dans les fichiers**), environnement ;
- `source_tests` — 44/44 ;
- `cats[18]` — par instance : goods/dummy/bids/xor, statut, optimum exact,
  valeurs étudiants, deltas `student_cp`/`student_milp` en milli-unités ;
- `price_scale_forensics` — observation, test d'hypothèse, reproduction ;
- `pedagogical` — toy 40, with_budget 80→50, with_xor 57 ;
- `vcg` — paiements toy (David 37), with_xor, CATS regions (6 résolutions,
  audit complet), sweep DSIC David (rapport 30–45) ;
- `counterexample` — régimes truthful/shading, surplus 0 vs 7, audits ;
- `brute_force_wall` — 2^n (n=10..20, seed 42) vs CP-SAT ;
- `greedy_los` — ratios empiriques (toy, with_xor, with_budget, regions).
