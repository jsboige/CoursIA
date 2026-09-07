# Provenance — App-30 Orbital Assembly Certificate Audit

## Travail étudiant distillé

- **Auteurs** : Gurvan Estable, Joris Bely et Kévin Lubert
- **Projet** : *Assemblage orbital de satellites (Orbital Assembly Scheduling)*, sujet C4, EPITA SCIA, Programmation par Contraintes 2026
- **Dépôt source** : <https://github.com/jsboigeEpita/2026-Epita-Programmation-par-Contraintes/tree/main/groupe-C4-Orbital_Assembly_Scheduling>
- **Pull request source** : [PR #53](https://github.com/jsboigeEpita/2026-Epita-Programmation-par-Contraintes/pull/53), fusionnée le 22 mai 2026 ; le corps de la PR nomme les trois auteurs, le compte de dépôt étant `popop1221`
- **Commit intégré** : `e9a751bc440f1063fa36582aab8b91eec3bdfd55`
- **Snapshot audité** : `b5f3f0351dbd41f3a76f047cf02e9c93e81192f3`
- **Licence source** : MIT, copyright 2026, *EPITA SCIA - Programmation par Contraintes (students and teaching staff)* — vendorisée dans `LICENSE`

Le dispositif étudiant articule une modélisation CP-SAT complète de l'assemblage orbital : intervalles à durée variable, deux profils de propulsion, exclusivité des couloirs par `AddNoOverlap`, précédences d'assemblage, séparations de sécurité réifiées dans les deux orientations, budget d'ergol global et capacité concurrente par `AddCumulative`, le tout adossé à une physique de transfert de Hohmann réellement calculée plutôt que simulée par des constantes arbitraires. Une baseline gloutonne, un validateur, une suite de benchmark sur 25 instances et deux figures complètent le rendu. Ce couplage explicite entre décisions temporelles et énergétiques est le geste central auquel App-30 rend hommage.

Le rapport source est méthodologiquement prudent : il qualifie lui-même son objectif d'« approximation lexicographique », signale que la rapidité observée « ne garantit pas un passage à l'échelle linéaire » et inscrit noir sur blanc que « le benchmark reste synthétique et limité à 12 modules ». App-30 prolonge ces réserves au lieu de les découvrir.

## Réécriture et collecte CoursIA

App-30 ne copie aucun module, test, notebook, figure, sortie, capture ou fragment de prose étudiante. En particulier, `src/solver_cp_sat.py`, `src/baseline_greedy.py`, `src/instance_generator.py`, `src/validation.py`, `src/orbit_physics.py`, `src/experiments.py`, `src/plotting.py`, `run_experiments.py`, `notebook.ipynb`, `benchmark_overview.png`, `single_instance_schedule_comparison.png` et les CSV de `results/` n'ont été ni repris, ni traduits, ni adaptés. Les seules grandeurs du rendu source citées dans le notebook sont des propriétés vérifiables de ses CSV publiés, recalculées par lecture et présentées comme telles.

L'appareil CoursIA est une construction indépendante : structures `Burn` / `AssemblyInstance`, générateur à module clé de voûte, auditeur externe par balayage événementiel, encodage pondéré, encodage lexicographique en deux passes, front d'échange par ε-contrainte et règle de répartition. Les relations de Hohmann, de vitesse circulaire et de période orbitale sont des identités canoniques à deux corps, redérivées des formules usuelles.

La **discrétisation est délibérément différente** de celle du rendu source — 900 s par créneau et 1 unité d'ergol = 5 m/s, contre 600 s et 10 m/s — afin que les grandeurs produites ici ne puissent jamais être confondues avec les siennes ni agrégées avec elles. Aucun chiffre d'App-30 n'est comparable à un chiffre du rendu source, et aucune conclusion n'est transférée d'une famille d'instances à l'autre : seul le protocole de mesure se transporte.

Le notebook exécuté produit :

- `grid_runs.csv` — les deux encodages et la règle de répartition sur la grille CoursIA, avec statut, makespan, ergol, conflits, branches, temps et verdict de l'auditeur externe ;
- `matched_comparison.csv` — la comparaison à makespan égal, qui isole l'inefficacité en ergol de l'heuristique de son retard d'échéancier ;
- `exchange_fronts.json` — les fronts d'échange makespan ↔ ergol par ε-contrainte, avec le niveau de certification de chaque point ;
- `difficulty_probe.csv` — la sonde au-delà de la grille publiée, en taille et en densité de disjonctions ;
- `provenance.json` — empreintes SHA-256 d'identité structurelle des instances et versions de l'environnement de collecte.

Commande de reproduction depuis la racine CoursIA :

```powershell
python scripts/notebook_tools/notebook_tools.py execute MyIA.AI.Notebooks/Search/Applications/Hybrid/App-30-OrbitalAssembly-Certificate-Audit.ipynb --timeout 600 --verbose
```

Environnement de la collecte : Windows 11, Python 3.13, OR-Tools CP-SAT, pandas, NumPy et matplotlib. Les versions exactes sont enregistrées dans `provenance.json` lors de l'exécution.

## Contrat d'identité des instances

Le nom d'une instance est informatif, jamais une clé suffisante. Deux instances ne sont réputées identiques que si l'empreinte SHA-256 de leur structure complète — couloirs, fenêtres d'accès, durées et coûts des deux profils, précédences triées, séparations triées, budget, capacité et horizon — coïncide. Aucune grandeur d'App-30 n'est rapprochée d'une grandeur externe sans cette égalité d'empreinte.

## Niveaux de preuve et limites

- `OPTIMAL` signifie que le solveur a certifié l'incumbent. `FEASIBLE` reste un plan valide mais non certifié optimal, et n'est jamais présenté comme un optimum.
- L'encodage en deux passes produit **deux** certificats indépendants. Un résultat noté `OPTIMAL/FEASIBLE` signifie que le makespan optimal est certifié et que le départage en ergol ne l'est pas ; cette information est perdue par l'encodage scalarisé, qui ne rend qu'un statut global.
- Un point du front d'échange n'est dit certifié que si sa passe ε-contrainte est `OPTIMAL` ; sinon il reste un point observé sous limites.
- L'auditeur externe est écrit à partir des seules sémantiques de contraintes et n'est appelé par aucun solveur pour établir sa propre faisabilité. Il signale l'intégralité des fautes, jamais la première.
- Les instances sont synthétiques et déterministes. Elles enseignent un protocole de mesure ; elles ne constituent ni une étude de performance industrielle, ni une revalidation du rendu source, ni une campagne d'assemblage réaliste.
- La physique reste volontairement simplifiée : orbites circulaires, transferts de Hohmann, aucune propagation haute fidélité ni perturbation. Cette simplification est héritée du cadrage du sujet et assumée.
- La ressource cumulative d'App-30 consomme un **débit** d'ergol par créneau, lecture dimensionnellement homogène. Une lecture par impulsion totale est également défendable et conduit à un modèle différent ; le choix est explicité, non imposé.
