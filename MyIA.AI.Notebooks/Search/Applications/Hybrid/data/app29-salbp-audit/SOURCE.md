# Provenance — App-29 SALBP Certificate Audit

## Travail étudiant distillé

- **Auteurs** : Ilias Kalalou et Kaelan Grall
- **Projet** : *Équilibrage de chaîne d'assemblage (SALBP)*, groupe B1, EPITA SCIA, Programmation par Contraintes 2026
- **Dépôt source** : <https://github.com/jsboigeEpita/2026-Epita-Programmation-par-Contraintes/tree/main/B1-SALBP-IliasKalalou-KaelanGrall>
- **Historique cumulé** : [PR #57](https://github.com/jsboigeEpita/2026-Epita-Programmation-par-Contraintes/pull/57) (solveurs, tests et application), [PR #67](https://github.com/jsboigeEpita/2026-Epita-Programmation-par-Contraintes/pull/67) et [PR #68](https://github.com/jsboigeEpita/2026-Epita-Programmation-par-Contraintes/pull/68) (slides et intégration ciblée)
- **Commits intégrés** : `7456bbcec169739a9c573b9c20e8cbf8c758c1cd` et `bf59d749`
- **Snapshot audité** : `b5f3f0351dbd41f3a76f047cf02e9c93e81192f3`
- **Licence source** : MIT, copyright 2026, *EPITA SCIA - Programmation par Contraintes (students and teaching staff)*

Le dispositif étudiant réunit SALBP-1, SALBP-2, CP-SAT, PuLP/CBC, l'heuristique Ranked Positional Weight, une variante multi-modèles, une exploration bi-objectif, 25 fichiers `.IN2`, 57 tests et une application Streamlit. Cette ampleur constitue le geste central de l'hommage.

## Réécriture et collecte CoursIA

App-29 ne copie aucun module, test, notebook, texte, graphique ou capture étudiante. Les petites instances sont générées dans le notebook avec des graines fixes ; les modèles, validateurs, expériences et figures sont des réécritures CoursIA indépendantes.

Le notebook exécuté produit :

- `provenance.json` — identité structurelle SHA-256 des instances et démonstration d'une jointure de référence acceptée/refusée ;
- `benchmark_runs.csv` — CP-SAT, PuLP/CBC et RPW avec statut, incumbent, borne, gap, temps et validation indépendante ;
- `pareto_fronts.json` — points du balayage ε-contrainte et niveau de certification ;
- `mmalbp_runs.json` — comparaison de la lecture conservatrice et de l'agrégation pondérée par la demande.

Commande de reproduction depuis la racine CoursIA :

```powershell
python scripts/notebook_tools/notebook_tools.py execute MyIA.AI.Notebooks/Search/Applications/Hybrid/App-29-SALBP-AssemblyLineBalancing-Audit.ipynb --timeout 300 --verbose
```

Environnement de la collecte : Windows 11, Python 3.13, OR-Tools CP-SAT, PuLP/CBC, pandas, NumPy et matplotlib. Les versions exactes sont enregistrées dans les métadonnées de `provenance.json` lors de l'exécution.

## Contrat de provenance

Le nom d'une instance est informatif, jamais une clé suffisante. Une référence n'est comparable que si le nombre de tâches, les durées, les arcs de précédence triés et le temps de cycle produisent le même hash. En cas d'écart, App-29 retourne `not_comparable` et ne calcule aucun gap à une valeur de référence.

## Niveaux de preuve et limites

- `OPTIMAL` signifie que le solveur a certifié l'incumbent ; `FEASIBLE` reste une solution valide, mais non certifiée optimale.
- La meilleure borne et le gap solveur sont conservés séparément d'une éventuelle référence externe.
- Le front est dit certifié seulement lorsque SALBP-1 et chaque SALBP-2 du balayage sont `OPTIMAL` ; sinon il reste un front observé sous limites.
- Les expériences portent sur de petites instances synthétiques déterministes. Elles enseignent le protocole et ne constituent ni une étude de performance industrielle ni une revalidation exhaustive des 25 fichiers sources.
- La lecture MMALBP conservatrice impose le cycle à chaque modèle ; la lecture pondérée étudie un mix moyen. Elles répondent à deux questions différentes et aucune n'est universellement supérieure.
