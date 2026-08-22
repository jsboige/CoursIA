# Pré-enregistrement du discriminant nerf/H¹ pour ICT-15d

> **Statut.** Document de travail grade **T-pré-enregistrement** (research-code, protocole verrouillé AVANT mesure). Suite directe de la micro-nit Hermes sur PR #12248 et du tracker [#12257](https://github.com/jsboige/CoursIA/issues/12257). Consigne le protocole de mesure **avant** l'exécution pour le rendre falsifiable. Aucune mesure n'est ici reportée — c'est un verrou, pas un résultat.
>
> **Objet.** La rangée ICT-15d de [`dissociations-matrix.md`](dissociations-matrix.md) porte un verdict courant `4/4 NON_TRIVIAL`, dominé par la SVD (`s2_over_s1`, `effective_rank`), avec un **contre-exemple fondateur** (`axelrod` à `mean_coboundary=0.5976`, `mean_cocycle=0.0000`, `obstruction_ratio=0.0000`, `sign_consistency=0.0000`) qui établit que la discrimination Čech **n'est pas** portée par la SVD. Le présent document propose une grandeur candidate (`b1` du nerf simplicial) et verrouille **avant mesure** le critère falsifiable qui tranchera si la discrimination Čech tient ou si elle retombe à nouveau sur un proxy redondant.
>
> **Référence amont.** Le calcul Čech actuel d'ICT-15d (`mean_coboundary`, `s2_over_s1`, `effective_rank`) est rangé par `count_code_sorry.py` sans `sorryAx`. Le bridge ICT-15c→ICT-15d exporte les sections locales en `dict[substrat] -> ndarray(n_fenetres, n_proxys, n_features)` — c'est **exactement** l'input requis pour le nerf. Pas de recalcul upstream. Pas de duplication d'instrument.

## La grandeur candidate

`nerve_simplicial_b1_count` — nombre de **classes d'homologie b₁** (cycles 1-dim) du nerf simplicial construit sur le recouvrement `{sections_locales_des_3_proxys}` du faisceau Φ/F/K.

### Construction (verrouillée avant mesure)

Pour chaque substrat (`gray_scott`, `axelrod`, `grokking`, `may`) :

1. **Charger** les 30 fenêtres × 3 sections locales depuis l'export ICT-15c (relecture idempotente : `np.load(...)` du fichier `.npy` produit par `ICT-15c-MetaProxyObstruction.ipynb` cellule de sortie).
2. **Vietoris-Rips** sur les 3 sections par fenêtre : arête si `‖s_i − s_j‖ ≤ ε`, avec `ε = médiane des distances par paires inter-proxys` sur la fenêtre.
3. **Persistance** : `gudhi.simplex_tree.SimplexTree` → `persistence()` → extraction `b1` (intervalles de dimension 1).
4. **Agrégation** par substrat : `b1_mean`, `b1_std`, `b1_max`.

### Bibliothèque et coût

Lib `gudhi` (open-source, MIT, TDA) — déjà requise par le dépôt (cf `requirements.txt` ICT). Vérifiable via `python -c "import gudhi; print(gudhi.__version__)"`. Coût CPU : ~5–15 s pour 4 substrats × 30 fenêtres × 3 proxys sur CPU laptop typique. **GPU-required : NON.** Branche exécutable par toute lane, pas de gate matériel.

## Critère falsifiable

| Prédiction | Critère vérifiable |
|---|---|
| `b1` **diverge** de `s2_over_s1` | Pearson `ρ(b1_mean, s2/s1) < 0.9` sur le panel 4 substrats |
| `b1` **discrimine** les 4 substrats | `(max(b1_mean) − min(b1_mean)) / max(b1_std) ≥ 2` |
| `b1` **non-trivial sur axelrod** | `b1_mean(axl) ≥ 1` (le contre-exemple fondateur de la non-discrimination par SVD) |

**Verdict** :
- `NON_TRIVIAL` si les trois prédictions sont satisfaites.
- `TRIVIAL` sinon, **avec énoncé explicite** du critère violé.

## Ce que la PR future portera

- Module `MyIA.AI.Notebooks/IIT/ICT-Series/ict/nerve_discriminant.py` (~80 lignes, idempotent) :
  - `build_nerve_b1(sections_window, eps=None)` → `dict[str, float]` (`{b1_mean, b1_std, b1_max, b1_max_window}`).
  - `verdict_falsifiable(b1_by_substrat, s2_over_s1_by_substrat) -> VerdictFalsifiable`.
  - `aggregate(substrat_b1) -> AggregateReport`.
- Notebook `ICT-15d-Discriminant-Nerve.ipynb` (≥ 8 cellules : imports, chargement sections, construction du nerf, calcul b1, falsifiabilité, verdict, **3 exercices stub C.1** : `# TODO étudiant : remplace ε = médiane par ε = knn-distance et observe le verdict`) — planches de visualisation et verdict falsifiable.
- Sortie committée (C.2) : tableau récapitulatif `b1_mean / b1_std / verdict` sur les 4 substrats.
- PR corps : section `## Diagnostic dérive` (C.4) obligatoire + section `## Verdict` falsifiable verbatim.

## Ce que ce grain **n'est PAS**

- **Pas** une redéclaration du verdict ICT-15d tel qu'il est écrit dans la matrice. La rangée 96 reste `Spéculatif (réserve de non-discrimination)` jusqu'à livraison du verdict discriminateur **mesuré** — pas avant.
- **Pas** une généralisation à ICT-15c, ICT-15e, ni aux bridges. La discrimination Čech est d'abord testée là où la question est ouverte (ICT-15d), puis étendue si elle porte.
- **Pas** une dépendance GPU. `gudhi` tourne sur CPU ; l'échelle 4 substrats × 30 fenêtres est triviale.
- **Pas** une modification du notebook ICT-15d. Le présent document décrit un **module frère** qui consomme la sortie d'ICT-15c et propose un verdict complémentaire. ICT-15d reste à 4/4 NON_TRIVIAL par SVD ; la question traitée ici est : *« cette lecture Čech discrimine-t-elle vraiment, ou est-ce un proxy redondant ? »*

## Voisinage

- [#12257](https://github.com/jsboige/CoursIA/issues/12257) — tracker du chantier discriminant
- [#12183](https://github.com/jsboige/CoursIA/issues/12183) — issue fondateur de la requalification ICT-15d
- [PR #12248](https://github.com/jsboige/CoursIA/pull/12248) — `3 temps (mesure / péremption / réserve)` de la rangée 96
- [#11690](https://github.com/jsboige/CoursIA/issues/11690) — ledger ICT strand 2 (consolidation ICT)

## Notes de rédaction

- Format âge-dépendant : si ICT-15c venait à changer d'export (taille, format, hypothèses), ce pré-enregistrement devient obsolète — il faudrait alors réouvrir [#12257](https://github.com/jsboige/CoursIA/issues/12257) avec un lien vers le changement upstream.
- L'option « ε = knn-distance » dans l'exercice stub C.1 est volontairement laissée à l'étudiant : c'est une hypothèse falsifiable supplémentaire qui ne demande qu'une ligne de modification. Pas de livrable supplémentaire pour le worker ; la mesure principale est verrouillée ci-dessus.
