# Pré-enregistrement du discriminant nerf/H¹ pour ICT-15d

> **Statut.** Document de travail grade **T-pré-enregistrement** (research-code, protocole verrouillé AVANT mesure). Suite directe de la micro-nit Hermes sur PR #12248 et du tracker [#12257](https://github.com/jsboige/CoursIA/issues/12257). Consigne le protocole de mesure **avant** l'exécution pour le rendre falsifiable. Aucune mesure n'est ici reportée — c'est un verrou, pas un résultat.
>
> **Objet.** La rangée ICT-15d de [`dissociations-matrix.md`](dissociations-matrix.md) porte un verdict courant `4/4 NON_TRIVIAL`, dominé par la SVD (`s2_over_s1`, `effective_rank`), avec un **contre-exemple fondateur** (`axelrod` à `mean_coboundary=0.5976`, `mean_cocycle=0.0000`, `obstruction_ratio=0.0000`, `sign_consistency=0.0000`) qui établit que la discrimination Čech **n'est pas** portée par la SVD. Le présent document propose une grandeur candidate (`b1` du nerf simplicial) et verrouille **avant mesure** le critère falsifiable qui tranchera si la discrimination Čech tient ou si elle retombe à nouveau sur un proxy redondant.
>
> **Référence amont.** Le calcul Čech actuel d'ICT-15d (`mean_coboundary`, `s2_over_s1`, `effective_rank`) est rangé par `count_code_sorry.py` sans `sorryAx`. Le bridge ICT-15c→ICT-15d exporte les sections locales en `dict[substrat] -> ndarray(n_fenetres, n_proxys, n_features)` — c'est **exactement** l'input requis pour le nerf. Pas de recalcul upstream. Pas de duplication d'instrument.

## La grandeur candidate

`nerve_simplicial_b1_persistance` — **diagramme de persistance de l'homologie b₁** du nerf simplicial Vietoris-Rips construit sur **les 90 sections locales par substrat** (30 fenêtres × 3 proxys mises à plat, **pas par fenêtre sur 3 points**). Trois grandeurs sont dérivées du diagramme : `n_classes_b1` (nombre de classes), `persistance_totale_b1` (somme des longueurs des intervalles), `persistance_max_b1` (longueur du plus long intervalle). Les seuils falsifiables sont verrouillés sur ces grandeurs-là, **avant** mesure.

### Pourquoi pas 3 points par fenêtre (chemin mort-né, **fermé**)

Le brouillon v1 construisait le VR sur les 3 sections par fenêtre. Un complexe VR est un **complexe drapeau** : dès que les 3 arêtes d'un triangle sont présentes, le 2-simplexe l'est aussi. Sur 3 points, le 1-cycle naît et meurt à la **même** valeur de filtration — l'intervalle de persistance est vide, `b1 ≡ 0` structurellement, pour tout ε, pour tout nuage. Contrôle positif ai-01 (`gudhi 3.13.0` installé hors-dépôt pour cette vérification) :

- 3 points en triangle équilatéral, ε forcé à 1×, 1.0001×, 2×, 10× le côté : `intervalles dim1 = []`, `b1 = 0`.
- 20 000 fenêtres aléatoires (n_features ∈ {2, 3, 5, 12, 64}) : somme des b1 sur tous les substrats = 0.
- 4 points en carré (contrôle positif) : `intervalles dim1 = [[1.0, √2]]`, `b1 = 1`. → l'instrument gudhi marche, le zéro n'est pas un artefact d'appel.

Conséquence sur les critères v1 — tous **réfutés avant mesure** :

| Critère v1 | État réel |
|---|---|
| `ρ(b1_mean, s2/s1) < 0.9` | indéfini (`nan`, variance nulle) |
| `(max − min) / max(std) ≥ 2` | `0/0` |
| `b1_mean(axl) ≥ 1` | impossible — `b1_mean ≡ 0` sur 3 points |

Sceller un protocole dont la grandeur centrale est mathématiquement inatteignable garantit un faux résultat lu ensuite comme une mesure : c'est précisément ce que ce verrou doit empêcher. **Le chemin par-fenêtre-sur-3-points est fermé ; ce PR documente la fermeture.**

### Construction (verrouillée avant mesure)

Pour chaque substrat (`gray_scott`, `axelrod`, `grokking`, `may`) :

1. **Charger** les 30 fenêtres × 3 sections locales depuis l'export ICT-15c (relecture idempotente : `np.load(...)` du fichier `.npy` produit par `ICT-15c-MetaProxyObstruction.ipynb` cellule de sortie).
2. **Mettre à plat** : `sections_substrat = sections.reshape(n_fenetres × n_proxys, n_features) = (90, n_features)`. Les 90 points sont l'**input géométrique** du nerf.
3. **Vietoris-Rips** sur les 90 points : arête si `‖s_i − s_j‖ ≤ ε`, avec ε balayé sur la filtration complète (`gudhi` produit le diagramme nativement — pas de médiane à choisir).
4. **Persistance** : `gudhi.simplex_tree.SimplexTree` → `persistence(homology_dimensions=[1])` → extraction des `intervals_b1` (list de `(birth, death)`).
5. **Grandeurs verrouillées par substrat** :
   - `n_classes_b1 = len(intervals_b1)` (cardinal du diagramme, entier ≥ 0)
   - `persistance_totale_b1 = sum(death − birth for _, _ in intervals_b1)`
   - `persistance_max_b1 = max(death − birth for _, _ in intervals_b1)` (= `b1_max_persistence`, notion ICT-15d canonique cf. #12285)

### Contrôle positif interne (porte de cohérence instrumentale)

Avant toute mesure sur substrat réel, la PR d'exécution **DOIT** vérifier que `n_classes_b1(4 points en carré) = 1` et `persistance_max_b1(4 pts carré) = √2 − 1 ≈ 0.4142`. Un zéro sur ce contrôle signifie que `gudhi` est mal invoqué, **pas** que le discriminateur est nul. Coût : ~1 s CPU. Aucune conclusion ICT-15d ne peut être tirée tant que ce contrôle n'est pas vert.

### Bibliothèque et coût (statut au 2026-08-22, **corrigé**)

Lib `gudhi` 3.13.x (open-source, MIT, TDA) — **NON encore déclarée dans les `requirements*.txt` du dépôt** au moment de ce pré-enregistrement. Vérification `git grep -ln gudhi -- 'requirements*.txt' '*.toml' '*.cfg'` retourne **0 hits** sur le dépôt complet (cf. c.461 review ai-01, `MyIA.AI.Notebooks/IIT/requirements.txt` la mentionne pas). **La PR d'exécution** ajoutera `gudhi>=3.13` dans `MyIA.AI.Notebooks/IIT/requirements.txt` (section "Optionnel (utilitaires ponctuels, 1-2 usages)" à créer si absente) et installera l'env (`pip install gudhi` + `import gudhi; print(gudhi.__version__)`). Coût CPU : ~5–15 s pour 4 substrats × 90 sections sur CPU laptop typique. **GPU-required : NON.** Branche exécutable par toute lane, pas de gate matériel.

## Critère falsifiable (verrouillé sur grandeurs de persistance)

Les trois critères sont **re-pré-enregistrés** sur les grandeurs de la filtration 90 points par substrat. Les seuils sont **plancher**, pas des optimums : un critère plus discriminant est acceptable, mais l'engagement pris ici est de **ne pas livrer** de verdict `NON_TRIVIAL` si l'un des trois n'est pas satisfait.

| # | Prédiction | Critère vérifiable | Tell |
|---|---|---|---|
| P1 | Le nerf détecte **quelque chose** sur le panel | `n_classes_b1` (somme sur les 4 substrats) ≥ **4** (≥ 1 classe par substrat en moyenne, pas exactement 1) | Si 0 partout, l'instrument est mal invoqué (cf. contrôle positif §2 ci-dessus) |
| P2 | Le nerf **divergence** de la SVD | Pearson `ρ(persistance_totale_b1, s2/s1) < 0.9` sur 4 substrats | Si `ρ ≥ 0.9`, c'est un proxy SVD redondant — même classe de défaut que #12248 |
| P3 | Le nerf **discrimine** les 4 substrats | `(max(n_classes_b1) − min(n_classes_b1)) / max(std(n_classes_b1)) ≥ 2` | Si écart < 2σ, discrimination trop faible — rejoint la "réserve de non-discrimination" ICT-15d actuelle |
| P4 | Le nerf **porte** sur `axelrod` (le contre-exemple fondateur) | `persistance_max_b1(axl) ≥ 0.05` (seuil de **non-trivialité numérique** — un intervalle vide = 0, un intervalle de longueur < 0.05 = quasi-vide) | 0 = le nerf **ne consulte pas** le contrefacteur que la SVD rate |

**Verdict** :
- `NON_TRIVIAL` **si et seulement si les 4 prédictions sont satisfaites**. **Manquer un seul critère = `TRIVIAL`**, **avec énoncé explicite** du critère violé (`P1_failed` · `P2_failed` · `P3_failed` · `P4_failed`).
- **Exclusion explicite des critères v1** : `ρ(b1_mean, s2/s1) < 0.9`, `(max−min)/max(b1_std) ≥ 2`, `b1_mean(axl) ≥ 1` sont **réfutés avant mesure** sur 3 points (cf. §2 chemin mort-né) et **interdits** comme critères. Tout notebook ICT-15d future PR qui les utilise **manque ce verrou**.

## Ce que la PR future portera

- Module `MyIA.AI.Notebooks/IIT/ICT-Series/ict/nerve_discriminant.py` (~80 lignes, idempotent) :
  - `build_nerve_b1(sections_substrat)` → `dict[str, float]` (`{n_classes_b1, persistance_totale_b1, persistance_max_b1, intervals_b1}`). **Input = 90 points à plat par substrat** (cf. §2 Construction).
  - `control_positive_4pts_square() -> bool` — porte de cohérence instrumentale (cf. §2 Contrôle positif interne). **DOIT être vert avant** toute mesure.
  - `verdict_falsifiable(b1_by_substrat, s2_over_s1_by_substrat) -> VerdictFalsifiable` — applique les 4 critères P1–P4, retourne `TRIVIAL` avec `P<n>_failed` explicite sinon.
  - `aggregate(substrat_b1) -> AggregateReport`.
- Notebook `ICT-15d-Discriminant-Nerve.ipynb` (≥ 8 cellules : imports, contrôle positif 4 pts carré, chargement sections par substrat, mise à plat 90 points, construction du nerf, persistance, **3 exercices stub C.1** : `# TODO étudiant : remplace la filtration gudhi native par une filtration kNN-distance et observe le verdict`) — planches de visualisation et verdict falsifiable.
- Sortie committée (C.2) : tableau récapitulatif `n_classes_b1 / persistance_totale / persistance_max / verdict` sur les 4 substrats.
- PR corps : section `## Diagnostic dérive` (C.4) obligatoire + section `## Verdict` falsifiable verbatim avec mention explicite des critères P1–P4 vérifiés ou violés.
- **Dépendance ajoutée** : `gudhi>=3.13` dans `MyIA.AI.Notebooks/IIT/requirements.txt` (section "Optionnel (utilitaires ponctuels, 1-2 usages)" à créer si absente). Documenté ici pour traçabilité — **rien n'est commité sur les requirements dans ce PR de pré-enregistrement**.

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
