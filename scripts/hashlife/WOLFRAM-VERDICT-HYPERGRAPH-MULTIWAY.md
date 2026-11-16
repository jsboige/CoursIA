# WOLFRAM-VERDICT-HYPERGRAPH-MULTIWAY — verdict d'outil du Pli 5 (Grain A)

**Issue** : #23093 Pli 5, Grain A (EPIC Origami #19742)
**PR** : #26671
**Date de la mesure** : 2026-11-15
**Lane** : myia-po-2024:CoursIA
**Organe mobilisé** : sonde d'invocation firsthand du paquet `setreplace` 0.2.0 — générateur committé : [`setreplace_probe.py`](setreplace_probe.py), sortie committée : [`setreplace_probe_results.json`](setreplace_probe_results.json)

## Question posée par le pli

Quel outil exécute les trois briques du Pli 5 — réécriture d'hypergraphes, systèmes multiway, graphe causal — sans contourner un moteur réel installable ? Le pli exige un **verdict unique et écrit**, chaque branche épuisée dans l'ordre, la prémisse mesurée à la source.

## Branches épuisées, dans l'ordre

1. **Noyau Wolfram Language** (le moteur de référence du projet). Absent du siège, mesuré des deux côtés : `which wolframscript` sous Windows → introuvable ; `command -v wolframscript` / `WolframKernel` sous WSL Ubuntu → tous deux absents. Son installation exige une licence, qui est une **décision de mainteneur** — le corps du pli le prévoit : « si le grain A conclut qu'il le faut, la question va au registre des questions user ». **Le grain A ne conclut pas qu'il le faut** (voir verdict) : aucune question registre n'est ouverte.
2. **Outil SOTA installable sans licence**. [`setreplace`](https://pypi.org/project/setreplace/) 0.2.0 sur PyPI, auteur **Kovas Boguta** (collaborateur du Wolfram Physics Project), moteur Rust, wheel abi3 sans dépendance native, « SetReplace-exact hypergraph substitution ». **Invocation prouvée firsthand** (2026-11-15, ce siège) : la règle de l'annonce du Physics Project `{{x, y}, {x, z}} -> {{x, z}, {x, w}, {y, w}, {z, w}}` évolue **1500 événements en 0,08 s** (3004 arêtes finales, 1504 atomes, 12 générations, terminaison `MaxEvents`), **déterminisme à graine égale vérifié**, et le **graphe causal est natif** : `causal_graph_edges()` rend 2996 arêtes de dépendance entre événements. Sortie intégrale : [`setreplace_probe_results.json`](setreplace_probe_results.json), **régénérée par [`setreplace_probe.py`](setreplace_probe.py)** (aucune valeur n'est écrite à la main ; le JSON est la sortie du script).
3. **Bibliothèques équivalentes**. `hypernetx` 2.4.3 (mesuré sur PyPI) : hypergraphes **statiques** — incidence, dessin, propriétés — aucune réécriture. `networkx` : pas de réécriture d'hypergraphes. Aucun équivalent installable pour la substitution.
4. **La brique multiway**. `setreplace`-py ne l'expose pas, mesuré à la source : README (« Not yet: multiway systems and branchial »), docs de l'API (« Later, when multiway lands in the engine »), et la surface elle-même — `replace_once()` déterministe par `event_ordering`, **aucune énumération des matchs** rendue. Le paclet WL `SetReplace` a `MultiwaySystem` mais exige le noyau WL (branche 1). La couche multiway du Grain B sera donc une **instrumentation maison déclarée** — pré-autorisée par le corps du pli (« le pli continue avec l'alternative retenue, il ne s'arrête pas ») et conforme au précédent des plis 3 à 9 (organes maison dans `scripts/hashlife/`). Elle n'est **pas** un contournement : aucun outil multiway installable n'a été mesuré.

Note de mesure : `str(Rule.parse(r))` **canonise** les noms de variables (`x` → `x1`, etc.) ; le re-parse de la forme canonique round-trippe — c'est une normalisation, pas une casse.

## Verdict

**SOTA-OK.** Le moteur de réécriture exact-SetReplace (`setreplace`-py, vrai outil, installé, invoqué) est l'outil du Pli 5 pour la substitution et le graphe causal : les sorties committées du pli seront ses vraies sorties. La couche multiway du Grain B est une instrumentation maison **déclarée** avec **cross-validation obligatoire** : sur le chemin déterministe à graine égale, l'état final produit par la couche maison doit reproduire l'état final de `setreplace` — c'est le contrôle de correction que le pli exige, et il est gratuit parce que les deux moteurs existent. Le noyau WL n'est pas conclu nécessaire ; si un Grain ultérieur établit le contraire, la question ira au registre selon les termes du pli.

## Ce que les grains suivants héritent

- **Grain B (la mesure)** : la règle de l'annonce comme règle témoin initiale ; l'échelle temps/nombre d'états multiway mesurée par la couche maison ; seuils déclarés **avant** la mesure ; témoin d'état final ; JSON verbatim committé ; cross-validation maison ↔ `setreplace` sur le chemin déterministe.
- **Grain C (le pont Gorard)** : `causal_graph_edges()` / `causal_graph_dot()` natifs — le pli part du graphe causal **calculé par l'outil**, pas redessiné à la main.

## Idées de la matrice du jalon 2 (#19766) utilisées par ce grain

- **[DISTILL-Pli5-A]** « Le projet de physique comme réécriture d'hypergraphes » — l'outil retenu implémente exactement ce substrat.
- **[DISTILL-Pli5-C]** « Le temps = application progressive d'une règle » — la sémantique événements/générations de `setreplace` est cette idée, en moteur.

(Pli5-B « l'espace = collection de relations abstraites » servira les grains B/C au carnet.)

## Hôte du carnet

Non tranché ici, conformément au pli : « ne pas créer de carnet avant que l'hôte soit tranché » — l'argument d'hôte (Complexity 08 réservée, branche Conway des carnets Lean, ou sous-série neuve) se fera au design-gate, après le Grain B.

See #23093 (le pli) · See #19742 (l'Epic) · See #19766 (jalon 2, matrice idées → plis) · See #19741 (Gorard, issue sœur) · See #8957 (précédent re-baseline, hors sujet ici mais voisin de dépôt)
