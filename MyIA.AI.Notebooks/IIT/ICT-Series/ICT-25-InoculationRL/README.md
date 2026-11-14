# ICT-25-InoculationRL — l'inoculation RL sous récompense hackable

Sous-série de la [série ICT](../README.md). Le capstone de la strate 5 et le pont ICT↔PostTraining : une récompense hackable est rendue au modèle par GRPO, et une persona est inoculée dans les poids pour mesurer ce que cette inoculation coûte et ce qu'elle révèle.

| Carnet | Ce qu'il démontre et sa place dans l'escalier |
|---|---|
| [ICT-25-InoculationRL-Python](ICT-25-InoculationRL-Python.ipynb) | **Tête de la sous-série** — le banc GRPO × inoculation : faille hackable certifiée par test, détection offline validée sur log synthétique, trio de system-prompts N/I/P, budget EOS calibré (80 → 1024 tokens), résultat négatif assumé à 0,5B (le hack n'éclôt pas dynamiquement à cette échelle) et scale-up 1,5B → 32B mesuré ; la comparaison causale N/I reste suivie dans [#5105](https://github.com/jsboige/CoursIA/issues/5105) sur GPU-2 |

Les artefacts de mesure voyagent avec le carnet qui les lit : `results/ict25/` (un fichier par bras, par graine, plus la mesure EOS du budget). Ils sont produits par `../scripts/ict25_arms.py` et `../scripts/ict25_eos.py`, et le carnet les relit seul, sans ré-exécution GPU.

Le retour vers la [série ICT](../README.md) se fait depuis le dernier carnet.
