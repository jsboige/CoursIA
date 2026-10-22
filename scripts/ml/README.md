# scripts/ml — outillage ML de mesure

Scripts de mesure reproductible pour la série **ML**. Ils vivent hors de
`MyIA.AI.Notebooks/` : ils ne rejouent pas un carnet, ils **verifient** ce
qu'un carnet a publie, en reconstruit le protocole et en rejoue la mesure sur
le corpus brut.

Regle commune : aucun acces reseau au corpus. Les scripts lisent les fichiers
IDX du cache local (format documenté par He et al., 2010) et echouent
explicitement (`rc=2`) si le cache est absent — jamais de repli silencieux.

## `reproduce_ws_probes.py`

Reproduction hors carnet des sondes de la souserie **Wavelet Scattering**
(`MyIA.AI.Notebooks/ML/DataScienceWithAgents/04b-Wavelet-Scattering/`).
Issue de suivi : #21823 (suite de la revue de la PR #21771).

```bash
python scripts/ml/reproduce_ws_probes.py \
    [--cache ~/.cache/ft00a/FashionMNIST/raw] \
    [--json scripts/results/ws_probe_<date>.json] \
    [--repeats 40] [--no-sweep]
```

Quatre mesures, en cascade :

| # | Mesure | Question a laquelle elle repond |
|---|--------|-----------------------------------|
| A | WS-00c §6, protocole exact du carnet | les valeurs **committes** sont-elles reproductibles ? |
| B | WS-03, temoin pixels bruts standardise | idem, pour le deuxieme carnet |
| C | WS-00c §6 en split non deterministe (N occurrences) | la paire publiee tombe-t-elle dans la dispersion ? |
| D | 16 variantes du protocole WS-00c | quel protocole, s'il y en a un, reproduit la paire publiee ? |

### Le piege de protocole que ce script documente

Les deux carnets translatent le jeu de test **de facon differente**, et la
difference est silencieuse :

- `WS-00c` (cellule 21) itere sur les **index d'origine** (`for i in te_i`) :
  la parite du decalage ±2 px suit l'index de l'image dans le corpus ;
- `WS-03` (cellule 2) itere sur `enumerate(X_te)` : la parite suit la
  **position** dans le tableau de test.

Rejouer l'un avec la recette de l'autre decale le test de quelques images et
fait varier le score « test ±2 px » de ~0,015 **sans lever aucune erreur**.
Les deux recettes sont donc nommees explicitement dans le script
(`translate_by_index`, `translate_by_position`), et chaque carnet est rejoue
avec la sienne.

### Mesures du 2026-10-21

Environnement : numpy 2.2.6, scikit-learn 1.9.1, cache `~/.cache/ft00a`.

| Mesure | Valeur | Attendu | Verdict |
|--------|--------|---------|---------|
| A — WS-00c §6 (graine 42) | 0,790 / 0,425 | 0,790 / 0,425 (sorties committes, cellule 21) | **reproduit** |
| B — WS-03 (graine 42) | 0,780 / 0,311 | 0,780 / 0,311 (sorties committes, cellule 8) | **reproduit** |
| C — WS-00c sans graine, 40 occurrences | enveloppe 0,755–0,835 / 0,385–0,510, σ ≈ 0,016 / 0,030 | — | la paire publiee est dans l'enveloppe (percentiles 2 et 25) |
| D — 16 variantes | 0 variante reproduisant 0,773 / 0,431 | — | **paire non reproductible** |

Les bornes de la ligne C dependent du tirage (le split de ce protocole est
volontairement sans graine) : elles sont celles de l'execution datee par
l'agregat, pas une constante. Ce qui reste stable d'une execution a l'autre —
et qui porte la lecture ci-dessous — est que A et B reproduisent les valeurs
committes, et qu'aucune des 40 occurrences de C ni aucune des 16 variantes de D
ne reproduit exactement la paire publiee.

Lecture : les valeurs **committes** des deux carnets sont reproductibles hors
carnet au chiffre pres, et le protocole des deux est correctement reconstitue.
La paire **0,773 / 0,431** reprise dans le corps de la PR #21771, elle, n'est
reproduite par **aucune** des seize variantes documentees : elle est
compatible avec la dispersion du protocole non deterministe, mais elle n'est
pas la sortie d'un protocole qu'on puisse nommer. Un nombre qui depend d'un
tirage non declare n'est pas un nombre qu'on peut opposer a une revue —
c'est ce que cette mesure etablit, et elle ne l'etablit que pour cette paire.

Agregat : [`scripts/results/ws_probe_2026-10-21.json`](../results/ws_probe_2026-10-21.json).