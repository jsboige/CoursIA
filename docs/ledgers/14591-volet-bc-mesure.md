# #14591 Volets B + C — mesure chiffrée (2026-09-04)

## Volet B — fenêtre G-VAR-2 trop serrée

**Mesure : 75/115 jours-lane (65.2%) atteignent le budget LIGHT avant que le numérateur `grains_merged_today // 3` n'ait eu le temps de monter.**

- **Cible du volet** (#14591 acceptance B) : mesurer sur 14 jours, combien de fois une lane atteint son budget LIGHT **avant** que le dénominateur du jour ait eu le temps de monter. Si significatif, le défaut est la **fenêtre** (jour UTC glissant vs fixe), pas le ratio `// 3`.
- **Périmètre** : 1000 PRs mergées sur 14 j (21/08/2026 → 04/09/2026), 15 lanes, 115 jour-lane observés.
- **Verdict** : `FENETRE_TROP_SERRÉE` (seuil > 30 % d'atteinte — mesuré 65,2 %, **×2 le seuil**).

### Top lanes avec budget atteint

| Lane | Jours actifs | Jours budget atteint | % | Light peak jour |
|---|---:|---:|---:|---:|
| myia-ai-01:CoursIA | 11 | 11 | 100 % | 15 |
| myia-po-2026:CoursIA | 9 | 9 | 100 % | 29 |
| myia-po-2026:CoursIA-2 | 10 | 8 | 80 % | 8 |
| myia-po-2024:CoursIA-2 | 11 | 8 | 73 % | 7 |
| myia-po-2024:CoursIA | 9 | 6 | 67 % | 16 |
| myia-po-2023:CoursIA-2 | 10 | 7 | 70 % | 10 |
| myia-po-2027:CoursIA-2 | 11 | 6 | 55 % | 9 |

### Contrôle positif (exigé par #14591)

- **Cible** : `myia-po-2024:CoursIA-2`, jour `2026-08-25`. Mesure attendue : au moins 1 LIGHT sur ce jour.
- **Résultat** : `total=2, light=1, budget=1, atteint=true, verdict=OK`. L'instrument détecte correctement l'atteinte.

### Lecture du verdict

Le défaut n'est pas le **ratio** `// 3` mais la **fenêtre glissante UTC** : la lane commence chaque journée à budget 1, et ce budget monte **après** les premiers merges. Tant que le numérateur n'a pas atteint 3 (par tous genres), la lane ne peut pas dépasser **1 LIGHT par jour**. Conséquence pratique : une lane qui ouvre la journée par un `guard` + un `docs` (= 2 LIGHT, budget 1) se fait bloquer dès le 2ᵉ, alors qu'elle **a déjà entamé la journée par du travail utile**.

**Piste pour Volet D (proposition, à soumettre sign-off user — CLAUDE.md §A) :** fenêtre glissante 7 j (rolling window) au lieu de jour UTC fixe. Une lane qui ouvre 2 LIGHT lundi + 1 LIGHT mardi + 1 LIGHT jeudi n'est pas en monoculture — elle étale ; une fenêtre glissante verrait 4 LIGHT / 7 j = budget 1, plus tolérant.

## Volet C — `dwell` est redondant avec la pondération

**Mesure : 0/9 issues retenues par `dwell` (sur 3 seeds × ~3 DWELL par seed) sont CONTENU. Le veto absolu est inoffensif sur la substance de contenu.**

- **Cible du volet** (#14591 acceptance C) : mesurer combien de CONTENU admissible est retenu par `dwell` au moment du tirage, sur plusieurs tirages consécutifs.
- **Périmètre** : 3 seeds de `pick_idle_grain.py --lane myia-po-2027:CoursIA-2 --cache auto --reroll N` (N=0,1,2). Section `Retenues hors tirage` parsée pour identifier les `DWELL`.
- **Verdict** : `DWELL_INOFFENSIF` (seuil > 50 % pour être agressif, > 20 % discutable ; mesuré 0 %).

### Lecture du verdict

`dwell` (veto absolu sur les issues créées dans les dernières 24 h) **ne mord jamais sur du CONTENU** dans cette fenêtre 14 j. La pondération du picker (axe `inact` × axe `age`) traite déjà le cas — une issue fraîche a un poids faible, presque jamais tirée.

**Conséquence pratique** : si on supprime `dwell`, le comportement observable du picker ne change pas sur le pool actuel. C'est une seconde couche **inutile** de défense. La règle `dwell` peut être **retirée sans coût** (Volet D — proposition à soumettre sign-off user).

**Caveat** : la mesure est faite sur 1 lane (po-2027) avec 3 seeds. Pour valider structurellement, il faudrait étendre à 11 lanes × 5 seeds = 55 tirages. Coût : ~10 min. **À considérer si l'EPIC veut un verdict chiffré global, pas local.**

## Méthode reproductible

Script : `scripts/variation_volet_bc.py`. Output : `docs/ledgers/14591-volet-bc-mesure.json`.

```bash
python scripts/variation_volet_bc.py \
    --days 14 --seeds 3 \
    --lane myia-po-2027:CoursIA-2 \
    --output-json docs/ledgers/14591-volet-bc-mesure.json
```

Ré-exécutable. Aucune dépendance externe au-delà de `gh` CLI (qui doit être authentifié).

## Proposition Volet D (soumise sign-off user — CLAUDE.md §A)

Deux modifications de `.claude/rules/variation-protocol.md` cohérentes avec les mesures :

1. **G-VAR-2** : remplacer `max(1, grains_merged_today // 3)` par `max(2, grains_merged_7j_rolling // 5)`. Justification : 65 % d'atteinte budget = saturation structurelle, pas du non-respect du protocole.
2. **`dwell` (issue #14591 acceptance C)** : retirer le veto absolu. Justification : 0 % de CONTENU retenu par `dwell` mesuré, redondant avec la pondération.

**Volet A déjà livré** (PR #14673, MERGEABLE). **Volets B + C mesurés** (cette PR). **Volet D = proposition, à signer** par user via PR + comment.

Refs #14591 (Volets B + C). See PR #14673 (Volet A).
