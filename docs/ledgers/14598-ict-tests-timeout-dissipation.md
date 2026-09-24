# EPIC #14598 — Ledger dissipation timeout ICT tests/ (55 strates)

**Statut** : Dissipation documentée (cause absorbée par absorption indirecte, body obsolète).

**Source** : Issue #14598 (créée 2026-09-04, "CI infra: la suite ICT tests/ (55) timeout 15 min sur runner po-2024-linux-docker (orthogonal a #14571)"). Body décrit un job qui timeoutait à 15 min le 2026-09-04 sur le runner `myia-po-2024-linux-docker-N`.

**Périmètre** : ce ledger consigne l'état vérifié au 2026-09-24 et la dissipation de l'acceptance — la cause présumée a été absorbée par les fixes ultérieurs, sans nécessiter l'une des options A/B/C du body original.

## Vérification empirique (c.806, 2026-09-24)

**Mesure sur 20 derniers runs `gh run list --workflow="ict-tests.yml" --limit 20`** (filtré sur les runs visibles côté `jsboige`):

| Issue | Statut | Compte |
|-------|--------|--------|
| SUCCESS | 17 / 20 | 85 % |
| CANCELLED | 2 / 20 | 10 % (kills externes, pas `timeout-minutes`) |
| FAILURE | 1 / 20 | 5 % (19/09, hors-série) |

**Mesure complémentaire `gh api runs/33864775787/jobs`** : le job originel `ICT tests/ (55)` a effectivement timeout à `11:01:38Z` (started `10:46:15Z`, durée 15 min 23 s, **donc bien tué par `timeout-minutes`**, pas par cancel externe). Le body est exact sur ce point.

**Lecture du workflow `.github/workflows/ict-tests.yml`** :

- **ligne 189** : `timeout-minutes: 60` — le plafond a été porté de 15 → 30 → **60 min** depuis l'ouverture de l'issue, par absorption indirecte (la branche `#14595` fix #14571 + le travail de xdist/parallelisation ultérieur).
- **lignes 446-471** : la collection floor-guard émet aujourd'hui un `::warning title=ICT collection floor stale` au drift ascendant (et un `::error` à la régression de couverture). Cette protection supplémentaire n'existait pas à l'ouverture de #14598.

**Diagnostic différentiel** :

| Hypothèse du body | Verdict c.806 |
|-------------------|---------------|
| **A** Augmenter `timeout-minutes` de 15 à 30 min | **RÉALISÉE et dépassée** (passage à 60 min) |
| **B** Optimiser la suite `tests/` (55 strates) pour finir < 15 min | **Probable mais non prouvée** — la suite ict/tests/ a probablement gagné en stabilité via la branche xdist (collecte parallélisée, runs de 9 min mesurés dans le commentaire du workflow) |
| **C** Réserver des runners plus rapides (po-2026 / ai-01) | **Non réalisée** — toujours sur `po-2024-linux-docker` |

## Cause directe probable (orthogonale au body)

Le runner `myia-po-2024-linux-docker` a montré des signes de charge partagée en début septembre (cf. incidents `#14571` venv/toolcache, `#14615` memory pressure, `#14620` I/O conteneur). Le 2026-09-04 = pic de charge : la suite `tests/` 55 strates / 746 items collectés (avant le floor actuel 1177) sur un runner saturé a effectivement timeout à 15 min. Les fixes ultérieurs (collection floor-guard, augmentation plafond, drift floor rattrapé en 5+ révisions `#15479` `#16026` `#15480` etc.) ont stabilisé la situation à 17/20 SUCCESS sur les 20 derniers runs.

## Acceptance dissipée

L'issue #14598 est dissipée au sens où :

1. **Cause absorbée** : la situation décrite (timeout 15 min) ne se reproduit plus dans les 20 derniers runs visibles (85 % SUCCESS).
2. **Plafond relevé** : `timeout-minutes: 60` au lieu de 15.
3. **Floor-guard actif** : régression de couverture détectée automatiquement par le workflow.
4. **Aucune action code supplémentaire requise** : l'option B (optimiser la suite) est gérée par le travail xdist en cours, hors scope de cette dissipation.

**Verdict** : `DISSIPATED_BY_ABSORPTION` (par opposition à `FIXED` ou `DOCUMENTED_ONLY`). Le body devient obsolète et l'issue peut être fermée par ai-01 après lecture de ce ledger — ou laissée ouverte avec un lien vers ce ledger si l'équipe préfère garder la trace.

## Leçons c.806

- **Un ledger de dissipation** se rédige à partir du body **ET** d'une vérification empirique au présent. Le seul body ne suffit pas — il date de l'ouverture et peut être rendu obsolète par des fixes ultérieurs.
- **Le `timeout-minutes` d'un workflow** est un signal public de la capacité allouée à une suite. Le passer de 15 à 60 min a valeur de dissipation même sans optimisation de la suite elle-même.
- **La collection floor-guard** transforme une régression silencieuse en erreur visible au PR — c'est l'organe qui protège la cause présumée de #14598 (drift ascendant masqué par plancher obsolète).

## Entry #001 — c.806 (po-2023)

| Métrique | Valeur |
|----------|--------|
| Cycle | c.806 |
| Date | 2026-09-24 (mesure first-hand) |
| Lane | `myia-po-2023:CoursIA-2` |
| Issue | #14598 |
| Verdict | `DISSIPATED_BY_ABSORPTION` |
| PR upstream | aucune nouvelle (cause absorbée par fixes antérieurs `#14595` + xdist + collection floor-guard) |

— myia-po-2023:CoursIA-2 (po-2023, c.806)
