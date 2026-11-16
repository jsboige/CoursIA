# Sous-archive root-campaigns-2026q3 — scripts de campagne retirés de la racine `scripts/`

Tranche **T3-b** de l'EPIC #25366 (sous-grain #26009, census T3-a). Ces scripts
restaient à la racine de `scripts/` sans aucun appelant opérationnel mesuré
(census #26009 : seuls leurs tests — depuis archivés avec eux — les mentionnaient),
pour des campagnes dont l'issue est **fermée** ou la PR **mergée**. Ils quittent la
racine pour respecter le plafond proposé (70 points d'entrée, #26009) ; git
history et l'issue citée restent la preuve de préservation.

Standard : [convention `_archive/`](../../../docs/reference/_archive-convention.md).

## Registre de disposition

| Script | Verdict | Superseded by | Verdict recorded in |
|--------|---------|---------------|---------------------|
| `rebaseline_twin_pairs_post_13606.py` | campagne post-merge #13606 (newline final) exécutée ; plus aucune paire à rebaseliner | rien — mission unique, `git log` du fichier conserve la dernière empreinte | PR #13606 (MERGED), issue #25366 |
| `variation_genre_recensement.py` | recensement initial G-VAR-2 livré (« le recensement est le livrable initial, pas l'organe ») | l'organe vivant `variation_light_cap.py` (calcul du budget, appelé par le picker) | #10290 (CLOSED) |
| `variation_volet_bc.py` | mesure ponctuelle volets B+C (fenêtre G-VAR-2, DWELL) rendue | `variation_light_cap.py` + `check_adjoint_prevalidation.py --queue` (`dwell_until`) | #14591 (CLOSED) |
| `remeasure_bad_pending.py` | re-mesure plateau acceptance #2 rendue (réutilise `pr_gate.classify()`, qui vit et reste la source) | `pr_gate.py` + `scripts/ci/pool_review_verdicts.py` | #12389 (CLOSED) |
| `ict_jlens_layers.py` | pilote J-Lens dose fixée du pilote de triangulation causale — étude conclue | l'étude publiée du pilote ; `scripts/repro/` pour toute reprise | #15480 (CLOSED) |
| `ict_pilot_transformer.py` | petit transformer hookable du même pilote — étude conclue | idem | #15480 (CLOSED) |
| `test_*.py` | tests des scripts ci-dessus, déplacés avec eux — hors `testpaths`, ils n'entrent plus dans la collecte pytest | couverture des successeurs cités | issue #25366 |

## Pourquoi `git mv` et pas suppression

Critère 5 de l'EPIC : aucune suppression sans preuve de préservation. Le
déplacement réversible vers `_archive/` (précédents #9535 items 4/4-bis/4-ter/4-quater,
#14251) satisfait le plafond de racine sans détruire rien ; la disposition ci-dessus
nomme le successeur de chaque script pour que la sous-archive reste un registre de
décisions, pas un puits de code mort.

Archivage : 2026-11-12, T3-b de #25366 (lane myia-po-2028:CoursIA).
