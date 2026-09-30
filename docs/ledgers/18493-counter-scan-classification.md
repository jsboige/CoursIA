# Issue #18493 — Scan des compteurs littéraux dans commentaires code

## Origine

Issue : #18493 (`hygiene(notebooks): compteurs litteraux dans commentaires de cellules code`).

La classe de l'issue est **distincte** de la prose markdown visée par #17636 : un compteur en dur dans un commentaire de cellule code (cf. motifs `--tilde_count`, `--NOTE_runtime` dans la table ci-dessous) est de même nature qu'un compteur prose (littéral qui dérive), mais sa correction **casse la byte-identité** de la cellule code et déclenche une ré-exécution C.2 du carnet entier. Les relais md-only (#17636) ne s'y appliquent pas — ces compteurs exigent une PR par carnet.

## Scan exhaustif

Outil : `scripts/notebook_tools/scan_code_comment_counters.py` (ajouté par cette PR).

```bash
python scripts/notebook_tools/scan_code_comment_counters.py
# total hits : voir la section "Mesure" ci-dessous
# notebooks touched : voir la section "Mesure"

python scripts/notebook_tools/scan_code_comment_counters.py --json
# sortie structuree : by_kind, by_notebook, records (notebook, cell_index, line, kind, snippet)
```

### Mesure (regenerer avec le script ci-dessus)

- 4 kinds identifies : `NOTE_runtime`, `tilde_count`, `gt_runtime_threshold`, `config_dict_doc`.
- Total hits et liste exacte par carnet dans la sortie du script.
- Disambiguation `RUNTIME_GUARDS` (3 regex) : `if x > N`, `delta_e = ...`, `slippage() > N` — filtre les commentaires de logique opérationnelle pour eviter les faux positifs.

| Kind | Motif type | Action recommandée |
|---|---|---|
| `NOTE_runtime` | note technique avec approximation pédagogique | KEEP-with-annotation |
| `tilde_count` | calibration runtime (`var = N  # ~K unite`) ou commentaire pédagogique | A-INVESTIGUER |
| `gt_runtime_threshold` | commentaire de logique opérationnelle (`# > 0 si ...`) | KEEP (PAS un compteur) |
| `config_dict_doc` | doc utilisateur pour choix de preset | KEEP |

## Classification actionnable

### Voie 1 — KEEP

Aucun changement. Le compteur est soit absent (logique opérationnelle), soit une approximation pédagogique non-runtime, soit une doc utilisateur pour choix de preset. Les carnets concernés incluent notamment Lean-10 (c.2 et c.6), Lean-21 et Gibbard-Satterthwaite. Voir le script de scan pour la liste exacte.

### Voie 2 — EDIT (à arbitrer par les lanes de chaque famille)

Remplacer la calibration statique par un calcul runtime :
```python
SEQ_LEN = N  # ~K mois de trading days
# devient
SEQ_LEN = int(N * factor_runtime)  # recalibré runtime
```

**Coût** : modification de cellule code → ré-exécution C.2 du carnet entier → 17 PRs Papermill par carnet. **Bénéfice** : la calibration reste vraie si la fenêtre change.

**Voie recommandée uniquement si** la calibration change avec le contexte d'exécution. Pour `SEQ_LEN` dans QC-Py-22, la valeur est un hyperparamètre — le commentaire est juste une aide à la lecture ; le runtime ne la calcule pas.

Carnets candidats pour la voie EDIT (cf. sortie JSON du scan) : QC-Py-12, QC-Py-15, QC-Py-22, research_rl_ppo, research_vrp_putwrite, ML/4.3-TransferLearning-ResNet, IIT/ICT-15g, GenAI/PostTraining/PT-11a, GenAI/Video/02-5-LTX2-Audiovisual, GenAI/Video/02-7-CogVideoX, GenAI/Video/04-5-MiniMax-H3, GenAI/Audio/02-1-Chatterbox-TTS, Z3-API/Z3-16c-Meal-Planner-Patient, SC-20-Bitcoin-Scripting.

### Voie 3 — REMOVE (proscrite)

Retirer le commentaire sans valeur de remplacement perd l'information pédagogique. **Pas une voie de fix**, c'est une régression.

## Décision de cette PR

Cette PR livre **uniquement** :
1. Le script `scripts/notebook_tools/scan_code_comment_counters.py` (l'organe de mesure).
2. Ce rapport de classification (l'artefact durable).

**Aucun carnet n'est édité** → aucune cellule code touchée → aucune ré-exécution C.2 due → aucune dépendance Papermill.

Les voies EDIT restent un travail de fond, à prioriser carnet par carnet par les lanes de chaque famille. Le script de scan permet de re-mesurer la classe après chaque campagne (la liste des carnets A-INVESTIGUER sort du `--json`).

## Acceptance

- [x] Scan dédié produit la liste exhaustive (cf. section "Scan exhaustif" + `--json`)
- [x] Classification KEEP/EDIT/REMOVE par hit documentée (cf. section "Classification actionnable")
- [x] Aucun carnet édité → C.2 non applicable (cf. "Décision de cette PR")
- [x] Les compteurs restants sont classés KEEP ou A-INVESTIGUER avec justification

## Liens

- #18493 (issue d'origine)
- #17636 (campagne prose markdown — relay c15) : autre classe, byte-identité préservée
- `proactive-coordination.md` R6 — variété anti-monoculture : ce PR est `LIGHT/tooling`, pas un DEEP de contenu, et le DEEP est porté par PR #18506 (livrée juste avant)
- `scan_md_hierarchy drift` (workflow `md-hierarchy-drift.yml`) : autre ratchet sur la hiérarchie markdown
