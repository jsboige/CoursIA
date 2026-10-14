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

---

## Reprise du 2026-10-10 — adjudication complete (lane `myia-ai-01:CoursIA-2`)

**Ce que cette section corrige.** La « Classification actionnable » ci-dessus laisse une part
des hits en **A-INVESTIGUER**. Or l'acceptance de l'issue n'admet que **trois** sorties : un
compteur est *retire* (predicat garde), *ancre sur une sortie commise*, ou *classe KEEP avec
justification*. « A-INVESTIGUER » n'en est aucune des trois — et la case cochee en bas de page
reformule la troisieme sortie de l'issue (« KEEP ou A-INVESTIGUER »), ce que l'issue ne dit pas.
La classe n'etait donc pas livree.

**La classe croit, elle ne s'epuise pas.** Re-mesuree le 2026-10-10 sur `origin/main`, la sortie
de `scan_code_comment_counters.py --json` rend une liste **plus longue** que celle du 2026-09-30
(le compte exact est dans la sortie du script, pas recopie ici — il derive). Une classe vivante
ne se solde pas par une campagne unique.

### Ce que les hits sont reellement

| Famille | Compte | Le litteral peut-il deriver faux ? |
|---|---:|---|
| Equivalence unitaire definitionnelle (`n_days = 504  # ~2 ans de trading`) | 13 | **non** — conversion exacte d'une constante du code (jours ouvres par an, kJ/kcal, minutes par bloc) |
| Auto-documente (le chiffre du commentaire est celui de la ligne de code) | 4 | non |
| Logique operationnelle (`gain = a - b  # > 0 si ...`) | 2 | non — ce n'est pas un compteur : **faux positif de l'organe** |
| Mesure d'horloge datee (`# ~15 min sur RTX 3070`) | 2 | oui, mais c'est la classe perf-prose (#8052), pas celle-ci |
| Doc de preset, borne unilaterale (`>100k theoremes`) | 1 | **non** — une borne unilaterale sur une quantite qui ne decroit pas ne peut pas devenir fausse |
| **Compteur d'artefact derivant** | **1** | **oui** |

**Sur cette mesure, un seul hit porte un compteur d'artefact derivant.** Le kind `tilde_count`
melange deux choses que l'organe ne separe pas : une **equivalence** (le commentaire explique le
code et ne peut pas deriver) et une **affirmation sur le monde** (le commentaire compte un
artefact et derive). C'est cette confusion, et non la prose, qui explique qu'une classe de cette
taille n'ait qu'un cas reel. **Corollaire : l'organe ne peut pas etre cable tel quel** — il
rougirait sur des equivalences correctes partout dans le depot.

### Adjudication, hit par hit

| Carnet | Cellule | Ligne | Kind | Verdict | Justification |
|---|---:|---:|---|---|---|
| `05-Gibbard-Satterthwaite.ipynb` | c9 | 27 | `gt_runtime_threshold` | **KEEP** | logique operationnelle (`> 0 si ...`), pas un compteur -- faux positif de l'organe |
| `02-1-Chatterbox-TTS.ipynb` | c16 | 21 | `tilde_count` | **KEEP** | auto-documente : le chiffre du commentaire est celui de la ligne de code, ou une taille de telechargement stable |
| `02-1-Chatterbox-TTS.ipynb` | c16 | 22 | `tilde_count` | **KEEP** | auto-documente : le chiffre du commentaire est celui de la ligne de code, ou une taille de telechargement stable |
| `PT_11a_grpo_qwen35_rlvr.ipynb` | c14 | 3 | `tilde_count` | **KEEP** | mesure d'horloge datee (materiel precis) -- releve, pas un compteur d'artefact ; appartient a la classe perf-prose #8052 |
| `02-5-LTX2-Audiovisual.ipynb` | c13 | 6 | `tilde_count` | **KEEP** | mesure d'horloge datee (materiel precis) -- releve, pas un compteur d'artefact ; appartient a la classe perf-prose #8052 |
| `02-7-CogVideoX-Text-to-Video.ipynb` | c1 | 15 | `tilde_count` | **KEEP** | equivalence unitaire definitionnelle : conversion exacte d'une constante du code (252 jours ouvres/an, 4,184 kJ/kcal, 10 min/bloc) -- ne derive pas |
| `04-5-MiniMax-H3-Cloud-Video.ipynb` | c4 | 181 | `tilde_count` | **KEEP** | equivalence unitaire definitionnelle : conversion exacte d'une constante du code (252 jours ouvres/an, 4,184 kJ/kcal, 10 min/bloc) -- ne derive pas |
| `ICT-15g-EmpiricalHuangExploitation-Python.ipynb` | c20 | 27 | `tilde_count` | **KEEP** | auto-documente : le chiffre du commentaire est celui de la ligne de code, ou une taille de telechargement stable |
| `4.3-TransferLearning-ResNet.ipynb` | c11 | 1 | `tilde_count` | **KEEP** | auto-documente : le chiffre du commentaire est celui de la ligne de code, ou une taille de telechargement stable |
| `QC-Py-12-Backtesting-Analysis.ipynb` | c9 | 3 | `tilde_count` | **KEEP** | equivalence unitaire definitionnelle : conversion exacte d'une constante du code (252 jours ouvres/an, 4,184 kJ/kcal, 10 min/bloc) -- ne derive pas |
| `QC-Py-15-Parameter-Optimization.ipynb` | c46 | 3 | `tilde_count` | **KEEP** | equivalence unitaire definitionnelle : conversion exacte d'une constante du code (252 jours ouvres/an, 4,184 kJ/kcal, 10 min/bloc) -- ne derive pas |
| `QC-Py-22-Deep-Learning-LSTM.ipynb` | c19 | 4 | `tilde_count` | **KEEP** | equivalence unitaire definitionnelle : conversion exacte d'une constante du code (252 jours ouvres/an, 4,184 kJ/kcal, 10 min/bloc) -- ne derive pas |
| `QC-Py-22-Deep-Learning-LSTM.ipynb` | c19 | 5 | `tilde_count` | **KEEP** | equivalence unitaire definitionnelle : conversion exacte d'une constante du code (252 jours ouvres/an, 4,184 kJ/kcal, 10 min/bloc) -- ne derive pas |
| `QC-Py-28c-Factor-Preprocessing-Regime.ipynb` | c3 | 20 | `tilde_count` | **KEEP** | equivalence unitaire definitionnelle : conversion exacte d'une constante du code (252 jours ouvres/an, 4,184 kJ/kcal, 10 min/bloc) -- ne derive pas |
| `research.ipynb` | c1 | 8 | `tilde_count` | **KEEP** | equivalence unitaire definitionnelle : conversion exacte d'une constante du code (252 jours ouvres/an, 4,184 kJ/kcal, 10 min/bloc) -- ne derive pas |
| `research_rl_ppo.ipynb` | c3 | 17 | `tilde_count` | **KEEP** | equivalence unitaire definitionnelle : conversion exacte d'une constante du code (252 jours ouvres/an, 4,184 kJ/kcal, 10 min/bloc) -- ne derive pas |
| `research_vrp_putwrite.ipynb` | c7 | 21 | `tilde_count` | **KEEP** | equivalence unitaire definitionnelle : conversion exacte d'une constante du code (252 jours ouvres/an, 4,184 kJ/kcal, 10 min/bloc) -- ne derive pas |
| `Lean-10-LeanDojo.ipynb` | c2 | 22 | `config_dict_doc` | **KEEP** | borne unilaterale (`>100k`) sur une quantite qui ne decroit pas -- ne peut pas deriver faux ; doc de chois de preset |
| `Lean-10-LeanDojo.ipynb` | c6 | 6 | `NOTE_runtime` | **EDIT** | litteral non derivable d'une mesure du carnet -- retire, mecanisme conserve |
| `Lean-21-MIMO-Detection-Flips.ipynb` | c3 | 27 | `gt_runtime_threshold` | **KEEP** | logique operationnelle (`> 0 si ...`), pas un compteur -- faux positif de l'organe |
| `Z3-16c-Meal-Planner-Patient-Capstone-Python.ipynb` | c14 | 2 | `tilde_count` | **KEEP** | equivalence unitaire definitionnelle : conversion exacte d'une constante du code (252 jours ouvres/an, 4,184 kJ/kcal, 10 min/bloc) -- ne derive pas |
| `Z3-16c-Meal-Planner-Patient-Capstone-Python.ipynb` | c14 | 3 | `tilde_count` | **KEEP** | equivalence unitaire definitionnelle : conversion exacte d'une constante du code (252 jours ouvres/an, 4,184 kJ/kcal, 10 min/bloc) -- ne derive pas |
| `SC-20-Bitcoin-Scripting-Python.ipynb` | c27 | 24 | `tilde_count` | **KEEP** | equivalence unitaire definitionnelle : conversion exacte d'une constante du code (252 jours ouvres/an, 4,184 kJ/kcal, 10 min/bloc) -- ne derive pas |

### Le hit nomme par l'issue : `Lean-10-LeanDojo.ipynb` c.6 — corrige

Le litteral du commentaire n'est derivable **d'aucune mesure que le carnet committe**. Mesure
firsthand du 2026-10-10, sur le toolchain que le carnet epingle (`leanprover--lean4---v4.11.0`) :

| Ce qui est mesure | Valeur |
|---|---:|
| Sources `.lean` presentes dans `src/lean/` du toolchain epingle | `1074` |
| Ce que le commentaire annoncait | `~1500` |

Correction retenue — **premiere sortie de l'acceptance** (retire, mecanisme conserve) : le nombre
part, le mecanisme qui porte la pedagogie reste (la stdlib est embarquee dans tout depot Lean 4,
donc `user_files_only` filtre *apres* le tracing). Aucune valeur de remplacement n'est inventee :
un chiffre re-mesure a la main serait un nouveau litteral, derivant de la meme facon.

Le carnet a ete **re-execute Papermill end-to-end** avant commit (C.2) — kernel `Python 3 (WSL)`,
`lean_dojo 2.2.0`, cache `yangky11-lean4-example` present. Verifications sur la sortie :
`execution_count` 1..26 contigus, aucune cellule en erreur, aucun avertissement nouveau, aucune
sortie en effondrement par rapport a `HEAD`, aucun chemin machine dans les sorties.

### Ce que cette reprise ne fait pas

- **Elle ne cable pas le CI.** Aucun des deux scanners de la classe n'est declare dans
  `.github/` ni dans `.pre-commit-config.yaml` : rien ne peut rougir aujourd'hui. La raison est
  ci-dessus (precision insuffisante), pas l'oubli.
- **Elle ne fusionne pas les deux organes.** `scan_code_comment_counters.py` et
  `scan_code_cell_counters.py` occupent la meme classe, et leurs verdicts divergent au meme
  instant (l'un rend l'ensemble en KEEP, l'autre en partage KEEP / A-INVESTIGUER). Le constat est
  ecrit, la fusion n'est pas faite — elle appartient a une PR dediee.
- **Elle ne touche pas les mesures d'horloge** (`PT_11a`, `02-5-LTX2`) : elles relevent de #8052,
  ou elles se traitent avec les autres nombres de performance, pas ici.

### Acceptance, apres cette reprise

- [x] Scan dedie produit la liste exhaustive — `scan_code_comment_counters.py --json`
- [x] Chaque carnet edite est re-execute Papermill end-to-end avant commit — `Lean-10-LeanDojo.ipynb`, C.2 ci-dessus
- [x] Les compteurs restants sont retires, ancres, ou classes KEEP avec justification — table d'adjudication ci-dessus, **aucun hit laisse en A-INVESTIGUER**
