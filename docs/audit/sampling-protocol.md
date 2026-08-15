# Protocole d'audit d'échantillonnage sémantique cross-famille

> **Statut.** Document de cadrage, grade **B-méthodologique** (protocole applicable, pas une simple suggestion).
> **Objet.** Répondre à l'acceptance d'[#8052](https://github.com/jsboige/CoursIA/issues/8052) — **protocole d'échantillonnage sémantique cross-famille** : (a) ≥5%/famille par cycle mensuel, (b) ré-exécution env-vierge (pas cache), (c) confrontation claims-du-markdown ↔ sorties réelles, (d) détection fallback silencieux (chemin dégradé au lieu de la vraie lib), (e) revue par humain/agent compétent dans le domaine.
> **Discipline.** NE remplace PAS les contrôles existants (`execution_count != null`, `validate_pr_notebooks.py`, anti-regression Lean) ; les **augmente** par une couche sémantique qui lit la relation narration↔sortie, pas la seule présence d'outputs. Cf incidents fondateurs documentés dans l'issue : **Sudoku réduit/non-réduit, Z3 20ms-vs-166ms, IIT MIP texte≠PyPhi, 8-reines diagonales absentes, fallback TenSEAL `ImportError`** — tous avaient survécu aux outputs + validation de structure + règles agentiques + labels `READY`/`PRODUCTION`.
> **Lien.** Issue-source : [#8052](https://github.com/jsboige/CoursIA/issues/8052) (parent #4208 EPIC open-courseware fiabilisé). Contribution partielle — l'epic reste ouverte. ICT déjà couvert par [#7734](https://github.com/jsboige/CoursIA/issues/7734) matrice de dissociations (instance scoping).

## Pourquoi ce protocole (≠ audit classique)

L'audit classique (cf [audit-reassessment.md](../../.claude/rules/audit-reassessment.md), protocol 4 étapes) vérifie **mécaniquement** qu'un notebook s'est exécuté (`execution_count == len(code)`, `errors == 0`). C'est un **plancher**, pas un **plafond** : il attrape les notebooks jamais exécutés, pas les notebooks dont l'exécution **ment**.

L'audit sémantique va plus loin : il confronte **ce que le markdown raconte** (titre, interpretation, conclusion, transition) à **ce que les outputs montrent réellement**. Le cas fondateur TenSEAL est paradigmatique : la cellule de code fait un `try: import tenseal except ImportError: ...` qui prend un chemin dégradé silencieux, l'output est *valide* (pas d'erreur), le markdown conclut "TenSEAL CKKS opérationnel" — mais le chiffrement homomorphe n'a jamais tourné. **Trois contrôles existants sont PASS, un claim faux est committé.**

## Sélection de l'échantillon (≥5%/famille)

### Définition de "famille"

Une famille = un sous-arbre `MyIA.AI.Notebooks/<Famille>/` (ex: `Probas/`, `Search/`, `IIT/`, `QuantConnect/projects/`, `GenAI/`, `SymbolicAI/`, `ML/`). Les sous-séries (ex: `Probas/Infer.NET`, `Probas/PyMC`) partagent le même audit-pattern.

### Critère de sélection (reproductible)

Pour chaque cycle mensuel :

1. **Énumérer** tous les notebooks de la famille (`find MyIA.AI.Notebooks/<Famille> -name "*.ipynb" -type f`).
2. **Stratifier** par sous-série pondérée par nombre de notebooks (≥5% par sous-série si ≥20 notebooks).
3. **Échantillonner** uniformément dans la liste (Python `random.sample` avec seed fixée `seed=42` + offset cycle pour reproductibilité inter-cycle mais varié intra-cycle).
4. **Marquer** les notebooks déjà audités dans les 90 derniers jours — `gh issue list --state all --search "<notebook>" --label audit-fallback-critical` + historique dashboard `[AUDIT-CYCLE]`. Ne pas ré-auditer sauf régression signalée.

### Volume cible

≥5% par famille avec **plancher absolu de 3 notebooks/famille/cycle** pour les petites familles (évite l'audit d'1 seul notebook sur une famille de 20 = sur-représentation).

## Grille de vérification claims↔outputs

### Les 5 litmus (à exécuter pour chaque notebook échantillonné)

| # | Litmus | Détection | Sortie |
|---|--------|-----------|--------|
| 1 | **Markdown claim numérique** vs **output réel** | `grep -nE '[Nn]ombre\|[Cc]hiffre\|résultat\|score\|accuracy\|%' <md_cells>` puis `grep <same_number> <output_cells>` | MATCH / MISMATCH documenté |
| 2 | **Fallback silencieux** (try/except ImportError) | `grep -nE 'try:\|except.*ImportError\|except.*Exception as.*pass\|except.*:'` dans code cells | Flag si exception broad swallow |
| 3 | **Verdict markdown positif** vs **exécution dégradée** | dernière cellule markdown `## Conclusion\|## Synthèse\|## Verdict` vs outputs précédents | Oui si claim positif alors que warnings/erreurs dans outputs |
| 4 | **SOTA tool vraiment invoqué** | imports réels dans cellules code vs mention dans markdown | Match import = vrai ; pas d'import alors que markdown mentionne l'outil = fallback |
| 5 | **Cohérence pédagogique** (exercice résolu ≠ marqué exercice, etc.) | cf [exercise-example-labeling.md](../../.claude/rules/exercise-example-labeling.md) | Stub cohérent avec titre |

### État de validation de la grille (après le pilote c.793)

Deux des cinq litmus n'ont **jamais tourné en conditions réelles**. Le savoir avant de lancer la grille évite de lire un silence comme un feu vert.

| Litmus | Statut | Détail |
|---|---|---|
| 1 — claim numérique | **validé** | extrait correctement, sous réserve du bruit de matching décrit ci-dessous |
| 2 — fallback silencieux | **implémenté, jamais déclenché** | `detect_fallback_silent` existe, mais l'échantillon pilote était .NET Interactive — le pattern `try/except ImportError` est Python. **À valider sur des notebooks Python** (ML.NET tutorials, Search Part1 Python). Tant que ce n'est pas fait, l'absence de finding litmus-2 ne prouve rien. |
| 3 — verdict positif markdown | **non déclenché** | absent de l'échantillon pilote |
| 4 — SOTA tool | **validé** | c'est ce litmus qui a produit le finding pilote `F-c793-1` (`pymc` mentionné, jamais importé) — la grille fonctionne |
| 5 — cohérence pédagogique | **non automatisable** | lecture cellule-par-cellule requise, hors périmètre du script |

### Limite connue du litmus 1 — `matched=0` est du bruit, pas un signal

`CLAIM_NUMERIC_RE` dans `scripts/audit/extract_claims_vs_outputs.py` attrape **tous** les nombres : `execution_count`, indices de liste, identifiants d'assets. Sur des notebooks riches en code, cela produit des `matched=0` massifs — mesuré sur le pilote : **0/319** et **0/242** claims appariés sur deux notebooks parfaitement sains.

**Ne pas lire un `matched=0` comme un finding.** C'est un défaut d'appariement, et l'interpréter comme un claim faux ferait conclure à une catastrophe là où il n'y a rien. Raffinement identifié, non implémenté : exclure les nombres < 10 (execution_count, indices) ou introduire une heuristique de contexte (`f"step {i}"` n'est pas un claim).

### Workflow d'audit (env-vierge)

```bash
# 1. Env vierge : pas de cache notebook, pas de state Jupyter persistant
jupyter kernelspec list  # confirmer kernel disponible
rm -rf ~/.local/share/jupyter/runtime  # reset state

# 2. Ré-exécution isolée : Papermill OU nbconvert --execute
papermill <notebook>.ipynb /tmp/audit_<famille>_<cycle>_<notebook>.ipynb \
    --cwd <famille_dir> --log-level INFO

# 3. Extraction outputs pour confrontation
python scripts/audit/extract_claims_vs_outputs.py <notebook>.ipynb

# 4. Revue domaine-compétent : agent/ML compétent OU humain PO
# (litmus anti-LIGHT : pas "j'ai lu le notebook", mais "j'ai vérifié chaque output
#  contre chaque claim numérique")
```

## Détection de fallback silencieux (litmus dédié)

Pattern dangereux à détecter systématiquement :

```python
try:
    from real_library import RealSolver
    solver = RealSolver()
except ImportError:
    solver = NaiveFallback()  # ← fallback silencieux, OK apparent
```

**Litmus** : `grep -nE 'except.*ImportError\|except.*:.*pass\|except.*Exception' <notebook>` + lecture des lignes qui suivent l'except. Si une variable d'état (`solver`, `model`, `result`) est réassignée à un substitut trivial **sans le mentionner explicitement dans le markdown**, c'est un fallback silencieux. À reporter avec un diff cell-par-cell.

## Format de finding (tag notebook + dashboard)

Chaque finding audit suit ce schéma (compatible avec le détecteur de dette structurelle) :

```yaml
notebook: <path/to/notebook.ipynb>
cycle: <cycle_id>  # ex: c.793, c.800, ...
family: <famille>
litmus_failed: <1..5>  # cf grille
claim_markdown: "<extrait verbatim du markdown>"
output_reality: "<extrait verbatim de l'output>"
severity: <CRITICAL|MAJOR|MINOR>  # CRITICAL = faux claim factuel ; MAJOR = claim exagéré ; MINOR = imprécision
fallback_detected: <bool>
fix_proposed: <PR #X ou "tracker #Y">
```

**Où va un finding.** Findings CRITICAL/MAJOR → **une issue GitHub** (label `audit-fallback-critical` pour les CRITICAL), une par finding actionnable, avec le bloc YAML ci-dessus dans le body. Findings MINOR → agrégés dans **un post dashboard** `[AUDIT-CYCLE]`. Dans les deux cas, la sortie de l'audit est un **verdict** — jamais un fichier de rapport committé dans l'arbre (cf § suivant).

## Application pilote (cycles c.793+)

### Familles pilotes (scope ce cycle)

Pour respecter le scope po-2025 (partition Probas/ML/Sudoku) ET le scope cross-famille (sans déborder hors-ligne), 2 familles pilotes :

- **Probas** : candidats = notebooks DecInfer (cf c.728y+ batch), ICT-related ProbBayesian. Litmus critique = `Probas/Infer.NET/*` vs `Probas/PyMC/*` jumeaux parité (cross-langage Python↔C#).
- **ML** : candidats = notebooks ML.NET tutorials. Litmus critique = vrais modèles ML.NET vs fallback `sklearn` ou `numpy` (incident fondateur).

### Familles différées (cycles suivants)

- **Sudoku** : couverture exhaustive déjà forte (cf PR #5604 Sudoku-13 incident fondateur). Cycle ultérieur.
- **Search** : twin Python↔C# à auditer via grille parité (#8057).
- **QC** : tracker #7575 multi-tranches (cf c.799/c.800), audit = grille claims-vs-backtest-reality (Sharpe réel vs Sharpe annoncé).

### ICT out-of-scope

Déjà couvert par [#7734 matrice dissociations](https://github.com/jsboige/CoursIA/issues/7734) (instance scoping).

## Sortie attendue par cycle — un verdict, jamais un fichier de rapport

Pour chaque cycle mensuel audité :

- **1 post dashboard** `[AUDIT-CYCLE] <famille> — <N>/<N_total> findings — <severity breakdown>` : le compte-rendu de cycle, éphémère par nature (échantillon tiré, litmus déclenchés, suite envisagée).
- **1 issue GitHub par finding CRITICAL/MAJOR**, avec le bloc YAML du § « Format de finding ». C'est le seul support qui survit au cycle et qui se referme quand le fix est livré.
- **0 fichier de rapport committé dans l'arbre** — ni `docs/audit/history/<cycle>/…`, ni `AUDIT-*.md`, ni `*_audit_cNNNN.md`, où que ce soit dans le dépôt.
- **0 PR de fix automatique dans le même cycle** (audit = reportage, fix = cycle séparé, pour ne pas confondre les genres G-VAR-3).

### Pourquoi pas un fichier de rapport

C'est une règle HARD du dépôt, pas une préférence de style : [`audit-cross-source-distillation.md`](../../.claude/rules/audit-cross-source-distillation.md) — « Un audit produit un **verdict**, pas un fichier. Le compte-rendu va sur le **dashboard RooSync** (éphémère) ; un finding **actionnable** devient une **issue**. » Et `CLAUDE.md` §A : « GitHub = code, jamais de […] rapports d'audit dans le repo. » Incident fondateur : 18 rapports d'audit déposés dans l'arbre notebooks, retirés par [#8168](https://github.com/jsboige/CoursIA/pull/8168).

La raison de fond est opérationnelle, pas bureaucratique. Un rapport committé **fige un état daté** dans un arbre qui bouge : il périme en silence, personne ne le referme, et un finding qui y dort n'est réclamé par personne. Une issue, elle, a un état, un assignataire possible, et se ferme quand le fix est livré. Le cycle pilote c.793 en est la démonstration : son finding MAJOR `F-c793-1` est resté **non tracké pendant tout le temps où il vivait dans un fichier de rapport** — il n'a existé comme finding réclamable qu'une fois remonté sur [#8052](https://github.com/jsboige/CoursIA/issues/8052#issuecomment-5090493572).

**Conséquence sur la sélection.** L'étape 4 du § « Critère de sélection » — marquer les notebooks déjà audités — ne peut donc pas s'appuyer sur `git log` d'un dossier de rapports. Elle s'appuie sur les **issues d'audit** (`gh issue list --search "<notebook> label:audit-fallback-critical --state all"`) et sur l'historique dashboard.

## Ce que ce protocole n'est PAS

- **Pas un remplacement de `validate_pr_notebooks.py`** : ce dernier valide la structure (execution_count, outputs présents) ; ce protocole valide la **sémantique** (claims ↔ outputs).
- **Pas un audit Lean/sorry** : la dette `sorry` Lean a son propre audit ([anti-regression.md](../../.claude/rules/anti-regression.md) règle HARD).
- **Pas une chasse au typos** : c'est un audit **sémantique**, pas rédactionnel.
- **Pas un audit exhaustif** : c'est un échantillonnage ≥5%/famille/cycle — l'exhaustivité viendrait dans un second temps si la dette le justifie.
- **Pas une auto-validation** : la grille nécessite une revue par humain/agent compétent dans le domaine — un agent généraliste qui "lit" sans comprendre les grandeurs n'attrape pas un claim faux sur un résultat numérique.

## Repères vérifiables

- Issue-source : [#8052](https://github.com/jsboige/CoursIA/issues/8052) (P0, parent #4208).
- ICT instance scoping : [#7734](https://github.com/jsboige/CoursIA/issues/7734) (matrice dissociations).
- Audits existants à NE PAS dupliquer : `validate_pr_notebooks.py` (structure), `audit-reassessment.md` (mécanique), `anti-regression.md` (Lean).
- Grille parité jumeaux : [#8057](https://github.com/jsboige/CoursIA/issues/8057) (complémentaire — twin Python↔C#).
- Coût/ressource par notebook : [#8056](https://github.com/jsboige/CoursIA/issues/8056) (complémentaire — méta par notebook).
