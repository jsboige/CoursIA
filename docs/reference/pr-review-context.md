# PR Review Discipline — Contexte, incident, anti-patterns

Document de référence détaillant les seuils auto-loaded de [.claude/rules/pr-review-discipline.md](../../.claude/rules/pr-review-discipline.md).

## Contexte (incident 2026-05-08)

Règle créée 2026-05-08 après constat user "vous êtes tous trop complaisants, on n'avance pas". Audit cycles 5-7 :
- 9/10 PRs nuit du 7→8 APPROVED par clusterManager-Myia sans contestation
- #801 mega-composite 7183 lignes / 41 files
- #806 +2 lignes
- #807 +46 lignes doc
- #791 du 7/05 +3561/-3543 prover refactor caché derrière "shapley sorry 2→1"

Cette rule s'applique à **tous les reviewers**, humains et bots (clusterManager-Myia, jsboige self-bot, ai-01 coordinateur).

## Anti-pattern : APPROVED en lot batch

Si un reviewer APPROVE >3 PRs dans une fenêtre <10 minutes : flag automatique, probable rubber-stamp.

## Mention explicite des bots

**@clusterManager-Myia** : ces critères s'appliquent en priorité. Première ligne de défense. Si APPROVE une PR violant un des critères, le coordinateur ai-01 conteste explicitement et la PR est bloquée jusqu'au split / fix.

**@jsboige (self-review bot)** : self-approval sans valeur GitHub. Reste en COMMENTED + signale les violations dans le body.

## Workflow ai-01 (coordinateur)

Avant tout merge cascade, ai-01 lit :
1. `gh pr view <N> --json files,additions,deletions,body,reviews` (pas juste `mergeStateStatus`)
2. Vérifie chacun des critères A-G applicables (cf rule)
3. Si violation : commente sur la PR (`gh pr comment <N>`) avec demande explicite (split, multi-seed, sorry-count, etc.) + ne merge pas
4. Si conforme : merge avec mention dans le bilan dashboard

Pas de merge en parallèle 5 PRs sans avoir lu les 5 bodies.

## Détails par critère

### Critère D : preuve d'exécution notebook
- Pas de validation visuelle (PPTX/Slidev) jamais "OK" sur "j'ai screenshotté". Liens vers screenshots obligatoires.
- Sortie `papermill` ou kernel exec — pas juste "Papermill SUCCESS" en mot-clé, coller les premières lignes des outputs.

### Critère E : anti-pattern visé
PRs micro qui inflate le compteur "PRs livrées" sans valeur réelle (#806 +2 lignes, #807 +46 lignes doc seul). Doc/README/CLAUDE.md/rules :
- Single PR < 50 lignes : refuser, exiger groupement avec autre PR du même cycle
- Single PR < 20 lignes : refuser systématiquement (commit direct sur main si trivial)
- Multiple READMEs touchés sans cohérence cross-series : refuser, exiger un seul focus

### Liens internes

- Criteres multi-seed (ML) : cf [.claude/rules/pr-review-discipline.md](../../.claude/rules/pr-review-discipline.md) section C
- Bot reviews pour dispatch : cf [.claude/rules/pr-review-discipline.md](../../.claude/rules/pr-review-discipline.md) section G
- Review state filter : cf [.claude/rules/verify-before-claiming.md](../../.claude/rules/verify-before-claiming.md)
- [.claude/rules/anti-regression.md](../../.claude/rules/anti-regression.md)
- CLAUDE.md section B (Reviews PR 5 points obligatoires)

---

## Incidents fondateurs des critères A-H

Détail déporté de [`.claude/rules/pr-review-discipline.md`](../../.claude/rules/pr-review-discipline.md).

### B.3 — le gate `proof-integrity` était structurellement aveugle au `native_decide` (corrigé #8740, issue #8738)

Le parser lisait la sortie de `#print axioms` **ligne par ligne**. Les noms d'axiomes natifs (`<theoreme>._native.native_decide.ax_1_1`, ~58 caractères) débordent la largeur de pretty-print de Lean et forcent un retour à la ligne — la déclaration entière était alors **silencieusement ignorée**.

Le gate était donc aveugle à la classe **exactement la plus dangereuse** : `native_decide` réduit par le noyau natif *sans preuve*, ce qui vide le théorème de son contenu tout en affichant un vert. **Conséquence de review : un `proof-integrity SUCCESS` daté d'avant le 2026-07-28 ne prouve rien sur `native_decide`** — ne pas l'accepter comme preuve.

Reproduction locale du check :

```bash
cd agent_tests/
python -c "from lean_server import LeanVerifier; print(LeanVerifier('<lake-root>').check_axioms('<Module>', fail_on_sorry=True))"
```

### B.3 — pourquoi la whitelist interdit les wildcards

`allow-axioms` liste les axiomes tolérés **un par un**. C'est un mécanisme à cliquet : tout nouveau `native_decide` introduit produit un nom **absent de la liste**, donc le gate rougit. Un motif générique (`*native_decide*`) détruirait cette propriété — le gate ne pourrait plus jamais rougir sur la classe qu'il est censé attraper, et un gate qui ne peut plus rougir n'est pas un gate.

### C — les deux contre-exemples ML inscrits (σ sans DM, et DM sur une perte symétrique)

**(1) `edge_sigma` seul ne prouve rien.** `edge_sigma = +19.97σ` avec `DM p = 0.236` n'est **pas** un BEATS (`validate_xrp_dt_holdout.py`, holdout_fresh du 06/08). Le dénominateur de `edge_sigma` mesure la dispersion **inter-seeds** — c'est-à-dire la *reproductibilité de la procédure*, pas la *significativité de l'edge*. σ croît donc sans borne quand les seeds s'accordent, que l'edge soit réel ou non. Un σ élevé sans DM est un flag « noise », jamais une preuve.

**(2) Le test DM doit porter sur une perte qui préserve le signe.** `mse` et `mae` sont **symétriques** (`(-e)² = e²`, `|-e| = |e|`) : elles rendent des `dm_stat` / `p_value` **bit-identiques** pour une série et son exact opposé — un test incapable de distinguer un modèle gagnant de son inverse ne teste rien.

Mesure d'intégration (#10232), série gagnante `e` vs son opposé `-e` contre baseline nulle :

| `loss_fn` | `dm_stat` pour `e` | `dm_stat` pour `-e` | Discriminant ? |
|---|---|---|---|
| `mse` | 10.0754 | 10.0754 | **non** |
| `linear` | −0.1771 | +0.1771 | **oui** (signes opposés) |

D'où l'exigence `loss_fn="linear"` dans `scripts/dm_test.py` (additif à `mse`/`mae`). Pin de régression : `test_dm.py::test_linear_loss_distinguishes_opposite_series`.

### D.5 — #8479 MusicGen : l'alignement qui enshrine un nombre périssable

Notebook MusicGen 02-3 : le RTF documenté `0.5-2x` a été « aligné » en `0.21-0.24x` **sur un run non-optimisé**, alors qu'une re-exécution Stop-&-Repair était **déjà due** sur ce notebook (cellule cassée).

Deux fautes cumulées : (a) la valeur ré-alignée est un **nombre de perf** sur un notebook **re-exécutable localement** — elle devait venir d'une re-exec fraîche, pas d'un markdown-align sur l'ancien output ; (b) une re-exec étant déjà due, l'alignement devait y être **foldé**, pas livré en PR markdown séparée. Enshriner un nombre qui changera au prochain passage kernel *est* la dérive que C.4 interdit.

### D — #5214 : l'advisory .NET lu comme un permis d'outputs vides

PRs Tweety-3 C# (#5194 / #5199 / #5202) mergées avec des notebooks à `execution_count: null` **et** `outputs: []`, au motif de l'advisory .NET.

L'advisory dit que la **CI** ne peut pas Papermill-exécuter du .NET Interactive (pas de kernel en CI). Il ne dit rien sur l'exécution **locale**, qui est disponible sur chaque worker (`dotnet-interactive`, règle F). Une cellule .NET committée doit donc porter `execution_count != null` = preuve d'exécution locale. `scripts/notebook_tools/validate_pr_notebooks.py` FAIL désormais dessus (verdict H.5 `STRUCTURAL_ONLY`), et ne tolère `null` que là où l'exécution locale est réellement impossible : QC Cloud (besoin QuantBook), Lean (advisory propre).

### E — #5345 Probas : l'intro corrigée, la liste laissée périmée

Plainte user 2026-07-04. La PR corrigeait l'intro et les compteurs d'un README de série tout en laissant, cent lignes plus bas, une **liste de notebooks PyMC obsolète** et un **arbre de structure périmé**.

D'où la clause « audit fichier ENTIER » : le format slim `+5/−5` du rollout README ne dispense pas de l'audit — il le **plafonne à tort**. Quand une série a subi un changement structurel, la passe DOIT être fichier-entier.

Audit associé au même mandat : Tweety / GameTheory / Search = **stale-body sévère** ; SymbolicLearning / SemanticWeb / SmartContracts = ciblé ; Sudoku = trivial.
