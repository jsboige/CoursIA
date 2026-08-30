# Registre des attributions arXiv — convention et maintenance

Issue #12853 (acceptance 9.4), parent EPIC #11168 (vérification des citations arXiv). Ce document fixe la convention du registre `arxiv_attributions_registry.yaml` et son organe CI.

## Le problème traité

La classe de défaut « attribution arXiv fausse » (#11065 Sendov, #11110, #11127) : un notebook cite un papier arXiv avec une année, un venue ou un titre erroné (ex. GAE attribué ICLR 2016 au lieu d'arXiv 2015). Quatre passes correctives (2026-08, #12824/#12832/#12838) ont corrigé les drifts trouvés, mais un correctif ponctuel ne se maintient pas seul : les notebooks évoluent, et une cellule réécrite peut perdre la citation corrigée. Le registre rend chaque correction **vérifiable mécaniquement**.

## Les trois pièces

| Pièce | Rôle |
|---|---|
| `arxiv_attributions_registry.yaml` (racine) | Une entrée par correction appliquée : `arxiv_id`, `notebook`, `cell_index` (0-based), `expected_citation` (chaîne exacte), `source_pr`, `correction`, `date` |
| `scripts/check_arxiv_attributions.py` | Vérifie que chaque entrée vit encore : la chaîne `expected_citation` doit être trouvable dans la cellule `cell_index` du notebook. Modes : défaut (RENAMED toléré pour triage), `--strict` (rename = FAIL, mode CI), `--paths` (limite aux globs), `--json` |
| `.github/workflows/arxiv-attributions-guard.yml` | Gate bloquant per-PR (paths filtrés : registre, script, tests, workflow, notebooks enregistrés) + nocturne 03:47 UTC + dispatch |

## Convention d'ajout (HARD)

1. **Chaque entrée est extraite MÉCANIQUEMENT depuis le diff de la PR source** (`git diff origin/main...<branche>`) : chemin, `cell_index`, `expected_citation` lus depuis le diff réel — **jamais rédigés de mémoire**. Le registre v1 de 18 entrées avait été fabriqué de mémoire (16 notebooks inexistants — nit Hermes sur #12900, leçon c.542-L1) puis régénéré en 7 entrées valides (#12941).
2. Une correction d'attribution = **une entrée de registre dans la même PR**. Le gate tourne sur le registre (dans les paths du workflow) : la nouvelle entrée est vérifiée dès son arrivée.
3. Un notebook déplacé = mise à jour du champ `notebook` dans la même PR (`--strict` fait échouer le rename sinon — c'est voulu : le registre suit les déplacements).
4. La chaîne `expected_citation` doit être **stable et courte** : ancrez sur la portion de citation portant la correction (l'année arXiv, le titre court), pas sur une phrase entière qu'un enrichissement Markdown déplacerait.

## Ce que le gate attrape et n'attrape pas

- **Attrape** : citation corrigée supprimée ou réécrite (FAIL), notebook enregistré déplacé sans suivi de registre (RENAMED → FAIL en strict), régression d'attribution sur les entrées connues.
- **N'attrape pas** : les nouvelles citations erronées dans des familles non auditées (11 familles restent à couvrir, veine 3 de #12853) — c'est le travail des passes d'audit et de la veine 2 (re-sonde arXiv API, sub-grain séparé). Le registre est un ratchet, pas un auditeur.

## Ajouter un notebook au filtre du workflow

Le `paths:` du workflow énumère les notebooks enregistrés. Un ajout d'entrée sur un notebook pas encore listé = ajouter son chemin au `paths:` dans la même PR (le registre est déjà dans les paths, donc le gate tourne et couvre la nouvelle entrée même sans ce geste — le filtre n'est qu'une économie de runs ; le nocturne couvre le reste).

## Historique

- Passes 1-4 (2026-08) : 6 IDs corrigés sur 16 notebooks (#12824, #12832, #12838 + passe 4 no-op).
- #12900 (fermée) → registre régénéré mécaniquement #12941 ; le guard a attrapé son propre drift sur #13349 (`rl_6c` cell 27).
- Workflow + ce document : clôture acceptance 9.3/9.4 de #12853.
