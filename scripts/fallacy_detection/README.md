# fallacy_detection — scripts d'exécution

Ce dossier porte le générateur de corpus `generate_teacher_corpus.py` et les
deux wrappers qui le lancent en tâche détachée, un par famille d'OS.

| Script | Plateforme | Usage |
|---|---|---|
| `run_teacher_volume.ps1` | Windows (PowerShell 5.1) | tâche planifiée `CoursIA-po2027-teacher-volume` |
| `run_teacher_volume.sh` | POSIX (bash) | `cron` / `systemd --user`, jumeau du précédent |

Les deux wrappers partagent la même logique : lecture de la clé
`VLLM_API_KEY_MEDIUM` dans `.secrets/master.env` (la valeur n'est jamais
écrite ni échoée), pré-flight TCP de 5 s vers le hub avant tout lancement,
puis appel de `python -m fallacy_detection.generate_teacher_corpus` avec
reprise par checkpoint. Codes de sortie identiques : `1` = clé absente,
`2` = hub injoignable (génération non lancée, aucun checkpoint touché),
autre = code du générateur.

Les chemins sont paramétrables (`-RepoRoot`/`--repo-root`, et ainsi de
suite) pour qu'une tâche planifiée puisse pointer le `.secrets` du clone
principal depuis un worktree. `--help` liste les options du wrapper POSIX.

## Contrôle aller-retour : deux régimes, deux significations

`generate_teacher_corpus.py` valide chaque texte généré par un contrôle
aller-retour : le modèle doit retrouver le nœud cible parmi des distracteurs.
La mesure deux-taux du 2026-10-23
([docs/transients/2026-10-23-17578-hard-distractors-measurement.md](../../docs/transients/2026-10-23-17578-hard-distractors-measurement.md),
`--split val --limit 40 --votes 3 --seed 7`) sépare ce que chaque régime
mesure — et ce qu'il ne mesure pas :

| Régime | Taux mesuré | Ce qu'il établit |
|---|---:|---|
| Distracteurs aléatoires (tirage par défaut) | 87,5 % (35/40) | le texte est plus proche de son nœud que de 5 nœuds pris au hasard — c'est tout |
| Distracteurs difficiles (`--hard-distractors`) | 47,5 % (19/40) | face aux pairs frères / parent / enfants / homonymes (`build_hard_peers`), le nœud n'est reconnu qu'une fois sur deux |

L'écart (40 points, McNemar exact p ≈ 1,4 × 10⁻⁴) est systématique par
famille : aucun des deux régimes ne se substitue à l'autre. Le tirage
aléatoire n'attrape un nœud difficile qu'avec ~2,8 % de chances par paire —
un score aléatoire élevé ne dit donc **rien** de la capacité du corpus à
séparer les nœuds fins de la taxonomie : la discrimination fine n'est pas
acquise au niveau de granularité visé. Toute évaluation de granularité doit
passer par `--hard-distractors` ; durcir le contrôle par défaut pour tout le
corpus reste un arbitrage ouvert (#17578).

## Rapport reconstruit depuis le checkpoint (`--report-only`)

Le rapport d'un run se recalcule **sans rappeler le maître** : le checkpoint
`<split>_<lang>.jsonl` enregistre par paire tout ce que `summarise` agrège. Le
mode `--report-only` relit ce checkpoint et le rapport qu'il a produit, rejoue
`summarise`, et réécrit le rapport en conservant tels quels les paramètres du
run et sa durée.

```bash
python -m fallacy_detection.generate_teacher_corpus \
    --out MyIA.AI.Notebooks/GenAI/FallacyDetection/data/teacher \
    --split val --lang fr --report-only
```

Ce que le checkpoint ne porte pas reste **absent**, et `report_provenance` le
nomme : l'historique de reprise (`resumed`, `n_resumed`, `n_todo`) n'est écrit
nulle part, une valeur inventée vaudrait moins qu'une absence nommée.

Le rapport `val`/`fr` committé datait d'avant le correctif de fidélité #20137 :
il ne publiait ni `n_generated` ni `n_below_floor`, et laissait donc croire que
tout texte généré respectait le plancher de `min_tokens`. Sa reconstruction
(2026-11-16) est **purement additive** — tous les chiffres déjà publiés sont
identiques, y compris l'auto-accord de 0,8679 (243/280) — et révèle **une paire
générée sous le plancher** sur 280, `val-V138-2.1.5`.

## Lot apparié : même scénario, même locuteur, avec et sans sophisme

La revue EPITA de la série relève que le corpus historique donne le rôle du
locuteur comme raccourci de classe : `smoothTalker` porte tous les sophismes,
`drawer` toutes les vertus. `paired_scenario_corpus.py` construit le lot
apparié demandé en retour :

- **bras positif** : le texte déjà validé du split `val` FR, provenance
  `generate_one(render_prompt)` conservée dans le rapport ;
- **bras négatif** : même scénario, même locuteur `smoothTalker`, même position
  défendue — seule la consigne change (`render_loyal_prompt`) : défense loyale,
  raisons vérifiables, limites reconnues ;
- **vérité-terrain du négatif mesurée, jamais supposée** : un vote de
  reclassement doit écarter le sophisme cible ; quand la taxonomie Argumentum
  déclare des vertus opposées au sophisme (`crossLink_Opposes`, cibles par PK),
  chaque vertu liée doit être retrouvée par un second vote. Vote muet, vote
  non parsé ou vertu manquante = paire **rejetée avec motif nommé** ;
- **raccourci de rôle coupé par construction et mesuré dans le rapport** : le
  rôle est constant dans chaque paire pendant que la polarité varie, donc il
  ne porte plus aucune information de classe.

Le lot publié (`paired_scenario_corpus.jsonl`, deux lignes par paire avec
`pair_group_id`) ne contient que les paires acceptées ; le rapport JSON
conserve toutes les tentatives, tous les votes et tous les motifs de rejet.
Le checkpoint est local et non committé ; `--report-only` reconstruit le
rapport sans clé ni réseau, depuis le checkpoint s'il existe, sinon depuis le
rapport publié. Le pont vertu-sophisme vient de la taxonomie elle-même, sans
approximation de titres : là où aucune vertu liée n'existe, cette absence est
publiée, jamais comblée.

```bash
python -m fallacy_detection.paired_scenario_corpus --limit 60
python -m fallacy_detection.paired_scenario_corpus --probe        # une paire, aucun corpus écrit
python -m fallacy_detection.paired_scenario_corpus --report-only  # sans clé, sans réseau
```
