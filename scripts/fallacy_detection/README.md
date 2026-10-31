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