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