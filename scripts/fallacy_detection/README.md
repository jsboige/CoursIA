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

## Split « nœud tenu à part » : mesurer un sophisme inédit, pas un décor inédit

`build_heldout_node_split.py` construit la variante du corpus dans laquelle un
ensemble de nœuds est **retiré du train et du val** et **conservé au test** —
seule configuration où le test porte un sophisme que le train n'a jamais vu.

La prémisse est mesurée sur l'inventaire committé (`data/phase2/`) : les
**1407 nœuds** sont présents dans **train, val et test** (1407/1407 dans les
trois, 0 nœud du val absent du train), support train 6-22, support test 2 ou 4.
Le gate mesure donc aujourd'hui des décors inédits sur des étiquettes connues
(section 2 de la revue EPITA du 2026-10-21/22, « un nœud tenu à part »).

Mesure du 2026-11-16 (`--holdout-count 222`, données locales, rapport seul) :

| Stratégie | Nœuds | Paires test tenues à part | Support test / nœud | Familles couvertes |
|---|---:|---:|---|---|
| `top-support` | 222 | **888** (222 × 4) | 4 partout | **7/7 vertus uniquement** |
| `seeded --seed 42` | 222 | **530** | 2 (179 nœuds) ou 4 (43) | 12 familles, sophismes et vertus |

**Le choix de la stratégie n'est pas neutre.** Le budget du builder
(12 000 sophismes / 2 000 vertus) donne 4 paires de test aux nœuds de vertu et
2 aux sophismes : `top-support` sélectionne donc **exactement les 222 nœuds de
vertu**, ce qui confond « nœud inédit » et « polarité vertu ». `seeded` mélange
les deux polarités, mais fait tomber le support moyen du lot tenu à part à
2,4 paires par nœud.

**Ce que le split ne répare pas** (section 3 de la même revue) : tenue à part
ou non, aucune configuration ne porte le support par nœud au-dessus de 4
paires — le plancher de support du niveau nœud vient de `test_per_node = 2` au
manifeste, pas du choix des nœuds. Relever ce plancher est un arbitrage de
protocole (`--holdout-count`, `--min-test-pairs`), que l'organe expose sans le
trancher.

Sorties : les splits filtrés vont **hors dépôt** (`--out-dir` ; `train.csv` est
gitignoré par politique d'artefacts, un split dérivé l'est aussi) ; seul le
rapport agrégé (`--report`) est citable.
