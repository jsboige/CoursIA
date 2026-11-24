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

## Accord inter-familles : un juge externe pour les étiquettes

L'auto-accord du générateur mesure la même famille de modèles qui a produit le
texte, avec la définition de l'étiquette visible dans la question : il ne peut
pas témoigner que l'étiquette survit à un changement de famille. La revue EPITA
du 2026-10-22 (c.6344505010, section 2a) demande donc un accord **inter-familles**
sur environ deux cents paires, avec intervalle de confiance.
`judge_family_agreement.py` mesure cet accord **sans rien générer** :

- tirage apparié à graine fixe sur le split `val` committé, stratifié
  proportionnellement par famille de taxonomie ;
- le même questionnaire de reclassement que le contrôle aller-retour
  (réutilisation de `pick_distractors`, `build_choice_question`, `parse_choice`
  depuis `generate_teacher_corpus` — cadre FR octet pour octet identique) ;
- des juges externes servis par endpoints compatibles OpenAI (catalogue
  `JUDGE_SPECS` : `openai`, `openrouter`), clés lues dans l'environnement
  (`OPENAI_API_KEY`, `OPENROUTER_API_KEY`), jamais en littéral ;
- le contraste gratuit : l'auto-accord du générateur **restreint au même
  sous-ensemble** se lit dans le champ `roundtrip` du corpus, sans aucun appel.

Une réponse non parsable est « non mesuré », jamais un vote raté. Chaque appel
s'écrit dans un checkpoint ligne à ligne : un run interrompu reprend à la paire
où il s'était arrêté. Le checkpoint est un artefact de run, non committé ;
`--report-only` le lit quand il est là (un run partiel ne s'efface jamais
derrière un rapport publié), et sinon le rapport committé, qui porte les mêmes
picks dans `per_pair` — la relecture marche donc aussi sur un clone frais, sans
clé et sans réseau. Le rapport pose le SHA-256 du corpus d'entrée ; le rendu
markdown porte celui du rapport JSON.

```bash
python -m fallacy_detection.judge_family_agreement --probe          # un appel par juge
python -m fallacy_detection.judge_family_agreement                  # mesure + rapport
python -m fallacy_detection.judge_family_agreement --report-only    # rapport depuis checkpoint
```

Ce que le taux **ne dit pas** : un juge externe bas ne désigne pas le coupable
(générateur ou juge), il dit que l'étiquette ne survit pas au changement de
famille — trancher exigerait la vérité-terrain humaine (#20222), pas un troisième
modèle.
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

