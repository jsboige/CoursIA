# Politique de taille du dépôt — CoursIA

> Le dépôt pèse ~1,2 GiB de pack pour un projet pédagogique. Ce document explique
> **pourquoi** ce poids est le prix d'une décision délibérée, **ce qui est acquis** (et ne
> sera pas réécrit), et **ce qui est surveillé** à l'avenir. Mesure, pas impression.

## 1. Pourquoi les sorties de notebooks restent committées (C.2 / H.1)

Les notebooks pédagogiques sont committés **avec leurs sorties**. C'est une règle dure du
projet ([notebook-conventions](../../.claude/rules/notebook-conventions.md) C.2) : les
outputs **sont** le livrable pédagogique — ils prouvent que le code s'exécute et montrent le
résultat attendu. Retirer les sorties détruirait cette preuve (H.1 : validation = exécution
complète + outputs vérifiés). Le poids du dépôt est donc, pour une large part, le coût
d'une exigence de qualité, pas une négligence.

## 2. Deux refus argumentés (acquis, non négociables)

### 2.1 `nbstripout` : NON

Stripping les sorties à l'indexation détruirait le livrable (C.2) et falsifierait la preuve
d'exécution (H.1). Un notebook pédagogique sans ses outputs n'est plus qu'un script : il
ne montre plus le résultat de l'algorithme, la figure générée, la métrique du backtest.
Cette règle est **posée noir sur blanc pour clore le sujet** — la taille n'est pas un motif
de retirer les sorties.

### 2.2 Réécriture d'historique (`git filter-repo`, BFG) : NON

Le dépôt compte ~95 forks étudiants. Réécrire l'historique casserait chacun d'eux (tout
`pull` ultérieur entrerait en conflit). Le poids passé est **acquis** : les grands blobs
déjà committés (cf. §3) restent dans l'historique. La politique est **entièrement tournée
vers l'avenir** — on surveille ce qui entre, on ne défait pas ce qui est fait.

## 3. Mesure réelle (plus gros blobs, ordre décroissant)

Mesuré firsthand via `git rev-list --objects --all | git cat-file --batch-check` (équivalent
fonctionnel à `git-sizer` pour le classement par blob, sans dépendance Go) :

| Taille | Blob | Statut | Décision |
|--------|------|--------|----------|
| 63 MB | `Sudoku/IKVM.Java.dll` | vendored (pont Java IKVM pour Sudoku/Tweety, #4667) | acquis — vendored légitime |
| 53 MB | `Argument_Analysis/libs/org.tweetyproject.tweety-full-1.28-…jar` | vendored (Tweety) | acquis — vendored légitime |
| 29 MB | `QuantConnect/ML-Training-Pipeline/checkpoints/lstm/…/model.pt` | **supprimé** (history-only, désormais gitignoré) | incident passé — §4 empêche la récurrence |
| 25 MB | `ML/ML.Net/taxi-fare.csv` | dataset pédagogique | candidat LFS futur (§5) |
| 21 MB | `GenAI/Audio/02-Advanced/02-4-Demucs-Source-Separation.ipynb` (+ ×N révisions) | notebook + outputs (audio base64) | acquis — poids légitime C.2 |

Le pack agrégé (~1,2 GiB bare) reflète : (a) les blobs vendored légitimes, (b) l'historique
des notebooks-avec-outputs (chaque révision d'un notebook riche compte), (c) quelques
incidents passés (le `model.pt`) désormais nettoyés de l'arbre courant.

> **Note locale** : `git count-objects -vH` peut afficher `size-pack` plus élevé et des
> `warning: garbage found: .git/objects/pack/tmp_pack_*` sur un clone de travail. Ces
> `tmp_pack_*` sont du **garbage local** à la machine (un `git gc` les élimine), pas un
> problème du dépôt distant. Ne pas les confondre avec le sujet.
>
> **`du -sh .git` n'est pas la taille du dépôt.** Sur une machine de dev, `du -sh .git`
> additionne des composantes **locales** qu'un cloneur ne paie jamais : (a) `size-pack`
> (le pack parent — accrète plusieurs fichiers `.pack` sur un clone longévif, non coalescés
> tant qu'un `git gc` n'a pas tourné), (b) `size-garbage` (`tmp_pack_*` orphelins, cf.
> ci-dessus), et (c) **`.git/modules/`** — les object stores des 8 submodules (cf. §5.1),
> checkoutés localement mais absents du pack parent. Mesure firsthand sur une machine du
> cluster : `size-pack ~2 GiB` + `size-garbage ~890 MiB` + `.git/modules ~270 MiB`, soit un
> `du -sh .git` dépassant largement le pack distant (~1,2 GiB bare, cf. en-tête) — un écart
> qui n'est **pas** une régression de taille, juste la somme de ces trois composantes locales.
> La source de vérité pour la taille du dépôt est le pack distant (ce qu'un `git clone` nu
> récupère), jamais `du -sh .git` sur une machine de travail.

## 4. Ce qui ne doit JAMAIS entrer

Ces catégories n'ont pas vocation dans le dépôt — un check advisory (§6) les signale, et le
`.gitignore` les exclut quand elles sont prévisibles :

- **Checkpoints de modèles** (`.pt`, `.pth`, `.ckpt`, `.safetensors` de training) — cf.
  l'incident `model.pt` 29 MB, supprimé puis gitignoré. Un checkpoint n'est pas un livrable
  pédagogique : le notebook documente *comment* l'entraîner, pas le poids binaire du résultat.
- **Artefacts `_output` volumineux** (sorties Papermill `_output.ipynb` régénérées) — ce sont
  des artefacts de processus, pas du matériel versionné.
- **Caches** (`__pycache__/`, `.pytest_cache/`, `bin/`, `obj/`) — déjà couverts par
  `.gitignore` et la convention `_archive/` (#9535).
- **Données brutes volumineuses** non pédagogiques (dump de production, logs complets).

## 5. Candidats Git LFS à l'avenir

Pour les **futurs** ajouts (pas de rétro-conversion de l'existant), Git LFS est la voie
désignée au-dessus du seuil advisory (§6) :

- **Datasets** (`.csv`/`.parquet` pédagogiques au-delà du seuil, ex: `taxi-fare.csv`) — le
  notebook les consomme mais le binaire n'a pas besoin d'être dans l'historique git.
- **Assets binaires GenAI** (modèles de base, poids, datasets d'images).
- **Renders et figures binaires** hors notebooks (galerie README) quand ils dépassent le seuil.

Le seuil advisory (§6) est là pour **déclencher la conversation** : un blob > seuil dans une
PR ouvre la question « LFS ou justification pédagogique ? », sans bloquer le merge.

### 5.1 Submodules : usage réel et angle mort du check §6

Le dépôt utilise **8 submodules** (inscrits dans `.gitmodules`), répartis en deux familles :

- **Libs vendored externes** : `foundry-lib/lib/{forge-std, openzeppelin-contracts,
  account-abstraction}` (SmartContracts Solidity), `Argumentum` (ArgumentumGames) —
  dépendances externes pointées par commit, non recopiées comme blobs.
- **Dépôts propres** : `MetaGeneticSharp` (jsboige), `Z3.Linq`, `Automata`, `semantic-fleet`
  (MyIntelligenceAgency) — sous-projets factorisés hors du monorepo.

Les submodules sont l'**alternative structurelle** à LFS pour externaliser le poids hors de
l'arbre : un gitlink pèse quelques octets, quel que soit le poids du dépôt référencé. C'est
précisément ce qui crée leur angle mort.

- **Angle mort du check §6** : un submodule n'est **pas** un blob du dépôt parent — c'est une
  référence de commit (`gitlink`). Le scan `git diff --diff-filter=A` de `repo-size-advisory.yml`
  ne le voit donc **jamais**, quel que soit le poids du dépôt référencé. L'introduction d'un
  submodule pointant vers un dépôt de plusieurs GiB ne déclencherait aucun warning advisory.
- **Décision** : les 8 submodules actuels sont des dépendances stables (libs vendored + sous-
  projets propres), légitimes au même titre que les blobs vendored de §3. L'ajout d'un
  **nouveau** submodule doit être **documenté dans la PR** avec le poids du dépôt référencé et
  la raison (vendored légitime vs sous-projet propre vs déplacement LFS-like) — le check §6 ne
  peut pas le mesurer, donc c'est la revue humaine qui porte la garde. Critère de refus : un
  submodule dont l'unique motivation est « cacher du poids » plutôt qu'une réelle factorisation
  ou dépendance externe stable.

## 6. Check advisory (jamais bloquant)

Un workflow CI (`.github/workflows/repo-size-advisory.yml`) signale, sur chaque PR, les blobs
ajoutés au-dessus du seuil retenu. Il est **advisory** (`exit 0`, `::warning::`) — conforme au
pattern des gates de visibilité (`variation-tag-guard`) : il rend le fait visible sans
bloquer le travail.

**Seuil retenu : 10 MiB**, justifié par la mesure §3 : il capture les datasets/checkpoints/
vendored-binaries (25–63 MB) tout en respectant la queue légitime des notebooks-avec-outputs
de taille modeste. Le seuil est calibré sur les chiffres réels, pas sur une intuition.

## Voir aussi

- [notebook-conventions.md](../../.claude/rules/notebook-conventions.md) — C.2 (outputs
  committés), H.1 (validation = exécution + outputs)
- [secrets-hygiene.md](../../.claude/rules/secrets-hygiene.md) — règle 6 (Stop & Repair,
  jamais scrubber une sortie)
- Convention `_archive/` — [#9535](https://github.com/jsboige/CoursIA/issues/9535)
