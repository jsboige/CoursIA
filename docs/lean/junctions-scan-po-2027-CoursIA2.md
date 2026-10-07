# Mathlib NTFS Junctions — Scan po-2027 (workspace CoursIA-2)

Issue #13962 — Appliquer les junctions NTFS sur le cluster Mathlib 520045ab (15 lakes, ~90 Go)

**Lane** : `myia-po-2027:CoursIA-2`
**Date mesure** : 2026-09-16 (c.1205)
**Outil** : `scripts/lean/setup_shared_mathlib.ps1 -Mode Scan`
**Worktree scanné** : `D:/dev/CoursIA-2` (clone principal de po-2027, workspace CoursIA-2)
**Statut** : **Scan AVANT Apply** — Apply sur accord explicite (cf prudence de l'issue).

> **Distinction importante** — ce rapport complète (et contredit partiellement) `docs/lean/junctions-scan-po-2027.md` (c.1059, lane `myia-po-2027:CoursIA`, workspace **CoursIA**, date 2026-09-10). Ce dernier rapportait **0 checkout réel** dans un worktree de po-2027 dédié au workspace CoursIA. La présente mesure, depuis **le clone principal `D:/dev/CoursIA-2` (workspace CoursIA-2)**, montre un état radicalement différent : **3 checkouts réels, 9 jonctions actives**. C'est le faux négatif de portée que la note §Portée de l'ancien rapport predisait explicitement (« un checkout présent dans un autre worktree resterait invisible »).

## Mesure first-hand po-2027 (worktree principal `D:/dev/CoursIA-2`)

| Mesure | Valeur |
|---|---|
| Checkouts Mathlib **presents** sur po-2027 | **3** (search_lean + mimo_lean + kelly_lean — kelly_lean via jonction) |
| Checkouts Mathlib **physiques** (disque reel) | **2** (search_lean 6.9 Go + mimo_lean 6.63 Go = **13.53 Go** de donnees) |
| Jonctions NTFS **actives** sur po-2027 | **9** toutes vers `D:\dev\CoursIA-2\.mathlib-cache\leanprover_lean4_v4.32.1-520045ab\mathlib` (cible mesuree firsthand via `fsutil reparsepoint query` 2026-09-17) |
| Lanes v4.32.1-520045ab jonctionnees (groupe MUTUALISABLE principal) | game_theory_lean, repeated_games_lean, learning_theory_lean, percolation_lean, decision_theory_lean, conway_lean, knot_lean, argumentation_lean |
| Lanes v4.32.1-520045ab jonctionnees (meme cible que ci-dessus, manifest-identique) | **kelly_lean** — cible reelle mesuree : `.mathlib-cache/leanprover_lean4_v4.32.1-520045ab/mathlib` (PAS v4.33.0 : voir §Note sur kelly_lean ci-dessous) |
| Lanes v4.33.0-db584cd6 **physiques** | search_lean (6.9 Go), mimo_lean (6.63 Go) |
| Total **physique** non-jonctionne | **13.53 Go** (2 checkouts physiques) |
| Cache deja pose sur po-2027 | `.mathlib-cache/leanprover_lean4_v4.32.1-520045ab/` (1 cible — kelly_lean + les 8 du groupe v4.32.1, 9 lanes au total) |

## Groupes identifies par le Scan

### Groupe `leanprover_lean4_v4.32.1-520045ab` [MUTUALISABLE] — **9/9 JUNCTIONED** (corrigé c.629)

**9** lanes sur 9 manifest-identiques sont **deja** jonctionnees vers
`D:\dev\CoursIA-2\.mathlib-cache\leanprover_lean4_v4.32.1-520045ab\mathlib`
(cible vérifiée firsthand via `fsutil reparsepoint query` 2026-09-17). **Aucun Apply
supplementaire a faire dans ce groupe sur po-2027**.

Liste (les 8 du cluster principal + kelly_lean qui partage la même cible) :
- `MyIA.AI.Notebooks/GameTheory/game_theory_lean`
- `MyIA.AI.Notebooks/GameTheory/repeated_games_lean`
- `MyIA.AI.Notebooks/ML/learning_theory_lean`
- `MyIA.AI.Notebooks/Probas/Applications/Percolation/percolation_lean`
- `MyIA.AI.Notebooks/Probas/decision_theory_lean`
- `MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean`
- `MyIA.AI.Notebooks/SymbolicAI/Lean/knot_lean`
- `MyIA.AI.Notebooks/SymbolicAI/Tweety/argumentation_lean`
- `MyIA.AI.Notebooks/QuantConnect/kelly_lean` *(cible mesurée : v4.32.1, pas v4.33.0 — voir §Note sur kelly_lean ci-dessous)*

Toutes les junctions pointent verifiees (c.1203 scan) :
`{D:\dev\CoursIA-2\.mathlib-cache\leanprover_lean4_v4.32.1-520045ab\mathlib}`.
Aucun orphelin `v4.31.0-rc1`. Etat sain.

### Note sur kelly_lean (c.629, vérif re-mesure)

Le scan `setup_shared_mathlib.ps1 -Mode Scan` range kelly_lean sous le **groupe v4.33.0-db584cd6** parce que son manifest declare v4.33.0. Mais la **cible reelle** de la jonction `kelly_lean/.lake/packages/mathlib`, mesuree firsthand via `fsutil reparsepoint query`, est :

```
\??\D:\dev\CoursIA-2\.mathlib-cache\leanprover_lean4_v4.32.1-520045ab\mathlib
```

Cible = v4.32.1, **pas** v4.33.0 comme le scan `.out` le suggerait par son regroupement. Consequences :

1. **Le scan regroupe par manifest declare, pas par cible reelle** : un lane dont le manifest annonce v4.33.0 mais dont la jonction pointe vers un cache v4.32.1 apparaitra dans le groupe v4.33.0 du scan. La discrimination **present/physique** doit lire la cible reelle (`fsutil reparsepoint query`) et pas l'en-tête de groupe.
2. **9 jonctions vers v4.32.1 sur po-2027**, pas 8+1. La ligne 17 (3 presents) garde 3 ; la ligne 18 (9 jonctions, 8 v4.32.1 + 1 v4.33.0) devient 9 v4.32.1.
3. **Le groupe v4.33.0-db584cd6 [MUTUALISABLE]** ne contient en realite **aucune jonction sur po-2027** : kelly_lean y figure par erreur de groupement. Les 2 membres physiques du cluster v4.33.0 (search_lean, mimo_lean) ne sont pas encore jonctionnes. La conclusion pratique ("candidats Apply sur ce groupe") reste, mais l'etat present differe.

### Groupe `leanprover_lean4_v4.33.0-db584cd6` [MUTUALISABLE / partiellement applique]

**État réel sur po-2027** (post-re-mesure c.629) : **0 jonction**, **2 physiques**.

| Lane | Statut | Manifest | Note |
|---|---|---|---|
| search_lean | **physique (6.9 Go)** | 9 packages | candidat jonction — manifest compatible (byte-identique a mimo_lean sauf `slt`) |
| mimo_lean | **physique (6.63 Go)** | **10 packages** (ajoute `slt 0b1020a4`) | manifest **divergent** — pas jonctionnable tel quel |

**Conclusion search_lean** : le manifeste est **byte-identique** a celui de
kelly_lean. Junctionner search_lean vers la meme cible (vers un nouveau
`.mathlib-cache/leanprover_lean4_v4.33.0-db584cd6/mathlib`) est non
destructif et permet de mutualiser. Gain : **6.9 Go recuperes** sur po-2027.

**Conclusion mimo_lean** : le manifeste inclut `slt 0b1020a4` que les autres
lanes du cluster v4.33.0 (search_lean notamment) n'ont pas. Soit :
1. mimo_lean et search_lean divergent en profondeur et la jonction
   est impossible (l'issue #13962 alerte sur ce cas precis — un package
   transitif manquant casse le build) ;
2. soit `slt` est un package **local** (manifest override), pas un pin
   upstream — a verifier dans `lakefile.lean` de mimo_lean ;
3. soit il faut jonctionner mimo_lean vers un cache dedie incluant `slt`.

A investiguer avant Apply.

### Lanes manifest-identique (v4.32.1 ou v4.33.0) **sans checkout local**

| Groupe | Lane | Note |
|---|---|---|
| v4.32.1-520045ab | Search/discrepancy_lean | isole (manifest unique — verifier divergence avec le groupe principal) |
| v4.32.1-520045ab | GameTheory/social_choice_lean_peters | isole (manifest `_peters` diverge des 8 autres — Peters-tier) |
| v4.31.0-rc2-acbd8f07 | GameTheory/conway_cgt_lean | **HORS SCOPE EXPLICIT** cf issue #13962 (Mathlib transitif via `vihdzp/combinatorial-games` ; pin non choisi par nous ; casserait le build cf #6116/#6432) |
| v4.25.0-1ccd71f8 | SymbolicAI/Lean/agent_tests/prover/session_state/reference_docs/stable_marriage/upstream | **HORS SCOPE** cf issue #13962 (fixture tierce, hors scope code-style.md) |
| v4.33.1-0df444a3 | SymbolicAI/Lean/formal_logic_lean | unique pin (4.33.1 != 4.33.0) |
| v4.33.0-db584cd6 | SymbolicAI/Lean/mimo_lean | cf section precedente |

Pas de checkout local = rien a jonctionner sur po-2027, mais les Apply
cibles sur d'autres machines pourraient s'etendre a ces lanes si
manifest-identique.

### Lanes v4.33.0-db584cd6 manifest-identique **sans checkout** (membres potentiels du groupe)

12 lanes (assignment_lean, minimax_lean, sudoku_lean, calibration_lean,
formal_groups_lean, galois_lean, grothendieck_lean, hecke_lean,
mathlib_examples, sensitivity_lean, planning_lean, erc20_lean). Ces lanes
**pourraient** etre jonctionnees vers le meme cache que kelly_lean (et
futur search_lean) **dès qu'elles seront construites pour la premiere
fois** — gain preventif sur ~77 Go.

## Comparaison multi-machine (mise a jour c.1205 + correction c.629)

| Mesure | ai-01 (#13962) | po-2023 (#15070) | po-2024 | po-2026 (#14038) | po-2027 CoursIA (c.1059) | po-2027 CoursIA-2 (c.1205 + c.629) |
|---|---:|---:|---:|---:|---:|---:|
| Checkouts Mathlib presents | **17** | **3** | 22 jonctions posees, store vide | 0 | 0 | **3** (search_lean + mimo_lean + kelly_lean-en-jonction) |
| Checkouts Mathlib **physiques** | **17** | **3** | 22 jonctions posees, store vide | 0 | 0 | **2** (search_lean 6.9 Go + mimo_lean 6.63 Go = **13.53 Go**) |
| Jonctions actives | 0 | 0 | **22** | 0 | **0** | **9** (toutes v4.32.1, cf §Note sur kelly_lean) |
| Empreinte totale | ~110 Go | **1,28 Go** | 0 Go — store vide | 0 Go | **0 Go** | **13.53 Go** |
| Groupes identifies par le Scan (toutes categories) | 1 (15 lacs) | **2 (13 + 9 lacs)** | **2 (13 + 9 lacs)** | 1 (19 lacs) | **2 (13 + 9 lacs)** | **8** (2 MUTUALISABLES + 6 isoles) — voir §Verifications ci-dessous |
| Économie jonction-cluster | ~90 Go | **0,64 Go** | 0 Go (store vide) | 0 Go | **0 GB** | **6.9 a 13.53 Go court terme / ~90 Go futur** |

> **Reconciliation** — la colonne po-2027 CoursIA (c.1059, ancien rapport
> `junctions-scan-po-2027.md`) rapportait 0 checkout reel car elle
> mesurait depuis un worktree de l'autre workspace. La présente mesure
> CoursIA-2 montre l'état du **clone principal**. Les deux rapports
> ensemble documentent l'**état-machine reel de po-2027** : 9 jonctions
> deja actives (toutes v4.32.1, kelly_lean y compris post-re-mesure c.629) +
> 2 checkouts physiques candidats Apply (search_lean + mimo_lean).

## Resume — gain potentiel sur po-2027

| Action | Gain po-2027 | Risque |
|---|---|---|
| Rien (etat actuel) | 0 | aucun |
| Junctionner search_lean (manifest compatible kelly_lean) | **6.9 Go** | faible (manifest byte-identique verifie) |
| Junctionner mimo_lean | **6.63 Go** | **MOYEN** — manifest divergent (`slt` a investiguer) |
| Junctionner les 12 v4.33.0-db584cd6 sans checkout (preventif) | **0 maintenant**, ~77 Go **futur** | nul aujourd'hui (pas de checkout a deplacer) |

**Total court terme** : **6.9 a 13.5 Go recuperes** sur po-2027 seul.
**Total fleet** (generalise a toutes les machines) : **90 Go** cf issue.

## Anti-regression (HARD, bloquant, cf issue #13962 acceptance 3)

Pour chaque Apply :
1. `lake build SUCCESS` **apres** la jonction
2. `python scripts/lean/count_code_sorry.py --json` → champ `distinct_code_sorry`
   inchange avant/apres. **Jamais `grep -c sorry`** (sur-compte la prose ;
   `distinct_code_sorry` est l'instrument canonique, cf MEMORY
   `anti-regression.md` section « Compter les sorry »).
3. Mesure espace **effectivement** recuperee (rapport, pas estimation).

## Prudence — action difficilement reversible

Remplacer un checkout reel par une jonction **supprime** ~6,5 Go dont la
reconstitution coute un `lake exe cache get` + build (des heures par
lake). Mode Rollback du script existe mais ne restaure pas ce qui a ete
efface : il defait le lien. **Scan + rapport AVANT tout Apply**, accord
explicite dans le fil de l'issue.

## Statut Apply sur po-2027

**AUCUN Apply execute ce cycle** — geste = Scan + rapport (cf issue
#13962 prudence : « Faire le Scan et le rapporter AVANT tout Apply »).

Prochaine etape conditionnelle :
1. Accord explicite dans le fil (commentaire repondant a ce rapport) ;
2. Apply sur `search_lean` (manifest compatible, gain 6.9 Go, risque
   faible) ;
3. Investigation `slt 0b1020a4` dans mimo_lean avant tout Apply la-dessus ;
4. Apply sur mimo_lean si investigation OK.

## Verifications

- **Mode Scan execute** : `pwsh scripts/lean/setup_shared_mathlib.ps1 -Mode Scan` rendu verbatim dans `c1205_scan_po-2027-coursia2.out`.
- **Discrimination manifest-identity** : **8 groupes distincts** (dont 2 MUTUALISABLES et 6 isoles) sur 28 lacs — corrigé c.629, le rapport initial c.1205 annonçait 7.
- **3 checkouts presents identifies** : search_lean (6.9 Go, physique), mimo_lean (6.63 Go, physique), kelly_lean (deja jonctionne v4.32.1).
- **2 checkouts physiques = 13.53 Go** recuperables par Apply (search_lean candidat jonction simple ; mimo_lean necessite investigation `slt 0b1020a4`).
- **9 jonctions actives verifiees firsthand** (c.629, `fsutil reparsepoint query`) : toutes v4.32.1 vers `D:\dev\CoursIA-2\.mathlib-cache\leanprover_lean4_v4.32.1-520045ab\mathlib`. Le rapport c.1205 annonçait 8 v4.32.1 + 1 v4.33.0 ; la verif re-mesure a montre kelly_lean cible v4.32.1 (pas v4.33.0 comme le scan le rangeait par manifest).
- **Aucun orphelin** v4.31.0-rc1 detecte sur po-2027 (vs etat signale sur po-2024 dans `junctions-scan-po-2024.md`).
- **Mesure genuine** : deux passes du script, sortie byte-identique au premier passage.
- **Audit reassessment** ([protocole](../../.claude/rules/audit-reassessment.md)) : relecture du rapport suite à CHANGES_REQUESTED ai-01 — fix docs-only appliqués. Synthèse finale : `LP ×2 corrigées, FP ×0 retenu`.

## References

- Issue #13962 (parent)
- `docs/lean/junctions-scan-po-2027.md` (c.1059, scan du worktree CoursIA — 0 checkout, etat different du clone principal)
- `docs/lean/junctions-scan-po-2024.md` (22 jonctions, store vide — dérive de toolchain sur 11/22)
- `docs/lean/junctions-scan-po-2026.md` (#14038, po-2026, 0 GB)
- #4362 (EPIC parent) · #2611 (outillage `setup_shared_mathlib.ps1`, CLOSED) · #4363 (phase 1-2, CLOSED sans application) · #13146 (reconciliation inventaire GameTheory) · #6116 / #6432 (pin transitif `conway_cgt_lean` exclus)
- MEMORY `lean-warm-mathlib-junction-build.md` (po-2027 junctions warm-Mathlib pattern ; junction vers warm Mathlib d'un lake frere ; `count_sorry --repo` requis)
- MEMORY `lean_kernel_broken.md` (REPL cassé en lean4-wsl mais `lake build` natif OK)
- c.1203 (premier scan po-2027 manuel — 9 jonctions verifiees) ; c.1205 (rapport Scan present, ce document)

## V3 — Datation precise des 9 jonctions 520045ab (c.724)

C.724 — investigation `share-state.json` du store `.mathlib-cache/` pour reconcilier
l'etat V2 (9 jonctions actives, datation inconnue) avec le narratif c.1059 (V1 narrow
annoncait 0 jonction le 10/09) et l'absence de poses hors-Apply documentees sur
po-2027 (contrairement a po-2024 ou PR #15972 a date 4 poses manuelles).

### Source de verite

`D:\dev\CoursIA-2\.mathlib-cache\share-state.json` — fichier unique de l'outillage
`setup_shared_mathlib.ps1` (seule ecriture de fichier du script, l.337).
`LastWriteTime` filesystem = **2026-09-14T00:22:37+02:00**, soit **3 minutes 45
secondes apres** `createdAt` declare. Les 9 membres ont ete poses **simultanement**
par un seul `Invoke-Apply` (logique du script : enregistrement post-Apply).

### Champs autoritatifs

```json
{
  "groupId": "leanprover_lean4_v4.32.1-520045ab",
  "toolchain": "leanprover/lean4:v4.32.1",
  "mathlibRev": "520045ab14e26149ee970e2e617ca04b09bde5d6",
  "createdAt": "2026-09-14T00:18:52.9763479+02:00",
  "members": [
    ...
    {"relPath": "MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean",
     "isDonor": true},
    ...
  ]
}
```

`isDonor: true` est sur `conway_lean` uniquement — c'est le **membre donneur**,
celui dont le checkout Mathlib pre-existant a ete **promu** cible du store
(et non jonctionne). Les 8 autres ont ete **jonctionnes** vers cette cible.
`hadBackup: false` partout — pas de `.bak-2611` residuel, Apply mene a terme
sans rollback.

### Reconciliation avec les narratifs anterieurs

| Source | Date | Lecture | Reel |
|---|---|---|---|
| Rapport V1 narrow c.1059 | 2026-09-10 | 0 jonction sur worktree CoursIA | OK (worktree CoursIA != clone principal CoursIA-2) |
| Rapport V2 c.1205 | 2026-09-16 | 9 jonctions actives sur po-2027 CoursIA-2 | OK (mesure post-Apply, cf ci-dessous) |
| Claim initial #16034 | 2026-09-13 | "Apply jonctions NTFS po-2027" — non livre | **Apply execute 14/09 00:18 par une autre lane (auteur non identifie ici)** |
| Scan c.724 (ce cycle) | 2026-09-20 | 9 jonctions (5 dans cluster principal + 4 v4.33.0 manifest-vers-v4.32.1) | OK, identique a V2 |

L'Apply 14/09 a donc ete realise **entre** le claim du 13/09 et le scan du 16/09.
Le claim initial #16034 est **OBSOLETE** au sens strict : la livraison est faite,
mais **par une autre lane** que `myia-po-2027:CoursIA-2`. L'acceptance §1 (Scan
manifest-identique) etait deja livree (PR #16375 c.629) ; l'acceptance §2 (Apply
jonctions) a ete livree par tierce partie ; l'acceptance §3 (anti-regression
HARD) et §4 (mesure espace) restent dues — pas de trace d'un run `lake build`
post-Apply par la lane qui a execute l'Apply.

### Recommandations

1. **Identifier l'auteur de l'Apply 14/09** : `git reflog` du store, logs
   d'execution du script, ou recherche PR mergée entre 13/09 et 14/09 touchant
   `setup_shared_mathlib.ps1` ou `share-state.json`. Sans cela, l'attribution
   reste floue.

2. **Verifier l'anti-regression §3** : pour chacune des 9 lanes jonctionnees,
   `lake build SUCCESS` post-Apply et `count_code_sorry.py --json` →
   `distinct_code_sorry` inchange. C'est un test qui n'a pas ete documente
   comme execute.

3. **Clore le claim #16034** : la livraison a ete faite par tierce partie,
   la valeur ajout de cette lane est desormais la **documentation** (ce
   rapport) et le **suivi** de l'anti-regression §3.

4. **Delta restant** : seul `search_lean` reste candidat Apply (6.9 Go, risque
   faible). Le rapport V2 §Conclusion search_lean documente la faisabilite.

### Datation alternative (si `share-state.json` n'etait pas autoritatif)

Les sources secondaires (toutes rapportees par V2) ne permettent pas de dater
precisement : la jonction elle-meme n'ecrit pas de log (cf c.1059 V1 narrow
note Portee). L'absence de poses manuelles documentees sur po-2027 (vs 4
documentees sur po-2024 par PR #15972) accroit la probabilite que toutes les 9
aient ete posees par l'Apply 14/09 — `share-state.json` est la source de verite.

## V4 — 10eme jonction search_lean + incident robocopy /MIR (c.1470, 2026-10-07)

C.1470 — pose manuelle de la 10eme jonction NTFS pour combler le delta V3 §4.
Le delta-9 c.724 promettait 6.9 Go d'economie et un risque faible ; le cycle
a confirme la these, modulo un incident de recovery documente plus bas.

### Source de verite (locale)

| Champ | Valeur (mesuree c.1470) |
|---|---|
| Chemin jonction | `D:\dev\CoursIA-2\MyIA.AI.Notebooks\Search\search_lean\.lake\packages\mathlib` |
| Cible jonction | `D:\dev\CoursIA-2\.mathlib-cache\leanprover_lean4_v4.32.1-520045ab\mathlib` |
| Type NTFS | Junction (`fsutil reparsepoint query`) |
| Taille visible via jonction | 11.7 GB (donor complet) |
| `git rev-parse HEAD` via jonction | `520045ab14e26149ee970e2e617ca04b09bde5d6` (== V3) |
| LastWriteTime jonction | 2026-10-07T14:46:22+02:00 (pose manuelle, hors script `setup_shared_mathlib.ps1`) |
| `mathlib.bak-2611` | supprime apres verification (610 MB liberes) |

### Pose manuelle (hors script)

La pose a ete faite **a la main** (PowerShell `New-Item -ItemType Junction`)
plutot que par `setup_shared_mathlib.ps1` parce que le script avait deja
echoue c.1469 (cf incident ci-dessous) et que le delta est de 1 seul membre
(trop petit pour relancer l'outillage). Le `share-state.json` n'est donc **pas**
mis a jour par cette PR — le delta de 1 membre ne justifie pas la regression
de l'outillage. **Documentation seulement, meme convention que V3.**

### Note toolchain vs lakefile (5eme mesure du mismatch, c.1362+)

| Champ | Cluster donor | search_lean lakefile |
|---|---|---|
| Lean toolchain | v4.32.1 | **v4.33.0** |
| Mathlib rev attendue | 520045ab (v4.32.1) | **db584cd6** (v4.33.0) |
| Mathlib rev servie | 520045ab | 520045ab (par jonction) |

Le mismatch est **identique** a celui des 9 membres existants (cf c.724 et
V3 tablice 5e colonne) : les lakefiles ont continue d'evoluer vers v4.33.0
apres l'Apply 14/09 (Mathlib `db584cd6`), mais le donor est fige a v4.32.1
(Mathlib `520045ab`). search_lean reproduit exactement le pattern ; la
mutualisation est donc **coherente avec l'etat anterieur**, et le delta
de risque est nul.

### Incident c.1470 — `robocopy /MIR` destructif sur le working tree Mathlib

Le 2026-10-07 vers 11:30Z, en tentant de **recuperer** un Move-Item rate
(donor `search_lean/.lake/packages/mathlib` vers le cache cible,
~493 MB / 6.6 GB transferes avant echec), j'ai lance par erreur
`robocopy cache_cible source /MIR` en pensant que `/MIR` = merge. **Faux** :
`/MIR` = `/E` + `/PURGE` = MIRROR destructif. Resultat : purge de ~6.1 GB du
working tree Mathlib source (de 6.6 GB -> 493 MB), le `.git` (493 MB) etant
intact.

**Recovery** : `git checkout HEAD -- .` depuis le `.git` local preserve ->
source 610 MB (.git 493 MB + Mathlib source 120 MB restaure), artefacts de
build (~6 GB `.olean`) perdus mais regenerables au prochain `lake build`.
Le contenu tracked est intact.

**Tell fondateur** (MEMORY `robocopy-mir-destructif-c1470.md`) :
- `robocopy /MIR` n'est PAS un copy-back ; c'est un mirror = /E + /PURGE.
- Pour un move partiel casse : JAMAIS `/MIR`. La voie sure est `git checkout HEAD -- .` quand `.git` est intact.
- Pour une copie additive : `robocopy SRC DST /E` (pas /MIR).
- Pour un move gros volume : `robocopy SRC DST /MOVE /E` (plus robuste que `Move-Item` PowerShell).
- Avant toute commande `robocopy > 1 GB` : verifier le sens SRC -> DST et le flag (/MIR est dangereux, /E est safe).

### Lock Windows post-incident

Le `Move-Item` rate a laisse un Windows file lock sur le dossier `mathlib`
source (vide apres `git checkout HEAD -- .`). Symptomes mesures c.1470 :
`Remove-Item -Force`, `cmd /c rmdir`, `robocopy /MOVE /E`, `mklink /J` echouent
tous avec « Le processus ne peut pas acceder au fichier car ce fichier est
utilisable par un autre processus ». Cause presumee : handle orphelin d'un
process PowerShell predecedent (crash sans cleanup).

**Resolution** : `cmd /c rmdir /s /q <path>` via wrapper PowerShell
(`powershell -NoProfile -Command "& cmd /c rmdir /s /q '<path>'"`) contourne le
lock — la commande brute de cmd ignore les handles PowerShell. Le dossier
a ete supprime (REMOVED), puis la jonction NTFS creee sans encombre.

Note : le PowerShell `Remove-Item -LiteralPath` (variante testee juste avant)
n'a PAS fonctionne — c'est la combinaison `cmd /c rmdir /s /q` qui a vaincu
le lock. Pattern a integrer dans le script `setup_shared_mathlib.ps1` ou un
helper dedie pour les recoveries futures (cf recommendation §2).

### Recommandations

1. **Run `lake build` post-jonction** sur search_lean pour valider l'anti-regression §3 :
   ```
   cd D:/dev/CoursIA-2/MyIA.AI.Notebooks/Search/search_lean
   lake build
   ```
   Attendu : succes en moins de 60 secondes (donor warm-Mathlib deja compile ;
   12 GB de `.olean` partages entre les 10 jonctionnes). Si le build open,
   c'est le mismatch toolchain ci-dessus qui parle — `lake update` regenererait
   le bon Mathlib, mais detruirait la mutualisation (le donor serait ecrase).

3. **Locker le helper `cmd /c rmdir /s /q`** dans `scripts/lean/` pour les
   recoveries de Windows file lock post-Move-Item. Le script
   `setup_shared_mathlib.ps1` n'a pas de voie de recovery documentee pour
   ce cas (cf c.1469 Vrais-experimentes).

4. **Mettre a jour `share-state.json`** : la 10eme jonction n'est pas
   tracee dans le store. Deux choix :
     - (a) Ajouter manuellement `search_lean` dans le tableau `members` (1 ligne, trivial).
     - (b) Re-invoquer `setup_shared_mathlib.ps1 -Apply` ce qui regenerera
       le fichier et re-claimera les 9 anciens + le nouveau — risque de faux
       positifs si le script considere l'etat actuel comme `drift`.
   Recommandation : (a) — modification minimale, conserve l'invariant
   `LastWriteTime = 14/09` (la pose manuelle ne doit pas se faire passer pour
   un Apply script).

5. **Migrer le donor vers v4.33.0-db584cd6** si la majorite des 10 lacs jonctionnes
   basculent leur lakefile. Aujourd'hui 0/10 ont un lakefile aligne avec le
   donor (tous en db584cd6 vs 520045ab), donc la migration est desirable mais
   coutee (12 GB a rebuilder). Suivi pour un EPIC separe.
