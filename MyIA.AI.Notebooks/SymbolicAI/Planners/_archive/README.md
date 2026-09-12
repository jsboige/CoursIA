# Notebook Planners archivé : Fast-Downward-Legacy

Ce dossier conserve l'unique notebook archivé de la série Planners : la version
monolithique d'origine du cours Fast Downward (69 cellules, dont 48 markdown et
21 code, kernel `.NET (C#)`), remplacée le 4 mars 2026 par la série renumérotée
`Planners-0` à `Planners-12`. Le notebook archivé n'est ni modifié ni
réexécuté : il est préservé byte-exact comme provenance historique.

## Registre de disposition

| Notebook | Verdict | Superseded by | Verdict recorded in |
|---|---|---|---|
| `Fast-Downward-Legacy.ipynb` | OBSOLETE (2026-03-04) — monolithe découpé en série pédagogique | [`../02-Classical/Planners-4-Fast-Downward.ipynb`](../02-Classical/Planners-4-Fast-Downward.ipynb) pour le cœur Fast Downward, et la série complète livrée dans le même commit (cf. disposition par section) | Commit `83b88a320` (« Split monolithic Fast-Downward.ipynb into 13 pedagogical notebooks », copie d'archivage C100 dans le même commit) ; cellule 0 du notebook (navigation `[<< Planners-4]`, PR #1487) ; ce registre |

## Disposition par section

La convention exige un en-tête de disposition par fonction pour chaque fichier
`.py` archivé. Pour un notebook archivé non modifiable, la disposition
équivalente vit dans cette section : chaque bloc de contenu du monolithe est
relié à son devenir, preuve à l'appui.

| Section du monolithe (cellules) | Devenue | Preuve |
|---|---|---|
| Présentation des technologies — Fast Downward, OR-Tools (md 0-1) | [`../01-Foundation/Planners-1-Introduction.ipynb`](../01-Foundation/Planners-1-Introduction.ipynb) pour la planification classique ; OR-Tools est traité par [`../03-Advanced/Planners-7-OR-Tools.ipynb`](../03-Advanced/Planners-7-OR-Tools.ipynb) | Série créée dans le même commit `83b88a320` |
| `FastDownwardRunner` C# : auto-téléchargement de la release 24.06.1, compilation, invocation CLI (code 2) | Remplacé par l'image Docker `jsboige/coursia-fast-downward` (serveur HTTP) — mise en place dans [`../00-Environment/Planners-0-Setup.ipynb`](../00-Environment/Planners-0-Setup.ipynb), invoquée dans [`../02-Classical/Planners-4-Fast-Downward.ipynb`](../02-Classical/Planners-4-Fast-Downward.ipynb) | `Planners-4` : « Fast Downward est execute via l'image Docker `jsboige/coursia-fast-downward` » ; 53 mentions fast-downward dans `Planners-0-Setup` |
| Syntaxe CLI : options translate/search, alias, limites temps/mémoire, benchmark `gripper` (md 4-15, code 6/10/13/19/25) | [`../02-Classical/Planners-4-Fast-Downward.ipynb`](../02-Classical/Planners-4-Fast-Downward.ipynb) (kernel Python) — architecture 3 étapes, benchmark `gripper` conservé | README de la série (apport pédagogique Planners-4) ; 10 occurrences `gripper` dans Planners-4 |
| Validation de plan (md 21) | Traitée dans la série courante | grep `validation` : Planners-6-Domains ×2, Planners-0/5 |
| Panorama des heuristiques via options FD-CLI : blind, goalcount, add, cea, cg, ff, h^m, hmax, lmcut, merge-and-shrink, iPDB, landmark cost partitioning (md 17-44 et 47-57) | [`../02-Classical/Planners-5-Heuristics.ipynb`](../02-Classical/Planners-5-Heuristics.ipynb) couvre h^add, h^max, h^FF, LM-cut (réimplémentations + comparaison expérimentale) ; le balayage exhaustif des options CLI (cea, cg, iPDB, operator-counting, post-hoc) reste sans équivalent dédié — conservé comme référence | README de la série (apport Planners-5) ; grep série : `operator-counting` 0, `post-hoc` 0 ; `cea`/`cg`/`pdb` 0 dans Planners-5 |
| Options avancées : portfolios (md 23, 59), adaptation des coûts (md 61), optimisation post-hoc (md 63), réduction des étiquettes (md 65), collections de motifs (md 67), compétitions (md 68) | Conservé comme référence — aucune section dédiée dans la série courante | grep série (25 notebooks) : `portfolio` ×1 (mention de passage, Planners-1), réduction d'étiquettes 0 |
| Exercices stub `Console.WriteLine("Exercice a completer")` (code 46, 58) | Stubs historiques conformes C.1, jamais complétés — aucune reprise | `execution_count` 11 et 17, sorties d'origine |

Le twin C# [`../02-Classical/Planners-4-Fast-Downward-Csharp.ipynb`](../02-Classical/Planners-4-Fast-Downward-Csharp.ipynb)
(PR #5591, 2026-07-07) n'est pas un port du monolithe : il conçoit son propre
translateur SAS+ (A*/GBFS/EHC, h-FF) au lieu d'invoquer le vrai Fast Downward —
approche distincte du runner auto-téléchargeur du monolithe.

## Historique (preuves Git)

| Date | Commit | Événement |
|---|---|---|
| 2024-05-24 | `0da5e56a9` | Création `MyIA.AI.Notebooks/Planners/Fast-Downward.ipynb` (« Ajout Fast-downward ») |
| 2025-01-31 | `a7848f075` | Déplacement vers `MyIA.AI.Notebooks/SymbolicAI/Planners/Fast-Downward.ipynb` (« Changement de repertoires ») |
| 2026-03-04 | `83b88a320` | Découpage du monolithe en 13 notebooks + copie d'archivage intégrale (C100) vers `Planners/archive/Fast-Downward-Legacy.ipynb`, dans le même commit |
| 2026-03-05 | `a10fb3bc5` | Suppression de l'original `Planners/Fast-Downward.ipynb` du vivant |
| 2026-05-23 | `817cd1b0d` (PR #1487) | En-tête de navigation de la cellule 0, pointant le successeur (`[<< Planners-4]`) |
| 2026-08-06 | `928147688` (PR #9724) | Renommage `archive/` → `_archive/` (issue #9535) |
| 2026-09-05 | `5064187dd` (PR #14716) | Normalisation mécanique source str→liste — dernière modification du fichier |

Après son archivage, le notebook a reçu les passes mécaniques globales de la
série (re-exécution PR #2204 — dernière exécution, 2026-06-03 ; scrubbing de
chemins PR #3487/#3891 ; bandeau probeAddresses PR #2733 ; accents PR #7261) :
il reste l'exécutable d'origine, `execution_count` 1 à 21 présents.

## État et références résiduelles

- Exclu du catalogue pédagogique : 0 occurrence dans `COURSE_CATALOG.generated.md` et `.json` ; compté « hors compteur pédagogique » dans le README de la série.
- Références résiduelles, toutes en qualité d'archivé :
  - `MyIA.AI.Notebooks/SymbolicAI/Planners/README.md` (arborescence de la série) ;
  - `docs/ledgers/3801-sota-axe2.md` (exclusion explicite du scan PDDL) ;
  - `docs/archive/reference/notebook-counts-reconciliation.md` (EXCLUDE_PEDAGOGICAL) ;
  - `translations/planners/planners.csv` (138 lignes au chemin `Planners/archive/`, antérieur au renommage de 2026-08 — registre de traduction historique).

## Pourquoi le conserver

La suppression ferait perdre la provenance exacte du premier support Fast
Downward du dépôt (2024) : le runner C# auto-téléchargeur, le balayage complet
des heuristiques FD-CLI et les sections sans successeur dédié (validation de
plan détaillée, coûts, portfolios, compétitions) n'existent plus qu'ici.
L'archive locale au domaine garde cette référence consultable sans présenter le
monolithe comme un notebook de la série : toute évolution du cours modifie les
notebooks `Planners-0` à `Planners-12`, jamais celui-ci.

## Références

- Convention appliquée : `docs/reference/_archive-convention.md`
- Umbrella de standardisation : #13749
- Découpage d'origine : commit `83b88a320`
- Renommage `archive/` → `_archive/` : PR #9724, issue #9535
