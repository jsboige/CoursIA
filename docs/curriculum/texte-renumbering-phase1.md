# GenAI/Texte — analyse renumérotation (EPIC #5081, phase-1)

**Série** : `MyIA.AI.Notebooks/GenAI/Texte/` (20 notebooks Python, série **plate** — pas d'arborescence par étage, numérotation linéaire `1..20`).
**Phase** : 1 (docs-only, analyse DAG — pas de modification de notebook).
**Verdict renumérotation** : **NO-RENUMBER**. Numérotation contiguë `1..20`, ordre pédagogique valide confirmé par le README, 0 navlink `<<` obsolète (stale-RESOLVES) parmi les liens existants.
**Constat séparé (hors scope #5081)** : **défaut d'hygiène de navigation** — la chaîne `Suivant >>` s'interrompt après le notebook 8, 7 notebooks n'ont **aucun** navlink, et 9 notebooks portent un lien `[Index]` au chemin obsolète. Ce défaut relève de la *complétude/correction des navlinks*, pas de la *numérotation narrative* ; il est documenté ici et renvoyé à un suivi dédié (§4).

L'objectif de #5081 est un *arc pédagogique cohérent*, pas une numérotation d'opportunité. La méthode phase-1 vérifie que la numérotation actuelle **est** déjà un tri topologique valide et qu'aucune référence narrative n'est cassée-mais-résolvable. Contrairement à Search (#6883), Sudoku (#6888), Probas/Infer (#6879), Probas/PyMC (#6885) et Planners (#6898), la série Texte est **plate** : l'ordre pédagogique est porté par le numéro de fichier seul (pas de sous-dossier par étage), et le README joue le rôle d'index autoritatif de la progression.

## Inventaire

20 fichiers `.ipynb` (hors `_output`), soit un **spine pédagogique Python de 20 unités** (`1_OpenAI_Intro` → `20_OWUI_Native_API`), rangés à plat dans `Texte/`.

| Plage | Thème (d'après le README) | Notebooks |
|-------|---------------------------|-----------|
| 1–4 | Fondations API & prompting | `1_OpenAI_Intro`, `2_PromptEngineering`, `3_Structured_Outputs`, `4_Function_Calling` |
| 5–9 | RAG, outils, raisonnement, production | `5_RAG_Modern`, `6_PDF_Web_Search`, `7_Code_Interpreter`, `8_Reasoning_Models`, `9_Production_Patterns` |
| 10–12 | Hébergement local & scaling | `10_LocalLlama`, `11_Quantization`, `12_Test_Time_Scaling` |
| 13–18 | Agents, mémoire, recherche arborescente, SK | `13_Agentic_Orchestration`, `14_Persistent_Memory`, `15_Tree_of_Thoughts_Search`, `16_Scaling_Test_Time_Compute`, `17_Native_Reasoning_vs_Scaling`, `18_Semantic_Kernel_Plugins` |
| 19–20 | Open WebUI (orchestration + API native) | `19_OWUI_Orchestration`, `20_OWUI_Native_API` |

**Couverture numérique `1..20` : complète et contiguë** (aucun trou, aucun doublon). Le `README.md` de la série (`GenAI Texte - Maîtrise des LLMs`) liste les 20 notebooks dans cet ordre linéaire, avec descriptions — c'est l'index autoritatif de la progression.

## 1. Vérification topologique (DAG des prérequis)

Extraction du navlink narratif `[<< Precedent](N.ipynb)` de chaque notebook, puis contrôle que tout prérequis déclaré pointe vers un numéro **strictement inférieur** (tri topologique valide).

- Les 12 notebooks porteurs d'un `<< Precedent` (2–12 + 19) pointent **tous** vers `own − 1` — arêtes en ordre inversé (`prev# ≥ own#`) : **0**.
- La numérotation `1..20` est cohérente avec l'ordre du README (fondations → RAG/outils → local/scaling → agents/SK → Open WebUI).

La numérotation actuelle **est** déjà un ordre pédagogique valide — rien à renuméroter. (L'absence de navlink sur 13–18/20 est une lacune de *complétude*, traitée en §3 ; elle ne remet pas en cause l'ordre, qui reste fixé par le numéro de fichier et le README.)

## 2. Scan stale-RESOLVES (toutes cellules, header + footer)

Un navlink « stale-RESOLVES » (classe L613-L1) est un `[<< Prev]` dont la cible a été **renommée/déplacée** : il résout-vers-un-fichier-existant (passe le checker 404) mais pointe vers le **mauvais** voisin narratif — typiquement un numéro **supérieur** au sien. Scan de **toutes** les cellules markdown (header ET footer), pas seulement les deux premières (leçon L615-L1).

```
[<< …N.ipynb] prev-navlinks (toutes cellules) : 12
backward vers cible# > own# (stale-RESOLVES)     : 0
[… >> N.ipynb] next-navlinks                     : 8  (notebooks 1..8)
forward vers cible# < own# (stale-RESOLVES)       : 0
```

**0 stale-RESOLVES** : les navlinks *présents* pointent tous vers le bon voisin de numéro. Aucune référence narrative « cassée-mais-résolvable » de type renumérotation.

## 3. Constat séparé — défaut d'hygiène de navigation (hors scope #5081)

L'analyse a mis au jour un défaut réel de navigation **distinct de la renumérotation**. Il ne s'agit ni d'un mauvais ordre ni d'un stale-RESOLVES, mais d'une **navigation incomplète et de liens `[Index]` obsolètes**. Trois classes, données vérifiées (`git ls-files` + parse par cellule) :

### Classe A — chaîne `Suivant >>` interrompue après le notebook 8

Le fil forward `[Suivant >>]` existe pour 1→2→…→8, puis s'arrête. Les notebooks 9, 10, 11, 12 et 19 portent un `<< Precedent` mais **aucun** `Suivant >>` : impossible de progresser vers l'avant par navlink au-delà de 8.

### Classe B — 7 notebooks sans aucune navigation

`13_Agentic_Orchestration`, `14_Persistent_Memory`, `15_Tree_of_Thoughts_Search`, `16_Scaling_Test_Time_Compute`, `17_Native_Reasoning_vs_Scaling`, `18_Semantic_Kernel_Plugins`, `20_OWUI_Native_API` — **aucune ligne `**Navigation**`** dans quelque cellule que ce soit. (Le notebook 20 référence 19 en **prose** de contenu, pas en navlink.) Sur 20 notebooks, seuls 13 portent une navigation ; 7 en sont dépourvus.

### Classe C — lien `[Index]` au chemin obsolète (stale-path, résout-vers-mauvais-README)

La série est **plate** dans `Texte/`, donc l'index de série est `README.md` (→ `Texte/README.md`, titré *GenAI Texte - Maîtrise des LLMs*). Or 11 des 13 notebooks porteurs d'un lien `[Index]` pointent vers un README **parent** — résout-vers-existant (passe le checker 404) mais ce n'est **pas** l'index de la série :

| Chemin `[Index]` écrit | Résout vers | Correct ? | Notebooks |
|------------------------|-------------|-----------|-----------|
| `../../README.md` | `MyIA.AI.Notebooks/README.md` (racine notebooks) | non | 1, 2, 3, 4, 10, 11 |
| `../README.md` | `MyIA.AI.Notebooks/GenAI/README.md` (hub modalité) | non | 5, 6, 7, 8, 9 |
| `README.md` | `MyIA.AI.Notebooks/GenAI/Texte/README.md` (index série) | **oui** | 12, 19 |

Signature typique d'un **chemin resté figé avant l'aplatissement** de l'arborescence : les `../` étaient corrects quand les notebooks étaient d'un ou deux niveaux plus profonds. Seuls 12 et 19 ont été corrigés.

### Pourquoi c'est hors du scope #5081

#5081 traite la *numérotation narrative* (renuméroter un arc mal ordonné). Ici la numérotation est saine — le défaut est la *complétude et la correction des navlinks*. Le corriger entièrement touche ~18 notebooks (compléter la chaîne `>>` sur 9–20, ajouter la navigation à 13–18/20, corriger le `[Index]` sur 9 notebooks), soit **> 15 fichiers** : au-delà du plafond G.4 d'une PR atomique, et un sujet différent de la renumérotation. Il relève donc d'un **grain dédié** (voir §4), pas de cette analyse #5081.

## 4. Suite recommandée (grain dédié, hors #5081)

Compléter et corriger la navigation de la série Texte, en appliquant le gabarit-maison unique :

```
**Navigation** : [Index](README.md) | [<< Precedent](<n-1>.ipynb) | [Suivant >>](<n+1>.ipynb)
```

- Corriger le lien `[Index]` (`../../README.md` / `../README.md` → `README.md`) sur les 9 notebooks concernés (classe C).
- Ajouter `[Suivant >>]` sur 9, 10, 11, 12, 19 (classe A) — extrémité 20 : pas de `>>`.
- Ajouter la ligne de navigation complète sur 13–18 et 20 (classe B).

Éditions **markdown-only** (ligne de navigation d'une cellule markdown de header) → **C.2-safe**, aucune ré-exécution. À découper si nécessaire pour respecter le plafond G.4 (ex. « correction des liens `[Index]` » et « complétion de la chaîne `>>` » en deux PR). Ce grain n'est **pas** tracké au moment de cette analyse ; il est renvoyé au pool d'issues ouvertes.

## 5. Baseline liens documentaires

```
check_docs_links --check → OK: No new broken links. (0 pre-existing, 3984 total) [exit 0]
```

Les navlinks `[Index]` obsolètes de la classe C **ne sont pas** signalés par le checker 404 : les trois cibles (`README.md`, `../README.md`, `../../README.md`) existent toutes. Le checker vérifie l'existence, pas la *pertinence* de la cible — d'où l'intérêt de l'analyse par série.

## Verdict

**NO-RENUMBER** pour la question #5081 : spine `1..20` contiguë, ordre pédagogique valide (confirmé par le README + les 12 navlinks `<<` en ordre strictement croissant), 0 stale-RESOLVES. Renuméroter ici serait une numérotation d'opportunité, contraire à l'objectif de #5081.

**Défaut d'hygiène de navigation constaté** (classes A/B/C ci-dessus), **hors scope renumérotation** et de taille > 15 fichiers : renvoyé à un grain dédié (§4), à sortir du pool d'issues ouvertes.

### Méthode (réutilisable)

1. Spine + couverture numérique (contiguïté, doublons).
2. DAG topologique : `[<< prev]` → cible de numéro strictement inférieur.
3. Scan stale-RESOLVES **toutes cellules** (header + footer) : `<<`/`>>` vers un numéro incohérent = résidu de réorg.
4. **Complétude & correction des navlinks** (série plate) : chaîne `>>` continue ? notebooks sans navigation ? lien `[Index]` vers le bon README de série (résout-vers-existant ≠ résout-vers-correct) ?
5. Baseline `check_docs_links --check`.

Voir : Search #6883 (1 stale-RESOLVES corrigé), Sudoku #6888 (1 corrigé), Probas/Infer #6879, Probas/PyMC #6885, Planners #6898, Video #6909.

*Analyse : po-2024:CoursIA-2. See #5081.*
