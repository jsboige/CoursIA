> **ARCHIVED 2026-07-20** — Verdict **NO-RENUMBER / no-defect-found** figé (cf PR #6898). EPIC #5081 phase-1 close. Document conservé pour référence historique (daté, immutable). Voir triage table c.674 [PR #7426](https://github.com/jsboige/CoursIA/pull/7426) + archive INDEX [`docs/archive/INDEX.md`](../INDEX.md). Superseded by EPIC #5081 closure. *Archivé par : po-2026 (lane CoursIA-2, c.695) — `See` partiel dispatch triage c.674 UPDATE/ARCHIVE catégorie, suite logique c.676 PR #7436 (GenAI Texte+Video) + c.748 PR #7525 (Probas/Infer, Probas/PyMC, Search) ; Planners = dernier dispatch restants dans la catégorie phase-1.*

# SymbolicAI/Planners — analyse renumérotation (EPIC #5081, phase-1)

**Série** : `MyIA.AI.Notebooks/SymbolicAI/Planners/` (EPIC #1344, renumérotée lors du passage à l'arborescence par étage `00-Environment` → `04-NeuroSymbolic`).
**Phase** : 1 (docs-only, analyse DAG — pas de modification de notebook).
**Verdict** : **NO-RENUMBER / no-defect-found**. Réorg propre : spine contiguë, sous-dossiers alignés sur les plages de numéros, 0 navlink `<<` obsolète (stale-RESOLVES) sur l'ensemble des cellules.

L'objectif de #5081 est un *arc pédagogique cohérent*, pas une numérotation d'opportunité. La méthode phase-1 vérifie que la numérotation actuelle **est** déjà un tri topologique valide et que la réorganisation n'a pas laissé de références narratives cassées-mais-résolvables (le `[<< Prev]` d'un notebook renommé qui pointe encore vers l'ancien voisin).

## Inventaire

23 fichiers `.ipynb` (hors `_output`, `_archives`), soit un **spine pédagogique Python de 13 unités** (`Planners-0` → `Planners-12`) + 9 jumeaux C# (`-Csharp`) + 1 annexe Lean (`Planners-5b-Lean-Relaxation`).

| Sous-dossier | Plage de numéros | Notebooks Python |
|--------------|------------------|------------------|
| `00-Environment` | 0 | `Planners-0-Setup` |
| `01-Foundation` | 1–3 | `Planners-1-Introduction`, `Planners-2-PDDL-Basics`, `Planners-3-State-Space` |
| `02-Classical` | 4–6 (+ 5b Lean) | `Planners-4-Fast-Downward`, `Planners-5-Heuristics`, `Planners-5b-Lean-Relaxation`, `Planners-6-Domains` |
| `03-Advanced` | 7–9 | `Planners-7-OR-Tools`, `Planners-8-Temporal`, `Planners-9-HTN` |
| `04-NeuroSymbolic` | 10–12 | `Planners-10-LLM-Planning`, `Planners-11-Unified-Planning`, `Planners-12-LOOP` |

**Les plages de numéros correspondent exactement aux sous-dossiers** : le rangement par étage est cohérent avec l'ordre pédagogique. Aucune unité mal classée.

## 1. Vérification topologique (DAG des prérequis)

Extraction du navlink narratif `[<< …](Planners-N.ipynb)` de chaque notebook, puis contrôle que tout prérequis déclaré pointe vers un numéro **strictement inférieur** (tri topologique valide).

- Couverture numérotation `0..12` : **complète et contiguë** (aucun trou, aucun doublon).
- Chaque `<< prev` détecté pointe vers `own − 1` (ou une étape antérieure légitime, ex. les jumeaux C# pointant vers le jumeau C# précédent).
- **Arêtes en ordre inversé (`prev# ≥ own#`) : 0.**

La numérotation actuelle **est** déjà un ordre pédagogique valide — rien à renuméroter.

## 2. Scan stale-RESOLVES (toutes cellules, header + footer)

Un navlink « stale-RESOLVES » (classe L613-L1) est un `[<< Prev]` dont la cible a été **renommée** pendant la réorg : il résout-vers-un-fichier-existant (passe le checker 404) mais pointe vers le **mauvais** voisin narratif — typiquement un numéro **supérieur** au sien. Les défauts trouvés sur Search-8 (#6883) et Sudoku-4 (#6888) résidaient dans le **header ET le footer**, d'où un scan de **toutes** les cellules markdown, pas seulement les deux premières.

```
total [<< …ipynb] prev-navlinks (toutes cellules) : 17
backward (cible# > own#, même série) = stale-RESOLVES : 0
```

**0 stale-RESOLVES** dans quelque cellule que ce soit. Contrairement à Search et Sudoku (1 défaut chacun), la réorg Planners est **propre** : aucun navlink `<<` ne pointe vers un voisin de numéro supérieur.

## 3. Inventaire des liens entrants (cross-série)

Références `Planners-N` depuis l'extérieur du dossier Planners (README parents, autres séries, `docs/`). Deux entrées ressortent comme suspectes ; les deux sont des **non-défauts** après vérification :

| Occurrence | Fichier | Nature | Verdict |
|------------|---------|--------|---------|
| `Planners-5-Heuristiques en Planification` | `docs/curriculum/ia-symbolique.md:57` | **Titre en prose** dans un tableau-catalogue (cellule non-lien), qui reprend le **titre pédagogique français** du notebook (`# Planners-5-Heuristiques…`, cellule 17 de `Planners-5-Heuristics.ipynb`) — le fichier est `Heuristics`, le titre est `Heuristiques`. | Non-défaut (pas un lien de fichier). |
| `Planners/Planners-4-Advanced-H…-csharp.ipynb` | `docs/ledgers/reviews/2026-07-11-h4-sweep-6021.md:14` | **Ledger daté** (audit H4 du 2026-07-11) enregistrant l'**ancien nom pré-réorg**. Les ledgers sont append-only : réécrire l'ancien nom falsifierait l'enregistrement historique. | Non-défaut (snapshot daté correct). |

Aucun **lien de navigation vivant** cassé. Le tableau-catalogue de `ia-symbolique.md` utilise des titres descriptifs (aucune cellule n'est un `[texte](fichier.ipynb)`), et le ledger est un instantané historique légitime.

## 4. Baseline liens documentaires

```
check_notebook_navlinks MyIA.AI.Notebooks/SymbolicAI/Planners → OK: 0 lien casse
check_docs_links --check → OK: No new broken links. (0 pre-existing, 3974 total)
```

## Verdict

**NO-RENUMBER / no-defect-found.** La réorganisation en arborescence par étage (#1344) a produit une numérotation qui est déjà un tri topologique valide : spine `0..12` contiguë, sous-dossiers alignés sur les plages de numéros, 0 navlink `<<` obsolète (toutes cellules), 0 lien vivant cassé. Les 2 anomalies entrantes sont un titre en prose et un ledger daté — ni l'un ni l'autre n'est un défaut de navigation.

Comme pour Probas/Infer (#6879) et Probas/PyMC (#6885), la valeur de cette phase-1 tient à ce qu'elle **écarte** : une renumérotation ici serait une numérotation d'opportunité, contraire à l'objectif de #5081.

### Méthode (réutilisable)

1. Spine + couverture numérique (contiguïté, doublons).
2. DAG topologique : `[<< prev]` → cible de numéro strictement inférieur.
3. Scan stale-RESOLVES **toutes cellules** (header + footer) : `<<` vers numéro supérieur = résidu de réorg.
4. Liens entrants cross-série : trier lien-vivant vs prose/ledger.
5. Baseline `check_docs_links --check`.

Voir : Search #6883 (1 stale-RESOLVES corrigé), Sudoku #6888 (1 corrigé), Probas/Infer #6879, Probas/PyMC #6885.
