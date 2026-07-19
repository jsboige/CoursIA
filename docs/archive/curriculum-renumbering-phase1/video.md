# GenAI/Video — analyse renumérotation (EPIC #5081, phase-1)

> **ARCHIVED 2026-07-19** — Verdict **NO-RENUMBER** + 1 défaut de spine « skip » corrigé (`02-5-LTX2-Audiovisual` ré-inséré). EPIC #5081 phase-1 close. Document conservé pour référence historique (daté, immutable). Voir triage table c.674 [PR #7426](https://github.com/jsboige/CoursIA/pull/7426) + archive INDEX [`docs/archive/INDEX.md`](../INDEX.md). Superseded by EPIC #5081 closure. *Archivé par : po-2023 (lane CoursIA-2, c.676) — `Closes` partiel dispatch triage c.674 UPDATE/ARCHIVE catégorie.*

**Série** : `MyIA.AI.Notebooks/GenAI/Video/` — arborescence hiérarchique à 4 étages (`01-Foundation` → `04-Applications`), 17 notebooks.
**Phase** : 1 (docs-only pour l'analyse ; 1 correctif navlink markdown appliqué — pas de ré-exécution, cf C.2).
**Verdict** : **NO-RENUMBER** sur la structure (numérotation à 2 niveaux `étage-index` déjà cohérente) **+ 1 défaut de spine « skip » corrigé** (02-5-LTX2-Audiovisual court-circuité par le pont d'inter-étage 02-4↔03-1).

L'objectif de #5081 est un *arc pédagogique cohérent*, pas une numérotation d'opportunité. La méthode phase-1 vérifie que la numérotation actuelle **est** déjà un tri topologique valide et que la réorganisation n'a pas laissé de références narratives cassées : lien `<<`/`>>` obsolète-mais-résolvable (stale-RESOLVES), ou notebook **sauté** par le fil narratif (skip).

## Inventaire

17 notebooks `.ipynb` (hors `_output`), répartis en 4 étages contigus.

| Sous-dossier | Plage | Notebooks |
|--------------|-------|-----------|
| `01-Foundation` | 1-1 → 1-5 | Video-Operations-Basics, GPT-5-Video-Understanding, Qwen-VL-Video-Analysis, Video-Enhancement-ESRGAN, AnimateDiff-Introduction |
| `02-Advanced` | 2-1 → 2-5 | HunyuanVideo, LTX-Video-Lightweight, Wan-Video, **SVD-Image-to-Video**, **LTX2-Audiovisual** |
| `03-Orchestration` | 3-1 → 3-3 | Multi-Model-Video-Comparison, Video-Workflow-Orchestration, ComfyUI-Video-Workflows |
| `04-Applications` | 4-1 → 4-4 | Educational-Video-Generation, Creative-Video-Workflows, Sora-API-Cloud-Video, Production-Video-Pipeline |

**Chaque plage de numéros correspond exactement à son étage** : le rangement est cohérent avec l'ordre pédagogique. Aucune unité mal classée, aucun trou, aucun doublon → **pas de renumérotation nécessaire**.

## 1. Vérification topologique (DAG des prérequis)

Extraction des navlinks narratifs `[<< …]` (prev) et `[… >>]` (next) de **toutes les cellules markdown** de chaque notebook (L615-L1 : header ET footer), puis contrôle que la clé d'ordre `(étage, index)` du prédécesseur est strictement inférieure à celle du notebook courant.

- Couverture `(1,1)..(4,4)` : **complète et contiguë** par étage.
- **Arêtes en ordre inversé (stale-RESOLVES, `prev# ≥ own#` intra-étage) : 0.**

## 2. Défaut « skip » détecté et corrigé (02-5-LTX2-Audiovisual)

**Classe de défaut distincte du stale-RESOLVES** (L613-L1). Dans un stale-RESOLVES, une cible *renommée* résout mais pointe un voisin de numéro supérieur. Ici, les voisins sont correctement ordonnés mais **sautent par-dessus un notebook intermédiaire existant** :

- `02-5-LTX2-Audiovisual` (capstone de l'étage 02, seul modèle vidéo **+** audio conjoints, LTX-2 22B) déclarait pourtant correctement sa place dans **deux** cellules (cell1 + cell23) : `[<< 02-4 SVD]` / `[Comparaison >>](03-1)`.
- Mais le **pont d'inter-étage** liait 02-4 et 03-1 **directement**, court-circuitant 02-5 : `02-4` `[Suivant >>]` → `03-1`, et `03-1` `[<< 02-4]` → `02-4`. Vestige d'un navlink antérieur à l'insertion de 02-5 dans l'étage (cf PR #3110 qui documentait 02-5 dans le README **après** coup).

Le lien passait le checker 404 (02-4 et 03-1 existent bien), mais le fil de lecture *sautait* le capstone.

### Source narrative autoritaire : le README

Le README de la série place déjà 02-5 **dans** le spine : parcours recommandé `… 02-4 → 02-5 → 03-Orchestration`, table de l'étage 02 listant 02-5 entre 02-4 et 03-1, et mermaid `B4 (02-5 LTX-2) → C1 (03-1)`. Le correctif **réaligne les navlinks des notebooks sur l'ordre déjà canonique du README**, il ne l'invente pas.

### Correctif appliqué (3 lignes markdown, C.2-safe)

| Fichier | Avant | Après |
|---------|-------|-------|
| `02-4-SVD` cell0 `>>` | `[Suivant >>](../03-Orchestration/03-1-…)` | `[02-5 LTX-2 >>](02-5-LTX2-Audiovisual.ipynb)` |
| `03-1-Comparison` cell0 `<<` | `[<< 02-4](../02-Advanced/02-4-SVD-…)` | `[<< 02-5 LTX-2](../02-Advanced/02-5-LTX2-Audiovisual.ipynb)` |
| `03-1-Comparison` prérequis | `notebooks 02-1 a 02-4` | `notebooks 02-1 a 02-5` (le capstone 02-5 fait partie de l'étage) |

Spine réparé : **02-3 → 02-4 → 02-5 → 03-1 → 03-2**, chaîne avant+arrière symétrique.

## 3. Faux positif écarté (non un défaut)

`04-4-Production-Video-Pipeline` `[Audio 01-1 >>]` → `../../Audio/01-Foundation/01-1-OpenAI-TTS-Intro.ipynb` : **pont cross-module Video→Audio intentionnel**, explicitement labellisé, en fin de série. Laissé tel quel.

## 4. Contrôle final

Scan all-cells post-correctif sur les 17 notebooks : chaîne **contiguë de bout en bout** (`01-1 → … → 02-4 → 02-5 → 03-1 → … → 04-4 → pont Audio`), backward = forward pour chaque arête, **0 anomalie** (stale-RESOLVES + skip). `check_notebook_navlinks --check` : 0 nouveau lien cassé vs baseline.

## Verdict

**Structure NO-RENUMBER** (4 étages contigus, cohérents) + **1 défaut de spine « skip » corrigé** : 02-5-LTX2-Audiovisual ré-inséré dans la chaîne narrative avant+arrière. La classe « skip » (voisins bien ordonnés qui sautent un notebook intermédiaire existant) complète la classe « stale-RESOLVES » (cible renommée pointant un voisin de numéro supérieur) du catalogue de défauts phase-1.

**Séries #5081 phase-1 traitées** : Infer (#6879), Search (#6883), PyMC (#6885), Planners (#6898), Video (ce document).

*Analyse : po-2024:CoursIA-2. See #5081.*
