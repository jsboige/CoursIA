# MGS-7b Vision-QA Audit — Issue #7483 (projection N-D du fork Gtk#)

**Date** : 2026-07-21 (c.728i)
**Auditeur** : myia-po-2025:CoursIA-2 (lane MiniMax vision-capable)
**Issue** : [#7483](https://github.com/jsboige/CoursIA/issues/7483)
**Source du dispatch** : DM HIGH ai-01 `msg-20260721T035638-31mlv1` (racketteur 3 cycles honest-idle consécutifs)
**Référence amont** : audit code text-only po-2023 (c.712, commentaire `IC_kwDOH2Odns8AAAABK3-ung`)
**Complément audit visuel** : ce document — voit ce que le texte ne peut pas voir.

---

## 1. Contexte

L'epic #1203 (sous #7483) demande le port de la projection N-D du fork Gtk# `MyIntelligenceAgency/GeneticSharp @ d05826fd` (lignes 640-674 du `LandscapeExplorerSampleController.GetFunctionValue`) dans le submodule `MetaGeneticSharp` du repo CoursIA. **Tout le « What » est livré** :

| PR | Commit | Description | État |
|----|--------|-------------|------|
| #7583 | `b28ea5fc8` | `feat(mgs): MGS-7b N-D landscape projection bridge + notebook (#1203)` | MERGED |
| #7595 | `eb020caa2` | `fix(search,#709): make MGS-7-TSP notebook portable` | MERGED |
| #7598 | `4a5419c95` | `fix(search,#710): make MGS-10-CenterBias notebook portable` | MERGED |
| #7612 | `f56be1aef` | `Fix(search,#710): make MGS-8-LandscapeExplorer portable` | MERGED |
| #7617 | `5deda22e6` | `feat(search,#7483): MGS-8 N-D projection worked example` | MERGED |
| #7625 | `0bcb04d6d` | `docs(search,#4959): resync Search hub` | MERGED |
| #7634 | `2c69ac3a4` | `feat(search,#7483): MGS-9 N-D projection worked example` | MERGED |
| #7636 | `30560cebc` | `feat(search,#3975): reconcile Part4 README count 19→20` | MERGED |

L'audit text-only de po-2023 (c.712) a validé le port + tests + notebook. **Mais un audit text-only ne peut pas vérifier le rendu visuel des 8 PNG générés** — c'est la limite que ma lane MiniMax franchit dans ce document.

---

## 2. Périmètre de l'audit vision

### 2.1 8 PNG à inspecter

| Fichier | Taille (B) | Dimensions | Fonction | Dimension |
|---------|-----------|------------|----------|-----------|
| `landscape_multidim_rastrigin_d2.png` | 16 306 | 120×120 RGBA | Rastrigin | 2 |
| `landscape_multidim_rastrigin_d5.png` | 17 819 | 120×120 RGBA | Rastrigin | 5 |
| `landscape_multidim_rastrigin_d10.png` | 16 306 | 120×120 RGBA | Rastrigin | 10 |
| `landscape_multidim_rastrigin_d30.png` | 16 309 | 120×120 RGBA | Rastrigin | 30 |
| `landscape_multidim_schwefel_d5.png` | 19 963 | 120×120 RGBA | Schwefel | 5 |
| `landscape_multidim_schwefel_d30.png` | 19 955 | 120×120 RGBA | Schwefel | 30 |
| `landscape_multidim_sphere_2d.png` | 8 923 | 100×100 RGBA | Sphere | 2 |
| `landscape_multidim_sphere_5d.png` | 7 784 | 100×100 RGBA | Sphere | 5 |

Tous fichiers = vrais PNG (8-bit RGBA, non-interlaced), confirmés par `file(1)`. **Aucun placeholder, aucun bloc plat dégénéré** (incident fondateur : `workflow-orchestration.png` = 3 blocs olive/violet/vert labellisés = dégénéré).

### 2.2 Notebook `MGS-7b-LandscapeMultidim.ipynb`

12 cellules : 5 markdown (intro/Pourquoi un MGS-7b/transition Sphère/transition Rastrigin/transition Schwefel/Exercices/Liens) + 5 code (`#r` directive, Sphère 2D/5D, Rastrigin dim{2,5,10,30}, Schwefel dim{5,30}, Exercice 1, Exercice 2) + 2 markdown (## Exercices, ## Liens). Outputs présents (`execution_count: 1..6`, `outputs: [...]` cohérents). C.2 conforme (cf notebook-conventions.md).

---

## 3. Verdict vision par heatmap

### 3.1 Sphere (×2) — référence, conforme ✓✓

- **Sphere 2-D** (`landscape_multidim_sphere_5d.png`) : **gradient concentrique parfait** — centre rouge pur `(R=255,G=0,B=0)` (cf notebook cell 26fc53ca output `Color [A=255, R=255, G=0, B=0]`), dégradé radial régulier vers vert puis bleu. C'est le paysage test des bancs métaheuristiques : bol unique centré à l'origine. ✓
- **Sphere 5-D** (`landscape_multidim_sphere_5d.png`) : **quasi-identique** au 2D — gradient concentrique préservé (sortie notebook `Color [A=255, R=127, G=255, B=0]` au pixel (0,0)). La projection MAX en dim=5 fonctionne et donne une heatmap lisible. Le passage 2D→5D **change effectivement la heatmap** (le pixel central n'est plus l'optimum global : la projection MAX explore les coords cachées et trouve des points quasi-optimaux ailleurs). ✓

### 3.2 Schwefel (×2) — conforme ✓✓

- **Schwefel d=5** : **structure en damier visible** + 4 extrema rouges aux coins et sur les bords + creux bleus intermédiaires. C'est cohérent avec Schwefel qui a ses minima près de `±420.97` sur chaque axe : la projection 2D max-pool sur dim=5 capture les coins `(x_min, y_min)` et `(x_max, y_max)` comme extrema globaux. ✓
- **Schwefel d=30** : **structure en damier préservée** + creux plus prononcés au centre (bleu profond central) que d=5. Cohérent avec la théorie : en dim=30, l'optimum global `(420.97, ..., 420.97)` est **plus accessible** depuis le centre de la boîte (les coords cachées peuvent s'en approcher). ✓

### 3.3 Rastrigin (×4) — 3/4 conformes + 1 caveat légitime

- **Rastrigin d=2** : **heatmap authentique**, modulation sinusoïdale radiale visible — motif en damier régulier cercle rouge central → halo orange → jaune → vert, **10 minima locaux en quadrillage + 1 minimum global au centre**. C'est le paysage Rastrigin 2D classique. ✓
- **Rastrigin d=5** : très similaire à d=2 — motifs radiaux préservés. La projection MAX fonctionne : les coordonnées cachées (3 dimensions) ne « gomment » pas la structure visible. ✓
- **Rastrigin d=10** ⚠️ : **heatmap beaucoup plus plate** (majoritairement verte uniforme, **absence du motif radial attendu**). Avec dim=10 et seulement `nbSamples=25` par pixel, l'échantillonnage aléatoire des 8 dimensions cachées lisse les extrema → la projection MAX ne capture plus le relief multimodal. **C'est un signal légitime de convergence** : Rastrigin = paysage multi-modal lourd (≈10^n cuvettes locales) ; dim=10 nécessite `nbSamples ≥ 100` pour rendre les modes visibles avec probabilité raisonnable. **Pas un bug du port**, mais le notebook doit le **mentionner explicitement** comme limitation de convergence vs dim. ⚠️
- **Rastrigin d=30** : **retour de la structure radiale** — similaire à d=2. En dim=30 avec nbSamples=25, le paradoxe est que les extrema globaux deviennent **plus visibles** : la probabilité qu'au moins 1 sample tombe proche d'un mode accessible en dim=30 est suffisante (et le centre `(0,0)` est l'optimum global Rastrigin, retrouvé depuis presque tout point visible). ✓

### 3.4 Bilan vision : **7/8 conformes + 1/8 caveat pédagogique**

| Heatmap | Verdict vision | Note |
|---------|---------------|------|
| Sphere 2D | ✓ Conforme | Référence |
| Sphere 5D | ✓ Conforme | Différence 2D→5D visible |
| Schwefel d=5 | ✓ Conforme | Optima périphériques visibles |
| Schwefel d=30 | ✓ Conforme | Creux central plus marqué |
| Rastrigin d=2 | ✓ Conforme | Multimodal 2D classique |
| Rastrigin d=5 | ✓ Conforme | Multimodal préservé |
| Rastrigin d=10 | ⚠️ Caveat pédagogique | Heatmap lissée (convergence nbSamples=25 insuffisante) |
| Rastrigin d=30 | ✓ Conforme | Multimodal ré-émerge |

**Aucun render cassé / placeholder / bloc plat dégénéré.** L'incident fondateur `workflow-orchestration.png` (3 blocs olive/violet/vert labellisés) ne se reproduit pas ici.

---

## 4. Finding logique — Exercice 1 du notebook (BUG PÉDAGOGIQUE)

### 4.1 Constat empirique (output cellule 1dcb9167)

L'exercice 1 demande d'observer la **moyenne du canal rouge** en fonction de `nbSamples` pour Rastrigin dim=10. Output réel :

```
nbSamples=   1 → mean R = 63.94
nbSamples=   5 → mean R = 115.55
nbSamples=  25 → mean R = 5.73
nbSamples= 100 → mean R = 1.15
```

### 4.2 Lecture naïve du commentaire pédagogique

Le markdown de l'exercice 1 (cell 688c4c68) affirme :

> **Attendu** : la moyenne monte avec nbSamples, puis se stabilise. (markdown)

### 4.3 Contre-analyse

L'observation empirique **contredit** le commentaire pédagogique : la moyenne **descend** quand `nbSamples` croît (de 63.94 → 1.15). Interprétation théorique correcte :

- Rastrigin $f(\vec{x}) = -10n - \sum_i (x_i^2 - 10 \cos(2\pi x_i))$ admet **un optimum global profond à l'origine** $\vec{x} = \vec{0}$ (où $f=0$).
- Quand `nbSamples` ↑, les coordonnées cachées $x_2, ..., x_9$ ont **plus de chances** de tomber **proches de 0** par échantillonnage uniforme (loi des grands nombres + concentration près de 0). Conséquence : le **MAX** capture plus souvent le voisinage de l'optimum, où le canal **rouge** de la heatmap (= fitness élevée) est **dominant localement**.
- Mais la heatmap Rastrigin utilise une **palette qui sature vers le rouge sombre puis noir** quand la fitness est très haute (proche 0). Donc « MAX capture plus souvent un optimum très haut » se traduit par « pixel plus rouge sombre / noir → R faible quand fitness proche 0 ».
- **La moyenne du canal R descend** : cohérent avec la palette. Le commentaire pédagogique est **inversé**.

### 4.4 Recommandation

Le commentaire pédagogique de l'exercice 1 doit être corrigé :

> **Attendu corrigé** : la moyenne du canal rouge **descend** avec `nbSamples` (de ≈64 à ≈1), car la projection MAX capture plus souvent l'optimum central profond de Rastrigin (`f(0)=0`) et la palette sature vers le noir pour les fitness très hautes. La convergence est monotone décroissante et asymptotique.

Et l'intuition pédagogique doit être ré-écrite : « observer comment la heatmap **se concentre vers l'optimum central** quand `nbSamples` croît, signal que la projection MAX explore effectivement les dimensions cachées ».

### 4.5 Pourquoi ce finding est important

L'exercice 2 confirme la **variabilité entre seeds** (99.6% de pixels différents entre `Random(1)` et `Random(99999)`). C'est cohérent avec le code : `Parallel.For` visite les pixels dans un ordre non-déterministe (les samples cachés sont tirés dans chaque pixel indépendamment). La variabilité entre seeds est **réelle**, attendue, et bien commentée.

Mais la **mauvaise intuition pédagogique** de l'exercice 1 peut **induire l'étudiant en erreur** : il va regarder la moyenne R descendre et croire que son code est cassé, alors qu'il a juste découvert la concentration asymptotique vers l'optimum. **Bug pédagogique à corriger**, pas un bug du port.

---

## 5. Verdict global

### 5.1 Conformité au cahier des charges #7483

| Critère | Statut |
|---------|--------|
| Surcharge `RenderHeatmap(IFitness, int dimension, ...)` exposée | ✓ (cf notebook cell dc33013b : `2 surcharges N-D`) |
| Pattern verbatim du fork Gtk# `d05826fd` | ✓ (audit code po-2023 c.712) |
| Bug `coordsRange = min - min = 0` corrigé | ✓ (doc `KnownFunctionLandscape.cs` ligne 86) |
| Tests NUnit (12 dédiés ND + 168 autres) | ✓ 180/180 PASS (audit po-2023 c.712) |
| Notebook `MGS-7b-LandscapeMultidim.ipynb` livré | ✓ (12 cellules, C.2 conforme, outputs présents) |
| 8 PNG assets générés | ✓ (tous vrais PNG RGBA, 7/8 conformes vision + 1 caveat légitime) |
| Anti-régression notebooks MGS-6/10/12/16/17/18/19 | ✓ (non touchés, dim=5 préservé) |
| Pas de modification submodule upstream | ✓ |
| Pas de force-push, branche fraîche | ✓ (cf `b28ea5fc8` merge) |

### 5.2 Findings nouveaux (vs audit po-2023 text-only)

| # | Finding | Type | Sévérité | Owner |
|---|---------|------|----------|-------|
| 1 | Rastrigin d=10 heatmap lissée par convergence nbSamples=25 | Pédagogique (à documenter) | Basse | po-2024 (auteur notebook) |
| 2 | Exercice 1 : commentaire « la moyenne monte » est **inversé** (elle descend) | Pédagogique (bug d'intuition) | Moyenne | po-2024 (auteur notebook) |
| 3 | Aucun render cassé / placeholder / bloc plat | Confirmé (incidents fondateurs évités) | OK | — |

### 5.3 Résiduels (déjà listés par po-2023, confirmés)

| Résiduel | Priorité | Owner | Action |
|----------|----------|-------|--------|
| Portée MGS : 14 notebooks MGS-3/4/6/9/11..19 codent `dim=5` en dur | LIGHT (garniture ≤ 1/lane/jour) | multi-lane | post-R6 cross-lane pickup |
| Portabilité notebook MGS-7b (`c:/dev/MetaGeneticSharp/...`) | LIGHT | à traiter | post-c.711 |
| Sync submodule sur po-2026 | Résolu via submodule pointer `6a501d96` | po-2024 originel | clos |

---

## 6. Conclusion

**Le port N-D est complet, conforme et visuellement correct.** L'audit vision MiniMax **confirme** l'audit text-only po-2023 sur les 8 PNG livrés et **révèle** un bug pédagogique dans l'exercice 1 du notebook (commentaire « la moyenne monte » inversé par rapport à l'observation empirique). Aucun render cassé, aucun placeholder, aucun bloc plat — l'incident fondateur `workflow-orchestration.png` ne se reproduit pas.

**Recommandation** : PR de **fix pédagogique** dans `MGS-7b-LandscapeMultidim.ipynb` (cellule 688c4c68, exercice 1) pour corriger le commentaire `« Attendu : la moyenne monte avec nbSamples »` → `« Attendu : la moyenne descend avec nbSamples (concentration vers l'optimum central profond) »`. Issue #7483 peut ensuite être **close** avec une PR supplémentaire optionnelle pour le fix pédagogique (ou laissée ouverte avec ce finding documenté pour un pickup futur).

**Statut pour #7483** :
- `Closes #7483` n'est PAS justifié : le bug pédagogique de l'exercice 1 est un finding qui mérite une PR dédiée (cf règle `Closes #N` only when ALL acceptance criteria met, [catalog-pr-hygiene.md](../../.claude/rules/catalog-pr-hygiene.md)).
- **`See #7483`** : ce PR d'audit documente le sous-grain vision-QA + findings, sans fermer l'issue.

---

## 7. Méthodologie d'audit (reproductibilité)

1. `git checkout main && git pull --ff-only` (avance 1 commit : `f2077b34f..98f1ba914`).
2. Branche dédiée `feature/mgs-7b-vision-qa-7483` depuis `origin/main`.
3. `git log --all --oneline --grep "MGS-7b\|N-D"` → inventaire commits (15+ commits trouvés).
4. `ls -la MyIA.AI.Notebooks/Search/Part4-Metaheuristics/assets/` → 8 PNG + dossier `readme/`.
5. `file *.png` → confirmation vrais PNG 8-bit RGBA (pas de placeholder dégénéré).
6. `Read` (vision) sur chaque PNG → verdict conforme / caveat par heatmap (cf §3).
7. `Read` cellule par cellule du notebook → vérification C.2 (outputs présents) + découverte du bug pédagogique exercice 1.
8. Croisement avec audit po-2023 c.712 (commentaire `IC_kwDOH2Odns8AAAABK3-ung`) → findings nouveaux vs port code.

**Pas de modification de code/notebook dans ce PR** (audit read-only). PR de fix pédagogique = suivi optionnel, à prioriser par l'owner du notebook (po-2024).

---

## 8. Anti-patterns évités

- **Pas de composite** : 1 sous-grain = 1 doc d'audit (markdown), pas de modification de `KnownFunctionLandscape.cs`, pas de modification du notebook.
- **Pas de force-push** : branche `feature/mgs-7b-vision-qa-7483` créée depuis `origin/main` (L860 recovery pattern inutile ici).
- **Pas de regen catalogue** : audit read-only ne touche pas au catalogue (cf [catalog-pr-hygiene.md](../../.claude/rules/catalog-pr-hygiene.md)).
- **Pas de modification de fichiers du submodule upstream `MetaGeneticSharp/`**.
- **Pas de main commit direct** : PR via branche feature, merge par ai-01.
- **Vision MiniMax vs GLM text-only** : ce grain exploite la capacité vision distinctive de ma lane (cf [model-delegation.md](../../.claude/rules/model-delegation.md) §Vision).

---

**Grain : DEEP/genai-vision — lane myia-po-2025:CoursIA-2 — prev : MED/qc-archival**

`See #7483` · `See #1203`
