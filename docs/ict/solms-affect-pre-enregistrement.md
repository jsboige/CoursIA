# Pré-enregistrement — réalisation de pertinence : l'affect comme forme élémentaire de la conscience (Solms & Friston)

**Issue :** #8182 (veille et distillation progressive, candidat Solms)
**Lane :** `myia-po-2028:CoursIA-2`
**Scellé :** 2026-11-08, **avant** toute implémentation et avant toute exécution sur les graines d'étude.

Ce document fixe les grandeurs mesurées, les bras comparés, les prédictions et leurs bandes **avant** de coder le module. Il est révisable une seule fois, par un commit distinct qui dit ce qui a changé et pourquoi (protocole de scellement v1 → v2 de la tranche Schurger, #13459) ; toute révision antérieure à l'évaluation held-out reste visible dans l'historique git.

---

## 1. Source, provenance et ce qui est attribué

**Référence lue :** Solms M, Friston KJ (2018), « The Hard Problem of Consciousness and the Free Energy Principle », *Frontiers in Psychology* 9:2714, DOI `10.3389/fpsyg.2018.02714`, CC-BY.

**Copie archivée :** `G:\Mon Drive\MyIA\IA\Bibliographie IA\Consciousness\2018 - Solms, Friston - The Hard Problem of Consciousness and the Free Energy Principle (Front Psychol 9-2714, CC-BY, OA).html`

Les passages sur lesquels repose ce carnet, cités verbatim depuis le texte extrait de cette copie (section Abstract + alinéa structurel, lus firsthand le 2026-11-08) :

1. « it identifies the elemental form of consciousness as *affect* and locates its physiological mechanism (an extended form of homeostasis) in the upper brainstem. » (Abstract)
2. « This mechanism is then formalized in terms of free energy minimization (in unpredicted contexts) where decreases and increases in expected uncertainty are felt as pleasure and unpleasure, respectively. » (Abstract)
3. « The second reconsiders the anatomical localization of consciousness (the so-called neural correlate of consciousness or NCC) in the cerebral cortex. In consequence, it reconceptualizes the functional roles of the "level" vs. "contents" of consciousness. » (alinéa structurel, § 2)

**Ce que l'article soutient et que ce carnet ne teste pas.** L'article défend aussi le dual-aspect monisme, clarifie des points de fonctionnalisme, et annonce un traitement de livre (*Consciousness Itself*). Aucune prédiction ci-dessous ne prétend réfuter ou confirmer ces thèses philosophiques : on ne teste **pas** la thèse métaphysique, on teste la **partie opérationnelle** que les citations 1–3 explicitent (affect = forme élémentaire ; mécanisme homeostatique formalisé par l'énergie libre ; dissociation level/contents ; localisation subcorticale), sur un terrain fini et déclaré.

**Grade de provenance.** Les citations sont de grade A (copie archivée, lue). L'**opérationnalisation** qui suit est de grade C : c'est une **traduction choisie par cette lane**, pas une mesure que l'article revendique. Aucune phrase du carnet ne présentera l'opérationnalisation comme un résultat de l'article.

---

## 2. Surrogate déclaré

**Terrain.** Un organisme tient `d = 4` variables homéostatiques `x_t ∈ R^d` autour de points consignes `x*`. Un exogène (marche aléatoire bruitée) perturbe `x_t` ; un contrôleur homéostatique le ramène vers `x*`. L'incertitude attendue `U_t` (proxie du « expected uncertainty » de la citation 2) est l'EMA de l'erreur homéostatique au carré : `U_t = α·‖x_t − x*‖² + (1−α)·U_{t-1}`, `α = 0,2`. Sur `T = 300` pas, `U_t` monte quand la perturbation s'accumule, descend quand le contrôleur restaure — `ΔU_t` prend les deux signes.

**Deux architectures, même terrain, mêmes graines :**

| Bras | Architecture | Ablation |
|---|---|---|
| `intact` | **H₁** (Solms) : affect généré subcorticalement par `a_t = −k_a·ΔU_t` ; contents = lecture corticale `c_t = W x_t` | aucune |
| `no_cortex` | **H₁** | canal cortical retiré → `c_t = 0` (contents supprimés) |
| `no_subcortex` | **H₁** | générateur subcortical retiré → `a_t = 0` (affect supprimé) |
| `null_cortical` | **H₀** (null) : affect calculé **à partir des contents** `a_t = φ(c_t)` | canal cortical retiré → `a_t = 0` |

La différence H₁/H₀ est le cœur du test : en **H₁** l'affect est produit par la **dynamique homéostatique** (subcortical), en **H₀** il est un **readout cortical des contents**. Le null H₀ est le régime adverse : s'il ne se distingue pas de H₁, le protocole n'isole pas le générateur subcortical.

**Métriques** (par bras, sur les `T` pas) :
- `feel` = `mean_t |a_mesure_t|`, où `a_mesure = a + η·N(0,1)` (η fixé pour que la corrélation mécanisme/bruit soit ~0,8, non triviale).
- `content_rich` = variance échantillon de la trajectoire `c_t` (somme des variances coordonnées) — mesure de la richesse des contents.
- `valence_tracks_dU` = corrélation de Pearson `corr(a_mesure, −ΔU)` sur la trajectoire (la citation 2 : −ΔU = plaisir).

**Déterminisme.** Tout est graine-fixe ; `numpy.random.default_rng(seed)`. Aucune dépendance hors stdlib + numpy.

---

## 3. Prédictions pré-enregistrées

Toutes portent sur les graines d'étude `(0, 1, 7, 42, 99)` ; les bandes sont **fixées ici**, avant le pilote de calibration (graine `1000`, disjointe, hors étude).

| # | Prédiction | Bande préfixée | Réfutation |
|---|---|---|---|
| **P1** | Le **level** survit à l'ablation corticale (conscience sans cortex). | `feel(no_cortex)/feel(intact) ≥ 0,5` sur **chaque** graine d'étude | une seule graine sous la bande ⇒ réfutée |
| **P2** | L'affect **suit le mécanisme** énergie-libre (−ΔU = plaisir). | `valence_tracks_dU(intact) ≥ 0,7` sur la **médiane** des graines | médiane < 0,7 ⇒ réfutée |
| **P3** | Le générateur est **subcortical** : le retirer supprime l'affect. | `feel(no_subcortex)/feel(intact) ≤ 0,2` sur **chaque** graine | une seule graine au-dessus ⇒ réfutée |
| **P4** | La dissociation est **spécifique** à l'architecture H₁, pas un artefact. | `[feel(no_cortex)/feel(intact)]_H1 − [feel(no_cortex)/feel(intact)]_H0 ≥ 0,3` sur la **médiane** | médiane < 0,3 ⇒ réfutée |
| **P5** | Les **contents** sont corticaux : l'ablation corticale les supprime. | `content_rich(no_cortex)/content_rich(intact) ≤ 0,3` sur **chaque** graine | une seule graine au-dessus ⇒ réfutée |

**Verdict.** `SUPPORTED` si P1–P5 tiennent toutes sur les 5 graines ; `PARTIAL` si P1 et P2 tiennent et au moins deux des trois autres (P3, P4, P5) ; `REFUTED` sinon. Un verdict `PARTIAL` se publie tel quel, avec la liste exacte des prédictions tombées.

**Contre-régime explicité d'avance.** (i) Si P3 tombe (`no_subcortex` ne supprime pas l'affect), l'affect ne serait **pas** spécifiquement généré subcorticalement — la traduction de la citation 1 discriminerait mal ; publié comme tel. (ii) Si P4 tombe (le null H₀ survit aussi à l'ablation corticale), le modèle n'isole **pas** le générateur subcortical d'un readout cortical — la dissociation level/contents n'est pas établie par ce terrain ; publié comme tel.

---

## 4. Ce qui ne sera pas fait

- Aucun ajustement de bande après lecture des graines d'étude. Un ajustement post-pilote est possible **avant** l'étude et se commit séparément (v2), en nommant la valeur v1 et la raison.
- Aucune généralisation à la thèse de dual-aspect monisme ni au programme de livre de l'article.
- Aucun terrain/paramètre choisi pour favoriser H₁ : le terrain, les deux architectures, les seuils et les métriques sont écrits avant le module et ne dépendent pas des résultats.
