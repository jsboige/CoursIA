# Pré-enregistrement — dissociation biais d'alignement / dérive précoce (Schurger 2012)

> **Statut.** Grade **T-pré-enregistrement** : scellage v1 avant implémentation ; re-verrouillage v2 après un **pilote exploratoire** limité à la graine 1000 (disjointe des graines d'étude) et **avant toute évaluation des gates P1–P5**. Ce document ne rapporte aucun résultat d'évaluation. Il est le « grain séparé » annoncé par le pré-enregistrement Owen/Cruse ([command-following-observers-pre-enregistrement.md](command-following-observers-pre-enregistrement.md), source 3) : la dissociation `potentiel de préparation moyen ≠ décision préalable` y était explicitement différée vers ce document.
>
> **Amendement v2 (2026-08-29, commit suivant le scellage initial).** Les paramètres v1 se sont révélés **infaisables avant toute évaluation de gate** (§« Amendement v2 »). Le re-verrouillage documenté ci-dessous a eu lieu après un pilote exploratoire — implémentation de faisabilité et métriques descriptives mesurées sur la seule graine 1000, disjointe des graines d'étude — et **avant la première évaluation des gates P1–P5** ; l'historique v1 reste visible au commit de scellage initial.
>
> **Objet formel.** Un accumulateur stochastique borné évolue sans aucune dérive déterministe montante ; le « mouvement » est défini comme le premier franchissement d'un seuil absorbant. La question instrumentale est double : (a) la moyenne des trajectoires **alignées sur le franchissement** montre-t-elle une rampe pré-événement alors même que chaque essai est dépourvu de dérive (« biais d'alignement ») ? (b) une **dérive précoce authentique** injectée essai par essai se laisse-t-elle séparer de ce pur artefact de sélection par une grandeur **qui ne recourt pas à l'alignement sur l'événement** ?

## Source primaire

Aaron Schurger, Jacobo D. Sitt et Stanislas Dehaene, « An accumulator model for spontaneous neural activity prior to self-initiated movement », *PNAS* 109 (2012), E2904–E2913, DOI [`10.1073/pnas.1210467109`](https://doi.org/10.1073/pnas.1210467109). Lecture firsthand. Claim central mobilisé : le potentiel de préparation (RP) **moyen** qui précède un mouvement auto-initié est reproductible par un accumulateur stochastique **sans dérive déterministe**, la rampe moyenne résultant du conditionnement sur le franchissement de seuil (sélection des trajectoires au moment où elles atteignent le seuil), tandis que la même dynamique observée sans conditionnement sur le franchissement reste plate. Contexte historique, cité comme cadre et non relu ici : Kornhuber & Deecke 1965 (Bereitschaftspotential) ; Libet et al., *Brain* 106 (1983), 623–642, dont la lecture « la préparation commence avant l'intention consciente » suppose que la rampe moyenne reflète une dérive préalable réelle, essai par essai.

## Claim, contre-claim et périmètre

- **Claim testée.** L'alignement temporel sur un franchissement de seuil suffit à produire une rampe pré-événement dans la moyenne, en l'absence totale de dérive déterministe ; la vue non alignée (contrôle sham) reste plate.
- **Contre-claim adversarial (comparateur à dérive).** La rampe reflète une dérive précoce authentique présente dans chaque essai. Le banc doit montrer que la **présence d'une rampe dans la vue alignée** ne suffit pas à distinguer les deux hypothèses, mais qu'une grandeur hors-alignement (le niveau moyen non aligné) **les sépare**.
- **Non-claim.** Ce jouet n'est **ni un modèle de conscience, ni une preuve au sujet du libre arbitre**, ni une claim sur l'origine des intentions ou la neurophysiologie réelle du RP. Aucune donnée EEG n'est analysée. La seule portée est méthodologique : comment un conditionnement sur l'événement fabrique une signature moyenne, et quel instrument sépare artefact de sélection et dérive réelle.

## Amendement v2 — pilote exploratoire, puis re-verrouillage held-out

Le scellage v1 (λ = 0,08 ; σ = 0,06 ; b = 1) posait des bandes dérivées d'une estimation de premier passage **purement diffusive**, ignorant la traction de fuite vers le bas. L'échelle de Kramers réelle, λ(b−m)²/σ² ≈ 22, rend le franchissement inatteignable : une exécution de faisabilité a produit **0 franchissement sur 2 000 essais × 5 000 pas**, donc aucune métrique évaluable — l'infaisabilité est un fait de simulation, pas un verdict. Sceller un protocole dont l'événement central est inatteignable garantit un faux résultat lu ensuite comme une mesure : ce chemin v1 est **fermé et documenté**, sur le précédent du pré-enregistrement Čech (chemin mort-né fermé avant mesure).

Le re-verrouillage v2 repose sur un **pilote exploratoire** : une implémentation de faisabilité exécutée sur la seule graine 1000 — disjointe des graines d'étude (0, 1, 7, 42, 99) — dont les métriques descriptives (temps de franchissement, niveaux stationnaires, pentes) ont servi à calibrer les échelles. Le protocole v2 est ensuite **held-out** : aucune gate P1–P5 n'a été évaluée avant ce re-verrouillage, et l'évaluation ne porte que sur les graines d'étude. Métriques du pilote (à distinguer de l'évaluation held-out) : M0 → 1 871/2 000 essais analysables, temps de franchissement moyen 759 (queue lourde), pente alignée 0,0061, pente sham 0,0002, amplitude 0,28, niveau sham 0,216 ; M1 → 1 273/2 000 analysables, pente alignée 0,0051, niveau sham 0,343, élévation 0,127. Les bandes ci-dessous sont posées avec des marges ≥ 2× sur ces échelles du pilote ; **aucun recalibrage des gates après l'évaluation held-out ne sera fait**.

## Modèle verrouillé (v2)

Accumulateur en temps discret (pas arbitraire ; fenêtre de 60 pas ≈ l'échelle RP-II de Libet si 1 pas ~ 10 ms) :

```text
x_{t+1} = x_t − λ·x_t + μ + σ·ε_t ,  ε_t ~ N(0, 1) iid
réflexion en 0 (x ≥ 0), seuil absorbant b : premier x_t ≥ b = « mouvement »
```

| Paramètre | Valeur | Rôle |
|---|---|---|
| λ (fuite) | `0,10` | relaxation vers le bas ; relaxation 1/λ = 10 pas |
| σ (bruit) | `0,15` | niveau stationnaire calibré : moyenne ≈ 0,22, écart-type ≈ 0,22 |
| b (seuil) | `1,0` | unité des amplitudes |
| x₀ | `0,0` | départ de chaque essai (réinitialisation post-franchissement, convention Schurger) |
| μ bras null (M0) | `0,00` | aucune dérive déterministe |
| μ bras comparateur (M1) | `0,035` | dérive précoce authentique, asymptote μ/λ = 0,35 ≈ b/3 |
| essais | `2 000` par bras et par graine | — |
| t_max | `5 000` | essais non franchis comptés à part |
| graines | `(0, 1, 7, 42, 99)` | — |

Temps de franchissement calibrés : M0 moyen ≈ 760 pas (médiane ≈ 540, queue lourde — l'attente « spontanée » est sans mémoire à longue échéance, comme dans le modèle Schurger) ; M1 moyen ≈ 120 pas. Les exclusions M1 par franchissement précoce (c < 61), de l'ordre du tiers des essais, sont **comptées et rapportées par graine** — c'est le prix de l'accélération déterministe, pas un silence d'instrument.

### Bras et flux aléatoires

Quatre flux `numpy.random.default_rng`, dérivés de la graine par offsets verrouillés : essais M0 = `graine` ; essais M1 = `graine + 10 000` ; sham M0 = `graine + 20 000` ; sham M1 = `graine + 30 000`. À chaque pas, le bruit est tiré pour l'intégralité des essais (le flux ne dépend donc pas du sous-ensemble d'essais encore actifs).

### Analyse (verrouillée)

- Ensemble analysé : essais dont l'indice de premier franchissement `c ≥ 61`. Les exclusions (franchissements trop précoces, essais non franchis) sont **comptées et rapportées**, jamais silencieuses.
- **Alignement vrai** : fenêtre des 60 derniers pas `[c−59, c]`, point d'événement inclus.
- **Alignement sham** (contrôle null, mêmes essais) : instant `a` tiré uniformément dans `{60, …, c−1}` ; fenêtre `[a−59, a]`.
- Grandeurs par bras : `pente` (OLS sur la moyenne des 60 points), `moyenne_précoce` (15 premiers points), `moyenne_tardive` (15 derniers), `amplitude = tardive − précoce`, `moyenne_sham` et `pente_sham` (fenêtre sham).

## Prédictions falsifiables (bandes v2)

Chaque critère s'applique par graine ; « passer » exige ≥ 4 graines sur 5. Les bandes remplacent celles (dérivées diffusive) du scellage v1, selon la même politique de marge, sur les échelles du pilote ci-dessus, et sont verrouillées **avant l'évaluation held-out** sur les graines d'étude.

| ID | Prédiction | Critère par graine | Lecture si échec |
|---|---|---|---|
| **P1 — rampe par sélection seule** | Sans aucune dérive (M0), l'alignement sur le franchissement produit une rampe pré-événement. | `pente_alignée(M0) ≥ 0,0030` **et** `pente_alignée(M0) ≥ 5·\|pente_sham(M0)\|` | La sélection sur franchissement ne suffit pas à reproduire la signature : le modèle n'instancie pas la claim. |
| **P2 — contrôle null plat** | Le même essai, aligné sur un instant non informatif, ne montre pas de rampe. | `\|pente_sham(M0)\| ≤ 0,0010` (5× la pente sham calibrée 0,0002) | La métrique de rampe tire des faux positifs sans conditionnement : instrument invalide. |
| **P3 — la rampe alignée n'est pas discriminante** | La **présence d'une rampe** pré-événement dans la vue alignée ne départage pas artefact de sélection et dérive réelle : les deux bras rampent au-dessus du plancher. | `pente_alignée(M0) ≥ 0,0030` **et** `pente_alignée(M1) ≥ 0,0030` | La présence d'une rampe alignée suffirait à distinguer les deux hypothèses, ce qui affaiblirait la lecture Schurger du présent jouet. |
| **P4 — le discriminant hors-alignement sépare** | Une dérive authentique laisse une trace **sans** alignement : le niveau sham du bras M1 dépasse celui du bras M0. | `moyenne_sham(M1) − moyenne_sham(M0) ≥ 0,060` (≈ moitié de l'élévation calibrée 0,127) | L'instrument hors-alignement ne sépare pas les deux hypothèses : la dissociation revendiquée n'est pas mesurable ici. |
| **P5 — localisation de l'artefact** | L'artefact de sélection est concentré près de l'événement : loin de l'événement, l'aligné rejoint le sham. | `amplitude(M0) ≥ 0,14` (≈ moitié de l'amplitude calibrée 0,28) **et** `\|moyenne_précoce(M0) − moyenne_sham(M0)\| ≤ 0,10` | La signature n'est pas localisée : le banc ne trace pas la frontière artefact/dérive attendue. |

### Verdict (tri-état honnête)

- `SUPPORTED` si P1–P5 passent toutes (chacune ≥ 4/5 graines).
- `FALSIFIED_MODEL` si P1 ou P2 échoue : le banc ne reproduit pas l'artefact de sélection, ou son contrôle null tire des faux positifs.
- `INCONCLUSIVE` si P1 et P2 passent mais que P3, P4 ou P5 échoue : l'artefact est reproduit, l'instrument de discrimination est insuffisant.

Un échec est conservé et rapporté tel quel dans le JSON de résultats.

### Limites d'interprétation déclarées

- **Portée exacte de P3.** P3 n'établit pas que la vue alignée *tout entière* serait indistinguable entre les deux bras : il porte uniquement sur la **présence d'une rampe** au-dessus du plancher scellé. D'autres statistiques de la vue alignée (niveau tardif, amplitude) pourraient départager les bras ; aucune claim d'indistingabilité globale n'est faite. La clé JSON `P3_aligned_view_not_discriminant`, figée dans l'artefact généré, est historique et ne doit pas être lue au-delà de cette portée.
- La fenêtre sham du bras M1 contient une pente résiduelle ≤ 0,001, trace du transitoire de montée (0 → 0,35) : un ordre de grandeur sous la pente d'artefact (~0,006). Le discriminant P4 porte sur le **niveau** sham, pas sur sa pente.
- La fraction d'essais M1 exclus (franchissement trop précoce) est une sélection réelle, rapportée par graine ; elle borne la généralité de la comparaison aux mouvements « tardifs ».
- Un pas de temps ≠ une milliseconde ; l'échelle RP-II n'est qu'une correspondance d'ordre de grandeur.

## Contrôles instrumentaux

- **Déterminisme** : dans un **même environnement** (même plateforme, même build NumPy), même graine → trajectoires, fenêtres et métriques identiques **bit à bit**. **Entre plateformes**, la génération des tirages gaussiens et l'ordre des sommations NumPy peuvent différer de quelques ULP sur les seuls flottants ; la structure discrète (clés des objets, longueurs et ordre des listes, chaînes, booléens, entiers — donc gates et verdict) est invariante. Le test de reproduction du JSON committé exige cette structure discrète exacte et compare les flottants en tolérance croisée-plateforme (`pytest.approx` avec `rel=1e-12`, `abs=1e-15`), largement au-dessus de l'écart ULP observé et largement en-deçà des bandes des gates.
- **Sémantique de franchissement** : l'indice de franchissement est le **premier** `t` avec `x_t ≥ b`, la valeur `x_t` du franchissement appartenant à la fenêtre ; la réflexion garantit `x ≥ 0` en tout point ; cas déterministe pur (`σ = 0`, `μ > 0`, `λ = 0`) → franchissement exact à `⌈b/μ⌉`.
- **Essai sans événement** : `σ = 0` et `μ = 0` → aucun franchissement ; un bras sans essai analysable lève une erreur explicite plutôt qu'une métrique fabriquée.
- **Domaines** : rejet de `σ < 0`, `λ ∉ [0, 1)`, `b ≤ 0`, `μ < 0`, tailles non positives.

## Livrables d'exécution

La tranche suivante, dans un commit distinct, portera :

- `MyIA.AI.Notebooks/IIT/ICT-Series/ict/threshold_alignment.py` ;
- `MyIA.AI.Notebooks/IIT/ICT-Series/ict/tests/test_threshold_alignment.py` ;
- `MyIA.AI.Notebooks/IIT/ICT-Series/ict/results/threshold_alignment_results.json`, produit par exécution réelle du module.

Aucun notebook ni sortie de cellule n'est modifié. Le registre [`dissociations-matrix.md`](dissociations-matrix.md) reste hors scope : le rattachement éventuel de ce résultat relève d'une tranche ultérieure de sa lane propriétaire.
