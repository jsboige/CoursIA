# Pré-enregistrement — dissociation biais d'alignement / dérive précoce (Schurger 2012)

> **Statut.** Grade **T-pré-enregistrement** : protocole verrouillé avant implémentation et avant toute mesure. Ce document ne rapporte aucun résultat. Il est le « grain séparé » annoncé par le pré-enregistrement Owen/Cruse ([command-following-observers-pre-enregistrement.md](command-following-observers-pre-enregistrement.md), source 3) : la dissociation `potentiel de préparation moyen ≠ décision préalable` y était explicitement différée vers ce document.
>
> **Objet formel.** Un accumulateur stochastique borné évolue sans aucune dérive déterministe montante ; le « mouvement » est défini comme le premier franchissement d'un seuil absorbant. La question instrumentale est double : (a) la moyenne des trajectoires **alignées sur le franchissement** montre-t-elle une rampe pré-événement alors même que chaque essai est dépourvu de dérive (« biais d'alignement ») ? (b) une **dérive précoce authentique** injectée essai par essai se laisse-t-elle séparer de ce pur artefact de sélection par une grandeur **qui ne recourt pas à l'alignement sur l'événement** ?

## Source primaire

Aaron Schurger, Jacobo D. Sitt et Stanislas Dehaene, « An accumulator model for spontaneous neural activity prior to self-initiated movement », *PNAS* 109 (2012), E2904–E2913, DOI [`10.1073/pnas.1210467109`](https://doi.org/10.1073/pnas.1210467109). Lecture firsthand. Claim central mobilisé : le potentiel de préparation (RP) **moyen** qui précède un mouvement auto-initié est reproductible par un accumulateur stochastique **sans dérive déterministe**, la rampe moyenne résultant du conditionnement sur le franchissement de seuil (sélection des trajectoires au moment où elles atteignent le seuil), tandis que la même dynamique observée sans conditionnement sur le franchissement reste plate. Contexte historique, cité comme cadre et non relu ici : Kornhuber & Deecke 1965 (Bereitschaftspotential) ; Libet et al., *Brain* 106 (1983), 623–642, dont la lecture « la préparation commence avant l'intention consciente » suppose que la rampe moyenne reflète une dérive préalable réelle, essai par essai.

## Claim, contre-claim et périmètre

- **Claim testé.** L'alignement temporel sur un franchissement de seuil suffit à produire une rampe pré-événement dans la moyenne, en l'absence totale de dérive déterministe ; la vue non alignée (contrôle sham) reste plate.
- **Contre-claim adversarial (comparateur à dérive).** La rampe reflète une dérive précoce authentique présente dans chaque essai. Le banc doit montrer que la vue alignée **ne distingue pas** les deux hypothèses, mais qu'une grandeur hors-alignement (le niveau moyen non aligné) **les sépare**.
- **Non-claim.** Ce jouet n'est **ni un modèle de conscience, ni une preuve au sujet du libre arbitre**, ni une claim sur l'origine des intentions ou la neurophysiologie réelle du RP. Aucune donnée EEG n'est analysée. La seule portée est méthodologique : comment un conditionnement sur l'événement fabrique une signature moyenne, et quel instrument sépare artefact de sélection et dérive réelle.

## Modèle verrouillé

Accumulateur en temps discret (pas arbitraire ; fenêtre de 60 pas ≈ l'échelle RP-II de Libet si 1 pas ~ 10 ms) :

```text
x_{t+1} = x_t − λ·x_t + μ + σ·ε_t ,  ε_t ~ N(0, 1) iid
réflexion en 0 (x ≥ 0), seuil absorbant b : premier x_t ≥ b = « mouvement »
```

| Paramètre | Valeur | Rôle |
|---|---|---|
| λ (fuite) | `0,08` | relaxation vers le bas ; relaxation 1/λ = 12,5 pas |
| σ (bruit) | `0,06` | écart-type stationnaire σ/√(2λ−λ²) ≈ 0,153 |
| b (seuil) | `1,0` | unité des amplitudes |
| x₀ | `0,0` | départ de chaque essai |
| μ bras null (M0) | `0,00` | aucune dérive déterministe |
| μ bras comparateur (M1) | `0,03` | dérive précoce authentique, asymptote μ/λ = 0,375 = b/4 |
| essais | `2 000` par bras et par graine | — |
| t_max | `5 000` | essais non franchis comptés à part |
| graines | `(0, 1, 7, 42, 99)` | — |

Estimations a priori (analytiques, consignées **avant** mesure) : moyenne stationnaire repliée ≈ 0,12 ; temps de premier passage diffusif b²/σ² ≈ 280 pas ; pente alignée attendue de l'ordre de (b − 0,12)/50 ≈ 0,018 par pas. Les bandes ci-dessous sont posées avec des marges ≥ 3× sur ces ordres de grandeur ; **aucun recalibrage post-mesure ne sera fait**.

### Bras et flux aléatoires

Quatre flux `numpy.random.default_rng`, dérivés de la graine par offsets verrouillés : essais M0 = `graine` ; essais M1 = `graine + 10 000` ; sham M0 = `graine + 20 000` ; sham M1 = `graine + 30 000`. À chaque pas, le bruit est tiré pour l'intégralité des essais (le flux ne dépend donc pas du sous-ensemble d'essais encore actifs).

### Analyse (verrouillée)

- Ensemble analysé : essais dont l'indice de premier franchissement `c ≥ 61`. Les exclusions (franchissements trop précoces, essais non franchis) sont **comptées et rapportées**, jamais silencieuses.
- **Alignement vrai** : fenêtre des 60 derniers pas `[c−59, c]`, point d'événement inclus.
- **Alignement sham** (contrôle null, mêmes essais) : instant `a` tiré uniformément dans `{60, …, c−1}` ; fenêtre `[a−59, a]`.
- Grandeurs par bras : `pente` (OLS sur la moyenne des 60 points), `moyenne_précoce` (15 premiers points), `moyenne_tardive` (15 derniers), `amplitude = tardive − précoce`, `moyenne_sham` et `pente_sham` (fenêtre sham).

## Prédictions falsifiables

Les seuils ci-dessous sont verrouillés avant implémentation. Chaque critère s'applique par graine ; « passer » exige ≥ 4 graines sur 5.

| ID | Prédiction | Critère par graine | Lecture si échec |
|---|---|---|---|
| **P1 — rampe par sélection seule** | Sans aucune dérive (M0), l'alignement sur le franchissement produit une rampe pré-événement. | `pente_alignée(M0) ≥ 0,004` **et** `pente_alignée(M0) ≥ 5·\|pente_sham(M0)\|` | La sélection sur franchissement ne suffit pas à reproduire la signature : le modèle n'instancie pas la claim. |
| **P2 — contrôle null plat** | Le même essai, aligné sur un instant non informatif, ne montre pas de rampe. | `\|pente_sham(M0)\| ≤ 0,0010` | La métrique de rampe tire des faux positifs sans conditionnement : instrument invalide. |
| **P3 — l'aligné n'est pas discriminant** | La vue alignée seule ne peut pas départager artefact de sélection et dérive réelle. | `pente_alignée(M0) ≥ 0,004` **et** `pente_alignée(M1) ≥ 0,004` | La vue alignée suffirait à distinguer les deux hypothèses, ce qui affaiblirait la lecture Schurger du présent jouet. |
| **P4 — le discriminant hors-alignement sépare** | Une dérive authentique laisse une trace **sans** alignement : le niveau sham du bras M1 dépasse celui du bras M0. | `moyenne_sham(M1) − moyenne_sham(M0) ≥ 0,15` | L'instrument hors-alignement ne sépare pas les deux hypothèses : la dissociation revendiquée n'est pas mesurable ici. |
| **P5 — localisation de l'artefact** | L'artefact de sélection est concentré près de l'événement : loin de l'événement, l'aligné rejoint le sham. | `amplitude(M0) ≥ 0,25` **et** `\|moyenne_précoce(M0) − moyenne_sham(M0)\| ≤ 0,10` | La signature n'est pas localisée : le banc ne trace pas la frontière artefact/dérive attendue. |

### Verdict (tri-état honnête)

- `SUPPORTED` si P1–P5 passent toutes (chacune ≥ 4/5 graines).
- `FALSIFIED_MODEL` si P1 ou P2 échoue : le banc ne reproduit pas l'artefact de sélection, ou son contrôle null tire des faux positifs.
- `INCONCLUSIVE` si P1 et P2 passent mais que P3, P4 ou P5 échoue : l'artefact est reproduit, l'instrument de discrimination est insuffisant.

Un échec est conservé et rapporté tel quel dans le JSON de résultats.

## Contrôles instrumentaux

- **Déterminisme** : même graine → trajectoires, fenêtres et métriques identiques bit à bit.
- **Sémantique de franchissement** : l'indice de franchissement est le **premier** `t` avec `x_t ≥ b`, la valeur `x_t` du franchissement appartenant à la fenêtre ; la réflexion garantit `x ≥ 0` en tout point ; cas déterministe pur (`σ = 0`, `μ > 0`, `λ = 0`) → franchissement exact à `⌈b/μ⌉`.
- **Essai sans événement** : `σ = 0` et `μ = 0` → aucun franchissement ; un bras sans essai analysable lève une erreur explicite plutôt qu'une métrique fabriquée.
- **Domaines** : rejet de `σ < 0`, `λ ∉ [0, 1)`, `b ≤ 0`, `μ < 0`, tailles non positives.

## Livrables d'exécution

La tranche suivante, dans un commit distinct, portera :

- `MyIA.AI.Notebooks/IIT/ICT-Series/ict/threshold_alignment.py` ;
- `MyIA.AI.Notebooks/IIT/ICT-Series/ict/tests/test_threshold_alignment.py` ;
- `MyIA.AI.Notebooks/IIT/ICT-Series/ict/threshold_alignment_results.json`, produit par exécution réelle du module.

Aucun notebook ni sortie de cellule n'est modifié. Le registre [`dissociations-matrix.md`](dissociations-matrix.md) reste hors scope : le rattachement éventuel de ce résultat relève d'une tranche ultérieure de sa lane propriétaire.
