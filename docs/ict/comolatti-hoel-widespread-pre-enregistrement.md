# Pré-enregistrement — L'émergence causale est-elle répandue ? (case 26 : les mesures de causation au coarse-graining)

> **Grade C explicite.** Ce document **scelle** le protocole de la tranche « émergence causale répandue / mesures de causation » de la veille [#8182](https://github.com/jsboige/CoursIA/issues/8182) **AVANT toute écriture du banc de mesure** — même discipline que le case 25 ([`hoel-causal-emergence-pre-enregistrement.md`](hoel-causal-emergence-pre-enregistrement.md)) : source primaire lue et archivée, pré-enregistrement commité avant l'implémentation et la mesure (commit dédié, séparé du banc), verdict borné.
>
> **Cycle du 2026-11-21**, lane `myia-po-2024:CoursIA`. Claim : [c.7066972471](https://github.com/jsboige/CoursIA/issues/8182#issuecomment-7066972471) (paths : banc, tests, résultats JSON et ce document). Désengorgement manuel documenté dans le corps du claim (quota GitHub atteint sur la garde).

## 1. Source primaire et archivage

**Source primaire** : Milan Comolatti, Erik P. Hoel, « Causal emergence is widespread across measures of causation », *Entropy* — prépublication receptive, 7 février 2022. **Archivage gisement** ([bibliography-hygiene](../../.claude/rules/bibliography-hygiene.md)) : `G:\Mon Drive\MyIA\IA\Bibliographie IA\Probabilistic\2022 - Comolatti Hoel - Causal emergence is widespread across measures of causation.pdf` — copie préexistante du rayon (recherche auteur ET titre : `comolatti`, `hoel`, `widespread`), 3 418 284 octets, vingt-deux pages, **identité vérifiée sur la première page** (Milan Comolatti / Erik P. Hoel, Tufts). Un seul dépôt.

**Méthode de lecture** : texte intégral extrait (`pypdf`) puis **relecture firsthand** par la lane — primitives et taxonomie (section 3), modèle bipartite et distributions d'intervention (section 4), démonstration de l'émergence répandue (Figs. 3-5), discussion (section 6). **Limite déclarée** : la paramétrisation précise du modèle bipartite (dégradés de déterminisme/dégénérescence des Figs. 3-5) vit dans le **Supplément §7.1, non archivé** dans ce PDF ; les heatmaps quantitatives du papier ne sont donc **pas reproductibles** depuis la seule source archivée — le banc les remplace par des coins analytiques dérivables (§5, H4), et cette exclusion est écrite.

## 2. Le cadre en deux phrases

Chaque mesure de causation examined par le papier — de Galton à Pearl en passant par Eells, Suppes, Lewis, Cheng — se décompose en **primitives causales** : suffisance `suff(e,c) = P(e|c)` et nécessité `nec(e,c) = P(e|C\c)`, généralisées au niveau système en **déterminisme** et **dégénérescence** (p. 9 : « *Across every measure of causation we examined the two primitives […] are explicitly put in some relationship* ») ; l'information effective elle-même n'est que `EI = log₂(n)·[det − deg]` (p. 9). Si toutes les mesures sont des fonctions des mêmes primitives, alors le coarse-graining — qui peut accroître `det` et réduire `deg` — doit déplacer **toutes** les mesures ensemble : c'est le claim du titre, démontré par le papier sur un modèle bipartite dont le macro (porte NON à deux états) reste « *deterministic, non-degenerate […] no matter the underlying noise in the microscale* » (p. 14), et dont la conclusion quantitative est que « *causal emergence occurs when the microscale is noisy* » (Fig. 5, p. 16).

**Point de contact avec la veille ICT** : le case 25 a établi le renversement EI-macro sur le système Fig. 4 de Hoel 2013 (EI micro 2.4338 → macro 3.0, vérifié organe) et son témoin négatif. Ce case demande la question d'après : **ce renversement est-il un artefact du choix d'EI, ou une propriété partagée par toute mesure décomposable en primitives ?**

## 3. Question falsifiable

**Le déplacement des mesures de causation au coarse-graining est-il prédit par leur décomposition en primitives causales ?**

Cinq sous-questions, une par énoncé distinct :

- **H1 (répandu, directionnel)** : sur le système calibré du case 25 (cycle de paires dupliquées, Fig. 4 de Hoel 2013 ; micro déterministe et dégénéré, macro COPY déterministe et non dégénéré), les mesures du panel **sensibles à la dégénérescence** montrent toutes un avantage macro strict.
- **H1b (saturation analytique de Cheng)** : la mesure de Cheng est **saturée** sur ce micro (toute cause entièrement suffisante donne PS = 1, quel que soit le reste) : avantage macro **exactement nul** — égalité ponctuelle, pas une défaillance du panel.
- **H2 (témoin bidirectionnel)** : sur le témoin du case 25 (COPY bruitées indépendantes, p = 0.1), là où l'organe donne CE ≤ 0, le **panneau médian** des mesures ne montre pas d'avantage macro — « répandu » vaut dans les deux sens.
- **H3 (explication par les primitives)** : à travers tous les points mesurés (systèmes × regroupements, section 4), le déplacement de chaque mesure est **monotone** dans le mouvement net des primitives `(Δdet − Δdeg)` (corrélation de rang de Spearman > 0).
- **H4 (le macro gagne quand le micro est bruité)** : sur la reconstruction bipartite bornée (section 4), chaque mesure passe de son coin propre à son coin bruité dans le sens prédit par la Fig. 5 : l'avantage macro croît strictement avec le bruit du micro, coin propre → coin bruité.

**Ce que ce banc n'est pas.** Il ne reproduit pas les heatmaps quantitatives du papier (paramétrisation du Supplément non archivée — exclusion écrite, remplacée par les coins analytiques) ; il ne teste pas les mesures à métrique (Lewis CPW, bit-flip : elles exigent une sémantique de « monde le plus proche » que le papier lui-même n'a pas décomposée — le banc ne prétend rien pour elles) ; il ne dit rien de systèmes biologiques réels.

## 4. Le substrat et l'instrument (scellés)

**Substrats** (TPM énumérées exactement, aucun Monte-Carlo — `stochastic: false` dans le JSON de résultats) :

- **S1 — système calibré case 25** : cycle de paires dupliquées (Fig. 4 de Hoel 2013), constructeur et regroupement repris du banc case 25, valeurs de référence vérifiées par Hermes (EI micro 2.4338, deg 0.5944 ; macro EI 3.0, Eff 1.0).
- **S2 — témoin case 25** : COPY bruitées indépendantes (p = 0.1), avec ses regroupements légaux énumérés.
- **S3 — reconstruction bipartite bornée** : seize micro-états en deux groupes (bit de tête), chaque état c du groupe A vise une **cible principale** `m(c)` du groupe B (bijection A ↔ B scellée) ; bruit symétrique de sortie vers le groupe cible : `P(c → m(c)) = 1 − ε + ε/8`, `P(c → autre état du groupe cible) = ε/8`, et symétriquement B → A ; grille scellée `ε ∈ {0, 0.25, 0.5, 0.75, 1}` (ε = 0 : bijection propre ; ε = 1 : uniforme sur le groupe cible) ; macro = porte NOT à deux états (regroupement des deux groupes), déterministe et non dégénéré **indépendamment de ε** (p. 14). L'axe « empilement » (dégénérescence de cible) du papier est **exclu** (Supplément non archivé).

**Instrument (organ-first)** :

1. **L'organe natif** [`ict.causal_emergence`](../../MyIA.AI.Notebooks/IIT/ICT-Series/ict/causal_emergence.py) fournit `determinism`, `degeneracy`, `effective_information`, `causal_profile` et `partition_profile(groups)` — invoqué pour **toute** valeur det/deg/EI et **tout** coarse-graining, jamais réimplémenté.
2. **Le panel des mesures** (nouveau code du banc, formules imprimées pp. 5-7, toutes sur TPM nue) — liste close : Eells `= P(e|c) − P(e|C\c)` ; Galton `= P(c)·P(C\c)·[P(e|c) − P(e|C\c)]` ; Suppes `= P(e|c) − P(e|C)` ; Suppes II `= P(e|c)/P(e|C)` ; Lewis (PN) `= [P(e|c) − P(e|C\c)]/P(e|c)` ; Cheng (PS) `= [P(e|c) − P(e|C\c)]/[1 − P(e|C\c)]` — la section Pearl (p. 7) scelle l'identification : PNS = Eells, PN = Lewis, PS = Cheng. L'EI de l'organe est la ligne de référence du panel.
3. **Agrégation système scellée** : `sys(m) = Σ_{(c,e)} P(c,e)·CS_m(c,e)` avec `P(c,e) = TPM[c,e]/n` (intervention max-entropie sur les causes — la convention d'EI, p. 11) ; pour les mesures ratio (Suppes II, Lewis, Cheng) : support restreint aux transitions définies (dénominateur > 0), somme **renormalisée** par la masse du support. Conventions écrites une fois, appliquées à l'identique aux deux échelles.

**Le déplacement mesuré** est `ΔCS_m = sys_m(macro) − sys_m(micro)` pour chaque mesure m du panel, aux côtés de `Δdet − Δdeg` (organe).

## 5. Prédictions scellées (aucune bande ne sera recalculée après mesure)

### Portes instrumentales (dormantes par construction, mesurées quand même)

| # | Porte | Critère | Si déclenchée |
|---|---|---|---|
| **G1** | double implémentation du panel | chaque `CS_m` calculée (a) par formule directe imprimée et (b) par substitution des primitives `suff`/`nec`, accord à `1e-12` sur **toutes** les transitions mesurées | `INSTRUMENT_INVALIDE`, aucune hypothèse évaluée |
| **G2** | cas analytiques | bijection à n états : Eells `sys = 1`, Lewis `= 1`, Cheng `= 1`, Suppes `= 1 − 1/n`, Suppes II `= n`, Galton `sys = (n−1)/n²` ; TPM uniforme : Eells = Galton = Suppes = Lewis = Cheng `sys = 0`, Suppes II `= 1` | `INSTRUMENT_INVALIDE` |
| **G3** | calibrage sur le case 25 | sur S1, l'organe reproduit ses valeurs vérifiées Hermes (EI micro 2.4338 ± 0.001, EI macro 3.0 exact, deg micro 0.5944 ± 0.001) **et** la ligne EI du panel coïncide avec l'EI de l'organe à `1e-9` | `INSTRUMENT_INVALIDE` |
| **G4** | gardes de légalité | les regroupements illégaux (identité d'éléments requise) sont rejetés par la garde héritée du banc case 25 | `INSTRUMENT_INVALIDE` |

### H1 — répandu, directionnel (S1)

Les mesures **sensibles à la dégénérescence** du panel — Eells, Galton, Suppes, Suppes II, Lewis (liste close) — montrent **toutes** `ΔCS > 0` strict sur S1. Verdict : `CONFIRMÉE` si toutes ; `PARTIEL` si une seule manque ; `FALSIFIÉE` sinon.

### H1b — saturation de Cheng (S1)

`|ΔCS_Cheng| < 1e-12` **exactement** : toute cause entièrement suffisante (P(e|c) = 1, micro déterministe) donne PS = 1 quel que soit le reste, aux deux échelles. Verdict : `CONFIRMÉE` si l'égalité ponctuelle tient (elle **prouve** le compte des primitives, saturation comprise) ; `FALSIFIÉE` sinon.

### H2 — témoin bidirectionnel (S2)

Sur chaque regroupement légal de S2 où l'organe donne CE ≤ 0 : la **médiane** des `ΔCS` du panel est ≤ 0. Verdict : `CONFIRMÉE` si la médiane tient sur **tous** ces regroupements ; `PARTIEL` sur la majorité ; `FALSIFIÉE` si la médiane est > 0 sur la majorité.

### H3 — les primitives expliquent le déplacement

À travers tous les points mesurés (S1 ; chaque regroupement de S2 ; chaque ε de la grille S3 — section 4), pour chaque mesure du panel : corrélation de rang de Spearman entre `ΔCS_m` et `(Δdet − Δdeg)` **strictement positive**. Verdict : `CONFIRMÉE` pour toutes les mesures du panel ; `PARTIEL` si elle ne tient que pour la majorité ; `FALSIFIÉE` sinon.

### H4 — le macro gagne quand le micro est bruité (S3)

Pour chaque mesure du panel : `ΔCS_m(ε = 1) > ΔCS_m(ε = 0)` **strict** (coin bruité > coin propre). Verdict : `CONFIRMÉE` pour toutes ; `PARTIEL` si une seule manque ; `FALSIFIÉE` sinon. La ligne EI (organe) est mesurée aux mêmes coins — `−3 bits` au coin propre (CR) et `0` au coin bruité (égalité : marginales uniformes ⇒ deg micro = 0, l'EI ne dépasse jamais son macro sur cette classe — l'« *effective information is a conservative measure of causal emergence* » du papier, p. 15) — comme témoin interne de la grille.

### Graines et multi-seed

Instrument exact (TPM énumérées) : aucune mesure ne dépend d'une graine ; le JSON de résultats porte `stochastic: false`. Les graines canoniques n'entrent nulle part (déclaré).

## 6. Verdict global et portée

Verdict global borné par les hypothèses ci-dessus (aucune agrégation au-delà) : `SOUTENU` (H1 et H1b et H4 confirmées, H2 et H3 confirmées ou partielles), `RÉFUTÉ` (une hypothèse falsifiée), `PARTIEL` (mélange sans falsification), `NON_CONCLUSIF` (porte instrumentale déclenchée). Portée écrite : ce verdict dit si **la décomposition en primitives prédit le déplacement des mesures de causation au coarse-graining sur des substrats reconstruits et bornés** — il ne dit rien des heatmaps quantitatives du papier (Supplément non archivé), des mesures à métrique (exclues, raisons écrites), ni d'aucun système réel.

See #8182
