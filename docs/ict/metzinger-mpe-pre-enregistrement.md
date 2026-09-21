# Pré-enregistrement — Metzinger MPE 2020 (case 16 : alertness tonique ⟂ saillance phasique)

> **Grade C explicite.** Ce document **scelle** le protocole de la tranche Metzinger de la veille [#8182](https://github.com/jsboige/CoursIA/issues/8182) (TOE ↔ conscience, carrefour Jaimungal) **AVANT toute écriture du banc de mesure** — héritage direct des tranches Owen/Cruse ([#13426](https://github.com/jsboige/CoursIA/pull/13426)) et Schurger ([#13459](https://github.com/jsboige/CoursIA/pull/13459)) : source primaire lue intégralement et archivée, pré-enregistrement commité avant l'implémentation et la mesure, verdict borné. Le banc (`ict/tonic_alertness_gain.py`) sera une **PR séparée** — le pattern de la case 4 (pré-enregistrement chiffré puis exécution) est la référence.
>
> **Cycle du 2026-09-21**, lane `myia-po-2027:CoursIA`. Claim : commentaire issuecomment-5755968787 sur [#8182](https://github.com/jsboige/CoursIA/issues/8182).

## 1. Source primaire et archivage

**Source** : Thomas Metzinger, « Minimal phenomenal experience: Meditation, tonic alertness, and the phenomenology of "pure" consciousness », *Philosophy and the Mind Sciences* 1(I)7 (2020), DOI [10.33766/jphims.1128](https://doi.org/10.33766/jphims.1128). Open access (CC-BY).

**Archivage gisement** ([bibliography-hygiene](../../.claude/rules/bibliography-hygiene.md)) : `G:\Mon Drive\MyIA\IA\Bibliographie IA\Consciousness\2020 - Metzinger - Minimal Phenomenal Experience (PhiMiSci 1(I)7, OA).pdf` — 323 887 octets, identité vérifiée sur la première page (auteur, titre, revue, DOI), recherche par auteur ET titre avant dépôt, une seule copie au rayon `Consciousness`.

**Méthode de lecture** : texte intégral extrait (corps l.1–1807, références l.1825–2112 du fichier de travail de la session — le fichier s'arrête à la l.2118). Fiche d'extraction en 7 sections (contraintes PC1–PC6, MPS vs MPE, §3 éveil/vigilance tonique, §4 hypothèse centrale avec toutes les occurrences « unpartitioned epistemic space »/« aperspectival »/« epistemic space », 16 études de cas, points de contact formels, limites) produite par sous-agent dédié, puis **spot-checks firsthand** des cinq citations pivots par la lane (G.1 — aucune citation du présent document n'est propagée sans relecture directe du passage source).

## 2. Le cadre en deux phrases

Le papier pose le prototype de la « conscience pure » (MPE — *minimal phenomenal experience*) comme **contenu d'un modèle prédictif bayésien de la vigilance tonique** : « the phenomenological prototype of "pure awareness" […] really is the content of a predictive model, namely, a Bayesian representation of tonic alertness. On a more abstract conceptual level, it can be described as a model of an unpartitioned epistemic space » (abstract). Six contraintes sémantiques (PC1 Éveil, PC2 Faible complexité, PC3 Auto-luminosité, PC4 Disponibilité introspective, PC5 Épistémicité, PC6 Transparence/Opacité) délimitent un **concept de prototype**, pas des conditions nécessaires/suffisantes.

**Relation à la case 4** ([`dissociations-matrix.md`](dissociations-matrix.md), déjà testée) : la case 4 opérationnalisait le **MPS** (*minimal phenomenal selfhood*, Blanke & Metzinger 2009 — identification globalisée, auto-localisation, 1PP faible) via le traitement différentiel `R_self` de `q(soi)` vs `q(autrui)` sur substrat SAE — verdict INCONCLUSIF (saturation broadcast). La note d'honnêteté (c) de la case 4 soulignait déjà : « le papier MPS 2020 borne lui-même la thèse : l'expérience phénoménale minimale (*pure awareness*) peut survenir **sans** MPS ». La présente case teste ce **complément dual** : non plus le selfhood, mais la thèse §4 du papier 2020 — l'expérience minimale comme modèle de **capacité** (pas de contenu), dont la propriété structurelle distinctive est la **non-partition** de l'espace épistémique.

## 3. La question falsifiable

Deux passages du papier portent l'opérationnalisation :

1. **Le pont fonctionnel** (§3.1) : « The phenomenal experience of wakefulness is a representation or, plausibly, a predictive Bayesian model of the functional property of tonic alertness » — la vigilance tonique étant définie fonctionnellement (Posner, cité l.1526–1529) comme « atteindre et maintenir un état de forte sensibilité aux stimuli entrants » : un **préparatif à traiter**, sans contenu propre.
2. **La non-partition** (§4, thèse ESM) : « the as-yet-unpartitioned nature of this space is what explains the abstract phenomenal character of Epistemicity » — et le contraste phasique (§3.2) : l'alerte phasique est « l'expérience d'être forcé d'adopter une nouvelle perspective attentionnelle », ascendante, **dirigée par la saillance** — c'est-à-dire orientée-contenu et partitionnée.

**Dissociation à tester** : un gain de disponibilité **tonique** (lent, global, sans contenu) se distingue-t-il, sur substrat, d'un gain **phasique** (rapide, orienté-contenu) — le premier amplifiant uniformément (non-partition), le second hiérarchisant (partition) ? C'est la plus petite paire de propriétés du papier qui se laisse opposer sur un jouet : *l'attente de connaissance amplifie sans sélectionner ; la saillance sélectionne sans être une attente*.

## 4. Prédiction chiffrée scellée (case 16)

### Substrat

Jouet **CPU-only**, numpy pur, deux étages hiérarchiques :

- **Étage tonique** : une variable scalaire lente `τ ∈ {bas, haut}` qui module le seuil d'adoption de **tous** les canaux phasiques identiquement (le modèle de capacité — aucune entrée de contenu ne l'alimente).
- **Étage phasique** : `K = 8` canaux de contenu indépendants, `N = 48` consommateurs à lectures bruitées, adoption par seuil d'alignement (la famille des cases 14/15 — générateur factoriel, adoption seuillée). `propa` = fraction des consommateurs ayant adopté le contenu injecté.
- **Bras phasique adversarial** : le même substrat où le gain est porté par un module de saillance phasique — budget de gain **total apparié** (somme des boosts égale entre bras), mais boost concentré sur le canal le plus saillant (orienté-contenu).
- **Null structurel** : substrat sans étage tonique, à couplage global apparié (même connectivité moyenne de l'étage phasique).

Graines `(0, 1, 7, 42, 99)`, M = 200 contenus iid par graine pour les nulls — la discipline commune des cases 14/15.

### Prédictions (scellées — aucune bande ne sera recalibrée après mesure)

| # | Prédiction | Bande / critère |
|---|---|---|
| **P1** (gain de disponibilité) | L'étage tonique haut amplifie la propagation de contenu nouveau : `R_alert = propa(τ haut) / propa(τ bas)` | médiane 5 graines ∈ **[1.2, 3.0]** |
| **P2** (non-partition — le cœur ESM) | Le gain tonique est **uniforme** across canaux : `g_k = propa_k(τ haut)/propa_k(τ bas)`, `max_k g_k / min_k g_k` | ≤ **1.25** sur ≥ 4/5 graines |
| **P3** (double dissociation) | Le module phasique au même budget **hiérarchise** : son `max_k g_k / min_k g_k` | ≥ **2.0** sur ≥ 4/5 graines |
| **Null (a)** | Sans étage tonique, couplage apparié : `R_alert` | médiane ∈ **[0.9, 1.1]** — c'est la hiérarchie lente/rapide qui porte le gain |
| **Null (b)** | Le phasique n'hiérarchise pas non plus (`< 2.0`) | → **NON CONCLUSIF_INSTRUMENT** : l'instrument ne discrimine pas les deux régimes, aucune lecture |

**Portes instrumentales** (leçon des cases 8b/8c — un plancher/plafond n'est jamais un verdict) : si `propa(τ bas) < 0.05` (plancher) ou `propa(τ haut) > 0.95` (plafond) sur ≥ 3/5 graines → `NON CONCLUSIF_INSTRUMENT`, les seuils de P1/P2 ne s'évaluent pas.

### Verdicts bornés

- **SUPPORTED** : P1 dans bande **ET** P2 tenue **ET** P3 tenue (les deux régimes existent et se distinguent) **ET** Null (a) dans bande.
- **NOT SUPPORTED** : P1 hors bande (le gain tonique n'existe pas ou sature), ou Null (a) violé (le gain ne vient pas de la hiérarchie), ou P2 violée avec P3 tenue (le « tonique » hiérarchise comme un phasique — la dissociation est vide).
- **NON CONCLUSIF** : Null (b) ou porte instrumentale.

## 5. Greffe sur la conjecture strates-adjonctions (lecture, jamais un claim)

Le prototype [`strates-as-adjunctions-prototype.md`](strates-as-adjunctions-prototype.md) (jalon 3 de #8182) pose : chaque strate ICT = acquisition d'une adjonction ; la **Cohesion** `∮ ⊣ ♭ ⊣ ♯` de Schreiber code la localité/partition. La thèse ESM de Metzinger offre un point de contact **documentaire** : l'espace épistémique « as-yet-unpartitioned » (l.1234) se lit comme l'état **avant** l'adjonction de partition — MPE serait le modèle d'un espace qui n'a pas encore acquis la structure que `∮` formalise. Si la case 16 tient, elle fournit le premier témoin substrat de cette lecture : **un gain de disponibilité sans partition** (tonique) et **un gain partitionné** (phasique) sont deux régimes mesurablement distincts — deux « points » de part et d'autre de l'adjonction hypothétique. Si la case 16 échoue, la lecture perd son témoin substrat le plus direct, pas sa cohérence documentaire. Cette greffe n'est **pas** testée par la case 16 : elle en est l'horizon d'interprétation, au même titre que les hooks Vervaeke/Hofstadter des cases 1/3/8.

## 6. Honnêteté grade C (limites)

1. **Aucune phénoménologie n'est mesurée.** Le jouet teste une signature de propagation ; l'identification de `τ` à la « représentation bayésienne de tonic alertness » est une **lecture** du design par le cadre Metzinger, pas une validation du papier. Metzinger ne spécifie aucun jouet, aucune bande, aucun ratio.
2. **La bande [1.2, 3.0] est calibrée à la classe des cases existantes** (cases 7/9 : ratios de dissociation de l'ordre de 1.5–3.0 sur jouets à adoption seuillée), pas dérivée du texte. C'est la convention de la famille, assumée comme telle.
3. **P2 est partiellement vraie par construction** (le tonique module tous les canaux identiquement par design) : sa force ne vient pas de sa surprise mais de sa conjonction avec P3 et Null (a) — c'est la **double dissociation** qui porte la lecture, pas l'uniformité seule. Le verdict le dira explicitement.
4. **Non-rapportabilité structurelle** : le papier lui-même note que les épisodes de pleine absorption ne sont pas rapportables (mémoire autobiographique suspendue, l.669–678) — toute validation empirique humaine du modèle est bornée par là ; le jouet n'a pas cette excuse et ne prétend pas la combler.
5. **Le papier est une étape 1 sur 3** (concept de prototype vers un instrument psychométrique validé) ; ses propres réponses §4 sont « préliminaires » (l.252). Une case 16 SUPPORTED dirait : *la plus petite paire de propriétés structurales du modèle MPE se laisse dissocier sur substrat* — rien de plus.

## 7. Ce qui suit

1. **Ce document, commité, est le scellé.** Toute modification ultérieure des bandes P1/P2/P3/nulls se fait par amendement **pré-exécution** horodaté dans ce fichier (le pattern des cases 14/15 : `v1 → v2 AVANT re-run`), jamais silencieusement.
2. Le banc `MyIA.AI.Notebooks/IIT/ICT-Series/ict/tonic_alertness_gain.py` + tests vivront dans une PR séparée, avec ligne matrice case 16 mise à jour au statut `TESTÉ (...)`.
3. Verdict rapporté sur [#8182](https://github.com/jsboige/CoursIA/issues/8182) avec les mesures brutes par graine.
