# Pré-enregistrement — STV v2 : seconde opérationnalisation (case 17bis : structure du lock ⟂ drive)

> **Grade C explicite.** Ce document **scelle** le protocole de la seconde opérationnalisation de la tranche STV Gómez-Emilsson/Johnson de la veille [#8182](https://github.com/jsboige/CoursIA/issues/8182), **AVANT toute écriture du banc de mesure** — pattern case 6 → case 14 et case 3 → case 15 : quand le premier instrument est `NON CONCLUSIF_INSTRUMENT` pour une limite **mesurée**, la réponse est un **second instrument pré-enregistré**, jamais un amendement post-hoc du premier. Le banc (`ict/stv_valence_symmetry_v2.py`) vit dans un second commit de la même PR — l'antériorité portée par la relation de parenté des commits (leçon case 8c).
>
> **Cycle du 2026-10-24**, lane `myia-po-2023:CoursIA`. Claim posé sur [#8182](https://github.com/jsboige/CoursIA/issues/8182) au moment du lancement.

## 0. Sources, cadre et thèse — hérités de la case 17, inchangés

Les sources primaires, leur archivage au gisement, le crédit témoins et les spot-checks firsthand sont ceux du scellé case 17 ([`stv-valence-symmetry-pre-enregistrement.md`](stv-valence-symmetry-pre-enregistrement.md) §1) : Johnson *Principia Qualia* (2016), Gómez-Emilsson « STV 2020 Overview », Johnson 2023 — **aucune nouvelle source n'est requise** : la thèse testée est la même, seul l'instrument change. La question falsifiable est la même : *l'attracteur suit-il la consonance, indépendamment du drive, et la cohérence brute sans structure harmonique se distingue-t-elle de la cohérence harmonique ?*

**Héritage direct du scellé v1/v3** (non re-spécifié ici, repris tel quel) : le couplage `H(φ) = Σ_{h≤4} sin(hφ)/h` à contenu harmonique fixe non accordé ; σ = harmonicité octave-repliée `p, q ≤ 4`, `τ = 0.03` ; le tirage des configurations (`draw_configs` v3 : échelle à membres exacts/décalés ±3-8 %, étal apparié ; bras N = 6 proches + 2 irrationnels) ; graines de test `(0, 1, 7, 42, 99)`, graines de calibration disjointes `(11, 22, 33)` ; DT = 5e-4, T = 40, sous-échantillonnage 10 ; `M = 120` configurations + `40` paires H/N par graine.

## 1. Les deux limites mesurées qui fondent cette seconde opérationnalisation

Le run case 17 ([§7 du scellé](stv-valence-symmetry-pre-enregistrement.md)) a verdicté `NON CONCLUSIF_INSTRUMENT (null b)` et **rapporté** (pas réparé) deux limites d'instrument :

1. **L'observable de P3 est aveugle au contraste qu'elle vise.** `CV(r)` mesure le battement de la cohérence brute ; le bras N y atteint la cohérence **maximale** (collapse 1:1 parfait, r̄(N) = 0.9999) au lieu de la « cohérence sans structure » attendue. Le discriminateur jhana/crise de la source (« high coherence alone is insufficient — must be harmonic structure ») exige un observable qui lit la **structure** du lock, pas sa seule existence.
2. **La perturbation d'énergie v1 passe par l'hétérogénéité d'amplitude** (`a_i ∈ {1 ± 0.1}` dans le produit `a_i·a_j` du couplage) : le drive modifie alors **par paire** la force de couplage effective, et c'est ce canal — pas un lien valence-énergie — qui a produit `|ρ(v, E)| = 0.31-0.42` (échec P2). La dissociation « attracteur ⟂ énergie » exige que le drive ne décide pas de la structure de verrouillage.

## 2. Les deux correctifs d'instrument (et uniquement eux)

### 2.1 — Observable de structure du lock (correctif de la limite 1)

Pour chaque paire verrouillée (critères v3 inchangés : concentration circulaire < 1.5 rad **et** |dψ/dt| < 0.03 rad/unité sur la seconde moitié, meilleur candidat (m, n) ≤ 4 par écart-type circulaire minimal), on enregistre la **classe du ratio** `m/n` repliée à ses valeurs distinctes : **{1:1, 4:3, 3:2, 2:1, 3:1, 4:1} — 6 classes**.

**Score de structure** : `S = −Σ_c p_c·ln p_c / ln(6)` — entropie de Shannon normalisée (nats) de la distribution des classes **parmi les paires verrouillées** de la configuration. `S = 0` si toutes les paires verrouillées sont dans la même classe ; `S → 1` si elles se répartissent uniformément sur les 6 classes. Si aucune paire n'est verrouillée, S n'est pas défini et la configuration n'entre pas dans la jambe P3 (déclaré ; le compte des exclusions figure dans les résultats).

**Anti-circularité** (même discipline que v pour σ) : la **classe** est lue sur la dynamique (quel couple (m, n) s'est **installé**), jamais sur le ratio naturel. Une paire de rapport naturel 2.05 qui ne verrouille pas ne contribue **pas** ; une paire de rapport 2.0 qui verrouille à 2:1 le doit à la dynamique. Le contenu informatif de S est le **fait que des locks structurés s'installent**, pas la géométrie du tirage.

**Lecture STV du contraste** : bras H (échelle octave) = analogue jhana — cohérent **et** structurellement riche (locks 2:1, 3:1, 3:2…) ; bras N (quasi-unisson + irrationnels) = analogue crise — cohérent **trivialement** (collapse 1:1, S ≈ 0).

### 2.2 — Régime de drive uniforme (correctif de la limite 2)

Amplitudes `a_i ≡ 1` **partout** (le tirage v3 les fixe déjà à 1 ; la perturbation v1 était la seule source d'hétérogénéité — elle est retirée). La dimension « énergie » devient le **drive global uniforme** : `K_eff = K2_c·(1+ε)`, `ε ∈ {−0.10, 0, +0.10}` — le drive agit sur le niveau global de couplage, **jamais par paire**. P2bis teste si `v` suit ce drive (ce que la STV nie : « it is the end result, the attractor ») ou la configuration (ce qu'elle affirme).

**Portée déclarée du correctif** : avec `a_i ≡ 1`, « énergie » et « force de couplage » sont la même variable — le test v2 porte le canal qui restait après fermeture du canal par-paire. C'est une restriction honnête du claim opérationalisé, pas une victoire par construction : P2bis peut encore échouer (v peut suivre le drive global).

### 2.3 — Fenêtre de calibration re-ciblée sur l'observable réelle

La calibration v1 gelait `K_c` sur `r̄(H) ∈ [0.5, 0.8]` — or `r` est **aveugle aux locks m:n** (constat v2-amendement, §6bis du scellé v1) : la fenêtre garantissait un régime de collapse 1:1, pas un régime de langues m:n. v2 gèle `K2_c` sur la lecture de l'instrument lui-même : **`v̄(u=1) ∈ [0.5, 0.8]`** (fraction verrouillée de l'échelle octave **exacte**, u = 1) sur les graines de calibration `(11, 22, 33)`, balayée sur la même grille `[4, 8, 16, 24, 32, 48, 64, 96, 128]`. Repli déclaré si la fenêtre est inatteignable : `K2_c` à **variance de v sur l'échelle u maximale** (sensibilité d'instrument, neutre en signe).

## 3. Prédictions scellées (aucune bande ne sera recalibrée après mesure)

| # | Prédiction | Bande / critère |
|---|---|---|
| **P1** (attracteur ∼ consonance — inchangée) | ρ de Spearman ρ(v, σ) sur l'échelle de consonance, à ε = 0 | ≥ **0.6** sur ≥ 4/5 graines |
| **P2bis** (dissociation drive) | Corrélation partielle de Spearman v ∼ ε **contrôlée par le décile de σ** (rangs résiduels par décile, jambe ε ∈ {−0.1, 0, +0.1} de chaque configuration) : \|ρ(v, ε \| σ-décile)\| | ≤ **0.2** sur ≥ 4/5 graines |
| **P3bis** (le discriminateur jhana/crise, par la structure) | À cohérence brute appariée (\|r̄(H) − r̄(N)\| ≤ 0.15 — **porte d'appariement**, voir gates) : `ΔS = S(H) − S(N)` par graine (moyenne sur les paires) | ≥ **0.25** sur ≥ 4/5 graines |
| **Null (a)** | σ permuté (étiquettes mélangées) : ρ(v, σ-permuté) | \|ρ\| ≤ 0.2 en médiane 5 graines |
| **Null (a3)** | Étiquettes H/N permutées : ΔS-permuté | \|ΔS\| ≤ 0.05 en médiane 5 graines |
| **Null (b)** | Couplage fort (K2_c × 8) : ρ(v, σ) | < 0.2 → `NON CONCLUSIF_INSTRUMENT` (régime saturation) |
| **Contrôle mécanique** | K_eff = 0 sur configurations **irrationnelles** (tirage dissident) : phases libres, le détecteur ne compte rien | v(K=0, irrationnelles) ≤ **0.05** sur 5/5 graines |

**Note de contrôle (défaut analytique détecté en concevant le banc, corrigé AVANT le commit du scellé — motif 6bis du v1 : un critère insatisfaisable par construction n'est pas une prédiction).** Les membres **exact** de l'échelle octave sont commensurables : une paire de rapport naturel 2/1, 3/1, 4/1, 3/2, 4/3 possède un couple (m, n) ≤ 4 dont la phase combinée est **stationnaire même à couplage nul** (ψ = constante cinématique — concentration et dérive nulles satisfaites sans aucun verrouillage). À K_eff = 0 ces paires sont donc comptées par le détecteur : v(K=0, échelle exacte) ≈ 20/28 = 0.71 **par construction**, pas par bug. Le contrôle mécanique porte donc sur les configurations **irrationnelles** (dérive ≥ DISSIDENT_DIST ≫ SLOPE_TOL à couplage nul → aucun compte attendu). En complément **diagnostique déclaré** (pas une porte) : v(K=0) sur échelle exacte est mesuré et rapporté — c'est le plafond cinématique du détecteur. Au point de travail K2_c > 0, l'argument cinématique ne tient plus : le couplage avec les membres incommensurables injecte dans chaque phase des composantes aux fréquences des autres, détruisant la stationnarité des paires non réellement entraînées (mesuré v1 : v max 0.536 ≪ 0.71 à K_c = 32) — la part cinématique de v au point de travail est une question empirique, déclarée ici, tranchée par les résultats.

**Portes instrumentales** (leçon cases 8b/8c/16/17) :

- `v̄(u=1) < 0.3` (plancher : l'échelle exacte n'entraine pas) sur ≥ 3/5 graines → `NON CONCLUSIF_INSTRUMENT` ;
- `v̄(u=0) > 0.7` (plafond : tout entraine, y compris l'échelle entièrement décalée) sur ≥ 3/5 graines → `NON CONCLUSIF_INSTRUMENT` ;
- **porte d'appariement P3bis** : `|r̄(H) − r̄(N)| > 0.15` sur ≥ 3/5 graines → P3bis `NON CONCLUSIF_INSTRUMENT` (le contraste serait porté par le niveau de cohérence, pas par la structure).

## 4. Verdicts bornés

- **SUPPORTED** : P1 ∧ P2bis ∧ P3bis ∧ Null (a) ∧ Null (a3) ∧ contrôle mécanique, aucune porte (les trois régimes : l'attracteur suit la consonance pas le drive ; la cohérence sans structure se distingue de la cohétrie harmonique).
- **NOT SUPPORTED** : P1 < 0.2 (l'attracteur est indifférent à la consonance même à régime propre), ou |ρ(v, ε)| > 0.5 (c'est le drive qui porte tout — rejet direct du « not the energy »), ou ΔS < 0.10 (structure indiscernable entre bras même par la structure du lock).
- **NON CONCLUSIF_INSTRUMENT** : Null (b), une porte instrumentale, la porte d'appariement, ou échec du contrôle mécanique.

## 5. Honnêteté grade C (limites — cumul du scellé v1 §6 et des siennes)

1. **Tout ce que §6 du scellé v1 déclarait reste vrai** : aucune phénoménologie ni valence émotionnelle n'est mesurée ; P1 reste partiellement vraie par la physique des langues d'Arnold (la charge de substance reste P2bis + P3bis) ; Plomp-Levelt/octave-replié comme modèle de σ est un choix déclaré ; la STV est déclarée robuste à l'échec algorithmique par ses auteurs ; le substrat Kuramoto est partagé avec les cases 6/14 à observables distincts.
2. **S hérite partiellement de la configuration** : les classes disponibles dépendent des détunings naturels (une paire d'écart 16:1 ne peut pas verrouiller à (m, n) ≤ 4). La jambe dynamique est que le lock **s'installe** — mais un partisan de la STV ne pourrait pas revendiquer S comme mesure phénoménologique ; c'est un discriminateur de substrat.
3. **Le plafond structurel v1 demeure** : seuls 20 des 28 couples de l'échelle octave ont un candidat (m, n) ≤ 4 — v reste borné par ~0.71 au régime m:n (déjà déclaré v1 §6ter.2) ; S le partage.
4. **La porte d'appariement est déclarée, pas garantie** : si le bras N ne collapse pas 1:1 à K2_c gelé (régime différent du run v1), P3bis peut être non concluant pour appariement — c'est un résultat honnête, pas un échec de thèse.
5. **Second instrument ≠ clôture** : même SUPPORTED, la case 17bis dit « oui, sur jouet, avec un instrument qui lit la structure » — rien de plus (pattern 6 → 14 : deux opérationnalisations, une thèse, jamais une validation).
6. **Commensurabilité cinématique** (cf. note de contrôle §3) : à couplage nul, les paires exactes commensurables satisfont les critères du détecteur sans verrouillage. Au point de travail, la perturbation croisée des membres incommensurables détruit cette stationnarité gratuite — mais la part résiduelle de v et de S(H) qui reste cinématique **n'est pas séparée** par cet instrument ; elle est déclarée, plafonnée par le diagnostic v(K=0, échelle exacte), et reportée dans les résultats.

## 6. Anti-duplication

Case 17 v1/v3 = instrument n° 1 (`NON CONCLUSIF_INSTRUMENT`, conservé tel quel — jamais réécrit) ; la présente = instrument n° 2 du **même claim**. Distinct de : case s ⟂ π (canaux saillance/valence, [#9553](https://github.com/jsboige/CoursIA/pull/9553)) ; cases 6/14 (frontière topologique, autre claim du même premier auteur) ; case 16 (MPS alertness). La ligne matrice `dissociations-matrix.md` ne sera **pas** éditée dans cette PR — deux PRs ouvertes (#22270, #22289) touchent déjà ce fichier ; la mise à jour de la ligne case 17 → 17bis est différée à une PR dédiée une fois celles-ci mergées.

## 7. Ce qui suit

1. **Ce document, committé, est le scellé.** Antériorité par parenté de commits (leçon case 8c).
2. Le banc `ict/stv_valence_symmetry_v2.py` + tests + artefact de résultats : second commit de la même PR (pattern #17164). Calibration (graines 11/22/33) → gel K2_c → run principal (5 graines) → nulls → JSON committé.
3. Verdict rapporté sur [#8182](https://github.com/jsboige/CoursIA/issues/8182) avec les mesures brutes par graine.
4. Statut au scellé : **`PRÉDIT` — banc non écrit.**

*See [#8182](https://github.com/jsboige/CoursIA/issues/8182) — la veille ne se clôt pas sur une tranche.*
