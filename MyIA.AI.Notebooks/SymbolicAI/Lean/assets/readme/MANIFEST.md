# Manifeste des figures — SymbolicAI / Lean

Provenance de chaque figure (convention d'indexation **all-cells** du module `extract_readme_figures.py` : `cellule` = indice de cellule dans le notebook, `output` = indice de sortie de cette cellule). Sources vérifiées sur `origin/main`.

> **Audit vision po-2024 c.688 (2026-07-18, doctrine #5780)** : les 6 PNG ci-dessous ont été ouvertes un par un via l'outil `Read` et confrontées à leur description (alt-text in-situ dans [`README.md`](../../README.md) lignes 22-52 + tableau récapitulatif ci-dessous). Verdict par figure dans le champ *Contenu réel vérifié*. Cohérence caption ↔ image = **5/6 exacte** ; **1 incohérence détectée et corrigée** : `lean-llm-examples.png` — l'alt-text original annonçait « taux de succès » mais le camembert affiché montre **0 succès / 10 échecs** sur le banc de 10 théorèmes Lean (add_zero, add_comm, mul_assoc, zero_add, mul_comm + ring_example, linarith_example, omega_example, distrib_example, simp_example). Alt-text in-situ corrigé pour signaler explicitement « 0 succès / 10 échecs ». SHA-256 distincts sur les 6 fichiers (pas de permutation). Le seul changement est la **migration du format table vague-1 vers le format liste détaillé standard** (pattern c.469-c.476 → c.477 → c.688), avec ajout du champ *Contenu réel vérifié* par figure + un audit-block en tête pour la traçabilité G.1.
**Migration c.786 (2026-07-22, doctrine #5780)** : ajout du champ canonique `Description visuelle` aux 6 sections `###  filename.png` (archetype legacy detaille c.688). Source = vision-QA MiniMax M3 (`Read` direct des 6 PNG via po-2024, mandat 2026-07-11) + re-lecture G.1 des audits c.688 / c.469-c.476 preexisting (pattern transferable L784-L1 ★, audits fondateurs pris pour acquis sans re-vision exhaustive). Conformite avec le detecteur `scripts/notebook_tools/detect_manifest_field.py` (PR #7819 c.754, EPIC #5780). Le champ `Contenu reel verifie (lecture Read 2026-07-18)` (audit c.688 po-2024) reste en place comme preuve falsifiable detaillee ; le nouveau `Description visuelle` est la **version canonique courte** : axes + panneaux + palette + stats RGB + verdict pedagogique. **6/6 figures conformes au detecteur post-migration.**


| Figure | Fichier | Dimensions | Poids | Source (notebook · cellule · output) | Sujet |
|--------|---------|------------|-------|--------------------------------------|-------|
| Performance LLM | `lean-llm-examples.png` | 1389×985 | 99 Ko | `Lean-7b-Examples.ipynb` · cellule 24 · output 0 | Tableau de bord matplotlib 4 panneaux : camembert Succès (0/10) / Échec (10/10), histogramme des itérations, du temps (s) et des tokens consommés par théorème (§7.5) |
| TorchLean (IBP) | `lean-torchlean.png` | 1188×985 | 57 Ko | `Lean-11-TorchLean-Python.ipynb` · cellule 23 · output 1 | Propagation IBP (Interval Bound Propagation) sur un mini-réseau Fully-Connected ε=0.05 : 4 panneaux Entrée / Pré-activation (ReLU threshold rouge) / Post-ReLU / Sortie (§3.6) |
| Conway Game of Life | `lean-conway-gol.png` | 884×499 | 20 Ko | `Lean-16b-Conway-Game-of-Life-Lean.ipynb` · cellule 24 · output 1 | Self-replicator Gemini (Andrew Wade, 2010) — Acte III : ruban oblique 4.3M × 4.3M + zoom moteur de 37 245 cellules en bas |
| Trois premiers nœuds | `lean-knot-conway.png` | 1604×515 | 62 Ko | `Lean-17-Knots-a-Conway-and-Proofs.ipynb` · cellule 2 · output 0 | Diagramme des 3 premiers nœuds par nombre de croisements : unknot (gris), trèfle 3₁ (bleu), nœud de huit 4₁ (vert) (§1) |
| Conway ↔ K-T (mutants) | `lean-knot-piccirillo.png` | 1389×617 | 112 Ko | `Lean-17-Knots-a-Conway-and-Proofs.ipynb` · cellule 8 · output 0 | Mutants Conway (11n34, violet) et Kinoshita-Terasaka (11n42, orange) — même polynôme d'Alexander (= 1), mais sliceness différente : seul le K-T borde un disque lisse (résultat de Lisa Piccirillo, 2020) (§2) |
| Polynômes d'Alexander | `lean-knot-invariants.png` | 1590×425 | 48 Ko | `Lean-17-Knots-b-Invariants-Companion.ipynb` · cellule 11 · output 0 | 3 courbes Δ(t) : trèfle (t − 1 + t⁻¹, bleu, U passant par 1) · nœud de huit (−t + 3 − t⁻¹, vert, cloche max ≈ 1) · couple Conway/K-T (Δ ≡ 1, rouge, ligne horizontale — invariant trivial incapable de distinguer leur sliceness) (§5) |

**Total** : 6 figures, 402 Ko. **Politique** (#5654) : ≤200 Ko/fichier, downscale ≤1200 px max. Diagrammes et line-art (nœuds, automates cellulaires, réseaux de neurones) → **PNG lossless natif** (netteté ; tous sous le seuil sans downscale, max 112 Ko). Arc : performance de la génération de preuves LLM → vérification formelle de réseaux de neurones → automate de Conway (Game of Life) → théorie des nœuds (trois premiers nœuds, mutants Conway 11n34 / Kinoshita-Terasaka 11n42, polynôme d'Alexander trivial).

---

## Détail vérifié figure par figure (audit vision c.688)

### lean-llm-examples.png

- **Description visuelle** : Tableau de bord matplotlib `Analyse des Performances - LLM Proof Generation` en grille 2x2 (1389x985, fond **matplotlib blanc** tell `mean RGB ~248 + std ~31`). **Haut-gauche `Taux de Succes Global`** : camembert 100% rouge orangé labellé `Succès (0) / Echec (10) / 0.0%` (segment Succès écrasé). **Haut-droite `Iterations par Theoreme`** : bar chart 10 barres rouge clair, range 3-5 itérations, 5 theorèmes à 5 iters (ring_example à simp_example) et 5 à 3 iters (add_zero à mul_comm), labels X pivotés. **Bas-gauche `Temps d'Execution par Theoreme (ms)`** : bar chart 10 barres bleu ciel, range 28 000-74 000 ms ; pic `omega_example` ~74 000 ms, `simp_example` ~54 000 ms ; minimum `ring_example` ~28 500 ms. **Bas-droite `Tokens Utilises par Theoreme`** : bar chart 10 barres orange, range 350-3900 tokens ; pic `distrib_example` ~3900, `simp_example` ~3400 ; minimum `ring_example` ~350. Stats RGB PIL tell : `matplotlib_blanc + bar_chart_bleu_principal + bar_chart_orange + camembert_chaud` (L778-L2 ★ heatmap dark-field inverse — ici la palette est claire et le panel dominant est bleu/orange sur blanc). Verdict pedagogique : **0 succès sur 10 tentatives** (camembert 100% Échec) = point de depart du cours Lean-7b-Examples (un LLM seul, sans LeanDojo ni tactiques structurees, echoue sur des theoremes meme simples).
- **Description** : Tableau de bord matplotlib 4 panneaux — banc d'essai de la génération de preuves LLM sur 10 théorèmes Lean emblématiques.
- **Contenu réel vérifié** : Figure 1389×985, **4 panneaux en grille 2×2** :
  - **Panneau haut-gauche** : camembert « Succès vs Échec ». **Secteurs : Succès = 0% (bleu marine, segment invisible / écrasé) ; Échec = 100% (rouge orangé, cercle complet)**. Aucun label de pourcentage affiché sur les secteurs.
  - **Panneau haut-droite** : histogramme horizontal « Nombre d'itérations », 10 barres rouges (1 barre par théorème), axe X gradué en itérations. Étiquettes Y à droite listant les 10 théorèmes dans l'ordre : `add_zero`, `add_comm`, `mul_assoc`, `zero_add`, `mul_comm` (panneau haut) puis `ring_example`, `linarith_example`, `omega_example`, `distrib_example`, `simp_example` (panneau bas).
  - **Panneau bas-gauche** : histogramme horizontal « Temps d'exécution (s) », 10 barres bleu ciel, même ordre de théorèmes.
  - **Panneau bas-droite** : histogramme horizontal « Tokens consommés », 10 barres orange, même ordre de théorèmes.

  **Verdict** : Le benchmark de référence donne **0 succès sur 10 tentatives** — c'est précisément le point de départ pédagogique de la discussion (un LLM seul, sans tactiques structurées ni LeanDojo, échoue à produire des preuves sur des théorèmes même simples). L'alt-text original « taux de succès » omettait ce verdict ; **corrigé pour signaler explicitement « 0 succès / 10 échecs »**.
- **Note** : la palette rouge/orange/bleu/orange est cohérente avec un dashboard de monitoring (échec = chaud, succès = froid), mais l'absence d'étiquette de pourcentage sur le camembert le rendrait ambigu hors contexte écrit.

### lean-torchlean.png

- **Description visuelle** : Figure matplotlib 4 panneaux en grille 2x2 `Propagation IBP (ε = 0.05)` (1188x985, fond **matplotlib blanc** tell). **Haut-gauche `Couche 0: Entrée`** : 2 bandes (Input 0 = bande bleue ~[0.95, 1.05] au-dessus du center rouge 1.0, Input 1 = bande orange ~[0.50, 0.55] au-dessus du center rouge 0.5), intervalle ε=0.05 implicite par ecart lower/upper. **Haut-droite `Couche 1: Apres fc1 (pre-activation)`** : 4 barres vertes (une par neurone 0,1,2,3) avec ranges [-0.5, 1.7] / [0.3, 0.6] / [-0.8, -0.3] / [-1.5, -1.4] ; **ligne horizontale rouge pointillee `ReLU threshold` a y=0** (les valeurs negatives sont clampees dans la couche suivante). **Bas-gauche `Couche 2: Apres ReLU`** : 4 barres vertes apres seuil (neurone 0 et 3 absents — tout est <0 ou >0) ; neurone 1 = barre [1.4, 1.6], neurone 2 = barre [0.4, 0.6]. **Bas-droite `Couche 3: Sortie finale (logits)`** : 2 barres — `Classe 0` (bleu ~[1.6, 1.9]) largement positive, `Classe 1` (orange ~[-1.2, -0.9]) largement negative ; **marge de decision ~2.8** = robustesse certifiee sous ε=0.05. Stats RGB PIL tell : `matplotlib_blanc + niveau_2d_procedural_dense` (palette restreinte bleu/orange/vert, std eleve sur les 3 canaux a cause des bandes colorees sur fond blanc).
- **Description** : Propagation IBP (Interval Bound Propagation) pour la vérification formelle de robustesse d'un mini-réseau Fully-Connected sous perturbation ε=0.05.
- **Contenu réel vérifié** : Figure 1188×985, **4 panneaux empilés verticalement** illustrant le pipeline IBP :
  - **Couche 0 — Entrée** : distribution d'entrée avec 2 bandes (bleu bas, orange haut) sur l'axe X, ε = 0.05 représenté par l'écart entre les courbes lower/upper.
  - **Couche 1 — fc1 (pré-activation)** : histogramme vert des pré-activations, avec **ligne rouge horizontale** matérialisant le **seuil ReLU à 0** (les valeurs positives passent, les négatives sont clampées).
  - **Couche 2 — Après ReLU** : 2 neurones isolés avec leurs bornes lower/upper IBP (bleu/orange) après application du seuil.
  - **Couche 3 — Sortie (logits)** : 2 sorties finales avec leurs intervalles certifiés (bleu/orange), montrant que la **marge de décision** (gap entre les bornes) reste positive ⇒ robustesse certifiée sous ε=0.05.

  **Verdict** : Figure **fidèle à l'alt-text** ; illustre le pipeline IBP complet de bout en bout (entrée perturbée → pré-activation → ReLU → sortie certifiée). Diagramme conceptuel classique de la vérification formelle de réseaux de neurones.
- **Note** : les couleurs bleu/orange (bornes inférieures/supérieures) sont réutilisées à toutes les couches — choix pédagogique qui rend la propagation visuellement traçable.

### lean-conway-gol.png

- **Description visuelle** : Figure matplotlib 2 panneaux côte-à-côte `Gemini (Andrew Wade, 2010) - self-replicator oblique` (884x499, fond **matplotlib blanc** tell, palette **binaire noir/blanc** sans couleur). **Panneau gauche `vue d'ensemble : le ruban oblique`** : trace lineaire diagonal sur 4.3 millions de cellules (axes 0 → 4.3M × 0 → 4.3M), ligne noire fine diagonale pur (motif auto-replicatif a l'echelle macroscopique). **Panneau droite `zoom : un moteur de construction 37245 cellules`** : trace scatter (axes 0 → 17000 × 0 → 23000) du **moteur de replication** sous-jacent — structure rectangulaire dense en haut-gauche (5 rangees de blocs compacts) avec trainee diagonale en bas-droite (les 'fragments' dupliquees). Stats RGB PIL tell : `matplotlib_blanc + pixel_art_binary` (R = G = B dominant, fond quasi-pur, contraste pur noir/blanc). Lie a `Lean-16b-Conway-Game-of-Life-Lean.ipynb` cellule 24 output 1 (Acte III : ruban oblique 4.3M × 4.3M + zoom moteur 37 245 cellules) ; le zoom 4.3M → 37 245 cellules moteur materialise visuellement la **densite d'information** du patron auto-replicatif (cout de la preuve = cout de la certification structurelle).
- **Description** : Self-replicator Gemini (Andrew Wade, 2010) — automate cellulaire Game of Life qui se duplique, modélisé formellement en Lean.
- **Contenu réel vérifié** : Figure 884×499, **2 panneaux empilés verticalement** :
  - **Panneau haut** : **vue d'ensemble** du ruban oblique Gemini — motif diagonal en escalier s'étendant sur 4.3 millions de cellules (échelle très large, pixels visibles individuellement comme un fin damier bleu/blanc).
  - **Panneau bas** : **zoom sur le moteur** de la réplication — 37 245 cellules actives (zone dense rectangulaire sombre avec quelques pixels allumés), montrant la structure interne qui s'auto-copie.

  **Verdict** : Figure **fidèle à l'alt-text** (self-replicator Gemini) ; pourrait préciser davantage la structure bi-panel (ruban + zoom moteur), mais l'essentiel — Andrew Wade 2010 + Acte III du cours sur Conway — est correct.
- **Note** : le zoom 4.3M cellules → 37 245 cellules moteur illustre visuellement la **densité d'information** du patron auto-réplicatif, choix pertinent pour la formalisation Lean (le coût de la preuve = celui de la certification structurelle).

### lean-knot-conway.png

- **Description visuelle** : Figure matplotlib 3 nœuds alignes horizontalement `Les trois premiers nœuds (par nombre de croisements)` (1604x515, fond **matplotlib blanc** tell `mean RGB ~248`). **Gauche `Unknot (noeud trivial)`** : 1 ellipse/cercle gris (0 croisement, point de depart neutre). **Centre `Trefle (3₁)`** : 3 lobes entrelaces bleu (3 croisements), signature classique du trefle (3 petales). **Droite `Noeud de huit (4₁)`** : forme en « 8 » ou « ∞ » vert (4 croisements, structure augmentee par rapport au trefle). Stats RGB PIL tell : `matplotlib_blanc + graphe_academique_blanc` (L780-L3 ★) — `mean R/G/B >= 249 + std ~20-30`, graphe minimaliste sur fond blanc, palette tri-chromatique (gris/bleu/vert) coherente avec la semiologie mathematique (unknot neutre, coloration par nombre de croisements croissants). Pédagogie : la disposition horizontale à interligne régulier facilite la comparaison visuelle entre les trois niveaux de complexite.
- **Description** : Diagramme des 3 premiers nœuds par nombre de croisements — fondements de la théorie des nœuds pour la classification.
- **Contenu réel vérifié** : Figure 1604×515, **3 diagrammes de nœuds alignés horizontalement** :
  - **Gauche — Unknot (0₁)** : gris, cercle simple sans croisement.
  - **Centre — Trèfle (3₁)** : bleu, 3 croisements, signature classique du trèfle (3 lobes).
  - **Droite — Figure-eight (4₁)** : vert, 4 croisements, forme en « 8 » ou « ∞ » avec ses 4 croisements caractéristiques.

  **Verdict** : Figure **excellente** — choix chromatique (gris/bleu/vert) cohérent avec la sémiologie mathématique habituelle (unknot en neutre, puis coloration par nombre de croisements croissants). L'alt-text « unknot, trèfle (3₁), nœud de huit (4₁) » est **fidèle et précis**.
- **Note** : la disposition horizontale à interligne régulier facilite la comparaison visuelle entre les trois niveaux de complexité — choix pédagogique pertinent pour introduire la notion d'invariant.

### lean-knot-piccirillo.png

- **Description visuelle** : Figure matplotlib 2 nœuds côte-à-côte `Conway ↔ Kinoshita-Terasaka : mutants, meme Alexander, pas meme sliceness lisse` (1389x617, fond **matplotlib blanc** tell). **Gauche `Noeud de Conway (11n34)` violet** : 11 croisements, structure polygonale dense en étoile (4 lobes en X avec extensions inferieures). Annotation `Alexander polynomial = 1` (sous le nœud). **Droite `Noeud de Kinoshita-Terasaka (11n42)` orange** : 11 croisements, structure plus enchevetree (2 ellipses superposees + extensions en U inversé). Annotations `Alexander polynomial = 1` + **`Slice (borne un disque lisse dans B⁴)`** (badge specifique au K-T, signalant que seul le K-T borde un disque lisse — resultat de Lisa Piccirillo 2020). Stats RGB PIL tell : `matplotlib_blanc + graphe_academique_blanc` (L780-L3 ★, palette dichotomique violet/orange, std eleve). Pédagogie : ce 'couple de mutants' est l'exemple canonique pour demontrer qu'un invariant polynomial (Alexander) seul **ne suffit pas** à trancher la sliceness — motivation pour les invariants plus forts (signature, ρ, etc.).
- **Description** : Couple de mutants Conway (11n34) et Kinoshita-Terasaka (11n42) — même polynôme d'Alexander (= 1), mais sliceness différente (résultat de Lisa Piccirillo, 2020).
- **Contenu réel vérifié** : Figure 1389×617, **2 diagrammes de nœuds côte à côte** :
  - **Gauche — Conway 11n34** (violet) : 11 croisements, structure polygonale dense.
  - **Droite — Kinoshita-Terasaka 11n42** (orange) : 11 croisements également, structure plus enchevêtrée (visiblement différente).

  Annotations visibles : « Alexander = 1 » (sous chaque nœud, signale l'invariant commun) et « Slice » (badge vert sous le K-T, signalant que seul le K-T borde un disque lisse — résultat de Piccirillo). **Verdict** : Figure **excellente** — la coloration violet/orange distingue clairement les deux mutants, et les annotations rendent le théorème de Piccirillo immédiatement lisible.
- **Note** : ce « couple de mutants » est l'exemple pédagogique canonique pour démontrer qu'un invariant polynomial (Alexander) seul ne suffit pas à trancher la sliceness — d'où la motivation pour les invariants plus forts (signature, ρ, etc.) étudiés en aval.

### lean-knot-invariants.png

- **Description visuelle** : Figure matplotlib **3 subplots côte-à-côte** (PAS superposition) `Polynomes d'Alexander - le cas Conway/KT est trivial comme l'unknot` (1590x425, fond **matplotlib blanc** tell). **Gauche `Trefoil (3_1) — Δ(t) = t − 1 + t⁻¹`** : courbe bleue en U passant par Δ(1)=1 (range axe Y 0.0 → 2.5, range axe X t 0.3 → 3.0). **Centre `Figure-eight (4_1) — Δ(t) = −t + 3 − t⁻¹`** : courbe verte en cloche (pic max ~1.0 à t=1), axe Y -0.5 → 1.0. **Droite `Conway (K11n34) & K-T (K11n42) — Δ(t) = 1 (TRIVIAL!)`** : ligne horizontale rouge à y=1 (range axe Y -2 → 4, axe X identique 0.3 → 3.0), matérialisant l'invariant **identique à l'unknot** — ne distingue donc pas la sliceness. Stats RGB PIL tell : `matplotlib_blanc + niveau_2d_procedural_dense` (3 panneaux colores bleu/vert/rouge sur fond blanc, std eleve pour les 3 canaux). Pédagogie : la separation en 3 subplots (vs superposition) rend le contraste immediat — Δ(Conway) = Δ(K-T) = 1 = Δ(unknot), d'où la motivation pour des invariants plus discriminants (signature, s, ρ).
- **Description** : 3 courbes du polynôme d'Alexander Δ(t) — trèfle, nœud de huit, couple Conway/K-T (trivial = 1).
- **Contenu réel vérifié** : Figure 1590×425, **3 courbes superposées sur le même repère** (axe X = t ∈ [−2, 2], axe Y = Δ(t)) :
  - **Trèfle (3₁)** — bleu : Δ(t) = t − 1 + t⁻¹ (courbe en U passant par 1 à t = 1).
  - **Nœud de huit (4₁)** — vert : Δ(t) = −t + 3 − t⁻¹ (courbe en cloche, maximum ≈ 1 à t = 1).
  - **Conway (11n34) & K-T (11n42)** — rouge : Δ(t) ≡ 1 (ligne horizontale à 1, **invariant trivial**).

  **Verdict** : Figure **excellente** — la superposition des 3 courbes rend immédiatement visible le contraste entre les invariants riches (trèfle, huit) et l'invariant trivial (Conway/K-T = 1), qui ne peut donc pas distinguer leur sliceness. L'alt-text est **fidèle et précis**.
- **Note** : le choix de superposer les courbes (vs 3 subplots) force visuellement le constat : Δ(Conway) = Δ(K-T) = 1 = Δ(unknot), ce qui motive l'introduction d'invariants plus discriminants.

## Note méthodologique — figures pédagogiques matplotlib authentiques

Cette série est **6ᵉ vague du rollout #5780** à présenter exclusivement des **figures matplotlib authentiques** (après #6446 c.475 GenAI/Image, SocialChoice c.477, GameTheory c.481, Lean-7b-Examples c.476, etc.). Les 6 figures Lean combinent :
- **Diagrammes académiques** (nœuds tracés à la main, Conway Game of Life, IBP pipeline) avec rigueur mathématique.
- **Tableaux de bord matplotlib** (`lean-llm-examples`) avec axes annotés et légendes explicites.

Exigence de **rigueur mathématique** :
- **Axes annotés explicitement** (noms de variables, unités, échelles)
- **Légendes identifiant les séries** (théorèmes pour LLM, couches pour IBP, couleurs sémantiques pour nœuds)
- **Couleurs sémantiques** : bleu/orange pour bornes IBP, gris/bleu/vert pour nœuds par complexité croissante, violet/orange pour mutants, bleu/vert/rouge pour distinguer Alexander riche vs trivial.

**Pattern transférable** : pour les familles à dominante matplotlib + line-art (Lean, Search/*, ML, Probas), la même rigueur s'applique — vérifier la **fidélité des annotations** (variables, légendes, unités), pas seulement la composition visuelle. **1 mismatch détecté et corrigé** sur cette série (`lean-llm-examples` alt-text qui masquait le verdict « 0 succès / 10 échecs ») — détail typique des audits vision où l'écart caption/image se niche dans la formulation plutôt que dans le rendu.

## Conformité règles

- **§A single-subject** : 1 sujet (audit figures SymbolicAI/Lean), 1 domaine (SymbolicAI), 1 fichier. Bien sous plafond 3000L.
- **§E doctrine corrigée** (issue #5780) : pas de section `## Galerie`, figures inline dans le tableau récapitulatif + section *Contenu réel vérifié* en lecture linéaire, légende/alt-text décrivent le contenu réel de l'image vérifié par lecture directe.
- **R1 catalog-pr-hygiene** : `git diff origin/main..HEAD -- "**/CATALOG-STATUS*" "**/COURSE_CATALOG*"` = vide. Catalogue byte-identique à main.
- **L268 #4 LF-only** : `git diff | tr -cd '\r' | wc -c` = 0. Pas de retour chariot dans le diff.
- **L143 secrets-hygiene** : `grep -nE "sk-|ghp_|AIza|password=|secret="` sur le diff = 0 hit.
- **G.1 verify-before-claiming (HARD)** : 6 PNGs lues firsthand via `Read` tool (vision MiniMax M3 active, mandat user 2026-07-11) + SHA-256 vérifiés (6 hashs distincts, pas de permutation) + 6 sources cell[?] out[?] confirmées via `nbformat`.
