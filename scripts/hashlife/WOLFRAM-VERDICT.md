# WOLFRAM-VERDICT — mesure K_trajectory sur automates 1-D (Origami pli 3)

**Issue** : #19766 pli 3 (EPIC Origami #19742)
**PR** : #19815
**Date de la mesure corrigée** : 2026-10-09 (correction d'un artefact de cadrage sur la mesure initiale du 2026-10-08, réserve coordinateur sur la tête `6e3eb8f602`)
**Lane** : myia-po-2024:CoursIA-2
**Organe mobilisé** : `ict.wolfram_step.wolfram_trajectory` (PR #19793)

## Question scientifique

Le discriminant K_trajectory (T12 #18446, `scripts/hashlife/k_trajectory.py`) sépare en 2-D les trajectoires de soupe (collapse LZ, la dissolution vide la grille) des programmes auto-entretenus. **Ce discriminant tient-il cross-dimension sur les automates 1-D ?** Hypothèse initiale : Rule 30 (chaos, classe III) ~ fragile-LZ, Rule 110 (Turing-complet, classe IV) ~ incompressible.

## L'artefact corrigé : la zone saturée à n_cells = 64

La mesure initiale (n_cells = 64, n_steps = 64, seed = 33) concluat « Rule 30 et Rule 110 donnent les mêmes K(t, W), donc K_trajectory ne détecte pas la Turing-complétude ». **Ce verdict était un artefact de cadrage zlib**, pas un résultat de contenu :

- à n_cells = 64, chaque état packé ne porte que **8 octets**, sous le plancher de cadrage zlib (~11 octets par fenêtre : en-tête + bloc stocké) ;
- 8 octets aléatoires → 16 compressés ; 512 octets aléatoires → 523 = 512 + 11 (bloc stocké, non compressé) ;
- les deux règles mesuraient donc **identiques à l'octet près** (1026 → 523, JSON n=64 historique) — l'instrument ne voyait que son propre cadrage ;
- le ratio brut K(W_last)/K(W_first) est lui-même contaminé : pour un contenu incompressible, il vaut mécaniquement (c + 11/64)/(c + 11) avec c = n_cells/8 octets — Rule 30 à n=1024 rend ratio 0.922 = exactement cette arithmétique (K(W=1)/état = 139.00 = 128 + 11).

**Correctifs appliqués** : plancher de mesure concluante n_cells ≥ 512 (verdict `SATURATED` en dessous) ; le classement se fait sur la **fraction de compression** frac = K(t, W_last) / raw_packed_bytes, insensible au cadrage.

## Résultat (falsifiable, remesuré firsthand)

**n_cells = 1024, n_steps = 1024, seed = 33** (mesure canonique, `wolfram_results.json` committé) :

| Règle | K(t, W=1) | K(t, W=64) | Ratio | **frac** | K(W=1)/état | Verdict |
|-------|-----------|------------|-------|----------|-------------|---------|
| Rule 30 (classe III, chaos) | 142 336 | 131 248 | 0.922 | **1.001** | 139.00 (= 128+11, plancher exact) | **CHAOTIC-INCOMPRESSIBLE** |
| Rule 110 (classe IV, Turing) | 98 439 | 56 204 | 0.571 | **0.429** | 96.13 (< 139 : compression réelle dès W=1) | **TURING-STRUCTURED-COMPRESSIBLE** |

**n_cells = 512, n_steps = 512, seed = 33** (plancher de la zone concluante) :

| Règle | K(t, W=1) | K(t, W=64) | Ratio | frac | Verdict |
|-------|-----------|------------|-------|------|---------|
| Rule 30 | 38 400 | 32 856 | 0.856 | 1.003 | CHAOTIC-INCOMPRESSIBLE |
| Rule 110 | 34 141 | 18 622 | 0.545 | 0.568 | TURING-STRUCTURED-COMPRESSIBLE |

**Cross-verdict** : `WOLFRAM-CROSS-DIMENSION-REFUTED` — la discrimination entre les deux règles est **réelle dès n = 512**, mais dans le sens **inversé** de l'hypothèse.

Note de reproductibilité : le K exact de Rule 110 dépend du build zlib (~3 % d'écart mesuré entre postes sur K(W=1) : 101 299 / 98 439) ; les fractions de compression (0.43–0.44) et les verdicts sont stables à ce bruit près. Rule 30 est build-indépendant (blocs stockés : contenu + cadrage, rien d'autre).

## Interprétation

1. **L'instrument discrimine, l'hypothèse de direction était fausse.** La conclusion initiale « K_trajectory ne détecte pas la Turing-complétude de Rule 110 » était un artefact de taille. Hors saturation, Rule 30 et Rule 110 se séparent nettement (frac 1.001 vs 0.429 à n=1024).
2. **Le chaos 1-D est incompressible.** Chaque fenêtre de Rule 30 reste au plafond d'entropie : zlib ne trouve rien (blocs stockés à toutes les échelles, K(W=1)/état = 128 + 11 exactement). Le collapse LZ observé sur la soupe 2-D vient de la **dissolution** (la grille se vide → régularité triviale), pas du chaos lui-même — il ne transfère pas au 1-D.
3. **La structure Turing-complète est compressible.** La trajectoire de Rule 110 (fond périodique + particules/gliders) est **régulière**, donc LZ-compressible (57 % de sa taille brute dès n=512, 43 % à n=1024, compression réelle dès W=1 : 96.13 octets/état < 139). La Turing-complétude se manifeste dans la diversité des configurations accessibles, pas dans l'incompressibilité d'une trajectoire particulière.
4. **Lecture épistémique** : K_trajectory mesure la **régularité LZ** d'une trajectoire, ni la classe de Wolfram, ni la Turing-complétude — la limite déjà documentée en tranche 1 (« l'instrument détecte l'entropie, pas l'auto-entretien ») se confirme cross-dimension, avec la direction mesurée ici.

## Limites documentées

1. **Horizon W = 64** : la fenêtre max reste 2^6 états ; à n_cells grand, W_last ≠ trajectoire entière. La fraction de compression est stable entre n=512 et n=1024 (0.57 → 0.43 pour Rule 110), mais un horizon W plus long reste à mesurer pour la convergence asymptotique.
2. **Deux règles** : le corpus couvre Rule 30 / Rule 110 ; l'ajout de classes I (règle 0) et II (règle 4) fixerait le pôle « triviallement compressible » du gradient.
3. **zlib comme approximateur de K** : borne supérieure atteignable, sensible au build (~3 % mesuré) ; un comptage de facteurs LZ76 éliminerait le cadrage résiduel — non requis pour la discrimination actuelle (0.43 vs 1.00).

## Verdict final tranche Origami pli 3

**WOLFRAM-CROSS-DIMENSION-REFUTED** (discrimination réelle, direction inversée) :

- L'extension au 1-D est mécaniquement valide (organe `ict.wolfram_step` invoqué, format 1×N compatible, mesure exécutée sans erreur) et **l'instrument sépare les deux règles dès n_cells ≥ 512**.
- L'hypothèse de transfert du discriminant soupe-2D est **réfutée dans sa direction** : chaos 1-D incompressible, structure Turing-complète compressible.
- La zone n_cells = 64 est **saturée** (plancher de cadrage zlib) : verdict `SATURATED`/`INCONCLUSIVE` par l'instrument, toute discrimination y est un artefact.

**Suites pli 5/pli 6 inchangées** : instrument de complexité de règle (Block decomposition, SAT-based minimal program) pour discriminer Turing-complet vs chaos ; graphe multiway Lean.

## Reproduction

```bash
# Placer ict.wolfram_step dans sys.path (organe PR #19793)
export PYTHONPATH=MyIA.AI.Notebooks/IIT/ICT-Series

# Mesure canonique (cross-regles, n_cells=1024)
python scripts/hashlife/k_trajectory.py --mode wolfram --all

# Plancher de la zone concluante
python scripts/hashlife/k_trajectory.py --mode wolfram --all --n-cells 512

# Zone saturee (verdict SATURATED attendu)
python scripts/hashlife/k_trajectory.py --mode wolfram --all --n-cells 64

# Sortie JSON pour verification
python scripts/hashlife/k_trajectory.py --mode wolfram --all --json-out wolfram_results.json
```

Les sorties JSON `scripts/hashlife/wolfram_results.json` (n=1024) sont versionnées pour reproductibilité. Tests : `python -m pytest scripts/hashlife/tests/test_wolfram_mode.py` (11 tests, dont le garde de saturation n=64 et la direction inversée à n=512).

## Sources

- T12 #18446, tranche 3 #19227 : `scripts/hashlife/k_trajectory.py` instrument original (2-D)
- PR #19793 : organe `ict.wolfram_step` (pli 2)
- Cook 2004 : "Universality in Elementary Cellular Automata" (Rule 110 Turing-complet)
- Wolfram 2002 *A New Kind of Science* chap. 2-3 (4 classes de comportement), 9-11 (Rule 110)
- Zenil, Soler-Toscano et al. : compression-based complexity of CA (encadrement de l'approximation LZ de K)

🤖 Generated with [Claude Code](https://claude.com/claude-code)

Co-Authored-By: Claude Haiku 4.5 (1M context) <noreply@anthropic.com>
