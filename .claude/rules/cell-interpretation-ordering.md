---
paths: MyIA.AI.Notebooks/**/*.ipynb
---

# Cellules d'interprétation — ancrage sémantique, pas positionnel (HARD)

S'applique à **tous les agents** insérant ou déplaçant une cellule markdown d'interprétation (header `### Lecture du résultat : …`, `### Interprétation : …`, ou prose « on observe / le résultat montre »), et à **tous les reviewers** (bots + humains) d'une PR d'enrichissement. Source : Epic **#10678** (désordre massif PyMC-15, PR #10580 / #10562 — angle mort review). Incident fondateur : 5 cellules d'interprétation ancrées par id arbitraire, décalées de 5 à 26 cellules de l'output qu'elles commentent, passées à travers NanoClaw + CI H.1/H.3 + golden-set + merge sans broncher.

## Règle HARD — l'interp suit le code dont elle commente l'OUTPUT, pas un id

Une cellule d'interprétation cite des valeurs mesurées (163 divergences, score 3.192, Doc 4 / 4.988). Ces valeurs sont produites par **une** cellule de code précise. L'interp DOIT être placée **immédiatement après la cellule de code dont l'output contient ces valeurs** — jamais après une cellule de code arbitraire identifiée par son id.

**Anti-pattern fondateur** (PyMC-15 #10580) : l'agent enricher génère un bon contenu, déclare dans le body « inséré APRÈS les outputs », mais ancre la cellule par id (`interp-<codeid>`) **sans vérifier que cet id correspond au code dont elle parle**. La cellule « classement final du Click Model (score 4.988) » s'est retrouvée 26 cellules plus haut, collée après la définition du modèle de factorisation. Illisible.

## Obligation de l'agent qui insère/déplace une interp

1. **Lire l'output réel** de la cellule de code que l'interp doit commenter (`Read` la cellule, grep les outputs pour la valeur citée).
2. **Placer l'interp immédiatement après CETTE cellule** (celle dont l'output contient la valeur citée), pas après une cellule d'id voisin.
3. **Vérifier au `NotebookEdit`** que chaque valeur chiffrée citée dans l'interp apparaît dans l'output de la cellule précédente. Si une valeur n'y est pas → mauvais ancrage, repositionner.

## Obligation du reviewer (bot + humain) sur PR d'enrichissement markdown-only

L'enrichissement markdown-only est dispensé de re-exécution (C.3) — ce qui est correct pour les outputs, mais crée l'angle mort : **personne ne rouvre le notebook pour voir où tombent les cellules**. Sur une PR qui insère/déplace une cellule d'interprétation :

1. **Vérifier visuellement la position** : chaque `### Lecture du résultat` / `### Interprétation` suit-elle bien un code dont l'output contient la valeur citée ?
2. Le check automatique **ne peut pas** faire ça (la détection sémantique de misplacement mesure ~99% de faux positifs — voir `scan_interp_output_anchor`, outil de tri opt-in, jamais un gate). **Le regard humain est obligatoire.**

## Outils

- `scripts/notebook_tools/scan_cell_ordering.py` : catche le variant **structurel** `INTERP_BEFORE_CODE` (MED) — une interp qui précède son code au lieu de le suivre. Reconnait désormais les headers #10488.
- `scan_cell_ordering.py --check-interp-anchor` : triage **opt-in** (`INTERP_OUTPUT_MISMATCH`, ~99% FP, ADVISORY) — liste des candidates à eyeballer, jamais un verdict.
- `cell_order_ci.py` : gate CI de régression (HIGH). Ne catche PAS le cas sémantique (par construction — précision d'abord).
- Skill `/check-cell-order`.

## Pourquoi pas un gate automatique sémantique ?

Mesuré firsthand (audit #10678 Phase 3, 2026-08-13) : une cellule d'interp cite souvent une valeur qui est dans un plot matplotlib / un DataFrame HTML / une cellule voisine, pas dans l'output texte adjacent. Exiger la valeur dans l'output adjacent produit **164 faux positifs pour ~1 vrai positif** sur `origin/main`. Un gate aussi bruyant formerait les reviewers à l'ignorer — pire que pas de gate. La précision d'abord : on shippe le check structurel (zero-FP) + le triage opt-in + **cette règle process** (le regard humain obligatoire reste le remède).

## Ce que les deux audits de #10678 ont calibré

L'audit de positionnement du 2026-08-13, puis son re-scan des interps en fin de carnet le 2026-08-15, ont mesuré ce que la mécanique peut voir. Deux résultats tiennent, et ils disent tous deux de **ne pas** traiter un écart de position comme un défaut :

- **Un écart de position n'est pas un signal.** L'heuristique d'écart (`avant ≥ 3` et `après ≥ 3`, ou un seul des deux `≥ 5`) remonte des candidates, mais le motif `code → interp → def suivante` est légitime et en explique l'essentiel : le `def` ouvre un sous-bloc, l'interp commente bien le code qui la précède. Le motif naïf « la cellule suivante est un `def`/`class` » avait déjà dû être écarté pour la même raison.
- **Une interp en fin de carnet n'est pas orpheline.** Les cellules sans cellule de code après elles ont été reprises une par une : toutes ferment la dernière section, et le verdict qui les laissait tranquilles était juste. Le rapport en dénombre une, `02-SemanticKernel-Advanced` (corrigée par #10705), et elle parlait d'un sujet **différent** du code voisin — le classificateur positionnel ne peut pas la voir, seule la lecture le peut.

Conséquence pratique pour un reviewer : `gap_after = None` (aucune cellule de code après l'interp) est une **absence de voisin**, pas un orphelin ; et un `def`/`class` entre l'interp et le code suivant n'est pas un déplacement. Un scan se **classe avant d'être committé** : la confiance dans un « détecteur élargi » est précisément ce qui a produit ces faux positifs. Méthode, comptes et cas nommés restent dans les rapports, cités ci-dessous.

## Voir aussi

- Epic **#10678** — remise en ordre + prévention (audit Phase 1, fix Phase 2 PyMC-15 #10685/#10686, cette règle Phase 3/4)
- [2026-08-13-10678-interp-positioning-audit.md](../../docs/transients/2026-08-13-10678-interp-positioning-audit.md) — rapport de l'audit de positionnement (Phase 1) : périmètre balayé, heuristique d'écart, cas classés
- [2026-08-15-10678-orphan-interp-scan.md](../../docs/transients/2026-08-15-10678-orphan-interp-scan.md) — rapport du re-scan des interps en fin de carnet (Phase 1b) : la calibration ci-dessus, cellule par cellule
- [notebook-conventions.md](notebook-conventions.md) C.3 — scope des re-exécutions (exception markdown-only = l'angle mort)
- [verify-before-claiming.md](verify-before-claiming.md) — l'agent enricher qui déclare « inséré après outputs » sans vérifier = claim non vérifié
- `scan_cell_ordering.py` docstring — catégorie `INTERP_BEFORE_CODE` (structurel) vs `INTERP_OUTPUT_MISMATCH` (triage)
