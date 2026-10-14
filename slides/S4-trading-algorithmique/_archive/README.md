# slides/S4-trading-algorithmique/_archive — superseded slide decks

Consolidation #13749 (2026-09-21, tranche 4 « slides »). Cette archive contient
les versions antérieures des decks S4 Trading Algorithmique, avant la refonte
vers Slidev et le split en 3 decks dedies.

Chaque fichier archive porte un en-tete de disposition (standard `_archive`
convention, cf `docs/reference/_archive-convention.md`) avec : date d'archivage,
successeur (chemin ou "none — closed dead-end"), preuve du verdict, et
disposition per-section.

## Table des fichiers archives

| Fichier | Verdict | Superseded by | Verdict recorded in |
|---------|---------|---------------|---------------------|
| `slides.md` | SUPERSEDED (deck unique → split en 3) | `deck-1-fondamentaux.md`, `deck-2-strategies.md`, `deck-3-pratique-lean.md` | commit `cc96a2c88d` (kernel drift guard) + split dans l'arbre |
| `slides.marp.md` | SUPERSEDED (Marp → Slidev) | `deck-1-fondamentaux.md` (meme contenu, frontmatter Slidev) | frontmatter `marp: true` vs Slidev theme |
| `slides-export.pdf` | SUPERSEDED (export du deck unique avant split) | `slidev-export/*.png` (127 slides exportees) | `extracted/inventory.json` |
| `deck-4-workflow-agentique.md` | NO BEATS (deck additionnel non retenu) | none — closed dead-end (serie fixee a 3 decks) | ce README + absence de `deck-4-*.md` dans l'arbre courant |

## Criteres d'eligibilite verifies (convention `_archive/`)

1. **Verdict enregistre durablement** : commits git (cf table ci-dessus) + ce README.
2. **Zero reference depuis docs actives** : aucun lien entrant depuis `deck-1/2/3.md`,
   `analysis/*.md`, ou `slidev-export/` vers les fichiers archives.
3. **Zero import** : les decks modernes ne referencent pas le contenu archive
   (la thematique agentique du deck-4 a ete partiellement absorbee dans
   `_tools/` / `analysis/`, pas dans les decks officiels).
4. **Successeur existe ou cloture explicite** : 3 fichiers ont un successeur
   explicite ; le deck-4 est documente comme dead-end ferme (la serie S4 reste
   a 3 decks par decision pedagogique).

## Application du standard `_archive/`

- Tranche 4 de l'umbrella #13749 (cf `docs/reference/_archive-convention.md` ligne 85).
- Convention `_archive/` preservee (sans 's' final, sans suffixe date), conformement
  a la campagne rename #9535 (commit `928147688d`) qui a renomme `archive/` → `_archive/`.
- Localisation preservee (pas d'unification `docs/archive/code/`) — les slides
  archivees referencent `../theme-ia101` et doivent rester a proximite de leur domaine.

## Per-section disposition (deck-4-workflow-agentique.md)

Le deck-4 contient une section "Workflow Agentique VSCode + MCP QuantConnect".
Cette thematique a ete partiellement reprise dans :
- `analysis/` (validation, comparaison) — pas dans les decks officiels
- `_tools/` (scripts d'outillage) — pas dans les decks

**Raison du dead-end** : la serie S4 reste structuree en 3 decks (fondamentaux /
strategies / pratique-lean). Le deck-4 aurait complete la serie avec un quatrieme
pilier, mais le volume pedagogique deja couvert dans les 3 decks a rendu cette
extension redondante. **Pas de resurrection prevue**.

## Pourquoi cette archive

Un `_archive/` standardise n'est pas une poubelle : c'est un **registre de
decisions**. Les decks archives ici permettent de :
- Reouvrir une version anterieure si le split en 3 decks pose probleme.
- Comprendre pourquoi le deck-4 n'a pas ete retenu (verdict dead-end documente).
- Preserver l'export PDF comme preuve de l'etat anterieur.

Cf CLAUDE.md global — « Consolider != Archiver » (preserver avant de reduire,
citer la cible comme preuve).
