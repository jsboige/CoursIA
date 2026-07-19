# Le Jeu de la Vie de Conway — Archive de Motifs RLE

Source : miroir [copy.sh/life](https://copy.sh/life/) des motifs de [LifeWiki](https://conwaylife.com/wiki/Main_Page).

## Motifs

| Fichier | Motif | Auteur | Taille | Grille | Période |
|---------|-------|--------|--------|--------|---------|
| `otcametapixel.rle` | OTCA Metapixel | Brice Due (2006) | 165 KB | 2058x2058 | 35 328 |
| `turingmachine.rle` | Machine de Turing | Paul Rendell (2000) | 104 KB | variable | N/A |
| `p5760unitlifecell.rle` | Cellule de Vie unitaire p5760 | David Bell | 15 KB | 499x499 | 5 760 |
| `gemini.rle` | Auto-réplicateur Gemini | Andrew Wade (2010) | 5,3 MB | immense | 33 699 586 |

## Correspondance avec Pillars.lean

Ces fichiers RLE correspondent aux théorèmes témoins échafaudés dans
`Conway.Life.Pillars` :

| Théorème pilier | Fichier RLE | Nombre de générations |
|-----------------|-------------|------------------------|
| `otca_metapixel_witness` | `otcametapixel.rle` | 35 328 |
| `unitcell_witness` | `p5760unitlifecell.rle` (le plus proche disponible) | 4 096 |
| `gemini_witness` | `gemini.rle` | 33 699 586 |
| `cpu_witness` | pas encore disponible | 1 048 576 |

## Téléchargement

```bash
# Depuis le miroir copy.sh (accessible sans détection de bot)
MIRROR="https://copy.sh/life/examples"
curl -L -A "Mozilla/5.0" "$MIRROR/otcametapixel.rle" -o otcametapixel.rle
curl -L -A "Mozilla/5.0" "$MIRROR/gemini.rle" -o gemini.rle
curl -L -A "Mozilla/5.0" "$MIRROR/turingmachine.rle" -o turingmachine.rle
curl -L -A "Mozilla/5.0" "$MIRROR/p5760unitlifecell.rle" -o p5760unitlifecell.rle
```

## Note sur Gemini

`gemini.rle` (5,3 Mo) est gitignoré en raison de sa taille. Il peut être
re-téléchargé depuis le miroir copy.sh avec la commande ci-dessus. La fonction
`fetch_rle()` du notebook gère ce cas gracieusement via un cache disque.
