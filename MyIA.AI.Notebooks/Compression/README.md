# Compression — Théorie et pratique du codage de source

Série en construction. Premier notebook de **découverte** : les **codes préfixes**, leur
optimalité et la borne de Shannon. Le codage statistique — Huffman en compression,
Lempel-Ziv en non-statistique — y est posé sur des corpus mesurés, et la borne théorique
$-\\sum p \\log_2 p$ y est dérivée cellule par cellule.

La série se lira ensuite par famille d'algorithmes : Shannon-Fano et Huffman (caractère par
caractère, optimal ou proche), Lempel-Ziv (sans connaître les fréquences à l'avance), puis
les codes arithmétiques et ANS (qui approchent vraiment la borne). Chaque notebook principal
posera une notion, avec un approfondissement `b` pour les résultats de pointe.

## Notebooks

| Notebook | Public | Accrétion | Hommage | Contenu | Langue |
|---|---|---|---|---|---|
| [`Compression-01-ShannonFano-Prefixe-Python.ipynb`](Compression-01-ShannonFano-Prefixe-Python.ipynb) | Découverte | — | — (socle) | Pourquoi un code de longueur variable doit être **préfixe** pour être décodable (ambiguïté du glouton sur `0/10/110` vs unicité du décodage sur l'arbre préfixe) ; inégalité de **Kraft** $\\sum 2^{-\\ell_i} \\leq 1$ comme condition nécessaire sur les longueurs ; **Shannon-Fano** construit récursivement (trier, partitionner, attribuer `0`/`1`, récurser) sur BANANE ORANGE puis sur 4 corpus-types ; **Huffman** par fusion itérative des deux plus petits nœuds sur les mêmes corpus — comparaison directe, mesure de l'écart à l'entropie $H = -\\sum p \\log_2 p$, conclusion pratique : longueur moyenne identique à celle de SF sur les corpus réguliers, écart réel quand la distribution est pathologique ; trois exercices exécutables (vérificateur de Kraft, code SF sur ABRACADABRA, comparaison SF/Huf sur 6 symboles) | Français |

## Parcours

| Position | Notebook principal | Public | Approfondissement |
|---|---|---|---|
| 01 | Codes préfixes, Shannon-Fano et Huffman | Découverte | — |
| 02 | Lempel-Ziv *(à venir)* | Découverte | — |
| 03 | Codage arithmétique *(à venir)* | Licence | — |

## Position dans le dépôt

La série Compression dialogue avec **Complexity** (même théorie de l'information sous-jacente :
la notion de **pas** vs la notion de **bit**) et avec **Search** (les algorithmes de
compression sont des algorithmes — leur coût en pas importe dès qu'on décompresse à la volée).
Le formalisme des codes préfixes est aussi la base du codage de Huffman utilisé dans
`Image-01-Compression` (GenAI), `Search-08` (heuristiques), et la famille des quantbooks
(sérialisation compacte des signaux).