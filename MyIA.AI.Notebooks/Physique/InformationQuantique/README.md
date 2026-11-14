# Information quantique — tester l'intrication d'états mixtes par le calcul

Sous-série Physique de la collection [MyIA.AI.Notebooks](../../README.md). Le fil
« information quantique » fait calculer les objets opérationnels de l'intrication des
états mixtes — états de Werner, transposition partielle, témoins, canal de Choi —
sur des matrices explicites, pas sur des phrases. Chaque seuil cité (séparabilité,
distillabilité, indice de rupture d'intrication) est **retrouvé numériquement** par le
carnet avant d'être confronté à son énoncé théorique dans la source archivée ; les
nombres que les sources n'établissent pas ne sont pas attribués.

La sous-série se distingue du fil « Chaînes » voisin : Chaînes-01/02 étudient un
programme de physique-de-l'information où l'« intrication » désigne un axiome
combinatoire sur des réseaux de paires ; ici, l'intrication est celle des états
d'un système bipartite — matrices de densité, spectre de la transposition partielle,
distillation par opérations locales. Les deux emplois du mot sont explicitement
distingués dans le premier carnet, avec renvoi vers l'organe CHSH du dépôt
(Lean-13b/13c) pour l'inégalité de Bell calculée sur des corrélations.

| Carnet | Ce qu'il démontre | Outils |
|---|---|---|
| [InfoQuant-01 — Intrication : Werner, PPT, distillation, canaux à rupture d'intrication](InfoQuant-01-Intrication-Werner-PPT-Distillation-Python.ipynb) | Six notions de l'intrication des états mixtes, chacune portée par un calcul de matrices : états mixtes et purification (décomposition spectrale puis vecteur de Schmidt par SVD) ; état de Werner à deux qubits avec les valeurs propres de Peres (éq. 7) retrouvées à $10^{-6}$ près ; critère PPT avec l'exemple de Peres (éq. 15), inséparable pour tout $x > 0$, et le rappel que PPT suffit en $2 \times 2$ et $2 \times 3$ mais pas au-delà ; distillabilité — le seuil 1-distillable des Werner $d \otimes d$ dérivé en forme fermée $(3-5\lambda)/12$ pour $d = 3$, qui s'annule exactement au seuil théorique $\lambda = 3/5$ de Dür et al., et la monotonie de $\lambda_N$ vers $1/2$ ; canaux à rupture d'intrication — seuil de Choi $p \geq d/(d+1)$ vérifié en $d = 2$ et $d = 3$, indice $n(\Delta_\lambda)$ coïncidant avec la formule de Lami (éq. 34) | numpy |

## Positionnement épistémique

Comme pour le fil Chaînes, chaque affirmation porte son statut : **calculé** (le carnet
produit le nombre), **démontré dans la source** (le théorème est cité avec sa référence
archivée) ou **non établi** (écarté). Le carnet ne démontre pas les théorèmes — la
suffisance de PPT en $2 \times 2$/$2 \times 3$, la non-distillabilité des états PPT,
le théorème de rupture d'intrication de Holevo-Shirokov — il les met en œuvre sur des
exemples et en vérifie les conséquences numériques. Les seuils présentés sont ceux
établis par les sources ; deux nombres mentionnés dans l'issue d'ouverture
(la borne 37/80, le seuil à trois copies en $d = 3, 4$) n'ont pas été retrouvés
dans les copies archivées et sont exclus de l'exposé.

Les sources sont archivées au gisement
`G:\Mon Drive\MyIA\IA\Bibliographie IA\Physics\` avant écriture, citées avec
attribution dans le carnet et sa bibliographie.
