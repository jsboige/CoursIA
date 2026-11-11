# Pli 5 : protocole de mesure multiway

Ce protocole est fixé avant le relevé `multiway_results.json`. La règle comporte
les deux alternatives `{{x,y}} → {{x,y},{x,x}}` et
`{{x,y}} → {{x,y},{y,y}}`, sur `{{1,2}}`. Un état est un **multiensemble**
d'arêtes ordonnées : on trie les arêtes pour fusionner les histoires conduisant
au même état, sans identifier les atomes par isomorphisme. Le nombre de chemins
et le nombre d'états ne sont pas interchangeables.

Pour chaque profondeur 16, 24, 32, 40 et 48, mesurer cinq parcours indépendants
à partir de la graine, avec `steady_clock`; prendre la médiane. Le temps inclut
la construction des états et la vérification exhaustive, pas la compilation.
Ajuster par moindres carrés `log(temps) = a + alpha log(nombre d'états finaux)`.
Le calcul d'alpha est descriptif : on qualifiera l'ajustement de peu informatif
si R² < 0,95. Il ne prouve ni irréductibilité générale ni complexité asymptotique.

Contrôle prédéclaré : au pas n il y a exactement n+1 états : l'arête 12 et n
boucles, dont k boucles 11 et n−k boucles 22, pour tout k de 0 à n. Comparer
l'ensemble entier obtenu à cet ensemble, à chaque pas et chaque répétition.
Un écart interrompt le programme avant toute mesure acceptée. Un contrôle
positif sur la graine et un contrôle négatif qui supprime une alternative
exercent ce témoin avant la mesure. Le processus est limité à 512 Mio et 40 s ;
le programme s’arrête à 30 s entre deux pas, à 49 états ou à 48 pas. Ce témoin découle
des règles : réécrire 12 ajoute 11 ou 22, réécrire une boucle la duplique.

Le cœur du matcher est libSetReplace officiel (`maxitg/SetReplace`, MIT), commit
`44c868bf4622e4542b306846ffdcc47c19d0bba8`. Le code local orchestre les états,
mais ne réimplémente pas l'appariement ou l'instanciation des règles. Les essais
exploratoires aux profondeurs 8 et 32 ont servi à fixer ce budget ; ils ne sont
pas inclus dans le relevé. Pli 5 utilise l'idée de la matrice de #19766 :
réécriture locale et ramifications multiway, comparées au pli 3 de #19742.
