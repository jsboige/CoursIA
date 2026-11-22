> REFERENCE — vivante — dernière révision 2026-11-21

# 3D Tiles — mesures publiques et prototype local

## Objet et périmètre

Cette note distingue deux observations qui ne doivent pas être confondues : le comportement d'un viewer public observé sur une scène publiée, et un prototype local construit pour tester une diffusion hiérarchique. Elles documentent un cas d'usage et un protocole de mesure ; elles ne certifient ni la précision géométrique, ni l'exactitude d'un modèle terrain, ni les performances d'un service en production.

Le carnet pédagogique [3D-10 — SIG web : couches, repères et niveaux de détail](../../MyIA.AI.Notebooks/GenAI/3D/10-SIG-3D-Tiles-Python.ipynb) reste volontairement autonome et synthétique : il compare des grilles et illustre les niveaux de détail, sans service distant, sans Cesium et sans mesure réseau. Les observations ci-dessous ne sont donc pas des sorties de ce carnet.

## 1. Viewer public — scène monolithique

Lors de l'observation initiale du viewer public, le contenu 3D était servi sous la forme d'un unique fichier `terrain.glb` de 17 337 Ko (environ 16,9 Mio). Le transfert observé durait 23,427 s, sans compression HTTP relevée. L'affichage utile attendait la fin du téléchargement complet. Un zoom n'a déclenché aucune ressource supplémentaire dans les interactions observées. La mémoire heap JavaScript mesurée était de 44 à 45 Mo ; cette mesure ne comprend pas la mémoire GPU où réside le maillage.

Ces chiffres décrivent cette session et ce viewer, pas une propriété générale des viewers 3D. En particulier, l'absence de requêtes additionnelles au zoom concorde avec le chargement monolithique observé ; elle ne prouve pas qu'aucune variante ou ressource n'existe dans d'autres conditions.

## 2. Prototype local — hiérarchie de tuiles

Un prototype local a ensuite servi à vérifier la faisabilité d'un découpage hiérarchique avec CesiumJS 1.135. Sur le jeu d'essai utilisé, 85 tuiles sur 85 étaient prêtes ; la scène affichait 303 457 triangles. Le proxy racine comptait 764 sommets et 1 437 triangles, pour 36 588 octets. La première tuile devenait visible après 6,55 s et le chargement complet était observé après 10,6 s. Les textures GPU représentaient 111 Mo.

Ces valeurs caractérisent une exécution de prototype local et son jeu d'essai. Elles ne sont pas directement comparables au transfert du viewer public : les scènes, les machines, le réseau et les conditions de mesure ne constituent pas un protocole contrôlé commun. Elles montrent qu'une hiérarchie rend possible une première visibilité avant la fin du chargement complet dans ce prototype ; elles ne démontrent pas à elles seules un gain généralisable.

## 3. Lecture et limites

- Le contraste observé porte d'abord sur le mode de livraison : un GLB monolithique dans le viewer public, contre un ensemble de tuiles hiérarchisées dans le prototype.
- Le délai de première visibilité et la durée de chargement complet sont deux métriques distinctes. Une mesure robuste doit aussi fixer le viewport, la caméra, la machine, le cache, la connexion et la définition de « visible » et « complet ».
- La heap JavaScript n'est pas la mémoire totale du processus : il faut relever séparément RAM, mémoire GPU et ressources réseau.
- Un maillage détaillé ou un rendu visuellement plausible ne prouve pas l'exactitude du terrain. Il faut des métadonnées, un CRS et un datum vertical explicites, ainsi que des points de contrôle indépendants.
- Le prototype ne constitue pas une comparaison contrôlée ni une validation métier. Aucune capture, donnée ou référence métier privée n'est publiée dans cette note.

Pour une comparaison reproductible, répéter chaque scénario avec cache froid puis chaud, garder une caméra et un viewport fixes, enregistrer les requêtes et leurs tailles, relever le temps jusqu'à la première image utile et jusqu'à stabilisation, puis répéter depuis un second angle. Présenter les résultats comme des observations de l'environnement testé, pas comme des garanties de service.

## Référence pédagogique

Le carnet [`3D-10-SIG-3D-Tiles-Python.ipynb`](../../MyIA.AI.Notebooks/GenAI/3D/10-SIG-3D-Tiles-Python.ipynb) explique les rôles différents de WMS, WMTS, services de terrain et 3D Tiles, et montre le sous-échantillonnage d'une grille synthétique. Il indique explicitement que cette simulation n'est ni un format 3D Tiles ni une mesure réseau.
