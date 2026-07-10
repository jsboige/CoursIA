# examples - Cas d'usage spécifiques

[← Image Applications](../04-Applications/) | [↑ Image](../README.md) | [→ Audio](../../Audio/README.md)

Exemples concrets d'utilisation des notebooks GenAI Image dans différents domaines éducatifs et professionnels.

**Dans le cadre du fil rouge contenu visuel educatif** : ces notebooks montrent l'application directe des techniques des niveaux precedents. [science-diagrams](science-diagrams.ipynb) genere des diagrammes et schemas techniques pour les cours de sciences. [history-geography](history-geography.ipynb) cree des cartes et reconstitutions historiques. [literature-visual](literature-visual.ipynb) illustre des textes litteraires.

## Vue d'overview

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 3 |
| Domaines | 3 |
| Durée totale | ~2-3h |
| Difficulté | Intermédiaire |

## Notebooks par domaine

| Domaine | Notebook | Description |
|---------|---------|-------------|
| **Histoire-Geographie** | [history-geography](history-geography.ipynb) | Création de cartes historiques, reconstitutions, illustrations éducatives |
| **Littérature** | [literature-visual](literature-visual.ipynb) | Illustrations de textes, couvertures de livres, visuels narratifs |
| **Science** | [science-diagrams](science-diagrams.ipynb) | Diagrammes scientifiques, schémas techniques, visualisations complexes |

## Exemples concrets

Les trois notebooks ont été exécutés avec `gpt-image-1` ; les figures ci-dessous sont leurs sorties réelles, réduites en WebP pour l'affichage. La provenance et le poids natif de chaque image sont détaillés dans [`assets/readme/MANIFEST.md`](assets/readme/MANIFEST.md).

### Histoire-Géographie

Le notebook [history-geography](history-geography.ipynb) couvre trois usages distincts : la cartographie pédagogique, la reconstitution de monuments et la mise en frise des événements.

Pour la **cartographie**, le prompt décrit une aire géographique, ses subdivisions et le contenu attendu de la légende ; le modèle rend alors une carte lisible plutôt qu'une illustration décorative. La figure ci-dessous représente l'Empire romain à son apogée en 117 ap. J.-C. : provinces en aplats colorés (Gallia, Britannia, Italia, Asia, Africa…), Méditerranée centrale, légende (province, cité, route) et rose des vents.

<p align="center">
<img src="assets/readme/imgex-hist1.webp" alt="Carte pédagogique de l'Empire romain à son apogée (117 ap. J.-C.) : provinces en aplats colorés, Méditerranée centrale, légende et rose des vents" width="480"/><br/>
<sub><b>Empire romain (117 ap. J.-C.)</b> — carte d'expansion en format paysage : provinces nommées, réseau routier, légende et rose des vents (usages : Histoire 6ᵉ, comparaison avec l'Europe actuelle)</sub>
</p>

La **reconstitution de monuments** restitue un édifice dans son état d'origine. Ici, le Colisée de Rome au Iᵉʳ siècle apparaît en rendu photoréaliste — amphithéâtre complet, velarium déployé, gradins peuplés d'une foule en toges — soit l'inverse de la ruine que l'on visite aujourd'hui.

<p align="center">
<img src="assets/readme/imgex-hist2.webp" alt="Reconstruction photoréaliste du Colisée de Rome au Ier siècle : amphithéâtre complet, velarium déployé, foule en toges" width="480"/><br/>
<sub><b>Colisée de Rome (Iᵉʳ siècle)</b> — reconstruction photoréaliste de l'amphithéâtre dans son état d'origine (marbre et travertin, velarium, gradins peuplés)</sub>
</p>

Enfin, pour la **chronologie**, le notebook compose une frise horizontale illustrée. Celle de la Révolution française jalonne la décennie 1789-1799 : prise de la Bastille (1789), Première République (1792), Terreur (1793), coup d'État de Napoléon (1799), sur une barre bleu-blanc-rouge, dans un style poster éducatif.

<p align="center">
<img src="assets/readme/imgex-hist3.webp" alt="Frise chronologique illustrée de la Révolution française 1789-1799 : Bastille, Première République, Terreur, coup de Napoléon, barre tricolore" width="480"/><br/>
<sub><b>Révolution française (1789-1799)</b> — frise chronologique horizontale : Bastille (1789), Première République (1792), Terreur (1793), coup de Napoléon (1799), barre bleu-blanc-rouge</sub>
</p>

### Littérature

Le notebook [literature-visual](literature-visual.ipynb) transforme un texte en image, de la scène de roman à la planche de personnage.

L'**illustration de scène** part d'un passage descriptif. La barricade des *Misérables* de Victor Hugo (1862) donne une peinture à l'huile romantique et dramatique : un jeune homme brandit le drapeau rouge au sommet de la barricade, un enfant tient un pistolet, dans une facture inspirée de Delacroix.

<p align="center">
<img src="assets/readme/imgex-lit1.webp" alt="Peinture à l'huile romantique de la barricade des Misérables : jeune homme au drapeau rouge, enfant au pistolet, style Delacroix" width="480"/><br/>
<sub><b>Les Misérables — la barricade</b> (Victor Hugo, 1862) — illustration de scène en peinture à l'huile romantique, format portrait (usages : français 4ᵉ/3ᵉ, révolution et justice sociale)</sub>
</p>

La **planche de personnage** (character design) rassemble plusieurs vues d'un même protagoniste. Le notebook la produit pour *Le Petit Prince* de Saint-Exupéry : une aquarelle réunit l'enfant blond à l'écharpe jaune sous plusieurs poses, le renard, la rose sous sa cloche de verre et le ciel étoilé.

<p align="center">
<img src="assets/readme/imgex-lit2.webp" alt="Planche de personnage aquarelle du Petit Prince de Saint-Exupéry : enfant blond à l'écharpe jaune sous plusieurs poses, le renard, la rose sous cloche, ciel étoilé" width="480"/><br/>
<sub><b>Le Petit Prince</b> (Saint-Exupéry) — planche de personnage à l'aquarelle : le prince à l'écharpe jaune en plusieurs poses, le renard, la rose sous cloche, ciel étoilé (usages : français CM2/6ᵉ, analyse de personnage et de symboles)</sub>
</p>

### Science

Le notebook [science-diagrams](science-diagrams.ipynb) génère des schémas annotés plutôt que des images d'ambiance. La coupe de cellule animale ci-dessous en est un exemple : membrane, noyau (enveloppe nucléaire et chromatine), mitochondries, réticulum endoplasmique (rugueux et lisse), appareil de Golgi, ribosomes, lysosomes et cytoplasme y sont légendés un à un.

<p align="center">
<img src="assets/readme/imgex-sci.webp" alt="Schéma pédagogique en coupe d'une cellule animale avec organites légendés : membrane, noyau, mitochondries, réticulum endoplasmique, Golgi, ribosomes, lysosomes" width="480"/><br/>
<sub><b>Cellule animale en coupe</b> — schéma des organites légendés (membrane, noyau, mitochondries, réticulum endoplasmique, appareil de Golgi, lysosomes) (usages : biologie cellulaire niveau lycée, identification des organites)</sub>
</p>

## Workflow typique

1. **Brief** : Définir le besoin et le style visuel
2. **Sélection du modèle** : Choisir le modèle le plus adapté
3. **Génération** : Créer les images avec paramètres précis
4. **Post-processing** : Amélioration et édition si nécessaire
5. **Intégration** : Utilisation dans le support final

## Ressources

- [Documentation Image principale](../README.md)
- [Tous les notebooks Image](../README.md)