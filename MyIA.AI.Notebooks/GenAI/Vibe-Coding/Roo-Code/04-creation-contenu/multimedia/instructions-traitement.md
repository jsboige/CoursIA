# 🛠️ Instructions de Traitement d'Images

Ce document présente des exemples d'instructions détaillées pour différentes tâches courantes de traitement d'images. Vous pouvez demander à Roo de vous fournir des instructions similaires, adaptées à vos besoins spécifiques et à votre niveau de compétence.

## Table des matières

1. [Remplacement d'arrière-plan dans Photoshop](#1-remplacement-darrière-plan-dans-photoshop)
2. [Correction de la balance des couleurs dans GIMP](#2-correction-de-la-balance-des-couleurs-dans-gimp)
3. [Optimisation d'images pour le web](#3-optimisation-dimages-pour-le-web)
4. [Création d'un effet vintage](#4-création-dun-effet-vintage)
5. [Retouche de portrait basique](#5-retouche-de-portrait-basique)
6. [Création d'un montage photo simple](#6-création-dun-montage-photo-simple)
7. [Restauration de photo ancienne](#7-restauration-de-photo-ancienne)

## 1. Remplacement d'arrière-plan dans Photoshop

### Niveau : Débutant à intermédiaire
### Logiciel : Adobe Photoshop (version CC 2020 ou ultérieure)

#### Objectif
Remplacer l'arrière-plan d'une photo de portrait par un fond uni professionnel.

#### Matériel nécessaire
- Image portrait originale
- Photoshop CC
- Souris ou tablette graphique (recommandée pour plus de précision)

#### Instructions étape par étape

1. **Préparation du document**
   - Ouvrez votre image dans Photoshop (Fichier > Ouvrir)
   - Dupliquez le calque d'arrière-plan en faisant un clic droit sur le calque dans le panneau Calques et en sélectionnant "Dupliquer le calque"
   - Renommez ce nouveau calque "Sujet"
2. **Sélection du sujet avec l'outil Sélection d'objet (méthode moderne)**
   - Sélectionnez l'outil "Sélection d'objet" dans la barre d'outils (ou appuyez sur W)
   - Cliquez sur "Sélectionner un sujet" dans la barre d'options en haut
   - Photoshop utilisera l'IA pour détecter et sélectionner automatiquement le sujet principal
   - Affinez la sélection si nécessaire en utilisant le mode "Ajouter" ou "Soustraire" dans la barre d'options

3. **Affinage de la sélection (pour les cheveux et détails fins)**
   - Allez dans Sélection > Sélectionner et masquer
   - Dans le panneau qui s'ouvre, utilisez les options suivantes :
     - Mode d'affichage : Sur calque (B) ou Incrustation (V) pour mieux voir votre sélection
     - Rayon intelligent : Cochez cette option et ajustez le curseur (environ 5-10 px)
     - Affiner les bords : Utilisez l'outil "Affiner les bords" (deuxième icône) pour peindre sur les zones de cheveux ou détails fins
     - Lissage : Environ 2-3
     - Contour progressif : 0.5-1 px pour un bord naturel
     - Décalage du contour : 0%
   - Cliquez sur "OK" et choisissez "Nouveau calque avec masque de fusion" comme sortie

4. **Création du nouvel arrière-plan**
   - Créez un nouveau calque en cliquant sur l'icône "Créer un nouveau calque" en bas du panneau Calques
   - Placez ce calque sous votre calque "Sujet"
   - Renommez-le "Arrière-plan"
   - Sélectionnez l'outil Pot de peinture (G)
   - Choisissez une couleur de fond appropriée (par exemple, un gris clair neutre #E0E0E0 ou un bleu très pâle #F0F5FA)
   - Cliquez sur le calque d'arrière-plan pour le remplir avec la couleur choisie

5. **Ajustements finaux**
   - Si nécessaire, affinez le masque de fusion du calque "Sujet" en le sélectionnant et en utilisant un pinceau noir (pour masquer) ou blanc (pour révéler)
   - Pour un effet plus professionnel, ajoutez une ombre portée au sujet :
     - Clic droit sur le calque "Sujet" > Styles de calque > Ombre portée
     - Paramètres recommandés : Opacité 30%, Angle 120°, Distance 10px, Diffusion 10px, Taille 15px

6. **Enregistrement du résultat**
   - Allez dans Fichier > Enregistrer sous
   - Choisissez le format PSD pour conserver les calques (pour modifications futures)
   - Pour une version finale, allez dans Fichier > Exporter > Enregistrer pour le Web (hérité) et choisissez JPG de haute qualité

#### Conseils supplémentaires
- Pour un arrière-plan plus élaboré, vous pouvez utiliser un dégradé au lieu d'une couleur unie
- Ajustez l'opacité de l'ombre portée selon la luminosité de votre arrière-plan
- Pour un effet studio, ajoutez un léger vignettage (Filtre > Correction de l'objectif > Personnalisé > Vignettage)

## 2. Correction de la balance des couleurs dans GIMP

### Niveau : Débutant
### Logiciel : GIMP (version 2.10 ou ultérieure)

#### Objectif
Corriger une dominante de couleur indésirable et obtenir des couleurs naturelles.

#### Instructions étape par étape

1. **Préparation du document**
   - Ouvrez votre image dans GIMP (Fichier > Ouvrir)
   - Dupliquez le calque en faisant un clic droit sur le calque dans le panneau Calques et en sélectionnant "Dupliquer le calque"
   - Renommez ce nouveau calque "Correction couleurs"

2. **Correction automatique (première approche)**
   - Allez dans Couleurs > Automatique > Balance des blancs
   - Observez le résultat. Si l'amélioration est satisfaisante, vous pouvez vous arrêter ici
   - Sinon, annulez (Ctrl+Z) et passez à la méthode manuelle

3. **Correction manuelle avec les Courbes**
   - Allez dans Couleurs > Courbes
   - Dans le menu déroulant "Canal", sélectionnez d'abord "Valeur" (luminosité globale)
   - Ajustez la courbe pour améliorer le contraste global :
     - Pour plus de contraste : créez une légère courbe en S
     - Pour éclaircir les tons moyens : tirez légèrement la partie centrale vers le haut
   - Passez ensuite aux canaux de couleur individuels :
     - Si l'image est trop rouge : sélectionnez le canal Rouge et abaissez légèrement la courbe
     - Si l'image est trop bleue : sélectionnez le canal Bleu et abaissez légèrement la courbe
     - Si l'image est trop verte : sélectionnez le canal Vert et abaissez légèrement la courbe
   - Cliquez sur "OK" pour appliquer les changements
4. **Ajustement de la température des couleurs**
   - Allez dans Couleurs > Température des couleurs
   - Si l'image est trop froide (bleuâtre), déplacez le curseur vers la droite (plus chaud)
   - Si l'image est trop chaude (jaunâtre/orangée), déplacez le curseur vers la gauche (plus froid)
   - Ajustez également le curseur de teinte si nécessaire pour corriger une dominante verte ou magenta
   - Cliquez sur "OK" pour appliquer

5. **Ajustement de la saturation (optionnel)**
   - Si les couleurs semblent ternes après correction, allez dans Couleurs > Teinte-Saturation
   - Augmentez légèrement la saturation (environ +10 à +20)
   - Vous pouvez ajuster la saturation par plage de couleurs (Rouges, Jaunes, Verts, etc.) si nécessaire
   - Cliquez sur "OK" pour appliquer

6. **Vérification avec des références**
   - Vérifiez les zones qui devraient être neutres (blanc, gris) pour vous assurer qu'elles n'ont pas de dominante de couleur
   - Vérifiez les tons chair pour vous assurer qu'ils paraissent naturels
   - Si nécessaire, faites des ajustements supplémentaires

7. **Enregistrement du résultat**
   - Allez dans Fichier > Exporter sous
   - Choisissez le format XCF pour conserver les calques (pour modifications futures)
   - Pour une version finale, exportez en JPG ou PNG selon vos besoins

#### Conseils supplémentaires
- Utilisez la touche de basculement d'aperçu (œil) dans les dialogues d'ajustement pour comparer avant/après
- Pour les photos de personnes, concentrez-vous sur l'apparence naturelle des tons chair
- Si possible, utilisez un écran calibré pour des résultats plus précis

## 3. Optimisation d'images pour le web

### Niveau : Débutant
### Logiciel : Divers (Photoshop, GIMP, ou outils en ligne comme Squoosh)

#### Objectif
Réduire la taille des fichiers images tout en maintenant une qualité visuelle acceptable pour le web.

#### Instructions étape par étape

1. **Redimensionnement de l'image**
   - Déterminez la taille maximale nécessaire pour votre image sur le web
     - Pour une image pleine largeur : généralement 1200-1600px de large
     - Pour une image de contenu : généralement 800-1000px de large
     - Pour une vignette : généralement 300-500px de large
   
   **Dans Photoshop :**
   - Allez dans Image > Taille de l'image
   - Entrez la largeur souhaitée (la hauteur s'ajustera proportionnellement si "Conserver les proportions" est coché)
   - Assurez-vous que la méthode de rééchantillonnage est définie sur "Automatique" ou "Bicubique plus net"
   
   **Dans GIMP :**
   - Allez dans Image > Échelle l'image
   - Entrez la largeur souhaitée (la hauteur s'ajustera automatiquement)
   - Choisissez "Sinc (Lanczos3)" comme méthode d'interpolation pour la meilleure qualité

2. **Choix du format approprié**
   - **JPEG** : Idéal pour les photographies et images avec beaucoup de couleurs
   - **PNG** : Meilleur pour les images avec transparence, texte ou peu de couleurs
   - **WebP** : Format moderne avec meilleure compression (vérifiez la compatibilité des navigateurs)
   - **SVG** : Pour les graphiques vectoriels (logos, icônes)
3. **Exportation optimisée**
   
   **Pour JPEG (Photoshop) :**
   - Allez dans Fichier > Exporter > Enregistrer pour le Web (hérité)
   - Sélectionnez JPEG comme format
   - Ajustez la qualité entre 60-80% (un bon équilibre qualité/taille)
   - Activez l'option "Optimisé"
   - Vérifiez la taille du fichier affichée en bas à gauche
   
   **Pour JPEG (GIMP) :**
   - Allez dans Fichier > Exporter sous
   - Nommez votre fichier avec l'extension .jpg
   - Dans la boîte de dialogue d'exportation JPEG, réglez la qualité entre 70-85
   - Cochez "Enregistrer les données EXIF" et "Enregistrer les données XMP" uniquement si nécessaire
   
   **Pour PNG (Photoshop) :**
   - Allez dans Fichier > Exporter > Enregistrer pour le Web (hérité)
   - Sélectionnez PNG-8 pour les images simples (moins de 256 couleurs) ou PNG-24 pour les images complexes
   - Pour PNG-8, ajustez le nombre de couleurs au minimum acceptable
   
   **Pour PNG (GIMP) :**
   - Allez dans Fichier > Exporter sous
   - Nommez votre fichier avec l'extension .png
   - Dans la boîte de dialogue d'exportation PNG, ajustez le niveau de compression (plus élevé = fichier plus petit mais export plus lent)

4. **Compression supplémentaire (optionnelle)**
   - Utilisez des outils en ligne comme TinyPNG, Squoosh, ou ImageOptim pour réduire davantage la taille
   - Ces outils utilisent des algorithmes avancés pour réduire la taille sans perte visible de qualité

5. **Vérification finale**
   - Ouvrez l'image optimisée dans un navigateur pour vérifier son apparence
   - Comparez la taille du fichier original et optimisé
   - Vérifiez qu'il n'y a pas d'artefacts de compression visibles à l'œil nu

#### Conseils supplémentaires
- Utilisez des images responsives avec l'attribut `srcset` en HTML pour servir différentes tailles selon l'appareil
- Envisagez le chargement différé (lazy loading) pour les images sous la ligne de flottaison
- Pour les sites avec beaucoup d'images, utilisez un CDN (Content Delivery Network)
- Nommez vos fichiers avec des mots-clés pertinents pour le SEO

## 4. Création d'un effet vintage

### Niveau : Intermédiaire
### Logiciel : Adobe Photoshop

#### Objectif
Transformer une photo moderne en une image au look vintage/rétro des années 60-70.

#### Instructions étape par étape

1. **Préparation du document**
   - Ouvrez votre image dans Photoshop
   - Dupliquez le calque d'arrière-plan (Ctrl+J ou Cmd+J)
   - Renommez ce calque "Effet vintage"

2. **Ajustement des couleurs de base**
   - Ajoutez un calque de réglage "Courbes" (cliquez sur l'icône de demi-cercle dans le panneau Calques et sélectionnez "Courbes")
   - Créez une légère courbe en S pour augmenter le contraste
   - Dans le même panneau, passez au canal Rouge et augmentez légèrement les tons moyens et hautes lumières
4. **Ajout de grain photographique**
   - Créez un nouveau calque et remplissez-le de gris 50% (code #808080)
   - Allez dans Filtre > Bruit > Ajout de bruit
   - Réglez la quantité entre 8-12%, sélectionnez "Gaussien" et "Monochromatique"
   - Changez le mode de fusion de ce calque en "Lumière tamisée" ou "Incrustation"
   - Réduisez l'opacité à environ 20-30%

5. **Ajout de vignettage**
   - Créez un nouveau calque
   - Sélectionnez l'outil Ellipse (U) et créez une sélection elliptique qui couvre presque toute l'image
   - Inversez la sélection (Sélection > Intervertir ou Shift+Ctrl+I / Shift+Cmd+I)
   - Remplissez la sélection avec du noir
   - Désélectionnez (Ctrl+D / Cmd+D)
   - Appliquez un flou gaussien (Filtre > Flou > Flou gaussien) d'environ 50-100 pixels
   - Changez le mode de fusion en "Densité couleur -" ou "Densité couleur +"
   - Ajustez l'opacité à environ 40-60%

6. **Ajout de fuites de lumière (optionnel)**
   - Créez un nouveau calque
   - Avec un pinceau doux de grande taille, peignez quelques taches de couleur jaune/orange (#FFD700) dans les coins
   - Changez le mode de fusion en "Superposition" ou "Lumière vive"
   - Réduisez l'opacité à environ 30-40%

7. **Ajout d'un léger flou (optionnel)**
   - Créez un calque fusionné au sommet (Ctrl+Alt+Shift+E / Cmd+Option+Shift+E)
   - Appliquez un très léger flou gaussien (Filtre > Flou > Flou gaussien) d'environ 0.5-1 pixel
   - Réduisez l'opacité à environ 50% si l'effet est trop prononcé

8. **Ajustements finaux**
   - Ajoutez un calque de réglage "Teinte/Saturation" au sommet
   - Réduisez légèrement la saturation globale (-10 à -20)
   - Si nécessaire, ajustez la luminosité et le contraste avec un calque de réglage supplémentaire

9. **Enregistrement du résultat**
   - Enregistrez en PSD pour conserver les calques
   - Exportez en JPG pour le partage

#### Variations de l'effet
- **Look années 50** : Plus contrasté, moins de teinte sépia, grain plus fin
- **Look années 70** : Teintes plus chaudes, contraste réduit, vignettage plus prononcé
- **Look Polaroid** : Ajoutez un cadre blanc, couleurs légèrement délavées, contraste réduit

## 5. Retouche de portrait basique

### Niveau : Débutant à intermédiaire
### Logiciel : Adobe Photoshop

#### Objectif
Effectuer une retouche de portrait naturelle qui améliore l'apparence sans paraître artificielle.

#### Instructions étape par étape

1. **Préparation du document**
   - Ouvrez votre portrait dans Photoshop
   - Dupliquez le calque d'arrière-plan
   - Renommez ce calque "Retouche"

2. **Correction des imperfections cutanées**
   - Sélectionnez l'outil Correcteur localisé (J)
   - Réglez la taille du pinceau légèrement plus grande que l'imperfection à corriger
3. **Réduction des cernes sous les yeux**
   - Créez un nouveau calque (Ctrl+Shift+N / Cmd+Shift+N)
   - Renommez-le "Cernes"
   - Sélectionnez l'outil Pinceau (B) avec une opacité très faible (10-15%)
   - Choisissez une couleur légèrement plus claire que la peau sous les yeux
   - Peignez doucement sur les zones sombres sous les yeux
   - Changez le mode de fusion du calque en "Lumière tamisée"
   - Ajustez l'opacité du calque pour un effet naturel

4. **Éclaircissement des yeux**
   - Créez un nouveau calque nommé "Yeux"
   - Avec un petit pinceau à faible opacité (10-15%), peignez du blanc sur le blanc des yeux
   - Changez le mode de fusion en "Superposition" ou "Lumière tamisée"
   - Réduisez l'opacité jusqu'à ce que l'effet soit subtil

5. **Amélioration des lèvres**
   - Créez un nouveau calque nommé "Lèvres"
   - Avec un pinceau doux à faible opacité (10-15%), peignez une couleur légèrement plus saturée que les lèvres naturelles
   - Changez le mode de fusion en "Couleur" ou "Superposition"
   - Ajustez l'opacité pour un effet naturel

6. **Lissage de la peau avec préservation de la texture**
   - Créez un calque fusionné au sommet (Ctrl+Alt+Shift+E / Cmd+Option+Shift+E)
   - Renommez-le "Lissage peau"
   - Dupliquez ce calque
   - Sur le calque supérieur, appliquez un flou gaussien (Filtre > Flou > Flou gaussien) d'environ 10-15 pixels
   - Ajoutez un masque de fusion au calque flouté
   - Remplissez le masque de noir (Ctrl+I / Cmd+I pour inverser le masque blanc par défaut)
   - Avec un pinceau blanc doux à faible opacité (20-30%), peignez sur les zones de peau à lisser
   - Évitez de peindre sur les yeux, sourcils, lèvres, narines et contours du visage
   - Réduisez l'opacité du calque à environ 40-60%

7. **Amélioration du contraste local (optionnel)**
   - Créez un calque fusionné au sommet
   - Allez dans Filtre > Autres > Passe-haut
   - Réglez le rayon à environ 2-3 pixels
   - Changez le mode de fusion du calque en "Lumière tamisée"
   - Réduisez l'opacité à environ 30-40%
   - Ajoutez un masque de fusion et masquez les zones où vous ne voulez pas accentuer les détails

8. **Ajustements de couleur finaux**
   - Ajoutez un calque de réglage "Vibrance" au sommet
   - Augmentez légèrement la vibrance (+10 à +15) et laissez la saturation inchangée
   - Ajoutez un calque de réglage "Teinte/Saturation" si nécessaire pour ajuster des couleurs spécifiques

9. **Enregistrement du résultat**
   - Enregistrez en PSD pour conserver les calques
   - Exportez en JPG pour le partage

#### Conseils supplémentaires
- Travaillez toujours de manière non destructive (utilisez des calques)
- Prenez régulièrement du recul (zoom arrière) pour évaluer l'aspect naturel
- Moins c'est plus : une retouche subtile est généralement plus flatteuse qu'une retouche excessive
- Utilisez des opacités faibles et construisez l'effet progressivement

## 6. Création d'un montage photo simple

### Niveau : Intermédiaire
### Logiciel : Adobe Photoshop

2. **Placement de l'image d'arrière-plan**
   - Sélectionnez l'image que vous souhaitez utiliser comme arrière-plan
   - Utilisez l'outil Déplacement (V) pour faire glisser cette image dans votre nouveau document
   - Redimensionnez si nécessaire en utilisant Édition > Transformation > Échelle (maintenez Shift pour conserver les proportions)
   - Positionnez l'image comme souhaité

3. **Extraction du sujet de la seconde image**
   - Sélectionnez votre deuxième image
   - Utilisez l'outil "Sélection d'objet" (dans la barre d'outils ou appuyez sur W)
   - Cliquez sur "Sélectionner un sujet" dans la barre d'options
   - Affinez la sélection si nécessaire avec les outils "Ajouter à la sélection" ou "Soustraire de la sélection"
   - Pour les sélections plus complexes, utilisez Sélection > Sélectionner et masquer pour affiner les bords
   - Une fois satisfait, copiez la sélection (Ctrl+C / Cmd+C)

4. **Placement du sujet dans le montage**
   - Retournez à votre document de montage
   - Collez le sujet (Ctrl+V / Cmd+V)
   - Utilisez l'outil Déplacement (V) pour positionner le sujet
   - Redimensionnez si nécessaire avec Édition > Transformation > Échelle
   - Renommez ce calque avec un nom descriptif

5. **Harmonisation des couleurs**
   - Sélectionnez le calque du sujet
   - Ajoutez un calque de réglage "Correspondance de la couleur" (Calque > Nouveau calque de réglage > Correspondance de la couleur)
   - Dans les options, sélectionnez "Source : Document fusionné" et "Calque : Arrière-plan"
   - Ajustez l'opacité du calque de réglage pour un effet plus subtil si nécessaire
   - Alternativement, utilisez des calques de réglage "Teinte/Saturation" ou "Balance des couleurs" pour harmoniser manuellement

6. **Création d'ombres réalistes**
   - Créez un nouveau calque sous le calque du sujet
   - Renommez-le "Ombre"
   - Sélectionnez l'outil Pinceau (B) avec une couleur noire
   - Réglez l'opacité du pinceau à environ 30% et la dureté à 0%
   - Peignez l'ombre sous le sujet, en suivant la direction de la lumière de l'image d'arrière-plan
   - Appliquez un léger flou gaussien à l'ombre (Filtre > Flou > Flou gaussien, environ 10-15 pixels)
   - Ajustez l'opacité du calque d'ombre selon l'effet désiré

7. **Ajustement de l'éclairage**
   - Créez un nouveau calque au-dessus du calque du sujet
   - Réglez le mode de fusion sur "Incrustation" ou "Lumière tamisée"
   - Avec un pinceau doux blanc à faible opacité (15-20%), peignez sur les zones du sujet qui devraient recevoir plus de lumière
   - Avec un pinceau noir à faible opacité, assombrissez les zones qui devraient être dans l'ombre
   - Ajustez l'opacité du calque pour un effet réaliste

8. **Harmonisation finale**
   - Créez un calque fusionné au sommet (Ctrl+Alt+Shift+E / Cmd+Option+Shift+E)
   - Appliquez un léger flou (Filtre > Flou > Flou gaussien, 0.5-1 pixel) pour unifier les éléments
   - Ajoutez un calque de réglage "Vibrance" ou "Teinte/Saturation" pour des ajustements finaux
   - Si nécessaire, ajoutez un effet de vignettage pour attirer l'attention sur le sujet principal

9. **Enregistrement du résultat**
   - Enregistrez en PSD pour conserver les calques
   - Exportez en JPG ou PNG pour le partage

#### Conseils pour un montage réaliste
- Assurez-vous que la direction de la lumière est cohérente entre le sujet et l'arrière-plan
- Faites attention aux proportions et à la perspective
- Ajoutez du bruit ou du grain uniformément pour masquer les différences de qualité d'image
- Utilisez des calques de réglage avec des masques pour cibler des zones spécifiques
- Évitez les bords trop nets autour du sujet extrait

## 7. Restauration de photo ancienne

### Niveau : Intermédiaire à avancé
### Logiciel : Adobe Photoshop

#### Objectif
Restaurer une photo ancienne endommagée en réparant les déchirures, taches et décolorations.

#### Instructions étape par étape

1. **Numérisation et préparation**
   - Numérisez la photo à haute résolution (minimum 300 dpi, idéalement 600 dpi)
   - Ouvrez l'image dans Photoshop
   - Dupliquez le calque d'arrière-plan
   - Renommez ce calque "Restauration"

2. **Recadrage et redressement**
   - Utilisez l'outil Recadrage (C) pour éliminer les bords indésirables
   - Si la photo est inclinée, utilisez l'option de rotation dans l'outil Recadrage pour la redresser
3. **Réparation des rayures et déchirures**
   - Sélectionnez l'outil Correcteur localisé (J)
   - Réglez la taille du pinceau légèrement plus grande que la rayure à corriger
   - Réglez le Type sur "Créer une texture" et assurez-vous que "Échantillonner tous les calques" est décoché
   - Cliquez et faites glisser le long des rayures pour les réparer
   - Pour les déchirures plus importantes, utilisez l'outil Tampon de duplication (S) avec une opacité de 100%
   - Échantillonnez (Alt+clic / Option+clic) une zone intacte proche de la déchirure, puis peignez sur la zone endommagée

4. **Élimination des taches et points**
   - Utilisez l'outil Correcteur (J) pour les petites taches
   - Pour les taches plus grandes ou les zones de décoloration, créez un nouveau calque
   - Réglez le mode de fusion du nouveau calque sur "Couleur"
   - Utilisez l'outil Pinceau (B) avec une opacité faible (20-30%)
   - Échantillonnez une couleur appropriée à partir d'une zone intacte (Alt+clic / Option+clic)
   - Peignez doucement sur les zones décolorées ou tachées

5. **Correction de la décoloration générale**
   - Ajoutez un calque de réglage "Niveaux" (Calque > Nouveau calque de réglage > Niveaux)
   - Ajustez les curseurs d'entrée pour améliorer le contraste :
     - Déplacez le curseur noir vers la droite jusqu'au début de l'histogramme
     - Déplacez le curseur blanc vers la gauche jusqu'à la fin de l'histogramme
     - Ajustez le curseur gris du milieu pour équilibrer les tons moyens
   - Ajoutez un calque de réglage "Courbes" pour affiner le contraste et la luminosité

6. **Correction de la dominante de couleur**
   - Pour les photos en noir et blanc : Ajoutez un calque de réglage "Noir et blanc" pour éliminer toute dominante de couleur
   - Pour les photos en couleur : Ajoutez un calque de réglage "Balance des couleurs"
     - Ajustez séparément les tons foncés, moyens et clairs
     - Compensez les dominantes de couleur (par exemple, ajoutez du cyan pour réduire une dominante rouge)

7. **Reconstruction des zones manquantes (si nécessaire)**
   - Créez un nouveau calque
   - Utilisez une combinaison des outils Tampon de duplication (S), Pinceau (B) et Correcteur (J)
   - Pour les zones complexes, utilisez plusieurs calques pour travailler sur différentes parties
   - Utilisez des masques de fusion pour fondre harmonieusement les zones reconstruites

8. **Amélioration de la netteté**
   - Créez un calque fusionné au sommet (Ctrl+Alt+Shift+E / Cmd+Option+Shift+E)
   - Allez dans Filtre > Netteté > Netteté optimisée
   - Utilisez des paramètres modérés (Quantité : 50-75%, Rayon : 0.5-1 pixel)
   - Ajoutez un masque de fusion si nécessaire pour limiter la netteté à certaines zones

9. **Ajout d'un léger grain (optionnel)**
   - Créez un nouveau calque
   - Remplissez-le de gris 50% (code #808080)
   - Allez dans Filtre > Bruit > Ajout de bruit
   - Utilisez une quantité faible (2-5%), sélectionnez "Gaussien" et "Monochromatique"
   - Changez le mode de fusion en "Lumière tamisée" ou "Incrustation"
   - Réduisez l'opacité à environ 10-20%

10. **Enregistrement du résultat**
    - Enregistrez en PSD pour conserver les calques
    - Exportez en TIFF ou JPG haute qualité pour le partage ou l'impression

#### Conseils supplémentaires
- Travaillez toujours de manière non destructive (utilisez des calques)
- Sauvegardez régulièrement votre travail
- Prenez votre temps, surtout pour les photos à valeur sentimentale
- Pour les restaurations complexes, travaillez par zones plutôt que sur toute l'image à la fois
- Comparez régulièrement avec l'original pour vous assurer que vous préservez l'authenticité de la photo

## Conclusion

Ces instructions détaillées vous permettent de réaliser des traitements d'images courants avec des résultats professionnels. N'hésitez pas à demander à Roo des instructions personnalisées pour vos projets spécifiques, adaptées à votre niveau de compétence et aux outils dont vous disposez.

Rappelez-vous que la pratique est essentielle pour maîtriser ces techniques. Commencez par des projets simples et progressez vers des manipulations plus complexes à mesure que vous gagnez en confiance et en expérience.
   - Confirmez le recadrage en appuyant sur Entrée
#### Objectif
Combiner deux images différentes en un montage cohérent.

#### Instructions étape par étape

1. **Préparation des images sources**
   - Ouvrez Photoshop et créez un nouveau document (Fichier > Nouveau)
   - Choisissez une taille adaptée à votre projet (par exemple 2000x1500 pixels)
   - Ouvrez vos deux images sources dans Photoshop
   - Assurez-vous que la résolution et l'éclairage des deux images sont relativement similaires
   - Réglez le Type sur "Créer une texture" et assurez-vous que "Échantillonner tous les calques" est décoché
   - Cliquez sur chaque imperfection pour les corriger une par une
   - Pour les zones plus larges, utilisez l'outil Tampon de duplication (S) avec une opacité réduite (environ 50%)
   - Passez au canal Bleu et abaissez légèrement la courbe pour ajouter une teinte jaunâtre/sépia

3. **Ajout d'un filtre de couleur vintage**
   - Créez un nouveau calque au-dessus de tous les autres
   - Remplissez-le avec une couleur sépia (#704214) ou ambre (#FFBF00) selon l'effet désiré
   - Changez le mode de fusion de ce calque en "Superposition" ou "Lumière tamisée"
   - Réduisez l'opacité à environ 20-30%