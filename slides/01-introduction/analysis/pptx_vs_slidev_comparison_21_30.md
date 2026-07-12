# Comparaison PPTX vs Slidev - Slides 21-30

**Date**: 2026-03-25
**Deck**: slides/01-introduction
**Slides analysées**: 21-30 (10 slides)

---

## Résumé Exécutif

Cette analyse comparative identifie les problèmes de qualité entre les rendus PPTX originaux et les slides Slidev actuelles. Les problèmes sont classés en 5 catégories:
1. Contenu manquant ou différent
2. Hiérarchie visuelle perdue
3. Images/éléments mal positionnés
4. Alignement ou formatage dégradé
5. Couleurs ou contraste problème

---

## Slide 21 - Les agents

### Problèmes identifiés

#### 1. Contenu manquant ou différent
**CRITIQUE**: Terminologie incorrecte dans le diagramme
- Le diagramme Slidev utilise **"Capture"** et **"Actionneurs"** au lieu de **"Capteurs"** et **"Effecteurs"**
- "Capture" est un verbe, alors que "Capteurs" est le nom de l'appareil → discordance avec le texte "perçoit son environnement par des capteurs"

#### 2. Hiérarchie visuelle perdue
**MAJEUR**: Perte du minimalisme du diagramme
- PPTX: formes géométriques simples (cercle vert, ovale bleu)
- Slidev: agent stylisé avec bras, jambes et œil dessinés → style cartoonistique inapproprié
- La hiérarchie claire PPTX (cercle vs ovale) est fortement altérée

#### 3. Images/éléments mal positionnés
**MAJEUR**: Choix de l'image de l'agent
- Design anthropomorphe (bras, jambes, œil) avec couleurs vives
- Style "dessiné à la main" peu professionnel pour un diaporama technique
- Un simple ovale bleu serait plus efficace et pertinent

#### 4. Alignement ou formatage dégradé
- Pas de problème majeur d'alignement textuel visible

#### 5. Couleurs ou contraste problème
- Le purple vif et le design "animé" de l'agent créent un contraste esthétique négatif
- Vert pour l'environnement acceptable, mais bleu (PPTX) plus sobre

**Correction nécessaire**: Remplacer l'agent cartoon par un ovale bleu simple, corriger "Capture" → "Capteurs"

---

## Slide 22 - Les agents rationnels

### Problèmes identifiés

#### 1. Contenu manquant ou différent
- Aucun contenu manquant identifié

#### 2. Hiérarchie visuelle perdue
- Les sous-bullets utilisent des petits cercles gris avec indentation minimale
- PPTX: indentation plus prominente (1-2 espaces supplémentaires) ou style de puce distinct
- Les sous-points se mélangent visuellement avec les bullets principaux

#### 3. Images/éléments mal positionnés
- Aucun élément graphique majeur

#### 4. Alignement ou formatage dégradé
**MAJEUR**: Inconsistance d'indentation
- Sous-bullets sous "Agir rationnellement n'implique pas forcément de penser" apparaissent décalés
- Certains légèrement shiftés vers la gauche → bord gauche "ragged"
- PPTX: indentation uniforme, colonne gauche propre

**Espacement vertical**: Gap trop serré entre bullets principaux et sous-bullets (1-2pt vs 4-6pt PPTX)

#### 5. Couleurs ou contraste problème
- Titre "Agir de façon rationnelle : l'agent": rouge muted (#c0392b) vs rouge saturé PPTX (#d32f2f)
- Ligne rouge soulignement: 1px vs 2px PPTX → poids visuel diminué
- Sous-bullets: gris clair (#666666) vs gris foncé PPTX (#333333)
- Contraste ratio: ~4.5:1 vs ~7:1 PPTX → moins lisible

**Correction nécessaire**: Augmenter indentation des sous-bullets, augmenter espacement vertical, assombrir le gris des sous-bullets

---

## Slide 23 - Intelligences (Procédurale, Exploratoire)

### Problèmes identifiés

#### 1. Contenu manquant ou différent
**MAJEUR**: Structure des listes perdue
- PPTX: éléments sous "Symbolique" présentés comme listes à puces HIÉRARCHIQUES
- Slidev: blocs de texte indépendants, séparés en colonnes → dissociation visuelle
- Perte structurelle majeure du contenu

#### 2. Hiérarchie visuelle perdue
**CRITIQUE**: Faible relation titre/contenu
- Relation entre titre "Symbolique" et éléments listés très faible
- Textes non indentés, non formatés comme liste → hiérarchie plate et confuse
- Titre "Symbolique" n'apparaît pas comme en-tête des éléments

**Manque de structure de liste**: Absence de puces ou retraits visuels

#### 3. Images/éléments mal positionnés
**MAJEUR**: Image dans "Symbolique"
- Image du graphe placée milieu-droit → divise la colonne de texte maladroitement
- Perturbe la lecture

**Image dans "Probabiliste"**: en bas à droite, semble ajoutée en dernier, non alignée avec la liste

**Boutons "Automates" / "Algorithmes"**: placés à droite comme boutons indépendants, isolés du reste

#### 4. Alignement ou formatage dégradé
**MAJEUR**: Alignement des textes
- Blocs de texte dans colonnes "Symbolique" et "Probabiliste" : largeurs différentes
- Alignement gauche irrégulier → aspect "bricolé"

**Alignement des cadres**: 4 cadres principaux pas parfaitement alignés → aspect désordonné

**Espace entre éléments**: inégal et souvent trop important → cohésion visuelle affaiblie

#### 5. Couleurs ou contraste problème
- Fond corail uniforme et plat
- PPTX utiliserait gradients subtils, bordures légères ou ombres
- Intégration du violet: cadre violet "Théorie des jeux" = changement de couleur abrupt
- Attire l'œil de manière excessive, déconnecte l'item du reste "Probabiliste"

**Qualité des images**: résolution moyenne, simplement "collées" sans effets de bordure

**Correction nécessaire**: Restaurer la hiérarchie de listes à puces, intégrer les images proprement, unifier les couleurs

---

## Slide 24 - Intelligences (Symbolique, Probabiliste)

### Problèmes identifiés

#### 1. Contenu manquant ou différent
**MAJEUR**: Structure hiérarchique des sections
- Section "Probabiliste" présentée comme même niveau que "Symbolique"
- PPTX: "Probabiliste" = sous-ensemble de "Symbolique"
- Crée confusion sur la hiérarchie du contenu

#### 2. Hiérarchie visuelle perdue
**CRITIQUE**: Niveau de titre mal défini
- Titre principal "Intelligences": petite taille, gras (standard)
- Titres de section ("Procédurale", "Exploratoire", "Symbolique", "Probabiliste"): très grande taille, même typographie
- Efface différence entre sections principales et sous-section

**Perte de l'effet de regroupement**: boîtes sous "Symbolique" listées sans fond orange englobant

#### 3. Images/éléments mal positionnés
**MAJEUR**: Boîtes flottantes "Automates" et "Algorithmes"
- Positionnées à droite du titre "Procédurale", sans lien visuel clair
- Semblent "flottants", pas partie d'un conteneur → graphiquement désordonnés

**Images non intégrées**: 3 images placées comme "décorations", pas clairement associées au texte

#### 4. Alignement ou formatage dégradé
**MAJEUR**: Boîte "Théorie des jeux" mise en avant artificiellement
- Couleur violette la distingue fortement des autres
- Casse l'uniformité du design, peut paraître arbitraire
- Taille légèrement plus large que autres boîtes de sa colonne

#### 5. Couleurs ou contraste problème
**MAJEUR**: Fond trop saturé
- Fond orange/terre cuite très saturé → fatigant à lire sur écran
- Peut masquer les informations plutôt que les mettre en valeur

**Couleur accentuelle incohérente**: violet pour une seule boîte ("Théorie des jeux") → exception visuelle, casse harmonie

**Correction nécessaire**: Restaurer la hiérarchie des sections (Probabiliste sous Symbolique), unifier les couleurs des boîtes

---

## Slide 25 - Intelligence de la recherche

### Problèmes identifiés

#### 1. Contenu manquant ou différent
**CRITIQUE**: Terminologie erronée
- "Fonds de teint les bus" et "Fonds de teint un modèle" → termes incorrects/mal traduits
- Devrait être "Systèmes multi-agents" ou "Agents autonomes"
- "Exploratoire" dans section "Type" correct, mais "Recherche heuristique" pourrait être plus précis

#### 2. Hiérarchie visuelle perdue
**MAJEUR**: Réduction de l'espace hiérarchique
- Boîtes de même taille pour tous les éléments
- PPTX: encadrements plus larges pour catégories principales
- Aucune variation de taille/couleur pour indiquer importance hiérarchique

**Manque de gradation**: aucune variation entre sous-catégories

#### 3. Images/éléments mal positionnés
- Boîtes rouges contenant éléments non parfaitement alignées entre colonnes → effet désordonné
- Espace inégal entre boîtes → perturbe cohérence visuelle

#### 4. Alignement ou formatage dégradé
**MAJEUR**: Texte découpé
- Certains textes tronqués ou mal ajustés dans boîtes ("Apprentissage sur les données", "Meta learning")

**Police incohérente**: typographie non uniforme entre sections

**Interligne irrégulier**: espacement vertical entre lignes varie

#### 5. Couleurs ou contraste problème
**MAJEUR**: Palette de couleurs limitée
- Utilisation excessive du rouge/rose sans variation
- Réduit capacité à distinguer catégories

**Manque de contraste**: fond rose clair + texte noir → contraste insuffisant pour projection

**Absence de codage couleur par catégorie**: aucune différenciation chromatique entre sections

**Correction nécessaire**: Corriger la terminologie ("Fonds de teint"), ajouter codage couleur par catégorie, améliorer contraste

---

## Slide 26 - Intelligence de la pensée logique

### Problèmes identifiés

#### Analyse non disponible
- Le modèle n'a pas retourné d'analyse pour cette slide
- **Recommandation**: Analyse manuelle requise

---

## Slide 27 - Intelligence de l'incertitude

### Problèmes identifiés

#### 1. Contenu manquant ou différent
- Type: "Probabiliste" uniquement → PPTX aurait probablement plus de types (flou, bayésien, etc.)
- Inférences: Slidev liste 3 éléments → PPTX pourrait inclure d'autres méthodes
- Modèles: terminologie différente ("Perceptron de Markov" vs "Perception de Markov", "Modèles stratigraphiques" vs "Modèles stochastiques")
- Apprentissage: "Apprentissage renforcé" vs "Amélioration reinforcement"
- Agents: "Agents polynomiaux" vs "Agents politiques", "Agents stratigraphiques" vs "Agents stratégiques"

#### 2. Hiérarchie visuelle perdue
- Structure du tableau moins hiérarchique que PPTX
- PPTX: titres de rangée clairs + indentation visuelle pour sous-catégories
- Slidev: éléments présentés de manière plate, sans emphase sur relations parent-enfant

#### 3. Images/éléments mal positionnés
- Champs organisés en colonnes mais alignement pourrait être moins optimal
- Entrées colonne "Type" décalées par rapport aux autres → brisent uniformité visuelle
- Numérotation "27" centrée mais en-tête "Intelligence de l'incertitude" légèrement décalé → déséquilibre

#### 4. Alignement ou formatage dégradé
- Textes dans boîtes rouges non parfaitement alignés
- Entrées "Inférences" longueurs variées → espaces inégaux entre boîtes
- Police et taille texte incohérentes entre rangées

#### 5. Couleurs ou contraste problème
- Fond rose pâle pour boîtes → réduit contraste avec texte noir
- Lecture moins confortable, surtout vision nocturne
- PPTX utiliserait couleurs plus vives ou contraste plus élevé

**Correction nécessaire**: Corriger la terminologie, améliorer alignement des colonnes, augmenter contraste

---

## Slide 28 - Environnement de tâche

### Problèmes identifiés

#### 1. Contenu manquant ou différent
**MAJEUR**: Puces rouges manquantes
- PPTX: puces rouges distinctives
- Slidev: puces standard (défaut) → perte élément stylistique

#### 2. Hiérarchie visuelle perdue
**MAJEUR**: Sous-sections PEAS
- Mise en forme "Mesure de Performance", "Environnement", etc. moins distincte
- Hiérarchie entre éléments principaux et sous-éléments moins claire

**Exemple Taxi**: sous-sections "Performance:", "Environnement:", etc. manquent indentation/formatting visuel

#### 3. Images/éléments mal positionnés
- Pas d'éléments graphiques majeurs

#### 4. Alignement ou formatage dégradé
**MAJEUR**: Listes à puces
- Alignement éléments liste moins précis
- Variations indentation entre différents niveaux hiérarchiques

**Marge interne**: marges internes et espacement entre sections différents de PPTX

#### 5. Couleurs ou contraste problématique
- Fond gris clair contraste moins fortement avec texte que fond neutre PPTX
- Perte des puces rouges = dégradation contraste visuel et identité

**Formatage général**: titre "Environnement de tâche" formatage police différent (moins gras ou taille différente)

**Correction nécessaire**: Restaurer les puces rouges, améliorer indentation des sous-sections, augmenter contraste

---

## Slide 29 - Environnements de tâche: exemples

### Problèmes identifiés

#### Analyse limitée
- Le modèle n'a pas fourni d'analyse détaillée pour cette slide
- **Recommandation**: Analyse manuelle requise pour comparer les tableaux PPTX vs Slidev

---

## Slide 30 - Types d'environnement

### Problèmes identifiés

#### 1. Contenu manquant ou différent
- Aucun contenu textuel manquant
- Tous concepts et sous-concepts PPTX présents
- **Cependant**: structure différente et moins claire
- Slidev inclut lignes texte supplémentaires et explications altèrent structure initiale

#### 2. Hiérarchie visuelle perdue
**CRITIQUE**: Principal problème
- Slidev perd complètement hiérarchie visuelle
- Sous-points ("États de l'environnement", "Change pendant la délibération") présentés au même niveau que paires principales
- "États de l'environnement": même niveau que "Déterministe vs stochastique" au lieu d'être indenté
- "Change pendant la délibération (score = semi-dynamique)": sous-point de "Statique vs Dynamique" mais listé au même niveau
- PPTX: puces rouges structurées avec hiérarchie claire (paires en rouge gras, sous-points en noir indentés)

#### 3. Images/éléments mal positionnés
- Pas d'images complexes
- Élément "30" dans cercle très petit et peu visible

#### 4. Alignement ou formatage dégradé
**MAJEUR**: Manque d'indentation
- Absence indentation pour sous-points → affichage dense et peu structuré

**Espace entre lignes**: espace vertical uniforme et insuffisant → difficile à parser visuellement

**Arrière-plan**: gris uni très simple vs PPTX avec puces rouges et design plus soigné

**Typographie**: basique, sans variation de police/poids pour différencier niveaux hiérarchie

#### 5. Couleurs ou contraste problème
- Contraste acceptable (noir sur gris clair) mais choix basique et moins efficace
- Titre en pourpre, reste texte en noir
- PPTX: puces rouges = couleur cohérente et stratégique pour guider l'œil
- Slidev: points = ronds gris peu distincts
- Manque couleur unificatrice et contraste visuel → moins engageante et professionnelle

**Correction nécessaire**: Ajouter indentation pour sous-points, utiliser puces rouges pour hiérarchie, améliorer typographie

---

## Synthèse des Problèmes par Catégorie

### 1. Problèmes de Contenu (terminologie, structure)
- **Slide 21**: "Capture"/"Actionneurs" au lieu de "Capteurs"/"Effecteurs"
- **Slide 25**: "Fonds de teint les bus" → terminologie erronée
- **Slide 27**: terminologie incohérente ("Perceptron", "stratigraphiques")
- **Slides 23-24**: structure de liste hiérarchique perdue

### 2. Problèmes de Hiérarchie Visuelle
- **Slides 22-24, 30**: indentation insuffisante des sous-bullets
- **Slides 23-24**: titres de sections même taille → confusion hiérarchique
- **Slide 24**: "Probabiliste" au même niveau que "Symbolique" au lieu de sous-section
- **Slide 30**: sous-points au même niveau que concepts principaux

### 3. Problèmes de Positionnement
- **Slide 21**: agent cartoon au lieu de forme géométrique simple
- **Slides 23-24**: images "flottantes" non intégrées au contenu
- **Slides 25, 27**: boîtes non alignées entre colonnes

### 4. Problèmes d'Alignement et Formatage
- **Slide 22**: indentation et espacement vertical insuffisants
- **Slides 23-24**: textes tronqués dans boîtes, police incohérente
- **Slides 28, 30**: indentation manquante pour sous-sections

### 5. Problèmes de Couleurs et Contraste
- **Slide 22**: titre rouge muted, sous-bullets gris clair → contraste insuffisant
- **Slide 25**: fond rose pâle + texte noir → contraste insuffisant
- **Slides 23-24**: fond corail saturé → fatigant
- **Slide 24**: boîte violette "Théorie des jeux" → exception incohérente
- **Slides 28, 30**: perte des puces rouges → perte identité visuelle

---

## Priorités de Correction

### URGENT (impact pédagogique majeur)
1. **Slide 21**: Corriger "Capture" → "Capteurs", remplacer agent cartoon par ovale bleu
2. **Slide 25**: Corriger "Fonds de teint les bus" → terminologie correcte
3. **Slide 30**: Restaurer hiérarchie avec indentation des sous-points
4. **Slides 23-24**: Restaurer structure de listes hiérarchiques

### IMPORTANT (qualité visuelle)
1. **Slide 22**: Améliorer indentation et espacement, assombrir sous-bullets
2. **Slide 24**: Unifier couleurs des boîtes (supprimer violet)
3. **Slide 27**: Corriger terminologie et alignement des colonnes
4. **Slides 28, 30**: Restaurer puces rouges

### MOYEN (cohérence globale)
1. Améliorer contraste texte/fond sur toutes slides
2. Standardiser indentation des sous-bullets
3. Unifier taille des titres de section

---

## Recommandations Générales

1. **Restaurer la hiérarchie visuelle PPTX**:
   - Indentation systématique des sous-bullets (1-2 em)
   - Puces rouges pour les éléments principaux
   - Variation de taille/gras pour les niveaux de titre

2. **Améliorer le contraste**:
   - Sous-bullets: gris foncé (#333333) au lieu de gris clair (#666666)
   - Titres: rouge saturé (#d32f2f) au lieu de muted (#c0392b)

3. **Standardiser les layouts**:
   - Alignement parfait des boîtes dans les grilles
   - Espacement vertical uniforme (4-6pt entre bullets, 1-2pt entre sous-bullets)

4. **Corriger la terminologie**:
   - Réviser toutes les traductions techniques
   - Uniformiser la terminologie avec le cours original

5. **Intégrer les images proprement**:
   - Éviter les éléments "flottants"
   - Ajouter bordures/ombres pour intégration professionnelle
