# Deck 05 - Théorie des Jeux : Analyse Visuelle et Plan d'Amélioration

**Date d'analyse** : 2026-02-13
**Fichier source** : `05-IA-Cours-Theorie-des-Jeux.pptx`
**Statistiques** : 29 slides, 54 images, 1554 mots, 2.17 MB
**Dernière mise à jour** : Décembre 2022
**Sections** :
- Analyse stratégique
- Jeux Bayésiens
- Théorie des mécanismes
- Jeux différentiels

---

## 1. Diagnostic global

### Points forts

- **Densité visuelle excellente** : 54 images pour 29 slides = ~1.9 image/slide (ratio optimal)
- **Compacité efficace** : 29 slides seulement - deck concis, pas de dilution de contenu
- **Visuels pédagogiques** : Slide 10 avec loi de Hotelling (plage/électeurs) - bon exemple concret
- **Structure claire** : 4 sections bien délimitées malgré la brièveté
- **Slides "Questions?"** : Présents comme pauses (à conserver selon préférence utilisateur)

### Problèmes identifiés

1. **Incohérence footer** : Mentionne "CS 405" au lieu de standard CoursIA
2. **Datation obsolète** : Décembre 2022 - aucune mention des applications modernes (IA multi-agents, game theory dans RLHF)
3. **Slide 20 trop dense** : Allocation par négociation avec petits diagrammes tabulaires difficiles à lire
4. **Manque de profondeur** : 29 slides pour 4 sections = ~7 slides/section - certains concepts survolés
5. **Absence de liens notebooks** : 26 notebooks dans `GameTheory/` non référencés (GameTheory-2b à GameTheory-16b)
6. **Pas d'exemples IA modernes** : Aucune connexion avec multi-agent RL, LLM negotiations, mechanism design dans les marketplaces IA

### Métriques visuelles estimées

- Slides avec visuels pertinents : ~85% (excellent ratio images)
- Slides trop denses (texte trop petit ou >3 tableaux) : ~10%
- Slides nécessitant modernisation contenu : ~40%
- Slides avec footer incohérent : ~100% (problème systématique)

---

## 2. Recommandations par section

### Analyse stratégique (slides 1-10)

**Conserver** :
- Slide 10 : Loi de Hotelling (plage/électeurs) - excellent exemple visuel de stratégies spatiales
- Structure introductive claire

**Améliorer** :
- Développer section espaces de stratégies infinis : ajouter 2-3 slides supplémentaires
- Créer slide "Équilibre de Nash dans les jeux modernes" avec exemples :
  - Jeux vidéo multi-joueurs (Fortnite, LoL)
  - Enchères publicitaires (Google Ads, Meta Ads)
  - Négociation multi-agents RL
- Ajouter références vers notebooks :

| Slide | Concept | Notebook |
|-------|---------|----------|
| 5-10 | Équilibre Nash | `GameTheory/GameTheory-2b-MDP.ipynb`, `GameTheory-3b-Nash.ipynb` |

---

### Jeux Bayésiens (slides 11-15)

**Conserver** :
- Concepts fondamentaux présentés

**Améliorer** :
- **CRITIQUE** : Section trop courte (5 slides) pour concept complexe - étendre à 8-10 slides
- Ajouter slide "Information incomplète et IA" :
  - Poker bots (Pluribus, Libratus)
  - Négociation avec LLMs (information asymétrique dans les prompts)
- Créer exemple visuel concret : enchère à prix scellé avec distributions bayésiennes
- Ajouter cross-référence :

| Slide | Concept | Notebook |
|-------|---------|----------|
| 11-15 | Jeux Bayésiens | `GameTheory/GameTheory-5b-Bayesian-Games.ipynb` |

---

### Théorie des mécanismes (slides 16-20)

**Conserver** :
- Slide 20 : Concept d'allocation par négociation (malgré densité)

**Améliorer** :
- **URGENT** : Slide 20 trop dense - découper en 2 slides :
  1. Principes d'allocation (texte + schéma conceptuel agrandi)
  2. Exemple numérique (tableaux lisibles, police >14pt)
- Ajouter slide "Mechanism Design dans l'économie numérique" :
  - Algorithmes de matching (Airbnb, Uber)
  - Enchères publicitaires (Vickrey auction dans AdWords)
  - Marketplaces décentralisées (blockchain, smart contracts)
- Créer parallèle avec RLHF : reward modeling comme mécanisme d'alignement
- Ajouter cross-référence :

| Slide | Concept | Notebook |
|-------|---------|----------|
| 16-20 | Mechanism design | `GameTheory/GameTheory-7b-Mechanism-Design.ipynb` |

---

### Jeux différentiels (slides 21-29)

**Conserver** :
- Slide 29 : Merci - bon closing slide
- Slides "Questions?" entre sections

**Améliorer** :
- Section trop courte (9 slides) - étendre à 12-15 slides
- Ajouter slide "Applications en robotique et véhicules autonomes" :
  - Poursuite-évasion multi-agents
  - Coordination de flottes (drones, taxis autonomes)
- Créer slide "Jeux différentiels et apprentissage par renforcement" :
  - Multi-agent RL (MARL)
  - AlphaGo/AlphaZero comme jeu différentiel
- Ajouter exemples visuels : trajectoires 2D, champs vectoriels
- Enrichir cross-références :

| Slide | Concept | Notebook |
|-------|---------|----------|
| 21-29 | Jeux différentiels | `GameTheory/GameTheory-14b-RL-Basics.ipynb`, `GameTheory-15b-Multi-Agent-RL.ipynb` |

---

## 3. Cross-references notebooks

### Mapping complet proposé

| Slide(s) | Concept | Notebooks |
|-----------|---------|-----------|
| 1-5 | Introduction théorie des jeux | `GameTheory/GameTheory-1b-Intro.ipynb` |
| 6-10 | Équilibre de Nash | `GameTheory/GameTheory-3b-Nash.ipynb`, `GameTheory-4b-Nash-Computation.ipynb` |
| 11-15 | Jeux Bayésiens | `GameTheory/GameTheory-5b-Bayesian-Games.ipynb`, `GameTheory-6b-Incomplete-Info.ipynb` |
| 16-20 | Théorie des mécanismes | `GameTheory/GameTheory-7b-Mechanism-Design.ipynb`, `GameTheory-8b-Auctions.ipynb` |
| 21-25 | Jeux différentiels | `GameTheory/GameTheory-13b-Differential-Games.ipynb` |
| 26-29 | Applications RL | `GameTheory/GameTheory-14b-RL-Basics.ipynb`, `GameTheory-15b-Multi-Agent-RL.ipynb`, `GameTheory-16b-AlphaGo.ipynb` |

**Action** : Créer slide récapitulative (nouvelle slide 28) avec QR codes vers notebooks avant slide "Merci".

---

## 4. Plan d'amélioration prioritaire

### P1 : Corrections immédiates (1.5h)

1. **Standardiser footer** : Remplacer "CS 405" par "CoursIA - Théorie des Jeux" (rechercher/remplacer global)
2. **Découper slide 20** : Séparer principes allocation + exemple numérique en 2 slides, agrandir police tableaux à >14pt (~30min)
3. **Corriger date** : Remplacer "Dec 2022" par "Dernière mise à jour : Février 2026" dans propriétés
4. **Vérifier slides "Questions?"** : S'assurer qu'ils sont présents entre chaque section (conserver selon préférence utilisateur)

### P2 : Améliorations visuelles et expansion (4h)

1. **Étendre le deck à 45-50 slides** (actuellement trop court à 29 slides) :
   - Jeux Bayésiens : +3 slides (5→8)
   - Théorie des mécanismes : +5 slides (5→10)
   - Jeux différentiels : +4 slides (9→13)
   - Nouvelles sections : +3 slides (applications modernes)
2. **Créer 5 nouvelles slides "Applications modernes IA"** :
   - "Équilibre de Nash dans les enchères publicitaires" (Google Ads Vickrey auction)
   - "Jeux Bayésiens et négociation LLM" (information asymétrique dans prompts)
   - "Mechanism design et RLHF" (reward modeling comme mécanisme)
   - "Multi-agent RL" (AlphaGo, Dota 2 OpenAI Five)
   - "Jeux différentiels en robotique" (poursuite-évasion, coordination flottes)
3. **Améliorer visuels existants** :
   - Slide 10 : Agrandir diagramme Hotelling, ajouter annotations
   - Créer 3-4 nouveaux schémas pour concepts abstraits (équilibre bayésien, mécanismes VCG)
4. **Ajouter slide récapitulative notebooks** : Tableau cross-référence avec QR codes (avant slide "Merci")

### P3 : Modernisation contenu (3h)

1. **Enrichir exemples avec cas 2024-2026** :
   - Remplacer exemples théoriques par applications concrètes :
     - Enchères publicitaires réelles (Meta Ads, Google AdWords)
     - Poker bots (Pluribus comme jeu bayésien)
     - Véhicules autonomes (jeux différentiels multi-agents)
2. **Créer section "Game Theory et IA générative"** (3-4 slides nouvelles) :
   - Négociation multi-agents avec LLMs
   - Constitutional AI comme mechanism design (Anthropic)
   - RLHF et reward modeling (ChatGPT, Claude)
   - Adversarial training (GANs comme jeu à somme nulle)
3. **Ajouter références bibliographiques modernes** :
   - Papers 2023-2026 sur multi-agent RL
   - OpenAI Five, AlphaGo, Pluribus (DeepMind, OpenAI, CMU)
   - Mechanism design dans crypto/blockchain
4. **Intégration notebooks OpenSpiel** :
   - Créer slides de transition avec captures d'écran `GameTheory/` notebooks
   - Ajouter instructions pratiques : "Exercice : ouvrir `GameTheory-3b-Nash.ipynb` dans WSL"
   - Note WSL : Mentionner kernel issues et workarounds (voir `.claude/rules/wsl-kernels.md`)

### Estimation totale : ~8.5h d'améliorations

**Ordre recommandé** : P1 (corrections footer + densité slide 20) → P2 (expansion deck trop court) → P3 (modernisation contenu)

---

## 5. Considérations spécifiques

### Expansion du deck justifiée

- **29 slides trop court** pour couvrir 4 sections majeures (~45min présentation)
- Cible recommandée : **45-50 slides** pour session 90min (rythme ~2min/slide)
- Ratio images déjà excellent (1.9/slide) - maintenir lors expansion

### WSL et notebooks GameTheory

- **26 notebooks disponibles** (GameTheory-2b à GameTheory-16b)
- **OpenSpiel nécessite WSL** : Mentionner dans slides cross-référence
- Voir `.claude/rules/wsl-kernels.md` pour workarounds kernel issues
- Ajouter slide "Configuration OpenSpiel" avec instructions WSL setup

### Cohérence avec Deck 04 (Probabilités)

- Deck 04 couvre MDP (slides 71-98) - **éviter redondance**
- Deck 05 doit se concentrer sur **interactions stratégiques multi-agents**
- Cross-référencer Deck 04 pour MDP mono-agent, Deck 05 pour MARL

---

## Notes d'implémentation

- Utiliser PowerPoint 2024 ou LibreOffice Impress pour édition
- Sauvegarder version originale en `05-IA-Cours-Theorie-des-Jeux_v2022.pptx` avant modification
- Tester rendu PDF après expansion (vérifier pagination, footer)
- Valider cross-références notebooks en exécutant :
  ```bash
  scripts/notebook_tools.py validate MyIA.AI.Notebooks/GameTheory/ --quick
  ```
- **Important** : Installer OpenSpiel dans WSL avant démo notebooks (voir `GameTheory/README.md`)
- Considérer création deck compagnon "Game Theory - Exercices pratiques" (15-20 slides) pour session hands-on
