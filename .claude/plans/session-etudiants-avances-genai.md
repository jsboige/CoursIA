# Session Étudiants Avancés - GenAI Series

## Contexte

- **Durée** : 3h
- **Date** : 26/02/2026
- **Public** : Étudiants ayant terminé leur projet (PR faite)
- **Objectif** : Explorer la série GenAI complète avec challenges bonus

## État des Projets (au 25/02)

| Groupe | Statut | PR |
|--------|--------|-----|
| RobinVaz | Projet Review | Merged |
| devinjayasuriya | Projet Review | Merged |
| NacimAfrikou | Extracteur Documents | Merged |

**3 groupes prêts** pour la session avancée.

---

## Séquence pour Étudiants Avancés

*Note: Aucun switch de container nécessaire - tous les notebooks utilis l'OPENAI_API_KEY` ou des APIs locales.*

### Phase 1 : Setup et Texte (45 min)

1. `00-1-Environment-Setup.ipynb` - Vérifier .env
2. `Texte/1_OpenAI_Intro.ipynb` - Bases API
3. `Texte/2_PromptEngineering.ipynb` - Techniques de prompt

**Challenge #1** : Prompt en cascade pour histoire (0.5 pt)

- Générer un personnage JSON, puis un conflit, puis une résolution
- Pattern : mémoire conversationnelle + few-shot

---

### Phase 2 : Texte Avancé (45 min)

1. `Texte/3_Structured_Outputs.ipynb` - JSON structuré
2. `Texte/4_Function_Calling.ipynb` - Fonctions

**Challenge #2** : Assistant de planification multi-outils (0.5 pt)
- Définir 3 outils : événements, temps de trajet, restaurant
- Pattern : `run_conversation()` avec tools

---

### Phase 3 : Audio API (45 min)

1. `Audio/01-1-OpenAI-TTS-Intro.ipynb` - Text-to-Speech

**Challenge #8** : Narration multi-voix (0.5 pt)
- Créer un dialogue avec 2+ voix différentes

2. `Audio/01-2-OpenAI-Whisper-STT.ipynb` - Speech-to-Text

**Challenge #9** : Sous-titrage automatique (0.5 pt)
- Générer sous-titres SRT synchronisés

3. `Audio/01-3-Basic-Audio-Operations.ipynb` - Opérations audio

**Challenge #3** : Analyse et transformation conditionnelle (0.5 pt)
- Analyser audio avec librosa, appliquer transformations avec pydub

---

### Phase 4 : Image et Video (60 min)

1. `Image/01-1-OpenAI-DALL-E-3.ipynb` - Génération DALL-E

**Challenge #4** : Icône d'application (0.5 pt)
- Générer une icône style "app store"

2. `Video/01-1-Video-Operations-Basics.ipynb` - Opérations vidéo
**Challenge #7** : Slideshow vidéo (0.5 pt)
- Créer une vidéo avec 5 frames message

3. `Video/01-2-GPT-5-Video-Understanding.ipynb` - Analyse vidéo
**Challenge #10** : Analyse de vidéo personnalisée (0.5 pt)
- Analyser une vidéo avec GPT-5

---

### Phase 5 : RAG et Musique (optionnel, si temps)

1. `Texte/5_RAG_Modern.ipynb` - Retrieval Augmented Generation

**Challenge #5** : Mini FAQ engine avec RAG (0.5 pt)
- Créer une base Q/R et implémenter la recherche

2. `Audio/02-3-MusicGen-Generation.ipynb` - Génération musicale

**Challenge #6** : Musique pour scène vidéo (0.5 pt)
- Générer 2 versions avec paramètres différents

---

## Système de Points

| Action | Points |
|--------|-------|
| Compléter Challenge #1 | 0.5 pts |
| Compléter Challenge #2 | 0.5 pts |
| Compléter Challenge #3 | 0.5 pts |
| Compléter Challenge #4 | 0.5 pts |
| Compléter Challenge #5 | 0.5 pts |
| Compléter Challenge #6 | 0.5 pts |
| Compléter Challenge #7 | 0.5 pts |
| Compléter Challenge #8 | 0.5 pts |
| Compléter Challenge #9 | 0.5 pts |
| Compléter Challenge #10 | 0.5 pts |
| Faire une PR avec solutions | +0.5 pts |
| Aider un autre étudiant | +0.2 pts/interaction |

**Récompenses (bonus sur note /20)** :
- 3+ challenges : +0.5 pt
- 5+ challenges : +1.0 pt
- 7+ challenges : +1.5 pts (max)
- 10 challenges + aide + PR : +2.0 pts (max théorique)

---

## Déroulement Optimal (3h)

| Temps | Activité | Notebooks |
|------|----------|----------|
| 0-5 min | Introduction et setup | Environment |
| 5-50 min | Phase 1 : Texte | 3 notebooks |
| 50-95 min | Phase 2 : Texte avancé | 2 notebooks |
| 95-140 min | Phase 3 : Audio API | 3 notebooks |
| 140-200 min | Phase 4 : Image/Video | 3 notebooks |
| 200-180 min | Phase 5 : RAG/Musique (optionnel) | 2 notebooks |

---

## Pour l'enseignant

### Services Docker et URLs

**Services actifs par défaut (pas de switch nécessaire)** :

| Service      | Container | URL Locale               | URL Distante                                      | GPU         |
|--------------|-----------|--------------------------|---------------------------------------------------|-------------|
| forge-turbo  | UP        | `http://localhost:17861` | `https://turbo.stable-diffusion-webui-forge.myia.io` | RTX 3090    |
| whisper-webui| UP        | `http://localhost:36540` | `https://whisper-webui.myia.io`                   | RTX 3080 Ti |

**Services inactifs (non nécessaires pour les challenges)** :

| Service       | URL Distante                         | GPU requis | Note           |
|---------------|--------------------------------------|------------|----------------|
| comfyui-qwen  | `https://qwen-image-edit.myia.io`    | ~29GB      | Container DOWN |
| vllm-zimage   | `https://z-image.myia.io`            | ~10GB      | Container DOWN |

### Switches si nécessaire

```bash
# Démarrer un service spécifique
python scripts/genai-stack/genai.py docker start <service>

# Arrêter un service
python scripts/genai-stack/genai.py docker stop <service>

# Vérifier le statut
python scripts/genai-stack/genai.py docker status
```

### Points d'attention

- **Tous les notebooks de challenges fonctionnent avec OpenAI API uniquement**
- MusicGen utilise le GPU local (pas de container)
- Vérifier que chaque étudiant a bien configuré son `.env`
- Les challenges doivent être soumis via PR sur le fork du repo
- Prévoir des sessions de debug pour les groupes en difficulté

---

## Liste complète des Challenges

| # | Notebook | Challenge | Compétences |
|---|----------|-----------|------------|
| 1 | `Texte/2_PromptEngineering.ipynb` | Prompt en cascade | Few-shot, mémoire |
| 2 | `Texte/4_Function_Calling.ipynb` | Assistant planification | Tools, boucle agentique |
| 3 | `Audio/01-3-Basic-Audio-Operations.ipynb` | Analyse + transformation | librosa, pydub |
| 4 | `Image/01-1-OpenAI-DALL-E-3.ipynb` | Icône application | DALL-E 3 prompting |
| 5 | `Texte/5_RAG_Modern.ipynb` | Mini FAQ engine | Embeddings, recherche vectorielle |
| 6 | `Audio/02-3-MusicGen-Generation.ipynb` | Musique scène vidéo | MusicGen, paramètres |
| 7 | `Video/01-1-Video-Operations-Basics.ipynb` | Slideshow vidéo | PIL, imageio |
| 8 | `Audio/01-1-OpenAI-TTS-Intro.ipynb` | Narration multi-voix | TTS, voices |
| 9 | `Audio/01-2-OpenAI-Whisper-STT.ipynb` | Sous-titrage | Whisper, timestamps |
| 10 | `Video/01-2-GPT-5-Video-Understanding.ipynb` | Analyse vidéo | GPT-5 multimodal |

---

## Checklist Pré-Session

- [x] Vérifier .env des étudiants (clés API)
- [x] Confirmer que les notebooks sont bien exécutables
- [x] Préparer grille de notation
- [x] Créer fork template pour PRs challenges
- [x] Planifier sessions de debug individuelles
