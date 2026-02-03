# EPF - Projets Etudiants GenAI

Projets realises par les etudiants EPF dans le cadre du cours IA101, utilisant les technologies d'IA generative.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Projets | 4 |
| Kernel | Python |
| Contexte | Cours IA101 EPF 2026 |

## Projets

| Projet | Auteurs | Description |
|--------|---------|-------------|
| [barbie-schreck](Carole%20%26%20Cléo/barbie-schreck.ipynb) | Carole & Cleo | Generation d'images style Barbie/Shrek |
| [receipe_maker](Dorian%20%26%20Bastien/cuisine/receipe_maker.ipynb) | Dorian & Bastien | Generateur de recettes de cuisine |
| [medical_chatbot](Louise%20et%20Jeanne%20Céline/medical_chatbot.ipynb) | Louise & Jeanne Celine | Chatbot medical educatif |
| [fort-boyard-python](fort-boyard-python.ipynb) | - | Jeu Fort Boyard en Python |

## Structure

```
EPF/
├── Carole & Cleo/
│   └── barbie-schreck.ipynb
├── Dorian & Bastien/
│   └── cuisine/
│       └── receipe_maker.ipynb
├── Louise et Jeanne Celine/
│   └── medical_chatbot.ipynb
└── fort-boyard-python.ipynb
```

## Technologies utilisees

| Projet | Technologies |
|--------|--------------|
| barbie-schreck | OpenAI DALL-E, PIL |
| receipe_maker | OpenAI GPT, LangChain |
| medical_chatbot | OpenAI GPT, Streamlit |
| fort-boyard | OpenAI GPT |

## Prerequisites

```bash
pip install openai langchain python-dotenv pillow
```

Configuration API dans `GenAI/.env` :
```
OPENAI_API_KEY=sk-...
```

## Relation avec le cours

Ces projets sont evalues dans le cadre de :
- [CC1-Exploratoire-Symbolique](../../EPF/IA101-Devoirs/CC1-Exploratoire-Symbolique/)
- [CC2-Symbolique-Probabiliste](../../EPF/IA101-Devoirs/CC2-Symbolique-Probabiliste/)

## Licence

Projets etudiants - Usage educatif uniquement.
