# EPF - Projets Etudiants GenAI

[← Documentation GenAI](../README.md) | [↑ ..](../README.md) | [→ Projet Fort Boyard](fort-boyard-python.ipynb)

Bienvenue dans la galerie de projets réalisés par les étudiants de l'EPF dans le cadre du cours IA101. Ces notebooks illustrent la créativité et les compétences acquises en utilisant les technologies d'IA générative pour résoudre des problèmes concrets et innovants.

## Ce que ces projets illustrent

Cette collection démontre la richesse des applications de l'IA générative à travers quatre approches complémentaires :

- **Création artistique** : génération d'images hybrides entre univers Barbie et Shrek
- **Assistance quotidienne** : création intelligente de recettes de cuisine sur mesure
- **Éducation santé** : chatbot médical pour apprentissage interactif
- **Jeux interactifs** : réinvention du Fort Boyard avec une intelligence narrative

Chaque projet explore comment l'IA générative peut transformer différents domaines de notre quotidien.

## Projets

| Projet | Auteurs | Description |
|--------|---------|-------------|
| [barbie-schreck](Carole%20%26%20Cléo/barbie-schreck.ipynb) | Carole & Cleo | Génération d'images style Barbie/Shrek |
| [receipe_maker](Dorian%20%26%20Bastien/cuisine/receipe_maker.ipynb) | Dorian & Bastien | Générateur de recettes de cuisine |
| [medical_chatbot](Louise%20et%20Jeanne%20Céline/medical_chatbot.ipynb) | Louise & Jeanne Céline | Chatbot médical éducatif |
| [fort-boyard-python](fort-boyard-python.ipynb) | - | Jeu Fort Boyard en Python |

## Structure des projets

```text
EPF/
├── Carole & Cleo/
│   ├── barbie-schreck.ipynb
│   └── README.md
├── Dorian & Bastien/
│   ├── cuisine/
│   │   ├── receipe_maker.ipynb
│   │   └── README.md
│   └── README.md
├── Louise et Jeanne Celine/
│   ├── medical_chatbot.ipynb
│   └── README.md
├── fort-boyard-python.ipynb
└── README.md
```

## Technologies utilisees

| Projet | Technologies |
|--------|--------------|
| barbie-schreck | OpenAI DALL-E, PIL |
| receipe_maker | OpenAI GPT, LangChain |
| medical_chatbot | OpenAI GPT, Streamlit |
| fort-boyard | OpenAI GPT |

## Prérequis techniques

Les notebooks suivants nécessitent l'installation de ces bibliothèques Python :

```bash
pip install openai langchain python-dotenv pillow
```

Configuration requise dans `GenAI/.env` :
```
OPENAI_API_KEY=sk-...
```

## Relation avec le cours

Ces projets sont evalues dans le cadre de :
- [CC1-Exploratoire-Symbolique](../../EPF/IA101-Devoirs/CC1-Exploratoire-Symbolique/)
- [CC2-Symbolique-Probabiliste](../../EPF/IA101-Devoirs/CC2-Symbolique-Probabiliste/)

## Licence

Projets etudiants - Usage educatif uniquement.
