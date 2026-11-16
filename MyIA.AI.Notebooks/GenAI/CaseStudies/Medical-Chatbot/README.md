# Medical-Chatbot - Chatbot médical

[← CaseStudies](../README.md) | [↑ GenAI](../../README.md)

Chatbot médical intelligent utilisant des agents IA pour l'assistance aux patients.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 1 |
| Difficulté | Avancé |
| Durée | ~30 min |
| Thème | Santé et assistance médicale |

## Comment lire ce README

Ce cas d'usage se lit à plusieurs vitesses, et le choix vous appartient.

- **Vous voulez voir la consultation simulée tourner** : exécutez le carnet en lecture suivie — chaque étape (kernel, plugins, prompts, agents, groupe, dialogue) s'ouvre sur sa « Lecture du résultat ».
- **Vous voulez comprendre l'auto function calling** : entrez par les plugins médicaux — `DoctorPlugin`, le plugin d'allergies de l'exemple guidé, et le réglage `FunctionChoiceBehavior.Auto()` qui laisse l'agent appeler ces fonctions de lui-même.
- **Vous cherchez un point précis** (terminaison métier, logging, orchestration du dialogue) : chaque section est autonome et se referme sur le résultat qu'elle produit.

Le principe général — les vitesses de lecture et comment les reconnaître dans un README de série — est exposé dans [Choisir sa vitesse de lecture](../../../../README.md#choisir-sa-vitesse-de-lecture).

## Parcours principal

| # | Notebook | Ce qu'on y apprend |
|---|----------|--------------------|
| 1 | [medical_chatbot](medical_chatbot.ipynb) | Faire travailler ensemble un médecin généraliste, une IA d'analyse et un pharmacien — prompts système par rôle, plugins `@kernel_function` (questions de suivi, gravité, recommandation), auto function calling et terminaison métier dans un `AgentGroupChat` |

## Approfondissements

Aucun carnet de cette série ne porte de palier lettré : le parcours principal ci-dessus couvre tout ce qui s'exécute dans le dossier. Les approfondissements vivent dans le carnet lui-même, à ouvrir au moment où ils servent :

- l'**exemple guidé** sur le plugin de vérification des allergies montre le chemin complet d'une compétence ajoutée à un agent ;
- les **exercices non résolus** — vérifier une ordonnance face au dossier d'allergies, adapter les prompts à un scénario pédiatrique, terminer sur détection du diagnostic — reprennent chacun une brique de la consultation ;
- le carnet jumeau [medical_chatbot_en](medical_chatbot_en.ipynb) en donne la version anglaise.

La série qui possède l'organe de l'orchestration d'agents est [SemanticKernel](../../SemanticKernel/README.md) : ce cas d'usage en est une application, pas le cours. Pour un second duel d'agents complet (sélection du locuteur, score, historique), voir [Fort-Boyard](../Fort-Boyard/README.md).

## Technologies

- **Python** : Interface de development
- **Semantic Kernel** : Orchestration d'agents
- **OpenAI** : Modèles de langage

## Prérequis

```bash
pip install semantic-kernel python-dotenv
```

**Important** : Ce chatbot est un outil d'assistance et ne remplace pas un professionnel de santé.

---

*Projet étudiant - Janvier 2026*
