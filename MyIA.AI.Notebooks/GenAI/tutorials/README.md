# Tutoriels GenAI — guides pratiques complémentaires

Ce dossier rassemble des **guides pratiques approfondis** qui complètent les
notebooks de la série [GenAI](../README.md). Là où les notebooks démontrent une
technique pas à pas (cellule par cellule, sortie à l'appui), ces tutoriels
présentent une vue d'ensemble réutilisable : écosystème d'un fournisseur,
patterns d'intégration production, bibliothèques de templates pédagogiques. Ils
se lisent indépendamment ou en parallèle d'un notebook de la série.

## Sommaire des guides

| Guide | Sujet couvert | Quand le lire |
|-------|---------------|---------------|
| [DALL-E 3 — guide complet](dalle3-complete-guide.md) | Génération d'images via l'API OpenAI : prompt engineering, variations, éditions, intégration aux workflows CoursIA, troubleshooting | Avant ou après les notebooks de la sous-série [Image](../Image/README.md) |
| [GPT-5 multimodal — analyse d'images](gpt5-image-analysis-guide.md) | Analyse et description d'images via OpenRouter, conversations multimodales, alt-text pour l'accessibilité, intégration avec DALL-E | Pour approfondir la boucle génération → analyse |
| [OpenRouter — écosystème](openrouter-ecosystem-guide.md) | Multi-endpoints, switching entre modèles, rate limiting, error handling, patterns d'intégration production | Avant de chaîner plusieurs fournisseurs dans un pipeline |
| [Workflows pédagogiques GenAI](educational-workflows.md) | Création automatique de supports, évaluations visuelles, story-boarding, brand building étudiant, templates par matière, accessibilité | Pour les enseignants qui industrialisent la production de matériel |

## Position dans la série

Ces guides ne remplacent pas les notebooks : ils en élargissent le contexte. Le
parcours canonique reste la [série GenAI principale](../README.md) (Environment →
Image → Audio → Vidéo → Texte → Vibe-Coding), et l'on vient ici chercher un
éclairage transverse sur un fournisseur (OpenAI, OpenRouter) ou un cas d'usage
(pédagogie, accessibilité) qui déborde d'une seule modalité.

## Note de maintenance

Le sous-dossier [`Image/tutorials/`](../Image/tutorials/) contient actuellement
une copie identique de ces quatre guides (duplication historique). La source
autoritaire est le présent dossier `GenAI/tutorials/` ; la consolidation de la
copie est tracée séparément (voir Epic nettoyage #9535).
