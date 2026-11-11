#!/usr/bin/env python
# -*- coding: utf-8 -*-


# Verbatim copy of `argumentation_analysis/agents/core/informal/prompts.py` from
# the 2025-Epita-Intelligence-Symbolique project
# (https://github.com/jsboigeEpita/2025-Epita-Intelligence-Symbolique),
# Copyright (c) 2025 jsboigeEpita, MIT License.
# Source commit: a8025f60 (2026-07-02) "feat(conv-c): de-templatised PM prompt +
# designation backfill + pipeline cap (#1334 phase 3/3) (#1345)".
# Verbatim import rationale: see NOTICE-EPITA at the root of this directory.
#
# Verbatim integrity: file content below this header is byte-for-byte identical
# to the upstream source at the cited commit. No CoursIA modification.
#
# RUNTIME WIRING (#23633, Volet B etape 4) : ce module est enregistre sous son
# nom amont par `_epita_vendor_shim.install_informal_runtime_shim()` pour que
# les imports litteraux de `_informal_definitions.py` (verbatim, non modifiable)
# resolvent au runtime.

"""
Collection de prompts pour les fonctions sémantiques de l'analyse informelle.

Ce module contient les chaînes de caractères formatées (templates) utilisées
comme prompts pour les fonctions sémantiques du `InformalAnalysisAgent`.
Chaque prompt est une constante de module conçue pour une tâche LLM spécifique.
"""

# agents/core/informal/prompts.py
import logging

# --- Prompt pour l'Identification d'Arguments ---
# Ce prompt demande au LLM d'extraire les arguments ou affirmations distincts
# d'un texte.
#
# Variables:
#   - {{$input}}: Le texte brut à analyser.
#
# Sortie attendue:
#   Une liste d'arguments, formatée avec un argument par ligne.
prompt_identify_args_v8 = """
[Instructions]
Analysez le texte argumentatif fourni ($input) et identifiez tous les arguments ou affirmations distincts.

Un bon argument doit:
1. Exprimer une position claire ou une affirmation défendable
2. Être concis (idéalement 10-20 mots)
3. Capturer une idée complète sans détails superflus
4. Être formulé de manière neutre et précise

Pour chaque argument identifié:
- Formulez-le comme une affirmation simple et directe
- Concentrez-vous sur les affirmations principales défendues ou attaquées
- Évitez les formulations trop longues ou trop complexes
- Assurez-vous de capturer tous les arguments importants, même secondaires

Retournez UNIQUEMENT la liste des arguments, un par ligne, sans numérotation, préambule ou commentaire.

[Texte à Analyser]
{{$input}}
+++++
[Arguments Identifiés (un par ligne)]
"""

# --- Prompt pour l'Analyse de Sophismes ---
# Ce prompt demande au LLM d'analyser un argument et d'identifier les
# sophismes potentiels.
#
# Variables:
#   - {{$input}}: L'argument à analyser.
#
# Sortie attendue:
#   Un objet JSON unique avec une clé "sophismes", contenant une liste
#   d'objets. Chaque objet représente un sophisme et doit contenir les clés
#   "nom", "explication", "citation", et "reformulation".
prompt_analyze_fallacies_v1 = """
[Instructions]
Analysez l'argument fourni ($input) et identifiez les sophismes potentiels qu'il contient.
Votre réponse doit être un objet JSON valide contenant une seule clé "sophismes", qui est une liste d'objets.
Chaque objet doit représenter un sophisme identifié et contenir les clés suivantes : "fallacy_type", "explication", "citation", "reformulation".
Si aucun sophisme n'est identifié, retournez un objet JSON avec une liste vide : {"sophismes": []}.
Ne retournez aucun texte ou explication en dehors de l'objet JSON.

[Argument à Analyser]
{{$input}}
+++++
[Sophismes Identifiés (JSON)]
"""

# --- Prompt pour l'Analyse de Sophismes (V3 - Tool Use) ---
# Ce prompt instruit le LLM pour qu'il utilise les fonctions natives (outils)
# afin d'identifier un sophisme de manière autonome et raisonnée.
prompt_analyze_fallacies_v3_tool_use = """
[Contexte]
Vous êtes un assistant spécialisé dans l'analyse critique. Votre objectif est d'identifier des sophismes dans un argument en utilisant les outils à votre disposition pour explorer une taxonomie.

[Objectif]
Analysez l'argument fourni ($input) et utilisez les fonctions du plugin `InformalAnalyzer` pour identifier, valider et nommer correctement les sophismes.

[Outils Disponibles (fonctions du plugin InformalAnalyzer)]
Vous pouvez utiliser les fonctions suivantes :
- `list_fallacy_categories()`: Pour obtenir la liste des grandes familles de sophismes.
- `list_fallacies_in_category(category_name: str)`: Pour lister les sophismes d'une famille spécifique.
- `get_fallacy_details(fallacy_pk_str: str)`: Pour obtenir les détails (définition, etc.) d'un sophisme par son ID (PK).
- `find_fallacy_definition(fallacy_name: str)`: Pour rechercher une définition de sophisme par son nom ou des mots-clés.

[Démarche OBLIGATOIRE et SÉQUENTIELLE]
1.  **Hypothèse** : Lisez l'argument et formulez une hypothèse sur le type de sophisme général.
2.  **Exploration** : Utilisez `list_fallacy_categories()` et `list_fallacies_in_category(...)` pour trouver le nom et l'ID (PK) du sophisme général le plus probable.
3.  **Validation** : Utilisez `get_fallacy_details(...)` avec l'ID (PK) trouvé pour obtenir la définition exacte et confirmez qu'elle correspond à l'argument.
4.  **Raffinement (CRUCIAL)** : Une fois un sophisme général validé (ex: `ad-hominem`), **cherchez systématiquement s'il existe une variante plus spécifique**. Utilisez `list_fallacies_in_category` sur la même catégorie ou `find_fallacy_definition` avec des mots-clés pour trouver des sous-types (ex: `appeal-to-hypocrisy`, `ad hominem circumstantial`). Comparez les définitions et **choisissez TOUJOURS le plus spécifique**.
5.  **Réponse Finale** : Une fois le sophisme le plus spécifique identifié et validé, et SEULEMENT à ce moment-là, structurez votre réponse finale en JSON.

[Exemples de Logique de Raffinement]
- **Exemple 1 : Appel à l'hypocrisie**
  - Si l'argument est : "Mon médecin me dit de perdre du poids, mais il est lui-même en surpoids."
  - Votre hypothèse initiale est 'ad-hominem', mais après exploration, vous identifiez 'appeal-to-hypocrisy' comme plus spécifique.
  - **Votre réponse finale DOIT être 'appeal-to-hypocrisy'.**

- **Exemple 2 : Concept Volé**
  - Si l'argument est : "La raison n'est pas fiable, donc on ne peut pas l'utiliser pour trouver la vérité."
  - Votre raisonnement doit identifier que l'argument utilise la raison pour s'auto-invalider. C'est une contradiction performative.
  - Après exploration, vous identifiez 'stolen-concept' (ou 'self-refuting idea') comme le terme exact.
  - **Votre réponse finale DOIT être 'stolen-concept'.**

[RÈGLE D'OR DE LA SPÉCIFICITÉ]
Avant de produire la réponse JSON, posez-vous cette question finale : "Est-ce que le sophisme que j'ai choisi est le plus spécifique possible ?". Si un sous-type existe et correspond, vous DEVEZ l'utiliser. Par exemple, si l'argument est un cas clair de 'Appeal to Hypocrisy', retourner 'ad-hominem' est une erreur.

[Format de la Réponse Finale]
La réponse finale doit être un unique objet JSON valide. Ne retournez rien d'autre.
Cet objet JSON doit contenir une clé "sophismes", qui est une liste d'objets.
Chaque objet de la liste représente un sophisme identifié et doit contenir :
- "nom": Le nom exact et normalisé du sophisme, validé via les outils.
- "justification": Une explication concise expliquant pourquoi l'argument constitue ce sophisme spécifique, en lien avec la définition que vous avez récupérée.

Si, après une analyse rigoureuse avec les outils, aucun sophisme ne correspond, retournez une liste vide : `{"sophismes": []}`.

[RAPPEL FINAL]
Votre seule et unique sortie doit être l'objet JSON contenant la clé "sophismes". N'incluez aucun texte, aucune pensée, aucun appel d'outil, aucune explication avant ou après le bloc JSON.

[Argument à analyser]
{{$input}}
"""

# --- Prompt pour la Justification d'Attribution de Sophisme ---
# Ce prompt guide le LLM pour qu'il rédige une justification détaillée
# expliquant pourquoi un argument donné correspond à un type de sophisme
# spécifique.
#
# Variables:
#   - {{$argument}}: L'argument analysé.
#   - {{$fallacy_type}}: Le nom du sophisme à justifier.
#   - {{$fallacy_definition}}: La définition du sophisme pour contextualiser.
#
# Sortie attendue:
#   Un texte de justification structuré et détaillé.
prompt_justify_fallacy_attribution_v1 = """
[Instructions]
Vous devez justifier pourquoi l'argument fourni contient le sophisme spécifié.

Votre justification doit:
1. Expliquer clairement le mécanisme du sophisme indiqué
2. Montrer précisément comment l'argument correspond à ce type de sophisme
3. Citer des parties spécifiques de l'argument qui illustrent le sophisme
4. Fournir un exemple similaire pour clarifier (si pertinent)
5. Expliquer l'impact de ce sophisme sur la validité de l'argument

[Argument]
{{$argument}}

[Sophisme à Justifier]
{{$fallacy_type}}

[Définition du Sophisme]
{{$fallacy_definition}}
+++++
[Justification Détaillée]
"""

# Log de chargement
logging.getLogger(__name__).debug(
    "Module agents.core.informal.prompts chargé (V9 - Template dynamique pour analyse)."
)
