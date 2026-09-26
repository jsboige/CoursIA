"""Règles symboliques de détection de sophismes en français.

Organe pur (aucune dépendance hors stdlib). Il porte l'étage symbolique de la
détection de sophismes **tel qu'il vit dans le cœur du dépôt EPITA**
(``argumentation_analysis/adapters/french_fallacy_adapter.py``,
``_SYMBOLIC_FALLACY_RULES`` : 5 clés, 13 motifs). Le sous-projet étudiant
``2.3.2-detection-sophismes`` (``jsboigeEpita/2025-Epita-Intelligence-Symbolique``,
fichiers ``symbolic_rules.py`` et ``argument_mining_rules.py``) reste en
généalogie : les règles y ont d'abord existé, la consolidation du cœur en a
retenu une partie et corrigé une autre (G4 #1186).

**Nature de ce qui est repris — déclaration exigée par la liste « bruit »**
(décision coordinateur du 2026-09-26, portée par le corps de l'épic #4960).
Ce que cet organe tient du dépôt tiers est une **extraction de données** — la
table de règles elle-même — et **non un import de code** : il n'importe rien de
``adapters/``, ``mocks/`` ni de l'orchestration, et sa seule dépendance est
spaCy, en import tardif (l'organe reste importable sans elle). La table est
**re-déclarée ici en données** parce que l'étage dont elle vient n'est **pas
consolidé dans le tronc de CoursIA** : ``argumentation_analysis/`` y est absent
— mesuré sur ``main``, où ``_SYMBOLIC_FALLACY_RULES`` n'existe nulle part — et
cet étage ne vit que dans le dépôt tiers. C'est précisément la condition mise à
l'extraction de données : elle est admise quand l'en-tête du module consommateur
la déclare comme consolidation d'un étage que le tronc n'a pas consolidé.

Contenu porté — 13 motifs / 5 clés, identiques au cœur :

- ``FALLACY_RULES`` : AD_HOMINEM_DIRECT (3), PENTE_GLISSANTE (3),
  GENERALISATION_HATIVE (2), APPEL_A_LA_TRADITION (3), ARGUMENT_AUTORITE (2).
- ``CLAIM_PATTERNS`` : 2 motifs de claim ; ``PREMISE_PATTERNS`` : 2 motifs de
  prémisse.
- ``justify_fallacy()`` : justification française par famille (G5 #1186),
  *fail-loud* (#1019) — ``None`` plutôt qu'une justification fabriquée. Les quatre
  gabarits hérités couvrent **3 des 5 familles** de cet organe : la pente
  glissante et l'appel à la tradition n'en ont pas et rendent ``None`` (mesuré,
  section des limites du notebook).

Ce que la re-fondation a changé par rapport à la première distillation :

1. **Deux motifs retirés.** ``[NOUN] (le) dire`` et ``[PROPN] dire`` reposaient
   sur une simple paire sujet-verbe, sans marqueur d'autorité ; le cœur ne les a
   pas retenus. Leur clé ``ARGUMENT_D_AUTORITE_GENERAL`` disparaît avec eux —
   les deux motifs restants partagent ``ARGUMENT_AUTORITE``.
2. **Un motif de prémisse retiré.** ``les/des NOUN montrer/indiquer que``,
   absent du cœur.
3. **Deux réparations G4 (#1186) adoptées.** Elles viennent du cœur, qui les a
   restaurées depuis le projet étudiant en corrigeant ce qui les empêchait de
   mordre sur du texte réel :
   - *ad hominem, motif 2* : le slot de ponctuation optionnel ``IS_PUNCT?``
     manquait — « Pierre est malhonnête, donc son argument est faux. » ne
     matchait jamais, la virgule s'intercalant entre l'adjectif et le
     connecteur ;
   - *généralisation hâtive, motif 1* : un slot ``NOUN`` surnuméraire précédait
     ``exemples``, qui est lui-même le nom — le motif était immatchable.

   Le notebook mesure ces deux réparations : dormants avant, vivants après.
4. **Clés non accentuées.** ``GENERALISATION_HATIVE``, ``APPEL_A_LA_TRADITION``,
   ``ARGUMENT_AUTORITE`` sont désormais nommées comme dans le cœur. La première
   distillation conservait les accents du source étudiant ; un identifiant
   accentué est un risque de régression (cure #2876).

Divergences conservées, mesurées dans le notebook :

- Les specs de tokens nues ``{"OP": "+"}`` des motifs de minage sont écrites en
  jokers explicites ``{"TEXT": {"REGEX": ".*"}}``. Choix de lisibilité : spaCy
  3.8.16 accepte les deux formes, avec ou sans ``Matcher(validate=True)``, et
  elles rendent les mêmes matches (mesure du 2026-09-23).
- ``mine_claims_premises`` déduplique par position de début (plus long match
  conservé) : le joker ``OP: "+"`` fait rendre au Matcher toutes les longueurs
  imbriquées depuis le même point de départ.

L'API ``detect_fallacies()`` construit le Matcher si spaCy est disponible (le
modèle français doit être installé : ``python -m spacy download fr_core_news_sm``).
"""

from __future__ import annotations

# Étiquettes pédagogiques par famille.
FALLACY_LABELS = {
    "AD_HOMINEM": "Attaque personnelle (Ad Hominem)",
    "PENTE_GLISSANTE": "Pente glissante (Slippery Slope)",
    "GENERALISATION_HATIVE": "Généralisation hâtive (Hasty Generalization)",
    "APPEL_A_LA_TRADITION": "Appel à la tradition (Appeal to Tradition)",
    "ARGUMENT_D_AUTORITE": "Argument d'autorité (Appeal to Authority)",
}

FAMILY_KEYS = {
    "AD_HOMINEM": ["AD_HOMINEM_DIRECT"],
    "PENTE_GLISSANTE": ["PENTE_GLISSANTE"],
    "GENERALISATION_HATIVE": ["GENERALISATION_HATIVE"],
    "APPEL_A_LA_TRADITION": ["APPEL_A_LA_TRADITION"],
    "ARGUMENT_D_AUTORITE": ["ARGUMENT_AUTORITE"],
}

FALLACY_RULES = {
    "AD_HOMINEM_DIRECT": [
        # "Vous avez tort parce que vous êtes [ADJECTIF NÉGATIF]"
        {
            "PATTERN": [
                {"LOWER": {"IN": ["tu", "vous", "il", "elle"]}},
                {"LEMMA": "être"},
                {"POS": "DET", "OP": "*"},
                {"POS": "ADJ"},
                {"LOWER": {"IN": ["donc", "alors", "parce que", "car"]}},
                {"TEXT": {"REGEX": ".*"}},
            ],
            "FALLACY_TYPE": "Attaque personnelle (Ad Hominem)",
        },
        # Discrédit généralisé : "On ne peut pas faire confiance à [GROUPE]"
        {
            "PATTERN": [
                {"LOWER": "on"},
                {"LOWER": "ne"},
                {"LEMMA": "pouvoir"},
                {"LOWER": "pas"},
                {"LEMMA": "faire"},
                {"LOWER": "confiance"},
                {"LEMMA": "à"},
                {"POS": "DET", "OP": "?"},
                {"POS": "NOUN"},
            ],
            "FALLACY_TYPE": "Attaque personnelle (Ad Hominem)",
        },
        # Attaque de caractère : "[Nom] est [adjectif], donc son argument est faux."
        # G4 (#1186) : le slot de ponctuation optionnel manquait, la virgule
        # s'intercale dans « Pierre est malhonnête, donc … » et le motif ne
        # matchait jamais — le cœur l'a restauré avec cette correction.
        {
            "PATTERN": [
                {"POS": "PROPN"},
                {"LEMMA": "être"},
                {"POS": "ADJ"},
                {"IS_PUNCT": True, "OP": "?"},
                {"LOWER": {"IN": ["donc", "alors"]}},
                {"POS": "DET"},
                {"POS": "NOUN"},
                {"LEMMA": "être"},
                {"LOWER": "faux"},
            ],
            "FALLACY_TYPE": "Attaque personnelle (Ad Hominem)",
        },
    ],
    "PENTE_GLISSANTE": [
        # "Si nous autorisons A, alors B se produira inévitablement."
        {
            "PATTERN": [
                {"LOWER": "si"},
                {"LOWER": "on"},
                {"LEMMA": "autoriser"},
                {"POS": "NOUN"},
                {"LOWER": "alors"},
                {"TEXT": {"REGEX": ".*"}},
            ],
            "FALLACY_TYPE": "Pente glissante (Slippery Slope)",
        },
        # Chaîne de conséquences négatives : "Cela mènera inévitablement à..."
        {
            "PATTERN": [
                {"LOWER": "cela"},
                {"LEMMA": "mener"},
                {"LOWER": "inévitablement"},
                {"LEMMA": "à"},
                {"TEXT": {"REGEX": ".*"}},
            ],
            "FALLACY_TYPE": "Pente glissante (Slippery Slope)",
        },
        # "Le premier pas vers..."
        {
            "PATTERN": [
                {"LOWER": "le"},
                {"LOWER": "premier"},
                {"LOWER": "pas"},
                {"LOWER": "vers"},
                {"TEXT": {"REGEX": ".*"}},
            ],
            "FALLACY_TYPE": "Pente glissante (Slippery Slope)",
        },
    ],
    "GENERALISATION_HATIVE": [
        # "[QUANTIFICATEUR] [GROUPE] sont [ADJECTIF]."
        {
            "PATTERN": [
                {"LOWER": {"IN": ["tous", "toutes", "chaque", "personne"]}},
                {"POS": "NOUN", "OP": "+"},
                {"LEMMA": "être"},
                {"POS": "ADJ"},
            ],
            "FALLACY_TYPE": "Généralisation hâtive (Hasty Generalization)",
        },
        # Moteur : "Sur la base de [petit nombre] exemples..."
        # G4 (#1186) : un slot NOUN surnuméraire précédait "exemples", qui est
        # lui-même le nom — le motif ne matchait jamais. Le cœur l'a restauré
        # sans ce slot.
        {
            "PATTERN": [
                {"LOWER": "sur"},
                {"LOWER": "la"},
                {"LOWER": "base"},
                {"LOWER": "de"},
                {"POS": "NUM"},
                {"LOWER": "exemples"},
            ],
            "FALLACY_TYPE": "Généralisation hâtive (Hasty Generalization)",
        },
    ],
    "APPEL_A_LA_TRADITION": [
        # "Nous avons toujours fait comme ça."
        {
            "PATTERN": [
                {"LOWER": "on"},
                {"LOWER": "a"},
                {"LOWER": "toujours"},
                {"LEMMA": "faire"},
                {"LOWER": "comme"},
                {"LOWER": "ça"},
            ],
            "FALLACY_TYPE": "Appel à la tradition (Appeal to Tradition)",
        },
        # "Depuis toujours..."
        {
            "PATTERN": [{"LOWER": "depuis"}, {"LOWER": "toujours"}],
            "FALLACY_TYPE": "Appel à la tradition (Appeal to Tradition)",
        },
        # G4 (#1186) : "C'est la tradition." — appel nu, restauré du projet
        # étudiant par le cœur.
        {
            "PATTERN": [
                {"LOWER": "c'"},
                {"LEMMA": "être"},
                {"LOWER": "la"},
                {"LOWER": "tradition"},
            ],
            "FALLACY_TYPE": "Appel à la tradition (Appeal to Tradition)",
        },
    ],
    "ARGUMENT_AUTORITE": [
        # "[GROUPE] dit que [PROPOSITION], donc [CONCLUSION]."
        {
            "PATTERN": [
                {"POS": "NOUN", "OP": "+"},
                {"LEMMA": "dire"},
                {"LOWER": "que"},
                {"TEXT": {"REGEX": ".*"}},
                {"LOWER": {"IN": ["donc", "alors"]}},
                {"TEXT": {"REGEX": ".*"}},
            ],
            "FALLACY_TYPE": "Argument d'autorité (Appeal to Authority)",
        },
        # "Selon [source non qualifiée]..."
        {
            "PATTERN": [
                {"LOWER": "selon"},
                {"POS": "DET"},
                {"POS": "NOUN"},
                {"TEXT": {"REGEX": ".*"}},
            ],
            "FALLACY_TYPE": "Argument d'autorité (Appeal to Authority)",
        },
    ],
}

# --- Argument mining : claims et prémisses ---

CLAIM_PATTERNS = [
    # "Je pense que...", "Nous croyons que..."
    {
        "PATTERN": [
            {"LOWER": {"IN": ["je", "nous"]}},
            {"LEMMA": {"IN": ["penser", "croire", "affirmer"]}},
            {"LOWER": "que"},
            {"TEXT": {"REGEX": ".*"}, "OP": "+"},
        ]
    },
    # Marqueurs de conclusion : "Donc...", "En conclusion..."
    {
        "PATTERN": [
            {"LOWER": {"IN": ["donc", "par", "en"]}},
            {"LOWER": {"IN": ["conséquent", "conclusion"]}},
            {"IS_PUNCT": True, "OP": "?"},
            {"TEXT": {"REGEX": ".*"}, "OP": "+"},
        ]
    },
]

PREMISE_PATTERNS = [
    # "Parce que...", "Étant donné que..."
    {
        "PATTERN": [
            {"LOWER": {"IN": ["parce", "car", "étant"]}},
            {"LOWER": {"IN": ["que", "donné"]}},
            {"TEXT": {"REGEX": ".*"}, "OP": "+"},
        ]
    },
    # "Selon [source]...", "D'après [source]..."
    {
        "PATTERN": [
            {"LOWER": {"IN": ["selon", "d'après"]}},
            {"POS": "NOUN"},
            {"TEXT": {"REGEX": ".*"}, "OP": "+"},
        ]
    },
]

# --- G5 (#1186) : justification française par famille de sophisme ---
#
# Un gabarit spécifique par famille, au lieu d'une ligne générique pour tout.
# Le projet étudiant émettait ces justifications verbatim ; le cœur les a
# restaurées. Chaque gabarit porte les sous-chaînes de familles qu'il couvre :
# la résolution se fait par clé directe OU par sous-chaîne de famille, car
# l'étiquette d'une détection peut venir d'un étage non symbolique (NLI, LLM)
# dont le vocabulaire diffère.
FALLACY_JUSTIFICATIONS_FR = [
    {
        "template": (
            "L'argument attaque la personne ou le caractère de l'adversaire "
            "plutôt que de réfuter son argument."
        ),
        "matches": ["Attaque personnelle", "Ad hominem", "Obstruction"],
    },
    {
        "template": (
            "Une conclusion générale est tirée à partir d'un échantillon trop "
            "limité ou non représentatif."
        ),
        "matches": ["Généralisation", "Erreur mathématique"],
    },
    {
        "template": (
            "L'argument s'appuie sur l'opinion d'une figure d'autorité ou sur "
            "l'émotion sans fournir de preuves suffisantes pour étayer "
            "l'affirmation."
        ),
        "matches": ["autorité", "Influence", "Appel à l'émotion"],
    },
    {
        "template": (
            "L'argument tente de discréditer une source ou une affirmation sans "
            "aborder le fond de la question, ou s'appuie sur des idées reçues "
            "sans les remettre en question."
        ),
        "matches": ["crédibilité", "Préjugé", "Insuffisance"],
    },
]


def justify_fallacy(fallacy_type: str) -> str | None:
    """Rend la justification française par famille d'un type de sophisme.

    Ordre de résolution : (1) correspondance directe sur l'une des
    sous-chaînes ``matches`` (insensible à la casse), (2) aucune
    correspondance → ``None``. *Fail-loud* (#1019) : une famille inconnue rend
    ``None``, jamais une justification générique fabriquée.
    """
    if not fallacy_type:
        return None
    needle = fallacy_type.lower()
    for entry in FALLACY_JUSTIFICATIONS_FR:
        for token in entry["matches"]:
            if token.lower() in needle:
                return entry["template"]
    return None


def _wildcard(op: str = "+") -> dict:
    """Spec de token joker, équivalent de la spec nue ``{"OP": op}``.

    Forme explicite retenue pour la lisibilité ; spaCy accepte aussi la spec
    nue (divergence documentée en en-tête de module).
    """
    return {"TEXT": {"REGEX": ".*"}, "OP": op}


def rule_counts() -> dict:
    """Comptes mesurés des motifs (sophismes, claims, prémisses, gabarits)."""
    fallacy = sum(len(v) for v in FALLACY_RULES.values())
    return {
        "families": len(FALLACY_LABELS),
        "rule_keys": len(FALLACY_RULES),
        "fallacy_motifs": fallacy,
        "claim_motifs": len(CLAIM_PATTERNS),
        "premise_motifs": len(PREMISE_PATTERNS),
        "justification_templates": len(FALLACY_JUSTIFICATIONS_FR),
    }


def validate_patterns() -> list[str]:
    """Vérifie que chaque motif porte au moins un attribut hors OP.

    Rend la liste des descriptions invalides (vide = tout est valide).
    """
    invalid: list[str] = []
    groups = [("fallacy", FALLACY_RULES), ("claim", {"_": CLAIM_PATTERNS}), ("premise", {"_": PREMISE_PATTERNS})]
    for group_name, group in groups:
        for key, motifs in group.items():
            for i, motif in enumerate(motifs):
                for j, spec in enumerate(motif["PATTERN"]):
                    if set(spec.keys()) == {"OP"}:
                        invalid.append(f"{group_name}[{key}].{i}.token{j}: OP seul")
    return invalid


def detect_fallacies(text: str, nlp=None) -> list[dict]:
    """Détecte les sophismes de ``text`` par motifs symboliques.

    Rend une liste de détections ``{"key", "label", "pattern_index", "start",
    "end", "excerpt", "justification"}`` ordonnée par position. Nécessite spaCy
    et un modèle français (``fr_core_news_sm`` ou plus) ; le paramètre ``nlp``
    permet d'injecter un pipeline déjà chargé.
    """
    if nlp is None:
        import spacy  # import tardif : l'organe reste importable sans spaCy

        nlp = spacy.load("fr_core_news_sm")
    from spacy.matcher import Matcher

    doc = nlp(text)
    matcher = Matcher(nlp.vocab)
    for key, motifs in FALLACY_RULES.items():
        for i, motif in enumerate(motifs):
            matcher.add(f"{key}#{i}", [motif["PATTERN"]])
    results = []
    for match_id, start, end in matcher(doc):
        key, idx = nlp.vocab.strings[match_id].split("#")
        family = next((f for f, keys in FAMILY_KEYS.items() if key in keys), key)
        results.append(
            {
                "key": key,
                "label": FALLACY_LABELS.get(family, key),
                "pattern_index": int(idx),
                "start": start,
                "end": end,
                "excerpt": doc[start:end].text,
                # G5 (#1186) : justification par famille, None quand la famille
                # n'a pas de gabarit (fail-loud #1019, jamais fabriquée).
                "justification": justify_fallacy(FALLACY_LABELS.get(family, key)),
            }
        )
    return sorted(results, key=lambda r: (r["start"], r["end"]))


def mine_claims_premises(text: str, nlp=None) -> dict:
    """Extrait claims et prémisses marquées de ``text`` par motifs.

    Rend ``{"claims": [...], "premises": [...]}`` avec pour chaque extraction
    ``{"start", "end", "excerpt"}``.
    """

    def run(matcher, doc):
        # Le joker OP:"+" du source rend toutes les longueurs imbriquées :
        # on conserve le plus long match par position de début.
        par_debut: dict[int, tuple[int, int]] = {}
        for _, s, e in matcher(doc):
            if s not in par_debut or (e - s) > (par_debut[s][1] - par_debut[s][0]):
                par_debut[s] = (s, e)
        return [
            {"start": s, "end": e, "excerpt": doc[s:e].text}
            for s, e in sorted(par_debut.values())
        ]

    if nlp is None:
        import spacy

        nlp = spacy.load("fr_core_news_sm")
    from spacy.matcher import Matcher

    doc = nlp(text)
    claim_matcher = Matcher(nlp.vocab)
    for i, motif in enumerate(CLAIM_PATTERNS):
        claim_matcher.add(f"claim#{i}", [motif["PATTERN"]])
    premise_matcher = Matcher(nlp.vocab)
    for i, motif in enumerate(PREMISE_PATTERNS):
        premise_matcher.add(f"premise#{i}", [motif["PATTERN"]])
    return {
        "claims": run(claim_matcher, doc),
        "premises": run(premise_matcher, doc),
    }