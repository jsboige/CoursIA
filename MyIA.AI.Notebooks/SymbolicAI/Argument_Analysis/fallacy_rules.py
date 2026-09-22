"""Regles symboliques de detection de sophismes en francais.

Organe pur (aucune dependance hors stdlib) issu de la distillation du
sous-projet EPITA ``2.3.2-detection-sophismes`` (depot
``jsboigeEpita/2025-Epita-Intelligence-Symbolique``, fichiers
``symbolic_rules.py`` et ``argument_mining_rules.py``, audit de maturite
R887 du 2026-08-30 : partie vivante = les regles et le dataset, le moteur
CamemBERT finetune 1,8 Go etant archaeologique et hors perimetre).

Contenu porte fidelement (divergences documentees plus bas) :

- ``FALLACY_RULES`` : 6 cles / 5 familles de sophismes, 15 motifs de
  tokens au format spaCy Matcher --
  AD_HOMINEM_DIRECT (3), PENTE_GLISSANTE (3), GENERALISATION_HATIVE (2),
  APPEL_A_LA_TRADITION (3), ARGUMENT_D_AUTORITE_SIMPLE (1),
  ARGUMENT_D_AUTORITE_GENERAL (3).
- ``CLAIM_PATTERNS`` : 2 motifs de claim (assertion marquee).
- ``PREMISE_PATTERNS`` : 3 motifs de premisse (support marque).

L'API ``matcher_rules()`` rend des motifs directement consommables par
``spacy.matcher.Matcher`` ; l'API ``detect_fallacies()`` construit le
Matcher si spaCy est disponible (le modele francais doit etre installe :
``python -m spacy download fr_core_news_sm``).

Divergences documentees vis-a-vis du source (convention distillation) :

1. Les cles accentuees du source (``GÉNÉRALISATION_HÂTIVE``,
   ``APPEL_À_LA_TRADITION``, ``ARGUMENT_D_AUTORITÉ_*``) sont conservees
   telles quelles : elles sont l'identite de la regle, pas de la prose.
2. Les specs de tokens nues ``{"OP": "+"}`` des motifs de mining (sans
   autre attribut) sont normalisees en jokers explicites
   ``{"TEXT": {"REGEX": ".*"}}`` avec le meme operateur : spaCy exige au
   moins un attribut hors ``OP`` par spec de token. Semantique inchangee.
3. Les comptes mesures ici (15 motifs sophismes, 2+3 motifs mining)
   divergent des comptes annonces par l'audit R887 (13 et 6) : les
   nombres ci-dessous sont recomptes sur le source charge, fichier par
   fichier ; l'ecart est consigne, pas silencieux.
4. ``mine_claims_premises`` deduplique les matches par position de
   debut (plus long match conserve) : le joker ``OP: "+"`` du source,
   applique a une spec ``TEXT`` quelconque, fait rendre au Matcher
   toutes les longueurs possibles (matches en cascade imbriques).
   Semantique du marqueur conservee, bruit d'affichage supprime.

Le mapping famille -> etiquette pedagogique (``FALLACY_LABELS``) et
l'index famille -> cles (``FAMILY_KEYS``) sont ajoutes par la
distillation : le source repetait l'etiquette dans chaque motif.
"""

from __future__ import annotations

# Etiquettes pedagogiques par famille (fusion AUTORITE_SIMPLE/GENERAL
# dans une meme famille : le source les separe en deux cles mais les
# etiquette identiquement).
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
    "GENERALISATION_HATIVE": ["GÉNÉRALISATION_HÂTIVE"],
    "APPEL_A_LA_TRADITION": ["APPEL_À_LA_TRADITION"],
    "ARGUMENT_D_AUTORITE": [
        "ARGUMENT_D_AUTORITÉ_SIMPLE",
        "ARGUMENT_D_AUTORITÉ_GÉNÉRAL",
    ],
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
        # Discredit generalise : "On ne peut pas faire confiance à [GROUPE]"
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
        # Attaque de caractere : "[Nom] est [adjectif], donc son argument est faux."
        {
            "PATTERN": [
                {"POS": "PROPN"},
                {"LEMMA": "être"},
                {"POS": "ADJ"},
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
        # Chaine de consequences negatives : "Cela mènera inévitablement à..."
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
    "GÉNÉRALISATION_HÂTIVE": [
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
        # "Sur la base de [petit nombre] exemples..."
        {
            "PATTERN": [
                {"LOWER": "sur"},
                {"LOWER": "la"},
                {"LOWER": "base"},
                {"LOWER": "de"},
                {"POS": "NUM"},
                {"POS": "NOUN"},
                {"LOWER": "exemples"},
            ],
            "FALLACY_TYPE": "Généralisation hâtive (Hasty Generalization)",
        },
    ],
    "APPEL_À_LA_TRADITION": [
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
        # "C'est la tradition."
        {
            "PATTERN": [
                {"LOWER": "c'"},
                {"LEMMA": "être"},
                {"LOWER": "la"},
                {"LOWER": "tradition"},
            ],
            "FALLACY_TYPE": "Appel à la tradition (Appeal to Tradition)",
        },
        # "Depuis toujours..."
        {
            "PATTERN": [{"LOWER": "depuis"}, {"LOWER": "toujours"}],
            "FALLACY_TYPE": "Appel à la tradition (Appeal to Tradition)",
        },
    ],
    "ARGUMENT_D_AUTORITÉ_SIMPLE": [
        # "[EXPERT/SOURCE] a dit que [PROPOSITION], donc c'est vrai."
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
        }
    ],
    "ARGUMENT_D_AUTORITÉ_GÉNÉRAL": [
        # "[GROUPE] disent que [PROPOSITION]"
        {
            "PATTERN": [
                {"POS": "NOUN", "OP": "+"},
                {"LEMMA": "le", "OP": "?"},
                {"LEMMA": "dire"},
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
        # "[Personne célèbre] a dit..."
        {
            "PATTERN": [{"POS": "PROPN"}, {"LEMMA": "dire"}],
            "FALLACY_TYPE": "Argument d'autorité (Appeal to Authority)",
        },
    ],
}

# --- Argument mining : claims et premisses (source argument_mining_rules.py) ---

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
    # "Les faits montrent que...", "Des études indiquent que..."
    {
        "PATTERN": [
            {"LOWER": {"IN": ["les", "des"]}},
            {"POS": "NOUN"},
            {"LEMMA": {"IN": ["montrer", "indiquer"]}},
            {"LOWER": "que"},
            {"TEXT": {"REGEX": ".*"}, "OP": "+"},
        ]
    },
]


def _wildcard(op: str = "+") -> dict:
    """Spec de token joker, equivalent de la spec nue ``{"OP": op}``.

    spaCy exige au moins un attribut hors ``OP`` dans chaque spec de
    token (divergence 2 documentee en en-tete de module).
    """
    return {"TEXT": {"REGEX": ".*"}, "OP": op}


def rule_counts() -> dict:
    """Comptes mesures des motifs (sophismes, claims, premisses)."""
    fallacy = sum(len(v) for v in FALLACY_RULES.values())
    return {
        "families": len(FALLACY_LABELS),
        "rule_keys": len(FALLACY_RULES),
        "fallacy_motifs": fallacy,
        "claim_motifs": len(CLAIM_PATTERNS),
        "premise_motifs": len(PREMISE_PATTERNS),
    }


def validate_patterns() -> list[str]:
    """Verifie que chaque motif porte au moins un attribut hors OP.

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
    """Detecte les sophismes de ``text`` par motifs symboliques.

    Rend une liste de detections ``{"key", "label", "pattern_index",
    "start", "end", "excerpt"}`` ordonnee par position. Necessite spaCy
    et un modele francais (``fr_core_news_sm`` ou plus) ; le parametre
    ``nlp`` permet d'injecter un pipeline deja charge.
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
            }
        )
    return sorted(results, key=lambda r: (r["start"], r["end"]))


def mine_claims_premises(text: str, nlp=None) -> dict:
    """Extrait claims et premisses marquees de ``text`` par motifs.

    Rend ``{"claims": [...], "premises": [...]}`` avec pour chaque
    extraction ``{"start", "end", "excerpt"}``.
    """

    def run(matcher, doc):
        # Divergence 4 : plus long match par position de debut (le joker
        # OP:"+" du source rend toutes les longueurs imbriquees).
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
