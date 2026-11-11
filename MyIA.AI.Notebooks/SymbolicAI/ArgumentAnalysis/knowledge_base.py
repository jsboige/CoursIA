# -*- coding: utf-8 -*-
"""Base de connaissances d'un débat — propositions, arguments, conflits.

Port local (stdlib pur, déterministe, aucun LLM, aucune JVM) du module
``argumentation_analysis/agents/core/debate/knowledge_base.py`` du tronc EPITA
(restauration G8 #1184, adapté du moteur étudiant
``1_2_7_argumentation_dialogique/local_db_arg/src/core/knowledge_base.py``),
distillé dans le cadre du mandat Triple Distillation (sas trunk ligne 6,
EPIC #4960).

Le modèle tient en deux structures : un dictionnaire de propositions indexé
par contenu, et un dictionnaire d'arguments indexé par identifiant. La
sémantique est entièrement lexicale :

- la **population est transitive** — ``add_argument`` enregistre l'argument
  ET ses prémisses ET sa conclusion comme propositions ;
- le **support** (``find_supporting_arguments``) désigne les arguments dont
  la conclusion est exactement la proposition demandée ;
- l'**attaque** (``find_attacking_arguments``) désigne ceux dont la conclusion
  est la chaîne ``"¬" + contenu`` — la négation est un préfixe de chaîne, pas
  un opérateur logique ;
- la **cohérence** (``is_consistent``) échoue dès qu'une proposition et sa
  négation cohabitent — c'est le marqueur d'un débat ouvert ;
- ``entails`` est un test d'**appartenance** (``content in propositions``),
  pas un moteur d'inférence : la docstring du tronc le dit honnêtement
  (« contains ») alors que la docstring étudiante promettait « implique » —
  le nom est conservé pour la compatibilité, la sémantique documentée ici.

Divergences mesurées sur les sources, portées en documentation plutôt que
corrigées en silence :

1. **``rules`` et ``preferences`` non portés** : les deux sources déclarent
   ces attributs dans ``__init__`` mais aucune méthode ne les lit ni ne les
   écrit — état mort, exclu du port.
2. **``entails`` n'infère rien** : un argument ``[A] -> B`` plus la
   proposition ``A`` ne rend PAS ``entails(B)`` vrai — seule l'appartenance
   littérale compte (démontré au §4 du notebook).
3. **Négation purement lexicale** : ``¬¬P`` n'est pas reconnu comme ``P`` —
   une base contenant ``P`` et ``¬¬P`` est déclarée cohérente.
4. **Écrasement par contenu** : deux ``Proposition`` de même contenu mais de
   ``confidence`` différente ne laissent qu'un exemplaire en base (le
   dictionnaire est indexé par contenu).

Ajout du port (absent du tronc, qui construit la chaîne inline) : la fonction
utilitaire ``negation()`` rend la convention lexicale explicite et testable.

Usage direct (voir ``Argumentation-04b-Knowledge-Base-Python.ipynb`` pour la
démonstration exécutée) :

>>> kb = KnowledgeBase()
>>> kb.add_argument(FormalArgument(
...     premises=[Proposition(content="Les pauses restaurent la concentration")],
...     conclusion=Proposition(content="¬Le télétravail réduit la concentration")))
>>> kb.is_consistent()
True
"""

import uuid
from dataclasses import dataclass
from typing import Dict, List, Optional


@dataclass
class Proposition:
    """Une proposition logique identifiée par son contenu seul.

    L'égalité et le hachage ignorent ``truth_value``, ``confidence`` et
    ``source`` : deux propositions de même contenu sont la même proposition
    pour la base (divergence #4 du module).
    """

    content: str
    truth_value: Optional[bool] = None
    confidence: float = 1.0
    source: Optional[str] = None

    def __hash__(self):
        return hash(self.content)

    def __eq__(self, other):
        if isinstance(other, Proposition):
            return self.content == other.content
        return NotImplemented

    def __str__(self):
        return self.content


@dataclass
class FormalArgument:
    """Un argument structuré : prémisses, conclusion, force, schéma.

    Nommé ``FormalArgument`` pour ne pas confliguer avec les arguments du
    moteur de débat étudiant (convention du tronc).
    """

    premises: List[Proposition]
    conclusion: Proposition
    strength: float = 1.0
    scheme: Optional[str] = None
    id: str = ""

    def __post_init__(self):
        if not self.id:
            self.id = str(uuid.uuid4())

    def __str__(self):
        premises_str = ", ".join(str(p) for p in self.premises)
        return f"[{premises_str}] -> {self.conclusion}"


def negation(prop: Proposition) -> Proposition:
    """Négation lexicale d'une proposition : le préfixe « ¬ » sur le contenu.

    Convention du tronc : la négation n'est PAS un opérateur logique, c'est
    une construction de chaîne. ``negation(negation(p))`` produit donc
    « ¬¬P », qui est une proposition distincte de « P » (divergence #3).
    """
    return Proposition(content=f"¬{prop.content}")


class KnowledgeBase:
    """Base de connaissances d'un débat : propositions + arguments.

    Comportement verbatim du tronc (cf. docstring module pour les
    divergences documentées). Déterministe : aucune source d'aléatoire hors
    l'identifiant uuid4 des arguments (qui n'affecte aucun résultat).
    """

    def __init__(self):
        self.propositions: Dict[str, Proposition] = {}
        self.arguments: Dict[str, FormalArgument] = {}

    def add_proposition(self, prop: Proposition) -> None:
        """Ajoute une proposition (indexée par contenu — écrase un homonyme)."""
        self.propositions[prop.content] = prop

    def add_argument(self, arg: FormalArgument) -> None:
        """Ajoute un argument ET enregistre prémisses et conclusion.

        Conséquence mesurable : ``entails`` répond vrai sur une prémisse que
        personne n'a ajoutée explicitement — c'est l'argument qui l'a portée
        (population transitive).
        """
        self.arguments[arg.id] = arg
        for premise in arg.premises:
            self.add_proposition(premise)
        self.add_proposition(arg.conclusion)

    def find_supporting_arguments(self, prop: Proposition) -> List[FormalArgument]:
        """Arguments dont la conclusion est exactement la proposition."""
        return [
            arg
            for arg in self.arguments.values()
            if arg.conclusion.content == prop.content
        ]

    def find_attacking_arguments(self, prop: Proposition) -> List[FormalArgument]:
        """Arguments dont la conclusion est la négation lexicale de la proposition."""
        return [
            arg
            for arg in self.arguments.values()
            if arg.conclusion.content == f"¬{prop.content}"
        ]

    def is_consistent(self) -> bool:
        """Faux dès qu'une proposition et sa négation cohabitent.

        Le conflit ouvert P / ¬P est le marqueur qu'un débat a lieu sur P.
        """
        for prop_content in self.propositions:
            if f"¬{prop_content}" in self.propositions:
                return False
        return True

    def entails(self, prop: Proposition) -> bool:
        """Teste si la base CONTIENT la proposition (appartenance, pas inférence).

        Le nom est celui du tronc ; la sémantique est l'appartenance littérale
        au dictionnaire — ne pas y brancher d'attente déductive (divergence #2).
        """
        return prop.content in self.propositions

    def get_all_propositions(self) -> List[Proposition]:
        """Toutes les propositions enregistrées."""
        return list(self.propositions.values())

    def get_all_arguments(self) -> List[FormalArgument]:
        """Tous les arguments enregistrés."""
        return list(self.arguments.values())
