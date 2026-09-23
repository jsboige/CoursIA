"""Gestion de la verite en revison : JTMS et ATMS (strate 6, Epic #4588).

Port pedagogique DECLARE de la distillation-outil EPITA 2025 Argumentation,
projet ``1.4.1-JTMS`` (issues EPITA #1961 phase 4) :

* ``jtms.py`` (184 lignes) -> classes :class:`TMSBelief`, :class:`TMSJustification`,
  :class:`JTMS` ;
* ``atms.py`` (83 lignes) -> classes :class:`ATMSNode`, :class:`ATMS` ;
* corpus ``Beliefs/simple_beliefs.json`` et ``Beliefs/no_justification.json``
  reproduits en dictionnaires litteraux dans les tests.

Source mesureree firsthand au clone local ``2025-Epita-Intelligence-Symbolique``
a la tete ``487210fb`` (2026-09-22). Divergences declarees par rapport a la
source (regle ``organ-first-implementation``) :

1. **Pas de dependance ``networkx``** : le marquage ``non_monotonic`` des
   croyances en cycle (SCC non triviales) est calcule par fermeture
   d'accessibilite BFS, pas par ``nx.strongly_connected_components``.
   Resultat identique (memes SCC), dependance en moins (serie numpy-only).
2. **Pas de ``pyvis``** : la visualisation HTML de la source n'est pas
   portee (dependance lourde, sortie hors notebook) ; les carnets rendent
   les tables d'etats directement.
3. **Pas d'emojis** dans ``explain_belief`` (regle de style du depot) :
   les marqueurs ``[IN]`` / ``[OUT]`` remplacent les glyphes de la source.
4. La coquille ``update_non_monotonic_befielfs`` (source) est corrigee en
   ``update_non_monotonic_beliefs`` -- meme semantique, nom orthographie.

Semantiques COPIEES FIDELEMENT (ce sont elles que les gates des tests et le
temoin negatif du carnet verifient) :

* croyance tri-state ``valid in {True, None, False}`` (``None`` = inconnu) ;
* regle de soutien : une croyance est valide ssi IL EXISTE une justification
  dont tous les ``in`` sont valides ET aucun ``out`` n'est valide (un ``out``
  d'etat inconnu satisfait la clause de blocage : ``None`` est falsy) ;
* propagation recursive en profondeur via la liste des implications ;
* SCC non triviale dans le graphe des justifications -> croyance marquee
  ``non_monotonic`` -> son etat est force a ``None`` (refus de mesurer une
  croyance qui ne tient que par une boucle) ;
* ATMS : etiquettes = ensembles d'hypotheses (``frozenset``), produit
  carteien des etiquettes des ``in``, blocage si une etiquette d'un ``out``
  est incluse dans l'environnement fusionne, nogood via le noeud ``⊥``.

Conventions de la serie : determinisme complet (aucun aleatoire), CPU pur,
numpy non requis pour ce module.
"""

from __future__ import annotations

from itertools import product
from typing import Dict, Iterable, List, Optional, Set


# --------------------------------------------------------------------------- #
#  JTMS : un seul etat courant, revise par evenement                          #
# --------------------------------------------------------------------------- #


class TMSBelief:
    """Croyance JTMS : nom, etat tri-state, justifications et implications."""

    def __init__(self, name: str):
        self.name = name
        self.valid: Optional[bool] = None  # True / False / None (inconnu)
        self.non_monotonic = False  # la croyance ne tient que dans une boucle
        self.justifications: List["TMSJustification"] = []
        self.implications: List["TMSJustification"] = []

    def __str__(self) -> str:
        etat = "UNKNOWN" if self.valid is None else "VALID" if self.valid else "INVALID"
        suffixe = " (non-monotonic)" if self.non_monotonic else ""
        return f"{self.name} -> {etat}{suffixe}"

    def __repr__(self) -> str:
        return self.name

    def add_justification(self, justification: "TMSJustification") -> None:
        self.justifications.append(justification)
        self.compute_truth_statement()

    def remove_justification(self, justification: "TMSJustification") -> None:
        self.justifications.remove(justification)
        self.compute_truth_statement()

    def add_implication(self, justification: "TMSJustification") -> None:
        self.implications.append(justification)

    def set_truth_value(self, value: Optional[bool]) -> None:
        self.valid = value
        self.propagate()

    def compute_truth_statement(self) -> None:
        if self.non_monotonic:
            self.valid = None
            return
        self.valid = None
        for justification in self.justifications:
            if all(belief.valid for belief in justification.in_list) and not any(
                belief.valid for belief in justification.out_list
            ):
                self.valid = True
                break
        self.propagate()

    def propagate(self) -> None:
        for justification in self.implications:
            justification.conclusion.compute_truth_statement()


class TMSJustification:
    """Justification ``in_list`` / ``out_list`` -> ``conclusion``.

    Semantique de la source EPITA : la conclusion est soutenue si tous les
    ``in`` sont valides ET aucun ``out`` n'est valide.
    """

    def __init__(
        self,
        in_list: List[TMSBelief],
        out_list: List[TMSBelief],
        conclusion: TMSBelief,
    ):
        self.in_list: List[TMSBelief] = in_list
        self.out_list: List[TMSBelief] = out_list
        self.conclusion: TMSBelief = conclusion


class JTMS:
    """Systeme de maintenance de la verite base sur les justifications.

    Un seul etat courant : ``set_belief_validity`` pose une premisse et
    propage. Le marquage ``non_monotonic`` des cycles est recalcule a
    chaque ajout de justification (comportement de la source).
    """

    def __init__(self, strict: bool = False):
        self.beliefs: Dict[str, TMSBelief] = {}
        self.strict = strict

    def add_belief(self, name: str) -> None:
        if name not in self.beliefs:
            self.beliefs[name] = TMSBelief(name)

    def remove_belief(self, belief_name: str) -> None:
        if belief_name not in self.beliefs:
            raise KeyError(f"Unknown belief: {belief_name}")
        for justification in self.beliefs[belief_name].implications:
            self.beliefs[repr(justification.conclusion)].remove_justification(
                justification
            )
        self.beliefs.pop(belief_name)

    def set_belief_validity(self, belief_name: str, validity: Optional[bool]) -> None:
        if belief_name not in self.beliefs:
            raise KeyError(f"Unknown belief: {belief_name}")
        self.beliefs[belief_name].set_truth_value(validity)

    def add_justification(
        self,
        in_list: Iterable[str],
        out_list: Iterable[str],
        conclusion_name: str,
    ) -> None:
        in_list, out_list = list(in_list), list(out_list)
        for b in in_list + out_list + [conclusion_name]:
            if b not in self.beliefs:
                if self.strict:
                    raise KeyError(f"Unknown belief: {b}")
                self.add_belief(b)
        justification = TMSJustification(
            [self.beliefs[i] for i in in_list],
            [self.beliefs[o] for o in out_list],
            self.beliefs[conclusion_name],
        )
        self.beliefs[conclusion_name].add_justification(justification)
        for in_belief in justification.in_list:
            self.beliefs[in_belief.name].add_implication(justification)
        for out_belief in justification.out_list:
            self.beliefs[out_belief.name].add_implication(justification)
        self.update_non_monotonic_beliefs()

    def _justification_edges(self) -> List[tuple]:
        """Aretes (premisse -> conclusion) de toutes les justifications."""
        edges: List[tuple] = []
        for belief in self.beliefs.values():
            for justification in belief.justifications:
                for statement in justification.in_list + justification.out_list:
                    edges.append((statement.name, belief.name))
        return edges

    def update_non_monotonic_beliefs(self) -> None:
        """Marque ``non_monotonic`` chaque croyance d'une SCC non triviale.

        Divergence declaree n. 1 : fermeture d'accessibilite BFS au lieu de
        ``networkx.strongly_connected_components`` (memes composantes).
        """
        edges = self._justification_edges()
        succ: Dict[str, Set[str]] = {}
        for u, v in edges:
            succ.setdefault(u, set()).add(v)
        for name in self.beliefs:
            succ.setdefault(name, set())
        reach: Dict[str, Set[str]] = {}
        for start in succ:
            seen: Set[str] = set()
            front = [start]
            while front:
                node = front.pop()
                for nxt in succ.get(node, ()):  # acces direct, pas de defaultdict
                    if nxt not in seen:
                        seen.add(nxt)
                        front.append(nxt)
            reach[start] = seen
        for name, targets in reach.items():
            if any(name in reach[t] for t in targets if t != name):
                self.beliefs[name].non_monotonic = True

    def show(self) -> None:
        for b in self.beliefs.values():
            print(b)

    def status_table(self) -> Dict[str, Optional[bool]]:
        """Table {nom: valid} -- rendu des carnets et assertions des tests."""
        return {name: belief.valid for name, belief in self.beliefs.items()}

    def explain_belief(self, belief_name: str) -> str:
        """Explication textuelle des justifications d'une croyance.

        Divergence declaree n. 3 : marqueurs ``[IN]``/``[OUT]`` au lieu des
        glyphes emoji de la source (regle de style du depot).
        """
        belief = self.beliefs[belief_name]
        if not belief.justifications:
            return "No justification"
        explanations = []
        for j in belief.justifications:
            in_status = [
                f"{b} ({'VALID' if b.valid else 'not-VALID'})" for b in j.in_list
            ]
            out_status = [
                f"{b} ({'VALID' if b.valid else 'not-VALID'})" for b in j.out_list
            ]
            valid = all(b.valid for b in j.in_list) and not any(
                b.valid for b in j.out_list
            )
            block = (
                f"Justification :\n"
                f"IN : {', '.join(in_status) or '-'}\n"
                f"OUT : {', '.join(out_status) or '-'}\n"
                f"-> Results: {'VALID' if valid else 'not-VALID'}"
            )
            explanations.append(block)
        return "\n".join(explanations)


# --------------------------------------------------------------------------- #
#  ATMS : toutes les explications d'hypotheses, d'un coup                     #
# --------------------------------------------------------------------------- #


class ATMSNode:
    """Noeud ATMS : etiquette = ensemble d'environnements valides."""

    def __init__(self, name: str, is_assumption: bool = False):
        self.name = name
        self.label: Set[frozenset] = set()
        self.justifications: List["ATMSJustification"] = []
        self.is_assumption = is_assumption
        if is_assumption:
            self.label.add(frozenset({name}))

    def add_env(self, env: frozenset) -> bool:
        is_absent = env not in self.label
        if is_absent:
            self.label.add(env)
        return is_absent

    def __repr__(self) -> str:
        return self.name


class ATMSJustification:
    """Justification ATMS : meme forme ``in`` / ``out`` / conclusion que JTMS."""

    def __init__(
        self,
        in_nodes: List[ATMSNode],
        out_nodes: List[ATMSNode],
        conclusion: ATMSNode,
    ):
        self.in_nodes = in_nodes
        self.out_nodes = out_nodes
        self.conclusion = conclusion


class ATMS:
    """Assumption-based TMS : etiquettes globales et nogoods.

    Chaque noeud porte l'ensemble des environnements d'hypotheses sous
    lesquels il tient ; une contradiction ajoute un nogood et purge les
    environnements sur-ensembles.
    """

    CONTRADICTION = "⊥"  # perp, noeud "bottom"

    def __init__(self):
        self.nodes: Dict[str, ATMSNode] = {}
        self.contradiction_node = self.add_node(self.CONTRADICTION)

    def add_node(self, name: str, is_assumption: bool = False) -> ATMSNode:
        if name not in self.nodes:
            self.nodes[name] = ATMSNode(name, is_assumption)
        return self.nodes[name]

    def add_assumption(self, name: str) -> ATMSNode:
        return self.add_node(name, is_assumption=True)

    def add_justification(
        self,
        in_names: Iterable[str],
        out_names: Iterable[str],
        conclusion_name: str,
    ) -> None:
        justification = ATMSJustification(
            [self.nodes[n] for n in in_names],
            [self.nodes[n] for n in out_names],
            self.nodes[conclusion_name],
        )
        justification.conclusion.justifications.append(justification)

        in_env_lists = [node.label for node in justification.in_nodes]
        for combination in product(*in_env_lists):
            merged_env = frozenset().union(*combination) if combination else frozenset()
            if any(
                any(env.issubset(merged_env) for env in out_node.label)
                for out_node in justification.out_nodes
            ):
                continue
            if self.is_consistent(merged_env):
                justification.conclusion.add_env(merged_env)
                if justification.conclusion.name == self.CONTRADICTION:
                    self.invalidate_environment(merged_env)

    def invalidate_environment(self, env: frozenset) -> None:
        for node in self.nodes.values():
            node.label = {
                node_env for node_env in node.label if not env.issubset(node_env)
            }

    def get_environments(self, node_name: str) -> Set[frozenset]:
        return self.nodes[node_name].label

    def is_consistent(self, env: Iterable[str]) -> bool:
        return frozenset(env) not in self.nodes[self.CONTRADICTION].label
