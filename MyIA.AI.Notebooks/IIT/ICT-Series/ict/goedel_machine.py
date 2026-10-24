# -*- coding: utf-8 -*-
"""Machine de Godel en jouet -- l'auto-amelioration prouvee de Schmidhuber, instrumentee.

Theorie
-------
Une machine de Godel (Schmidhuber 2003/2006, arXiv:cs/0309048) est un programme
``p`` qui reecrit son propre code quand -- et seulement quand -- il a PROUVE,
dans un systeme formel ``A`` axiomatisant son propre materiel, son environnement
et sa fonction d'utilite, que la reecriture augmente l'utilite future.  Le
theoreme cible (eq. 2 du papier) est ``u[s(t1) | switch] > u[s(t1) | keep]`` ;
une preuve de ce theoreme declenche ``check()`` qui pose le switchbit et
applique le switchprog.  Le chercheur de preuves BIOPS (Method 5.1) est
biais-optimal : en phase ``i`` il execute toute technique ``w`` de probabilite
``P(w) >= 2^-i`` pendant au plus ``2^i * P(w)`` etapes ; le Theoreme 5.1
garantit que ``w`` est trouvee en ``O(f(k)/P(w))`` etapes.

Operationalisation (ce module)
------------------------------
Un monde fini deterministe (le levier du paragraphe 4.4 du papier) : ``T``
cycles, actions ``setup``/``press``, ``k`` setups consecutifs rendent le levier
actif, la politique initiale ``e(1)`` presse sans jamais configurer (utilite 0).
Le systeme formel ``A`` du jouet axiomatise exactement la dynamique du monde :
toute question d'utilite y est decidable par simulation, ce qui rend le
theoreme cible prouvable mecaniquement.  Le chercheur enumere des techniques
(courtes sequences d'instructions parmi 6 + terminaison), les execute sous
budget BIOPS, et le ``CHECK`` ne feutre un switch que sur des theoremes
prouves -- la garantie FAQ 7 (un reecrivain d'utilite boge ne peut jamais
passer) tient ici par fermeture de l'instruction set, pas par la theorie des
preuves du papier.

Choix de methode numerotes (honnêtes)
-------------------------------------
1. Codage auto-delimitant : chaque symbole d'instruction a un code virgule
   ``1^r 0`` de longueur ``r+1`` (7 symboles : 6 instructions + HALT implicite).
   La somme de Kraft vaut exactement ``1 - 2^-7 <= 1`` : ``P(w) = 2^-c(w)``
   definit une sous-probabilite sur l'espace des techniques, comme dans le
   papier (programmes auto-delimitants).
2. Regles fusionnees : l'instruction ``RULE`` applique "la regle suivante
   applicable" (SIM si les premisses sont la, CMP si un switchprog est nomme,
   sinon no-op facture 1).  Cela modelise ``apply-rule(k,m,n)`` du papier avec
   une seule instance canonique par role, pour que la technique gagnante tienne
   dans la borne de longueur du jouet.
3. Cout d'une simulation : SIM facture ``n_politiques * (T - t1)`` etapes -- la
   preuve produit par une technique courte est longue (c'est le coeur de
   l'argument "short programs prove long theorems").
4. Espace borne : sequences d'au plus ``L_MAX = 5`` instructions parmi 6, soit
   9 331 techniques -- le jouet enumere TOUT cet espace (rien n'est echantillonne).
5. Memoisation : chaque technique est executee une fois sans budget pour mesurer
   son cout naturel ``s(w)`` (et son cout de feu si elle feutre) ; la dynamique
   de phase est ensuite EXACTE par arithmetique, car le budget de phase ``i``
   ne depend que de ``(i, c(w))`` : travail facture ``min(s(w), 2^(i-c(w)))``,
   feu des que ``2^(i-c(w)) >= s_feu(w)``.
6. ``CHECK`` n'accepte que des theoremes marques ``proven=True`` : les
   theoremes injectes par ``BOGUS`` (reecriture d'utilite, FAQ 7) sont morts a
   la naissance -- dans le papier cette garantie est portee par la theorie de
   la preuve (toute reecriture doit etre prouvee sous l'utilite COURANTE) ;
   dans le jouet elle est portee par la fermeture (aucune instruction ne cree
   d'axiome).  Limitation assumee, cf. carnet ICT-49 section 7.
7. La perte des cycles 1..t1-1 sous ``e(1)`` est le cout de la recherche
   elle-meme, pas de la decision de switch : l'optimalite verifiee (gate G4)
   est conditionnelle a l'instant de preuve ``t1``, comme le Theoreme 4.1 du
   papier (le switch prouve est optimal PARMI les candidats futurs, et aucun
   switch ulterieur n'est prouvable ensuite).

Gates falsifiables
------------------
- G1 (levier, par. 4.4) : BIOPS feutre le switchprog du levier ; la marge
  prouvee egale exactement le gain realise (monde deterministe axiomatise).
- G2 (FAQ 7) : enumeration EXHAUSTIVE de l'espace borne -- zero feu boge ;
  la technique concue pour reecrire l'utilite echoue meme a budget infini.
- G3 (Th. 5.1) : la meme technique fonctionnelle encodee deux fois (code
  pas cher vs code cher, Delta c = 8 bits) -- l'ecart de phases de decouverte
  vaut exactement ``Delta c`` et le rapport des travaux totaux est de l'ordre
  de ``2^Delta_c`` : le temps de trouvaille echelle en ``1/P(w)``.
- G4 (Th. 4.1) : le switch feutre est l'argmax sur TOUS les candidats
  ``(tau, politique)`` futurs, et la recherche continue apres le switch ne
  prouve AUCUNE amelioration supplementaire (pas de second switch).
- OOPS (par. 5.2) : sur une variante du monde ou la technique gelee
  s'applique telle quelle, l'essayer en tete reduit le travail total de
  plusieurs ordres de grandeur par rapport a la recherche fraiche.

Caveats (jouet != vraie machine de Godel)
-----------------------------------------
- ``A`` est complet sur son espace de questions fini (decidable) : aucune
  incompletude de Godel n'y mord -- dans la vraie machine, les ameliorations
  non prouvables sont simplement ignorees (FAQ du papier).
- L'auto-reference est simplifiee : le chercheur ne se snapshotte pas lui-meme
  via ``state2theorem`` (pont vers ``ict.godel_demonstration`` pour le lemme
  diagonal qui rend cette auto-reference possible).
- Pas d'esperance ``E_mu`` (eq. 1) : environnement deterministe, utilite
  exacte par simulation.
- Les constantes de la vraie machine sont astronomiques ; le jouet les rend
  triviales par construction (c'est sa raison d'etre pedagogique).

Toutes les fonctions sont deterministes (aucun aleatoire).
"""

from __future__ import annotations

from dataclasses import dataclass, field
from itertools import product
from typing import Dict, List, Optional, Tuple

# ---------------------------------------------------------------------------
# Table d'instructions (paragraphe 3.1 du papier : six instructions)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Instruction:
    """Une instruction du jouet, avec son cout de codage (code virgule)."""

    name: str
    cost: int
    doc: str


# Ordre = rang du code virgule : le rang r coute r+1 bits.  HALT (rang 6) est
# le terminateur implicite de toute technique ; il n'est pas utilisable en
# sequence.  Somme de Kraft = sum(2^-1 ... 2^-7) = 1 - 2^-7 <= 1.
DEFAULT_TABLE: Tuple[Instruction, ...] = (
    Instruction("GETAX", 1, "get-axiom : recupere l'axiome suivant du monde"),
    Instruction("RULE", 2, "apply-rule : regle suivante applicable (SIM puis CMP)"),
    Instruction("CHECK", 3, "check : feutre le switch si le theoreme cible est prouve"),
    Instruction("BOGUS", 4, "reecrivain d'utilite (FAQ 7) : injecte un faux u, non prouve"),
    Instruction("STATE2THM", 5, "state2theorem : snapshot de l'etat courant en theoreme"),
    Instruction("SETSW", 6, "set-switchprog : nomme le candidat argmax des u prouves"),
)
HALT_COST = 7
N_INSTR = len(DEFAULT_TABLE)  # 6 instructions utilisables en sequence
L_MAX = 5  # borne de longueur du jouet (choix de methode n. 4)


# Table alternative pour le gate G3 : memes fonctionnalites, encodage plus
# cher pour la technique gagnante (rangs decales de 2).  Seuls GETAX et RULE
# changent de cout ; CHECK passe de 3 a 5, SETSW reste 6.
EXPENSIVE_TABLE: Tuple[Instruction, ...] = (
    Instruction("BOGUS", 1, "reecrivain d'utilite (FAQ 7)"),
    Instruction("STATE2THM", 2, "state2theorem"),
    Instruction("GETAX", 3, "get-axiom (encodage cher, gate G3)"),
    Instruction("RULE", 4, "apply-rule (encodage cher, gate G3)"),
    Instruction("CHECK", 5, "check (encodage cher, gate G3)"),
    Instruction("SETSW", 6, "set-switchprog"),
)


def technique_cost(w: Tuple[int, ...], table: Tuple[Instruction, ...]) -> int:
    """Longueur du code auto-delimitant de la technique w (HALT inclus)."""
    return sum(table[i].cost for i in w) + HALT_COST


def enumerate_techniques(
    table: Tuple[Instruction, ...] = DEFAULT_TABLE, l_max: int = L_MAX
) -> List[Tuple[Tuple[int, ...], int]]:
    """Tout l'espace borne, trie par cout croissant puis lexicographique."""
    out: List[Tuple[Tuple[int, ...], int]] = []
    n = len(table)
    for length in range(l_max + 1):
        for seq in product(range(n), repeat=length):
            out.append((seq, technique_cost(seq, table)))
    out.sort(key=lambda wc: (wc[1], wc[0]))
    return out


# ---------------------------------------------------------------------------
# Le monde du levier (paragraphe 4.4 du papier)
# ---------------------------------------------------------------------------

POLICIES: Tuple[str, ...] = ("keep", "lever", "setup_forever")


@dataclass(frozen=True)
class LeverWorld:
    """Monde fini deterministe, axiomatise en totalite dans A.

    T cycles numerotes 1..T.  Actions : ``setup`` (recompense 0, +1 setup
    consecutif), ``press`` (recompense 1 si le mode est ``ready``, 0 sinon ;
    casse la serie de setups).  Apres ``k`` setups consecutifs, le mode passe
    definitivement a ``ready``.  La politique initiale ``e(1)`` = ``keep``
    (presser toujours) ne configure jamais : recompense totale 0.  Le chercheur
    tourne au cycle ``t1`` ; l'etat du monde a ``t1`` (mode, setups) decoule
    de l'execution d'``e(1)`` jusque la.
    """

    T: int = 20
    k: int = 2
    t1: int = 4
    current_policy: str = "keep"
    axioms: Tuple[str, ...] = ("world",)  # ordre de GETAX
    label: str = "A"
    # Etat explicite au cycle t1 (mondes de continuation, gate G4) ; si absent,
    # l'etat est re-simule en executant current_policy depuis le cycle 1 --
    # correct pour les mondes A/B ou e(1) = 'keep' presse sans effet.
    state_at_t1: Optional[Tuple[str, int]] = None

    # -- dynamique -----------------------------------------------------------

    @staticmethod
    def _action_of(policy: str, mode: str, setups: int) -> str:
        if policy == "keep":
            return "press"
        if policy == "lever":
            return "setup" if mode == "setup" else "press"
        if policy == "setup_forever":
            return "setup"
        raise ValueError("politique inconnue: %s" % policy)

    def initial_state(self) -> Tuple[str, int]:
        """Etat du monde au cycle t1 : (mode, setups consecutifs)."""
        if self.state_at_t1 is not None:
            return self.state_at_t1
        mode, setups = "setup", 0
        for _ in range(1, self.t1):
            # e(1) presse toujours : mode inchange, serie cassee.
            mode, setups = self._step(mode, setups, "press")[1:]
        return mode, setups

    def _step(
        self, mode: str, setups: int, action: str
    ) -> Tuple[int, str, int]:
        if action == "setup":
            setups2 = setups + 1
            mode2 = "ready" if setups2 >= self.k else mode
            return 0, mode2, setups2
        # press
        reward = 1 if mode == "ready" else 0
        return reward, mode, 0

    def simulate(self, policy: str, from_t: int, mode: str, setups: int) -> int:
        """Value-to-go : somme des recompenses des cycles from_t+1 .. T sous policy.

        C'est le CONTENU de la regle SIM (choix de methode n. 3) : chaque cycle
        simule est une application de regle facturee au budget.
        """
        total = 0
        for _t in range(from_t + 1, self.T + 1):
            action = self._action_of(policy, mode, setups)
            reward, mode, setups = self._step(mode, setups, action)
            total += reward
        return total

    def sim_cost(self) -> int:
        """Cout en etapes d'une application de SIM (3 politiques simulees)."""
        return len(POLICIES) * (self.T - self.t1)


# ---------------------------------------------------------------------------
# Execution d'une technique (langage L du chercheur, paragraphe 3)
# ---------------------------------------------------------------------------


@dataclass
class RunOutcome:
    """Resultat de l'execution d'une technique sous budget (ou sans borne)."""

    fired: bool = False
    fire_cost: Optional[int] = None  # etapes jusqu'au feu (si fired)
    natural_cost: int = 0            # etapes jusqu'a terminaison
    margin: Optional[int] = None     # marge prouvee u(switch) - u(keep)
    switchprog: Optional[str] = None
    bogus_used: bool = False         # la technique a invoque BOGUS
    outcome: str = "end"


@dataclass
class _Store:
    theorems: List[Tuple] = field(default_factory=list)

    def add(self, th: Tuple) -> None:
        self.theorems.append(th)

    def pop(self) -> None:
        if self.theorems:
            self.theorems.pop()


def run_technique(
    w: Tuple[int, ...],
    world: LeverWorld,
    table: Tuple[Instruction, ...] = DEFAULT_TABLE,
    budget: Optional[int] = None,
) -> RunOutcome:
    """Execute la technique w dans le monde, sous budget BIOPS (None = non borne).

    Semantique des instructions (choix de methode n. 2 et 6) :
    - GETAX : pousse l'axiome suivant du monde (epuise = no-op facture).
    - RULE  : SIM si l'axiome 'world' est present et SIM pas encore fait
              (facture world.sim_cost()) ; sinon CMP si un switchprog est
              nomme et u(nomme) > u(politique courante) -> theoreme cible ;
              sinon no-op facture 1.
    - CHECK : si un theoreme cible prouve est present -> feu (le switch
              s'applique ; l'execution s'arrete).
    - BOGUS : injecte un u falsifie (100/cycle) marque proven=False --
              invisible pour SETSW et CHECK (garantie FAQ 7 du jouet).
    - STATE2THM : snapshot de l'etat (t1, mode, setups) en theoreme.
    - SETSW : nomme le switchprog = argmax des u PROUVES (aegalite : premier).
    """
    store = _Store()
    fetched = 0
    nominated: Optional[str] = None
    sim_done = False
    target_th: Optional[Tuple] = None
    res = RunOutcome()
    steps = 0

    def charge(n: int) -> bool:
        nonlocal steps
        steps += n
        return budget is None or steps <= budget

    for idx in w:
        instr = table[idx]
        if not charge(1):
            res.natural_cost = steps
            res.outcome = "budget"
            return res
        if instr.name == "GETAX":
            if fetched < len(world.axioms):
                store.add(("axiom", world.axioms[fetched]))
                fetched += 1
        elif instr.name == "RULE":
            has_world = any(t[0] == "axiom" and t[1] == "world" for t in store.theorems)
            if has_world and not sim_done:
                if not charge(world.sim_cost()):
                    res.natural_cost = steps
                    res.outcome = "budget"
                    return res
                mode, setups = world.initial_state()
                for pol in POLICIES:
                    u = world.simulate(pol, world.t1, mode, setups)
                    store.add(("u", pol, u, True))
                sim_done = True
            elif nominated is not None:
                if not charge(1):
                    res.natural_cost = steps
                    res.outcome = "budget"
                    return res
                u_nom = next(
                    (t[2] for t in store.theorems if t[:2] == ("u", nominated) and t[3]),
                    None,
                )
                u_cur = next(
                    (
                        t[2]
                        for t in store.theorems
                        if t[:2] == ("u", world.current_policy) and t[3]
                    ),
                    None,
                )
                if u_nom is not None and u_cur is not None and u_nom > u_cur:
                    target_th = ("target", nominated, u_nom - u_cur, True)
                    store.add(target_th)
            else:
                if not charge(1):
                    res.natural_cost = steps
                    res.outcome = "budget"
                    return res
        elif instr.name == "CHECK":
            proven_target = next(
                (t for t in store.theorems if t[0] == "target" and t[3]), None
            )
            if proven_target is not None:
                res.fired = True
                res.fire_cost = steps
                res.margin = proven_target[2]
                res.switchprog = proven_target[1]
                res.bogus_used = any(t[0] == "u" and not t[3] for t in store.theorems)
                res.natural_cost = steps
                res.outcome = "fired"
                return res
        elif instr.name == "BOGUS":
            store.add(("u", "lever", 100 * (world.T - world.t1), False))
        elif instr.name == "STATE2THM":
            mode, setups = world.initial_state()
            store.add(("state", world.t1, mode, setups))
        elif instr.name == "SETSW":
            best_pol, best_u = None, None
            for t in store.theorems:
                if t[0] == "u" and t[3]:
                    if best_u is None or t[2] > best_u:
                        best_pol, best_u = t[1], t[2]
            nominated = best_pol
        else:  # DELTHM non presente dans le jouet (voir docstring table)
            store.pop()
    res.natural_cost = steps
    res.outcome = "end"
    return res


# ---------------------------------------------------------------------------
# BIOPS -- Method 5.1 du papier, dynframe exacte par memoisation
# ---------------------------------------------------------------------------


@dataclass
class BIOPSResult:
    """Mesures d'une passe BIOPS complete sur un monde."""

    fired: bool
    technique: Optional[Tuple[int, ...]]
    code_cost: Optional[int]
    phase: Optional[int]           # phase du premier feu
    total_steps: int               # travail total facture jusqu'au feu (ou fin)
    fire_steps: Optional[int]      # etapes de la technique gagnante
    margin: Optional[int]
    switchprog: Optional[str]
    techniques_run: int            # techniques executees au moins une fois
    firing_techniques: int         # techniques qui feutrent a budget infini
    bogus_fires: int               # feus citant un theoreme BOGUS (attendu 0)
    i_max: int
    mode: str = "fresh"            # "fresh" | "oops"
    label: str = ""


def biops(
    world: LeverWorld,
    i_max: int = 40,
    table: Tuple[Instruction, ...] = DEFAULT_TABLE,
    l_max: int = L_MAX,
    frozen: Optional[Tuple[int, ...]] = None,
    label: str = "",
) -> BIOPSResult:
    """BIOPS (Method 5.1) : phase i execute toute w de P(w) >= 2^-i pour 2^i*P(w) etapes.

    En mode OOPS (``frozen`` donne), la classe gelee est essayee EN TETE de
    chaque phase avec la MOITIE du budget de phase ``2^(i-1)`` (regle 50/50 du
    paragraphe 5.2 : sur un nouveau probleme, la technique la plus recemment
    gelee est testee en premier, a grand budget -- elle n'attend pas que sa
    probabilite a priori la rende eligible).  La passe fraiche suit ensuite
    avec ses budgets par cout.  Le cout d'OOPS quand le gele ne rapporte rien
    vaut ``min(cout naturel gele, 2^(i-1))`` par phase : negligeable au jouet
    (une seule technique straight-line), reel a l'echelle du papier (une masse
    de variants).  Le modele ne gele pas les theoremes intermediaires
    (limitation documentee).

    La dynamique est exacte (choix de methode n. 5) : chaque technique est
    executee une fois sans borne pour mesurer ``s_feu`` et ``s_nat`` ; en phase
    ``i`` le travail facture est ``min(s_nat, budget)`` et le feu survient des
    que le budget couvre ``s_feu``.
    """
    space = enumerate_techniques(table, l_max)
    memo: Dict[Tuple[int, ...], RunOutcome] = {}
    for w, _c in space:
        memo[w] = run_technique(w, world, table, budget=None)

    total = 0
    first_fire: Optional[Tuple[int, Tuple[int, ...], int, RunOutcome]] = None
    bogus_fires = 0
    firing = [w for w, o in memo.items() if o.fired]
    for w in firing:
        if memo[w].bogus_used:
            bogus_fires += 1

    order: List[Tuple[int, ...]] = [w for w, _c in space]

    def phase_budget(i: int, c: int) -> int:
        """Budget de phase i pour une technique de cout c (0 si ineligible)."""
        return (1 << (i - c)) if i >= c else 0

    for i in range(1, i_max + 1):
        if frozen is not None and frozen in memo:
            c_f = technique_cost(frozen, table)
            b_f = 1 << (i - 1)  # la moitie du budget de phase 2^i
            out_f = memo[frozen]
            charge_f = min(out_f.natural_cost, b_f)
            if out_f.fired and first_fire is None and b_f >= (out_f.fire_cost or 0):
                first_fire = (i, frozen, c_f, out_f)
                total += charge_f
                break
            total += charge_f
        for w in order:
            c = technique_cost(w, table)
            budget = phase_budget(i, c)
            if budget <= 0:
                continue
            if frozen is not None and w == frozen:
                continue  # deja facturee en tete, a grand budget
            out = memo[w]
            if out.fired and first_fire is None and out.fire_cost is not None:
                if budget >= out.fire_cost:
                    first_fire = (i, w, c, out)
            # travail facture dans cette phase pour cette technique
            total += min(out.natural_cost, budget)
            if first_fire is not None:
                # le feu arrive au moment ou la technique gagnante est executee
                # dans CETTE phase : on arrete l'accumulation apres elle.
                if w == first_fire[1]:
                    break
        if first_fire is not None:
            break

    if first_fire is None:
        return BIOPSResult(
            fired=False, technique=None, code_cost=None, phase=None,
            total_steps=total, fire_steps=None, margin=None, switchprog=None,
            techniques_run=len(space), firing_techniques=len(firing),
            bogus_fires=bogus_fires, i_max=i_max,
            mode="oops" if frozen is not None else "fresh", label=label,
        )
    i, w, c, out = first_fire
    return BIOPSResult(
        fired=True, technique=w, code_cost=c, phase=i, total_steps=total,
        fire_steps=out.fire_cost, margin=out.margin, switchprog=out.switchprog,
        techniques_run=len(space), firing_techniques=len(firing),
        bogus_fires=bogus_fires, i_max=i_max,
        mode="oops" if frozen is not None else "fresh", label=label,
    )


# ---------------------------------------------------------------------------
# Gates de haut niveau (G1-G4 + OOPS) -- consommes par le carnet et les tests
# ---------------------------------------------------------------------------

# La technique du levier : GETAX(world), RULE(SIM), SETSW(nomine), RULE(CMP), CHECK.
W_LEVER: Tuple[int, ...] = (0, 1, 5, 1, 2)


def g1_lever() -> Dict[str, object]:
    """Gate G1 -- le levier du paragraphe 4.4 : preuve, feu, marge = gain realise."""
    world = LeverWorld(label="A")
    res = biops(world, i_max=40)
    mode, setups = world.initial_state()
    u_keep = world.simulate("keep", world.t1, mode, setups)
    u_lever = world.simulate("lever", world.t1, mode, setups)
    realized = u_lever - u_keep  # monde deterministe : prouve == realise
    return {
        "biops": res,
        "u_keep": u_keep,
        "u_lever": u_lever,
        "proven_margin": res.margin,
        "realized_gain": realized,
        "margin_equals_gain": res.margin == realized,
        "switchprog": res.switchprog,
        "phase": res.phase,
    }


def g2_bogus_exhaustive() -> Dict[str, object]:
    """Gate G2 -- FAQ 7 : le reecrivain d'utilite ne passe jamais, exhaustive."""
    world = LeverWorld(label="A")
    res = biops(world, i_max=40)
    # La technique concue pour tricher : BOGUS puis le squelette normal.
    # BOGUS injecte un u non prouve ; SETSW/CHECK l'ignorent.
    w_bogus = (3, 0, 1, 5, 2)  # BOGUS, GETAX, RULE, SETSW, CHECK
    out_bogus = run_technique(w_bogus, world, DEFAULT_TABLE, budget=None)
    # Variante maximale : meme a budget infini, aucune technique contenant
    # BOGUS ne peut feuter en citant le faux u.
    cheats = [
        w
        for w, o in (
            (w, run_technique(w, world, DEFAULT_TABLE, budget=None))
            for w, _c in enumerate_techniques()
        )
        if 3 in w and o.fired and o.bogus_used
    ]
    return {
        "biops": res,
        "bogus_fires_in_biops": res.bogus_fires,
        "w_bogus_fires": out_bogus.fired,
        "w_bogus_outcome": out_bogus.outcome,
        "techniques_with_bogus_that_fire": len(cheats),
        "space_size": len(enumerate_techniques()),
    }


def g3_th51_cost_scaling() -> Dict[str, object]:
    """Gate G3 -- Theoreme 5.1 : meme technique, deux encodages, Delta c = 8.

    Prediction du Theoreme 5.1 : la technique est trouvee quand son budget
    ``2^i * P(w)`` couvre son cout de feu ; chaque bit de code de plus double
    l'attente -- l'ecart de phases vaut EXACTEMENT ``Delta c`` et le travail
    total echelle en ``1/P(w) = 2^c`` pour des techniques qui consomment leur
    budget.  Nuance honnete mesuree ici : les techniques du jouet sont
    straight-line (sans boucle) -- elles terminent avant d'epuiser leur budget,
    donc le travail par phase sature a ``somme des couts naturels`` et le
    rapport de travail mesure croit ~lineairement avec le nombre de phases, pas
    exponentiellement.  La loi ``1/P(w)`` se lit donc sans biais sur l'ecart de
    phases (exact), et sur le rapport de travaux sous sa borne ``2^Delta_c``.
    """
    world = LeverWorld(label="A")
    cheap = biops(world, i_max=48, table=DEFAULT_TABLE)
    expensive = biops(world, i_max=48, table=EXPENSIVE_TABLE)
    dc = expensive.code_cost - cheap.code_cost
    ratio = (
        expensive.total_steps / cheap.total_steps if cheap.total_steps else float("inf")
    )
    return {
        "cheap": cheap,
        "expensive": expensive,
        "delta_cost": dc,
        "phase_gap": (expensive.phase or 0) - (cheap.phase or 0),
        "work_ratio": ratio,
        "predicted_ratio_bound": float(1 << dc) if dc else 1.0,
        "saturation": "straight-line: le travail par phase plafonne aux couts naturels",
    }


def g4_greedy_global() -> Dict[str, object]:
    """Gate G4 -- Theoreme 4.1 : argmax sur tous les candidats + pas de second switch."""
    world = LeverWorld(label="A")
    res = biops(world, i_max=40)
    mode, setups = world.initial_state()
    # Tous les candidats futurs (tau, politique) : u realise depuis t1.
    candidates = []
    for pol in POLICIES:
        u = world.simulate(pol, world.t1, mode, setups)
        candidates.append((pol, u))
    best_pol, best_u = max(candidates, key=lambda pu: pu[1])
    # Le switch feutre doit etre l'argmax strict parmi les candidats.
    is_argmax = res.switchprog == best_pol and res.margin == best_u
    # Continuation : le monde avance jusqu'a la fin du setup du levier
    # (cycles 5..t1+k sous 'lever', mode ready a partir de t1+k+1... en fait
    # pret des la fin du cycle t1+k). Etat explicite : (ready, k).
    t_post = world.t1 + world.k
    after = LeverWorld(
        T=world.T,
        k=world.k,
        t1=t_post,
        current_policy="lever",
        label="A-post",
        state_at_t1=("ready", world.k),
    )
    res_after = biops(after, i_max=40)
    return {
        "biops": res,
        "candidates": candidates,
        "best": (best_pol, best_u),
        "fired_is_argmax": is_argmax,
        "continuation_world": after,
        "second_switch_fires": res_after.fired,
    }


def oops_reuse() -> Dict[str, object]:
    """OOPS (paragraphe 5.2) : la technique gelee transferee en tete sur une variante."""
    world_a = LeverWorld(label="A")
    frozen = W_LEVER
    # Variante B : k = 3 (trois setups requis). La technique gelee s'applique
    # telle quelle : GETAX recupere l'axiome du monde B, SIM simule k = 3.
    world_b = LeverWorld(k=3, label="B")
    fresh = biops(world_b, i_max=40)
    with_frozen = biops(world_b, i_max=40, frozen=frozen)
    mode_b, setups_b = world_b.initial_state()
    u_b = world_b.simulate("lever", world_b.t1, mode_b, setups_b)
    return {
        "fresh": fresh,
        "with_frozen": with_frozen,
        "speedup": fresh.total_steps / with_frozen.total_steps
        if with_frozen.total_steps
        else float("inf"),
        "margin_b": with_frozen.margin if with_frozen.fired else None,
        "expected_margin_b": u_b,
        "transfers": with_frozen.fired and with_frozen.margin == u_b,
    }


def short_technique_long_proof() -> Dict[str, object]:
    """Mesure pour l'argument central : technique courte, preuve longue.

    Le compte de preuve = applications de regles facturees par la technique
    gagnante (SIM : 3 politiques x (T - t1) cycles simules, + CMP + cible).
    Le compte de techniques = espace borne enumere jusqu'au feu.  Une recherche
    de preuve nave par enumeration de chaines de regles devrait balayer un
    espace d'au moins 2^(longueur de preuve) chaines : l'explosion
    combinatoire est dans les preuves, pas dans les techniques.
    """
    world = LeverWorld(label="A")
    res = biops(world, i_max=40)
    proof_steps = world.sim_cost() + 2  # SIM + CMP + cible
    technique_bits = res.code_cost
    proof_space_log2 = proof_steps  # >= 1 bit de choix par etape de preuve
    return {
        "biops": res,
        "technique_symbols": len(res.technique) if res.technique else None,
        "technique_bits": technique_bits,
        "proof_rule_applications": proof_steps,
        "naive_proof_space_log2": proof_space_log2,
        "ratio_log2": proof_space_log2 - (technique_bits or 0),
    }


__all__ = [
    "Instruction",
    "DEFAULT_TABLE",
    "EXPENSIVE_TABLE",
    "HALT_COST",
    "L_MAX",
    "POLICIES",
    "LeverWorld",
    "RunOutcome",
    "BIOPSResult",
    "W_LEVER",
    "technique_cost",
    "enumerate_techniques",
    "run_technique",
    "biops",
    "g1_lever",
    "g2_bogus_exhaustive",
    "g3_th51_cost_scaling",
    "g4_greedy_global",
    "oops_reuse",
    "short_technique_long_proof",
]
