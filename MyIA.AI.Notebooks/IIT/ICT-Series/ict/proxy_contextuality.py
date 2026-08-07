"""Contextualite du zoo de proxys -- section globale ou obstruction (ICT #7290).

Le probleme
-----------
La synthese cross-substrat de la serie a falsifie le *scalaire universel* :
deux proxys de l'integration se suivent (Phi, F : tau = +1.00) quand un
troisieme diverge (K). Le constat courant s'arrete a « les proxys sont en
desaccord » -- un enonce **statistique**.

Ce module pose la question strictement plus forte, celle de Kochen-Specker :
**existe-t-il seulement une assignation de valeurs independante du
contexte ?** Si les proxys mesures dans des contextes differents (fenetres,
coarse-grainings, regimes de perturbation) n'admettent *aucune* assignation
globale coherente, le desaccord n'est pas un bruit a moyenner : c'est une
**obstruction de structure**.

Le cadre n'est pas invente ici. Le depot le nomme deja
(``docs/ict/synthese-invariants-dissociations-obstructions.md``) : lecture
faisceautique d'**Abramsky-Brandenburger**, ou la contextualite se pose « en
probleme de contraintes ou la section se recolle (SAT) ou se refuse (UNSAT) ».
Formellement, un *modele empirique* est une famille de distributions sur des
contextes de mesure ; sa version **possibiliste** ne retient que les supports,
et la question « une section globale existe-t-elle ? » devient litteralement un
CSP a contraintes extensionnelles (tables de tuples autorises).

Les trois crans d'Abramsky-Brandenburger
----------------------------------------
La hierarchie importe, parce qu'elle est ce qui empeche un verdict SAT d'etre
une impasse :

1. **Fortement contextuel** -- aucune section globale. C'est le cran de
   Kochen-Specker. Verdict :data:`STRONGLY_CONTEXTUAL`.
2. **Logiquement contextuel** -- des sections globales existent, mais au moins
   une section *locale* effectivement observee ne s'etend a aucune d'elles.
   L'obstruction est partielle : elle porte sur un evenement, pas sur le
   modele entier. Verdict :data:`LOGICALLY_CONTEXTUAL`.
3. **Non contextuel** -- toute section locale observee s'etend globalement.
   Verdict :data:`NON_CONTEXTUAL`. C'est le NON-resultat, et il est publiable
   tel quel : il clot la piste KS proprement.

Un SAT brut ne dit donc que « pas *fortement* contextuel ». Repondre « le zoo
est non-contextuel » exige le cran 2 en plus -- c'est
:func:`logical_contextuality` qui le tranche.

Les trois degenerescences (le garde-fou anti-analogie-decorative)
----------------------------------------------------------------
Le risque nomme par l'issue #7290 est « l'analogie decorative ». Trois
degenerescences rendent le test vide, et le module refuse de rendre un verdict
de contextualite dans ces cas :

* **Recouvrement total** (:data:`DEGENERATE_SINGLE_COVER`) -- si tous les
  contextes co-mesurent *le meme* ensemble de proxys, le recouvrement est
  trivial : la question « une section globale existe-t-elle ? » se reduit a
  « l'intersection des supports est-elle non vide ? ». C'est une question
  d'**accord entre protocoles**, pas de contextualite : la contextualite exige
  des contextes qui se recouvrent *partiellement* (A={p,q}, B={q,r}, C={r,p}),
  car c'est ce chevauchement partiel qui fait qu'une valeur assignee dans un
  contexte contraint un autre contexte sans etre determinee par lui. C'est la
  degenerescence que le zoo ICT exhibe aujourd'hui (voir la section « Portee
  du resultat » ci-dessous).
* **Aucun recouvrement** (:data:`DEGENERATE_NO_OVERLAP`) -- symetrique du
  precedent, a l'autre extreme : si aucun proxy n'apparait dans deux contextes,
  les contextes sont independants et une assignation globale existe *par
  construction* (on choisit chaque contexte separement). Un « SAT » n'y mesure
  rien.
* **Supports rigides** (:data:`DEGENERATE_RIGID`) -- si chaque contexte n'a
  qu'un seul tuple dans son support (une seule mesure, aucune variabilite),
  alors UNSAT signifie seulement « un proxy a change de valeur d'un contexte a
  l'autre ». C'est un constat de dissociation deja acquis (regime 2 de la
  grille #7399), pas une obstruction. La force de KS est qu'aucune assignation
  ne marche *alors que chaque contexte laisse localement plusieurs choix* : il
  faut donc des supports non triviaux, obtenus en mesurant chaque contexte sur
  plusieurs graines.

C'est la meme lecon qu'ICT-15d, ou la cochaine de Cech rendait ``TRIVIAL``
parce que les sections etaient colineaires *par construction* (rang 1) : un
verdict n'a de valeur que si sa negation etait atteignable.

Portee du resultat sur le zoo ICT (mesure, 2026-08)
---------------------------------------------------
Applique aux proxys de la serie, le diagnostic rend
:data:`DEGENERATE_SINGLE_COVER`, et la raison est **structurelle, pas
contingente** : les trois proxys du zoo (``spectral_gap``,
``sensitivity_mean``, ``sensitivity_max``) partagent la meme signature
``(states, n_symbols)``. Rien n'empeche de les calculer tous les trois sur la
meme trajectoire, dans le meme pretraitement -- ils sont **conjointement
mesurables**. Or c'est exactement la *non*-co-mesurabilite (la
non-commutativite, chez KS) qui cree les contextes distincts et rend la
contextualite possible.

Conclusion honnete : l'analogie Kochen-Specker ne meurt pas d'un SAT, elle
meurt **un cran plus tot**, faute de recouvrement non trivial. Le zoo ICT
n'est pas « non contextuel » ; la question de sa contextualite n'est pas encore
*posable*. L'ingredient manquant est identifie et unique : une structure de
co-mesurabilite **partielle et justifiee** -- deux proxys dont les
pretraitements sont genuinement incompatibles, de sorte qu'aucun protocole ne
les livre ensemble. Tant qu'elle n'est pas etablie, tout hypergraphe
proxys x contextes serait une decoration.

Le module est donc livre avec son detecteur valide (fixtures a
insatisfiabilite prouvee a la main) et son garde-fou : le jour ou une telle
structure est justifiee, le test se pose sans reecriture.

Ce que ce module n'est pas
--------------------------
* Ce n'est pas :mod:`ict.meta_proxy` (#7395), qui mesure la **dispersion
  numerique** des desaccords (verdicts ``STABLE`` / ``NOISE``).
* Ce n'est pas :mod:`ict.cech_obstruction` (#7744), qui calcule une
  **holonomie intra-substrat** (cobord, cocycle).
  Ici la question est **combinatoire** et son verdict est binaire : la section
  se recolle, ou elle ne se recolle pas.

Points de rupture avec le cas quantique (honnetete de l'analogie)
-----------------------------------------------------------------
1. **Origine des contraintes.** Chez KS elles viennent de l'algebre
   (orthogonalite, relations fonctionnelles) : *a priori* et exactes. Ici
   elles viennent de mesures : un UNSAT peut etre un artefact
   d'echantillonnage. D'ou l'exigence de supports mesures sur plusieurs
   graines, et le report explicite du protocole.
2. **Identite des observables.** En mecanique quantique, « le meme
   observable » dans deux contextes est *le meme operateur*, par definition.
   Ici, un proxy mesure sous deux fenetres n'est pas garanti etre la meme
   grandeur : l'identite cross-contexte est une **hypothese**, la plus forte
   du transfert.
3. **Pas de theoreme de dimension.** KS exige dim >= 3 et des configurations
   de rayons precises ; rien de tel ne contraint le zoo. L'absence
   d'obstruction ici n'a donc aucune portee sur KS, et reciproquement.
4. **Discretisation.** Les proxys sont des reels ; les rendre des issues
   discretes est un **choix** (seuils), pas une donnee. Le verdict doit etre
   reporte avec sa sensibilite a ce choix.

Numpy n'est meme pas requis (combinatoire pure). Le solveur CP-SAT d'OR-Tools
est utilise quand il est disponible -- ``AddAllowedAssignments`` code
exactement une contrainte de support -- et le module croise systematiquement
son verdict avec une enumeration exhaustive deterministe sur les instances
assez petites. Le verdict SAT/UNSAT est deterministe meme si le *temoin*
choisi par CP-SAT ne l'est pas (cf. la lecon du gate de determinisme du
depot) : on ne rapporte donc jamais un temoin CP-SAT sans le canonicaliser
par l'enumeration.
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass
from typing import Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

# --------------------------------------------------------------------------- #
#  Verdicts                                                                    #
# --------------------------------------------------------------------------- #
STRONGLY_CONTEXTUAL = "strongly_contextual"
LOGICALLY_CONTEXTUAL = "logically_contextual"
NON_CONTEXTUAL = "non_contextual"
DEGENERATE_SINGLE_COVER = "degenerate_single_cover"
DEGENERATE_NO_OVERLAP = "degenerate_no_overlap"
DEGENERATE_RIGID = "degenerate_rigid"
INCONCLUSIVE_TOO_LARGE = "inconclusive_too_large"

#: Plafond par defaut de l'enumeration exhaustive (nombre d'assignations
#: candidates). Au-dela, l'enumeration rend ``INCONCLUSIVE_TOO_LARGE`` plutot
#: que de tourner sans borne -- une cible trop grande est un fait a rapporter,
#: pas un silence.
DEFAULT_MAX_SEARCH = 1 << 22


@dataclass(frozen=True)
class Context:
    """Un contexte de mesure : des proxys co-mesures, et le support observe.

    ``proxies`` est le tuple (ordonne) des proxys co-mesurables dans ce
    protocole. ``support`` est l'ensemble des tuples d'issues effectivement
    observes, chacun de meme arite que ``proxies`` -- c'est le support de la
    distribution empirique du contexte, au sens d'Abramsky-Brandenburger.

    Un support **vide** est une erreur, jamais un contexte « sans contrainte » :
    un contexte qu'on n'a pas mesure ne doit pas se faire passer pour un
    contexte permissif (meme raison d'etre que les classes ``EMPTY_*`` du
    depot -- une cible non regardee ne rend pas un rapport propre).
    """

    proxies: Tuple[str, ...]
    support: Tuple[Tuple[int, ...], ...]

    def __post_init__(self) -> None:
        if not self.proxies:
            raise ValueError("un contexte doit porter au moins un proxy")
        if len(set(self.proxies)) != len(self.proxies):
            raise ValueError(f"proxys dupliques dans un contexte : {self.proxies}")
        if not self.support:
            raise ValueError(
                f"support vide pour le contexte {self.proxies} : un contexte non "
                "mesure n'est pas un contexte sans contrainte"
            )
        arity = len(self.proxies)
        for tup in self.support:
            if len(tup) != arity:
                raise ValueError(
                    f"tuple {tup} d'arite {len(tup)} dans un contexte d'arite {arity}"
                )

    def restrict(self, assignment: Mapping[str, int]) -> Tuple[int, ...]:
        """Restriction d'une assignation globale a ce contexte."""
        return tuple(assignment[p] for p in self.proxies)

    def admits(self, assignment: Mapping[str, int]) -> bool:
        """``True`` si la restriction de ``assignment`` tombe dans le support."""
        return self.restrict(assignment) in set(self.support)


@dataclass(frozen=True)
class EmpiricalModel:
    """Famille de contextes sur un alphabet d'issues commun.

    C'est le modele empirique possibiliste : on ne retient des distributions
    que leurs supports, ce qui suffit aux crans 1 et 2 de la hierarchie.
    """

    contexts: Tuple[Context, ...]
    outcomes: Tuple[int, ...]

    @property
    def measurements(self) -> Tuple[str, ...]:
        """Tous les proxys du modele, ordonnes (deterministe)."""
        seen: List[str] = []
        for ctx in self.contexts:
            for p in ctx.proxies:
                if p not in seen:
                    seen.append(p)
        return tuple(sorted(seen))

    @property
    def search_space(self) -> int:
        """Nombre d'assignations globales candidates."""
        return len(self.outcomes) ** len(self.measurements)


def empirical_model(
    contexts: Iterable[Mapping[str, object] | Context],
    outcomes: Optional[Sequence[int]] = None,
) -> EmpiricalModel:
    """Construit un :class:`EmpiricalModel` valide.

    ``contexts`` accepte des :class:`Context` ou des mappings
    ``{"proxies": [...], "support": [...]}``. ``outcomes`` par defaut est
    l'ensemble des issues apparaissant dans les supports.

    Valide que chaque issue de chaque support appartient bien a l'alphabet :
    une issue hors alphabet est une erreur de construction, pas une issue
    silencieusement ignoree.
    """
    built: List[Context] = []
    for c in contexts:
        if isinstance(c, Context):
            built.append(c)
        else:
            built.append(
                Context(
                    proxies=tuple(str(p) for p in c["proxies"]),  # type: ignore[index]
                    support=tuple(
                        tuple(int(v) for v in tup)
                        for tup in c["support"]  # type: ignore[index]
                    ),
                )
            )
    if not built:
        raise ValueError("un modele empirique doit contenir au moins un contexte")

    observed = sorted({v for ctx in built for tup in ctx.support for v in tup})
    alphabet = tuple(int(o) for o in outcomes) if outcomes is not None else tuple(observed)
    if len(alphabet) < 2:
        raise ValueError(
            f"alphabet d'issues trivial ({alphabet}) : avec une seule issue "
            "possible, toute assignation est forcee et la question est vide"
        )
    unknown = set(observed) - set(alphabet)
    if unknown:
        raise ValueError(f"issues hors alphabet {alphabet} dans les supports : {sorted(unknown)}")

    return EmpiricalModel(contexts=tuple(built), outcomes=alphabet)


# --------------------------------------------------------------------------- #
#  1. Degenerescences : le test est-il seulement capable de trancher ?          #
# --------------------------------------------------------------------------- #
def overlap_report(model: EmpiricalModel) -> Dict[str, object]:
    """Diagnostique la structure de recouvrement AVANT tout verdict.

    Un test dont la reponse est forcee par la construction ne mesure rien.
    Cette fonction rend explicite laquelle des deux degenerescences s'applique
    (cf. docstring du module) :

    * ``degenerate_no_overlap`` : aucun proxy n'est partage par deux contextes
      -- SAT est force, un verdict « non contextuel » serait vide.
    * ``degenerate_rigid`` : tous les supports sont des singletons -- UNSAT
      serait un simple constat de dissociation, pas une obstruction.

    Les deux peuvent etre vraies simultanement ; ``degeneracy`` retient alors
    l'absence de recouvrement, qui est la plus forte (elle force le verdict).
    """
    multiplicity: Dict[str, int] = {}
    for ctx in model.contexts:
        for p in ctx.proxies:
            multiplicity[p] = multiplicity.get(p, 0) + 1
    shared = sorted(p for p, n in multiplicity.items() if n >= 2)

    support_sizes = [len(ctx.support) for ctx in model.contexts]
    all_singletons = all(s == 1 for s in support_sizes)

    distinct_covers = {frozenset(ctx.proxies) for ctx in model.contexts}

    degeneracy: Optional[str] = None
    reason = ""
    if len(distinct_covers) == 1:
        degeneracy = DEGENERATE_SINGLE_COVER
        reason = (
            "tous les contextes co-mesurent le meme ensemble de proxys : le "
            "recouvrement est trivial et la question se reduit a "
            "« l'intersection des supports est-elle non vide ? » (accord entre "
            "protocoles). La contextualite exige un recouvrement PARTIEL "
            "(A={p,q}, B={q,r}, C={r,p}), donc des proxys non conjointement "
            "mesurables"
        )
    elif not shared:
        degeneracy = DEGENERATE_NO_OVERLAP
        reason = (
            "aucun proxy n'est co-mesure dans deux contextes : les contextes "
            "sont independants, une section globale existe par construction"
        )
    elif all_singletons:
        degeneracy = DEGENERATE_RIGID
        reason = (
            "tous les supports sont des singletons : un UNSAT signifierait "
            "seulement qu'un proxy change de valeur d'un contexte a l'autre "
            "(dissociation, regime 2), pas une obstruction de structure"
        )

    return {
        "context_multiplicity": dict(sorted(multiplicity.items())),
        "shared_proxies": shared,
        "n_shared_proxies": len(shared),
        "n_distinct_covers": len(distinct_covers),
        "support_sizes": support_sizes,
        "min_support_size": min(support_sizes),
        "max_support_size": max(support_sizes),
        "degeneracy": degeneracy,
        "degeneracy_reason": reason,
        "search_space": model.search_space,
    }


# --------------------------------------------------------------------------- #
#  2. Sections globales : enumeration exhaustive (oracle deterministe)          #
# --------------------------------------------------------------------------- #
def global_sections(
    model: EmpiricalModel,
    *,
    max_search: int = DEFAULT_MAX_SEARCH,
    limit: Optional[int] = None,
) -> List[Dict[str, int]]:
    """Enumere les sections globales, exhaustivement et deterministiquement.

    Une *section globale* est une assignation ``proxy -> issue`` dont la
    restriction a chaque contexte tombe dans le support de ce contexte. La
    liste rendue est ordonnee de facon reproductible (ordre lexicographique
    des issues sur les proxys tries) : c'est l'oracle qui canonicalise les
    temoins de CP-SAT.

    Leve :class:`OverflowError` si l'espace de recherche depasse
    ``max_search`` -- une cible trop grande doit etre rapportee, pas
    silencieusement tronquee.
    """
    if model.search_space > max_search:
        raise OverflowError(
            f"espace de recherche {model.search_space} > max_search {max_search}"
        )
    proxies = model.measurements
    position = {p: i for i, p in enumerate(proxies)}
    # Supports pre-calcules une seule fois (les reconstruire dans la boucle
    # dominerait le cout de l'enumeration).
    constraints = [
        (tuple(position[p] for p in ctx.proxies), frozenset(ctx.support))
        for ctx in model.contexts
    ]
    found: List[Dict[str, int]] = []
    for combo in itertools.product(model.outcomes, repeat=len(proxies)):
        if all(tuple(combo[i] for i in idx) in sup for idx, sup in constraints):
            found.append(dict(zip(proxies, combo)))
            if limit is not None and len(found) >= limit:
                break
    return found


def global_sections_cpsat(model: EmpiricalModel) -> Dict[str, object]:
    """Meme question, posee au solveur CP-SAT (outillage CSP du depot).

    Chaque contexte devient une contrainte extensionnelle
    ``AddAllowedAssignments`` : c'est *exactement* la definition d'un support,
    sans encodage intermediaire. Rend ``{"available": False}`` si OR-Tools est
    absent -- l'appelant garde alors l'oracle exhaustif, aucun resultat n'est
    fabrique.

    Ne rend **jamais** de temoin : la solution exhibee par CP-SAT n'est pas
    deterministe d'un run a l'autre. Seul le statut SAT/UNSAT l'est, et c'est
    lui seul qui est rapporte.
    """
    try:
        from ortools.sat.python import cp_model
    except ImportError:
        return {"available": False, "satisfiable": None}

    proxies = model.measurements
    index = {p: i for i, p in enumerate(proxies)}
    lo, hi = min(model.outcomes), max(model.outcomes)

    m = cp_model.CpModel()
    vars_ = [m.NewIntVar(lo, hi, f"v_{p}") for p in proxies]
    # L'alphabet peut etre non contigu : restreindre explicitement.
    allowed_values = set(model.outcomes)
    if allowed_values != set(range(lo, hi + 1)):
        for v in vars_:
            m.AddAllowedAssignments([v], [(o,) for o in model.outcomes])

    for ctx in model.contexts:
        m.AddAllowedAssignments(
            [vars_[index[p]] for p in ctx.proxies],
            [tuple(int(x) for x in tup) for tup in ctx.support],
        )

    solver = cp_model.CpSolver()
    solver.parameters.num_search_workers = 1
    status = solver.Solve(m)
    satisfiable = status in (cp_model.OPTIMAL, cp_model.FEASIBLE)
    return {
        "available": True,
        "satisfiable": bool(satisfiable),
        "status_name": solver.StatusName(status),
    }


# --------------------------------------------------------------------------- #
#  3. Cran 2 : contextualite logique (une section locale sans extension)        #
# --------------------------------------------------------------------------- #
def logical_contextuality(
    model: EmpiricalModel, *, max_search: int = DEFAULT_MAX_SEARCH
) -> Dict[str, object]:
    """Cherche les sections locales observees qui ne s'etendent pas globalement.

    C'est le cran 2 de la hierarchie : le modele peut admettre des sections
    globales (donc n'etre pas *fortement* contextuel) tout en contenant un
    evenement local observe qu'aucune section globale ne realise. L'obstruction
    est alors localisee sur cet evenement.

    C'est ce qui empeche un SAT d'etre une impasse : « pas fortement
    contextuel » n'autorise pas a conclure « non contextuel ».
    """
    sections = global_sections(model, max_search=max_search)
    witnesses: List[Dict[str, object]] = []
    n_local = 0
    for ci, ctx in enumerate(model.contexts):
        for tup in ctx.support:
            n_local += 1
            extends = any(ctx.restrict(s) == tup for s in sections)
            if not extends:
                witnesses.append(
                    {"context_index": ci, "proxies": list(ctx.proxies), "outcome": list(tup)}
                )
    return {
        "n_global_sections": len(sections),
        "n_local_sections": n_local,
        "n_without_extension": len(witnesses),
        "logically_contextual": bool(sections) and bool(witnesses),
        "witnesses": witnesses,
    }


# --------------------------------------------------------------------------- #
#  4. Caracterisation minimale de l'obstruction                                 #
# --------------------------------------------------------------------------- #
def minimal_obstruction(
    model: EmpiricalModel, *, max_search: int = DEFAULT_MAX_SEARCH
) -> Optional[Tuple[int, ...]]:
    """Plus petite sous-famille de contextes deja insatisfiable (par deletion).

    L'issue #7290 demande, en cas d'obstruction, de la « caracteriser
    minimalement ». On retire les contextes un a un tant que l'insatisfiabilite
    survit : le resultat est une sous-famille **irreductible** (retirer
    n'importe lequel de ses contextes la rend satisfiable), ce qui identifie
    *quels protocoles de mesure* portent le conflit.

    Rend ``None`` si le modele complet est satisfiable. Deterministe :
    l'ordre de deletion est l'ordre des contextes.
    """
    if global_sections(model, max_search=max_search, limit=1):
        return None

    keep = list(range(len(model.contexts)))
    changed = True
    while changed:
        changed = False
        for ci in list(keep):
            if len(keep) == 1:
                break
            trial = [i for i in keep if i != ci]
            sub = EmpiricalModel(
                contexts=tuple(model.contexts[i] for i in trial), outcomes=model.outcomes
            )
            if not global_sections(sub, max_search=max_search, limit=1):
                keep = trial
                changed = True
    return tuple(keep)


# --------------------------------------------------------------------------- #
#  5. Verdict                                                                   #
# --------------------------------------------------------------------------- #
def contextuality_verdict(
    model: EmpiricalModel,
    *,
    max_search: int = DEFAULT_MAX_SEARCH,
    cross_check: bool = True,
) -> Dict[str, object]:
    """Verdict complet : degenerescence, puis cran de la hierarchie.

    L'ordre est deliberement celui-ci : **la degenerescence est examinee
    avant** toute affirmation de contextualite. Un modele degenere ne recoit
    jamais ``NON_CONTEXTUAL`` ni ``STRONGLY_CONTEXTUAL`` : il recoit son
    verdict de degenerescence, qui dit que le test n'etait pas capable de
    trancher. C'est le garde-fou anti-analogie-decorative.

    Si ``cross_check`` et OR-Tools present, le statut CP-SAT est compare a
    l'oracle exhaustif ; un desaccord leve :class:`RuntimeError` (c'est un bug,
    jamais un resultat).
    """
    report = overlap_report(model)
    out: Dict[str, object] = {"overlap": report}

    too_large = model.search_space > max_search
    sat_exhaustive: Optional[bool] = None
    if not too_large:
        sat_exhaustive = bool(global_sections(model, max_search=max_search, limit=1))

    cp = global_sections_cpsat(model) if cross_check else {"available": False}
    out["cpsat"] = cp
    if cp.get("available") and sat_exhaustive is not None:
        if bool(cp["satisfiable"]) != sat_exhaustive:
            raise RuntimeError(
                "desaccord CP-SAT / enumeration exhaustive "
                f"({cp['satisfiable']} vs {sat_exhaustive}) : bug d'encodage, "
                "pas un resultat"
            )

    satisfiable = sat_exhaustive if sat_exhaustive is not None else cp.get("satisfiable")
    out["satisfiable"] = satisfiable

    if report["degeneracy"] is not None:
        out["verdict"] = report["degeneracy"]
        out["rationale"] = report["degeneracy_reason"]
        return out

    if satisfiable is None:
        out["verdict"] = INCONCLUSIVE_TOO_LARGE
        out["rationale"] = (
            f"espace de recherche {model.search_space} > max_search {max_search} "
            "et CP-SAT indisponible"
        )
        return out

    if not satisfiable:
        out["verdict"] = STRONGLY_CONTEXTUAL
        out["rationale"] = (
            "aucune assignation globale ne se restreint dans le support de tous "
            "les contextes : obstruction au recollement (cran KS)"
        )
        if not too_large:
            out["minimal_obstruction"] = minimal_obstruction(model, max_search=max_search)
        return out

    if too_large:
        out["verdict"] = INCONCLUSIVE_TOO_LARGE
        out["rationale"] = (
            "CP-SAT rend SAT mais l'espace de recherche interdit l'examen du "
            "cran 2 (contextualite logique) : verdict incomplet"
        )
        return out

    logical = logical_contextuality(model, max_search=max_search)
    out["logical"] = logical
    if logical["logically_contextual"]:
        out["verdict"] = LOGICALLY_CONTEXTUAL
        out["rationale"] = (
            f"{logical['n_without_extension']} section(s) locale(s) observee(s) ne "
            "s'etendent a aucune section globale : obstruction partielle, "
            "localisee sur ces evenements"
        )
    else:
        out["verdict"] = NON_CONTEXTUAL
        out["rationale"] = (
            f"{logical['n_global_sections']} section(s) globale(s), et toute section "
            "locale observee s'etend : le zoo est non contextuel sur ce modele, "
            "l'analogie KS meurt proprement"
        )
    return out


# --------------------------------------------------------------------------- #
#  6. Pont mesures -> modele empirique                                          #
# --------------------------------------------------------------------------- #
def median_split_thresholds(
    signatures: Mapping[str, Sequence[Mapping[str, float]]], proxies: Sequence[str]
) -> Dict[str, float]:
    """Seuils de discretisation : mediane de chaque proxy, toutes mesures confondues.

    La discretisation est un **choix**, pas une donnee (point de rupture 4).
    Ce seuil-la est le moins arbitraire disponible : il est calcule sur
    l'ensemble des mesures, donc il ne privilegie aucun contexte, et il garantit
    que chaque proxy prend effectivement ses deux issues sur l'ensemble du
    corpus (sans quoi le proxy serait constant, donc sans pouvoir discriminant).
    """
    thresholds: Dict[str, float] = {}
    for p in proxies:
        vals = sorted(
            float(run[p]) for runs in signatures.values() for run in runs if p in run
        )
        if not vals:
            raise ValueError(f"aucune mesure pour le proxy {p!r}")
        n = len(vals)
        thresholds[p] = vals[n // 2] if n % 2 else 0.5 * (vals[n // 2 - 1] + vals[n // 2])
    return thresholds


def model_from_signatures(
    signatures: Mapping[str, Sequence[Mapping[str, float]]],
    proxies: Sequence[str],
    *,
    thresholds: Optional[Mapping[str, float]] = None,
) -> Tuple[EmpiricalModel, Dict[str, float]]:
    """Construit le modele empirique depuis des mesures reelles.

    ``signatures`` associe a chaque contexte la liste de ses signatures
    mesurees -- **une par graine**. C'est cette pluralite qui donne au support
    plus d'un element, et donc au test une chance de trancher autrement que
    par rigidite (cf. :data:`DEGENERATE_RIGID`) : mesurer un contexte une seule
    fois rend le test vide, quelle que soit la suite.

    Discretisation binaire par seuil : ``1`` si la valeur est ``>=`` seuil,
    ``0`` sinon. Rend le modele et les seuils effectivement utilises (a
    rapporter avec le verdict, pour que sa sensibilite au choix soit
    verifiable).

    .. warning::
       Ce pont affecte **tous** les proxys a **chaque** contexte, donc le modele
       produit est necessairement :data:`DEGENERATE_SINGLE_COVER`. Ce n'est pas
       une limite d'implementation : c'est le constat mesure sur le zoo ICT
       (proxys conjointement mesurables, cf. « Portee du resultat »). Construire
       un modele a recouvrement partiel exige de *justifier* quels proxys ne
       sont pas conjointement mesurables -- ce que ce pont ne peut pas deviner,
       et ne doit donc pas simuler.
    """
    proxies = tuple(proxies)
    # Valider les contextes AVANT de calculer les seuils : sinon un contexte
    # vide remonte comme "aucune mesure pour le proxy X" (le symptome) au lieu
    # de "contexte X sans aucune mesure" (la cause).
    for name, runs in signatures.items():
        if not runs:
            raise ValueError(f"contexte {name!r} sans aucune mesure")

    thr = dict(thresholds) if thresholds is not None else median_split_thresholds(
        signatures, proxies
    )
    contexts: List[Context] = []
    for name, runs in signatures.items():
        support = {
            tuple(1 if float(run[p]) >= thr[p] else 0 for p in proxies) for run in runs
        }
        contexts.append(Context(proxies=proxies, support=tuple(sorted(support))))
    return empirical_model(contexts, outcomes=(0, 1)), thr


# --------------------------------------------------------------------------- #
#  7. Fixtures de validation : le detecteur detecte-t-il ?                      #
# --------------------------------------------------------------------------- #
def pr_box_model() -> EmpiricalModel:
    """La boite PR (Popescu-Rohrlich) : fortement contextuelle, par parite.

    Quatre observables ``a1, a2, b1, b2``, quatre contextes ``(ai, bj)``,
    issues ``{0, 1}``. Le support impose ``x XOR y = 0`` sauf dans le contexte
    ``(a2, b2)`` ou il impose ``1``.

    L'insatisfiabilite se **prouve a la main**, ce qui en fait un oracle et non
    une croyance : sommer les quatre contraintes donne
    ``2*(a1 + a2 + b1 + b2) = 1 (mod 2)``, dont le membre gauche est pair et le
    droit impair. Aucune assignation globale n'existe. Un detecteur qui rendrait
    SAT ici serait casse.
    """
    xor0 = ((0, 0), (1, 1))
    xor1 = ((0, 1), (1, 0))
    return empirical_model(
        [
            Context(("a1", "b1"), xor0),
            Context(("a1", "b2"), xor0),
            Context(("a2", "b1"), xor0),
            Context(("a2", "b2"), xor1),
        ],
        outcomes=(0, 1),
    )


def logically_but_not_strongly_contextual_model() -> EmpiricalModel:
    """Sections globales existent, mais un evenement observe ne s'etend pas.

    Construction : la boite PR dont on elargit le dernier contexte pour laisser
    passer ``(0, 0)``. Le modele devient satisfiable (``a1=a2=b1=b2=0`` est une
    section globale), mais les tuples ``(0, 1)`` et ``(1, 0)`` du contexte
    ``(a2, b2)`` restent sans extension -- l'obstruction survit, localisee.

    Cette fixture est ce qui rend le cran 2 non decoratif : elle exhibe un
    modele que le seul test SAT declarerait « non contextuel » a tort.
    """
    xor0 = ((0, 0), (1, 1))
    return empirical_model(
        [
            Context(("a1", "b1"), xor0),
            Context(("a1", "b2"), xor0),
            Context(("a2", "b1"), xor0),
            Context(("a2", "b2"), ((0, 0), (0, 1), (1, 0))),
        ],
        outcomes=(0, 1),
    )


def non_contextual_model() -> EmpiricalModel:
    """Modele plein : toute section locale s'etend (le NON-resultat)."""
    full = ((0, 0), (0, 1), (1, 0), (1, 1))
    return empirical_model(
        [
            Context(("a1", "b1"), full),
            Context(("a1", "b2"), full),
            Context(("a2", "b1"), full),
            Context(("a2", "b2"), full),
        ],
        outcomes=(0, 1),
    )


__all__ = [
    "STRONGLY_CONTEXTUAL",
    "LOGICALLY_CONTEXTUAL",
    "NON_CONTEXTUAL",
    "DEGENERATE_SINGLE_COVER",
    "DEGENERATE_NO_OVERLAP",
    "DEGENERATE_RIGID",
    "INCONCLUSIVE_TOO_LARGE",
    "DEFAULT_MAX_SEARCH",
    "Context",
    "EmpiricalModel",
    "empirical_model",
    "overlap_report",
    "global_sections",
    "global_sections_cpsat",
    "logical_contextuality",
    "minimal_obstruction",
    "contextuality_verdict",
    "median_split_thresholds",
    "model_from_signatures",
    "pr_box_model",
    "logically_but_not_strongly_contextual_model",
    "non_contextual_model",
]
