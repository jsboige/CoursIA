"""Plan d'echelle du protocole Geometry of Truth v2 (#16760, arbitrage ai-01 13:48Z + amendement 13:53Z).

Le Concern user du 2026-09-25 reprochait au notebook ICT-44 un protocole
delibrement sous-regime (1.5B). Le protocole v2 monte l'echelle
SYSTEMATIQUEMENT jusqu'a 70B (amendement user relaye par ai-01 13:53Z --
ce n'est plus une option soumise a arbitrage) :

* R1-R3 : 2B -> 9B -> 27B au sein de la generation Qwen3.5 (une seule variable
  d'echelle), les trois rungs SAE-couverts par la collection Qwen-Scope ;
* R4 : ``ukisai/Swift-1.5-Qwen3.8-27b-W4A16-AWQ`` -- dense 27B de generation
  Qwen3.8, deja quantifie AWQ, servi par vLLM sur GPU 0+1 d'ai-01 sous
  l'alias ``qwen3.6-35b-a3b``. Le contraste R3 (27B Qwen3.5) contre R4
  (27B Swift) isole l'effet de GENERATION a taille egale -- l'hypothese
  user : les structures qui n'apparaissaient qu'a 70B dans les generations
  precedentes existent peut-etre deja a 27B en Qwen3.8 ;
* sonde >= 70B : voie (a) d'abord (70B quantifie sur GPU 2 avec debordement
  CPU partiel, tres lent, plage genereuse) ; voie (b) -- requisition GPU 0+1,
  qui coupe le modele servi de la flotte -- en dernier recours seulement,
  fenetre annoncee a l'avance sur le dashboard global.

Couverture outillage par echelon (reponse exigee par l'amendement : ce que
J-Lens et F-Lens font SANS SAE pre-entrainee) :

* SAE : uniquement la ou la collection publie (R1-R3). R4 est un fine-tune
  hors collection, et rien n'est publie au-dessus du plafond 35B-A3B -- fait
  de registre, pas une estimation ;
* J-Lens et F-Lens ne dependent d'AUCUNE SAE pre-entrainee : ils lisent le
  residuel avec les propres poids du modele (unembed + layernorm appliques a
  chaque couche pour J-Lens, factorisation de sous-espaces pour F-Lens). La
  couverture outillage est donc maintenue a TOUS les echelons, R4 et >= 70B
  compris -- c'est le trio (SAE / J-Lens / F-Lens) qui degenere en duo aux
  echelons non couverts, jamais l'inverse.

Ce module est la partie GPU-free du plan (regle d'architecture de la serie :
``ict/`` reste numpy-only, torch est confine dans ``scripts/``) :

* ``BATTERY`` -- batterie d'enonces fixe et deterministe (24 villes, 12 vrai /
  12 faux, format ``cities`` du depot officiel geometry-of-truth), le meme
  pour tous les rungs ;
* ``LADDER`` -- les quatre rungs : R1-R3 derives de
  :data:`ict.sae_scales.QWEN_SCOPE_SCALES` (pas de duplication du registre :
  le rung cite le backbone), R4 declare ex nihilo (hors registre, SAE non
  couverte) ;
* arithmetique de cout (:func:`weights_gib`) et plan par carte
  (:func:`plan_rung`) -- le calcul est explicite et faux par construction tant
  que la mesure n'est pas passee (:mod:`scripts.measure_scale_budget`) ;
* reponse a la sonde >= 70B : :func:`sae_lookup` rend ``None`` pour tout
  backbone hors registre -- la collection Qwen-Scope recensee (#8236,
  extension verifiee sur #17842) culmine a 35B-A3B, donc aucune passe SAE
  n'est possible a un echelon >= 70B tant que Qwen ne publie pas.

Les tailles de modeles du LADDER sont NOMINALES (2/9/27 e9 parametres) :
elles ne servent qu'a l'arithmetique de planification. Le compte reel
(``sum(p.numel())``) est mesure au chargement par le harness et consigne
dans l'artefact -- c'est lui qui fait foi.
"""

from __future__ import annotations

from .sae_scales import QWEN_SCOPE_SCALES

__all__ = [
    "BATTERY",
    "BATTERY_LABELS",
    "LADDER",
    "NOMINAL_PARAMS_E9",
    "MAX_SAE_BACKBONE",
    "weights_gib",
    "sae_lookup",
    "plan_rung",
    "format_plan",
]


# Batterie fixe : 12 vrai / 12 faux, geographie verifiable, format exact du
# dataset cities (Marks & Tegmark 2023, arXiv 2310.06824). Deterministe par
# construction (litteral) -- identique sur toutes les executions et tous les
# rungs, c'est la seule entree temps du budget mesure.
BATTERY_TRUE = (
    "The city of Paris is in France.",
    "The city of Tokyo is in Japan.",
    "The city of Madrid is in Spain.",
    "The city of Rome is in Italy.",
    "The city of Berlin is in Germany.",
    "The city of Ottawa is in Canada.",
    "The city of Canberra is in Australia.",
    "The city of Cairo is in Egypt.",
    "The city of Lima is in Peru.",
    "The city of Oslo is in Norway.",
    "The city of Hanoi is in Vietnam.",
    "The city of Nairobi is in Kenya.",
)
BATTERY_FALSE = (
    "The city of Tokyo is in Poland.",
    "The city of Paris is in Spain.",
    "The city of Madrid is in Italy.",
    "The city of Rome is in Germany.",
    "The city of Berlin is in France.",
    "The city of Ottawa is in Mexico.",
    "The city of Canberra is in Brazil.",
    "The city of Cairo is in Turkey.",
    "The city of Lima is in Argentina.",
    "The city of Oslo is in Sweden.",
    "The city of Hanoi is in Thailand.",
    "The city of Nairobi is in Morocco.",
)
BATTERY = BATTERY_TRUE + BATTERY_FALSE
BATTERY_LABELS = tuple([True] * len(BATTERY_TRUE) + [False] * len(BATTERY_FALSE))

# Tailles nominales (milliards de parametres, marketing) : planification
# uniquement, le compte reel est mesure au chargement.
NOMINAL_PARAMS_E9 = {
    "Qwen/Qwen3.5-2B-Base": 2.0,
    "Qwen/Qwen3.5-9B-Base": 9.0,
    "Qwen/Qwen3.5-27B": 27.0,
}


def _suffix_e9(model: str) -> float:
    """Extrait la taille nominale du suffixe du nom (35B-A3B -> 35.0).

    Insensible a la casse : le nommage HF melange ``27B`` (Qwen) et ``27b``
    (checkpoints quantifies tiers, ex Swift W4A16).
    """
    name = model.split("/")[-1]
    for part in name.split("-"):
        p = part.upper()
        if p.endswith("B") and p[:-1].replace(".", "").isdigit():
            return float(part[:-1])
    return 0.0


def _backbone(model: str) -> dict:
    for scale in QWEN_SCOPE_SCALES:
        if scale["model"] == model:
            return scale
    raise KeyError(f"{model} hors registre Qwen-Scope (cf ict.sae_scales)")


def _registry_entry(model: str) -> dict:
    backbone = _backbone(model)
    variant = next(v for v in backbone["sae_variants"] if v["k"] == 50)
    return {
        "model": model,
        "generation": backbone["generation"],
        "n_layers": backbone["n_layers"],
        "d_model": backbone["d_model"],
        "nominal_params_e9": NOMINAL_PARAMS_E9[model],
        "sae_repo": variant["repo"],
        "d_sae": variant["d_sae"],
        "k": variant["k"],
    }


#: Specs des rungs, dans l'ordre du protocole v2 amendé. R1-R3 cites par
#: backbone registre (SAE reprise du registre, pas dupliquee) ; R4 declare
#: ex nihilo : fine-tune Swift de generation Qwen3.8, hors collection
#: Qwen-Scope, AUCUNE SAE publiee -- n_layers/d_model inconnus du registre,
#: lus au chargement depuis la config du checkpoint (archi hybride).
_LADDER_SPECS: tuple[dict, ...] = (
    {"rung": "R1", "model": "Qwen/Qwen3.5-2B-Base"},
    {"rung": "R2", "model": "Qwen/Qwen3.5-9B-Base"},
    {"rung": "R3", "model": "Qwen/Qwen3.5-27B"},
    {
        "rung": "R4",
        "model": "ukisai/Swift-1.5-Qwen3.8-27b-W4A16-AWQ",
        "nominal_params_e9": 27.0,
        "generation": "Qwen3.8",
        "sae_repo": None,
    },
)


def _ladder_entry(spec: dict) -> dict:
    if "sae_repo" in spec:
        return {
            "n_layers": None, "d_model": None, "d_sae": None, "k": None,
            **spec,
        }
    entry = _registry_entry(spec["model"])
    entry["rung"] = spec["rung"]
    return entry


#: Les quatre rungs du protocole v2 amendé, dans l'ordre croissant de
#: l'echelle (R4 n'est pas plus gros : c'est le contraste generation).
LADDER = tuple(_ladder_entry(s) for s in _LADDER_SPECS)

#: Plus gros backbone SAE-couvert de la collection recensee (reponse a la
#: sonde "passe SAE possible a >= 70B ?" : non, rien de publie au-dessus).
MAX_SAE_BACKBONE = max(
    ({"model": s["model"], "nominal_params_e9": _suffix_e9(s["model"])}
     for s in QWEN_SCOPE_SCALES),
    key=lambda d: d["nominal_params_e9"],
)


def weights_gib(n_params: int, bits: float) -> float:
    """Poids seuls en Gio : n_params * bits/8 / 2**30.

    Arithmetic pure (nb: Gio binaires, pas Go decimaux) -- les overheads
    (embeddings non quantifies, etat KV, activations, SAE) s'ajoutent et ne
    sont mesurables qu'au chargement.
    """
    return n_params * (bits / 8.0) / (1024.0 ** 3)


def sae_lookup(model: str) -> dict | None:
    """Variante L0_50 du backbone si la collection la couvre, sinon None.

    R4 (Swift) et tout echelon >= 70B rendent None : aucune SAE publiee ni
    pour le fine-tune, ni au-dessus de MAX_SAE_BACKBONE -- fait mesurable
    depuis le registre committé, pas une estimation.
    """
    for scale in QWEN_SCOPE_SCALES:
        if scale["model"] == model:
            variant = next(v for v in scale["sae_variants"] if v["k"] == 50)
            return {"model": model, "sae_repo": variant["repo"],
                    "d_sae": variant["d_sae"], "k": variant["k"],
                    "n_layers": scale["n_layers"], "d_model": scale["d_model"],
                    "nominal_params_e9": _suffix_e9(model),
                    "generation": scale["generation"],
                    "rung": None}
    return None


def plan_rung(model: str, card_gib: float, *, two_cards: bool = False,
              cpu_ram_gib: float = 64.0,
              nominal_params_e9: float | None = None) -> dict:
    """Plan arithmetique d'un rung sur une carte (ou deux) : place requise
    par mode, debordement CPU ou bi-carte, disponibilite SAE.

    Modes du harness G1 : ``bf16`` (16 bits, debordement CPU si la carte est
    trop petite -- la metrique reste bf16 integre, convention
    ``extract_sae_fidelity``), ``nf4`` (4.25 bits effectifs : 4 de poids +
    ~0.25 d'echelle par bloc ; cout mesure, lecture NON conforme a la garde
    ``assert_bf16_readout`` -- jamais pour la fidelite SAE) et ``as-is``
    (checkpoint deja quantifie, ex AWQ W4A16 -- meme arithmetique que nf4,
    le checkpoint impose sa propre quantification).

    ``nominal_params_e9`` surcharge la taille deduite du nom : obligatoire
    pour un chemin local (``D:/models/Swift-...``) ou le suffixe nominal
    n'est pas extractible.

    Regles de placement : le bf16 deborde en RAM CPU (jusqu'a ``cpu_ram_gib``,
    au-dela irrealisable) ; le nf4 ne deborde pas (il existe pour tenir SUR
    les GPU) -- sur une seule carte trop petite il est irrealisable, sur deux
    cartes reunies il devient bi-carte.
    """
    entry = sae_lookup(model)
    nominal_e9 = nominal_params_e9
    if nominal_e9 is None:
        nominal_e9 = NOMINAL_PARAMS_E9.get(model)
    if nominal_e9 is None:
        nominal_e9 = _suffix_e9(model)
    n_params = int(nominal_e9 * 1e9)
    bf16 = weights_gib(n_params, 16)
    nf4 = weights_gib(n_params, 4.25)

    if bf16 <= card_gib:
        bf16_placement = "carte unique"
    elif bf16 <= card_gib + cpu_ram_gib:
        bf16_placement = "debordement CPU (device_map=auto)"
    else:
        bf16_placement = "irrealisable sur ce parc"

    if nf4 <= card_gib:
        nf4_placement = "carte unique"
    elif two_cards and nf4 <= 2 * card_gib:
        nf4_placement = "bi-carte"
    else:
        nf4_placement = "irrealisable sur ce parc"

    return {
        "model": model,
        "nominal_params_e9": nominal_e9,
        "n_params_nominal": n_params,
        "sae": {"available": entry is not None,
                "repo": entry["sae_repo"] if entry else None},
        "bf16": {"weights_gib": round(bf16, 2), "placement": bf16_placement},
        "nf4": {"weights_gib": round(nf4, 2), "placement": nf4_placement},
        "card_gib": card_gib,
        "two_cards": two_cards,
        "cpu_ram_gib": cpu_ram_gib,
        "measured": False,  # passe a True uniquement par l'artefact du harness
    }


def format_plan(plans: list[dict]) -> str:
    """Tableau texte compact du plan (note : arithmetique, pas mesure)."""
    lines = [
        "rung  modele                     bf16 Gio  placement nf4            SAE",
        "-" * 96,
    ]
    for p in plans:
        model = p["model"].split("/")[-1]
        lines.append(
            f"     {model:26s} {p['bf16']['weights_gib']:>7.1f}  {p['bf16']['placement'][:24]:24s}"
            f"{p['nf4']['weights_gib']:>5.1f}  {'oui' if p['sae']['available'] else 'NON'}"
        )
    lines.append("-" * 96)
    lines.append(
        f"Plafond SAE de la collection publiee : {MAX_SAE_BACKBONE['model']} "
        f"(rien de couvert au-dessus -- la sonde >= 70B rend SAE: NON)."
    )
    lines.append("Arithmetique nominale -- le compte reel et la VRAM pointe sont mesures par")
    lines.append("scripts/measure_scale_budget.py et consignes dans traces/scale_budget_*.json.")
    return "\n".join(lines)
