"""Capstone strate 5 -- triade d'evenements temporels (Epic #4588, See #7259).

Axe *derivee temporelle* du capstone ICT : la triade fondatrice Phi/F/K est
**statique**. ICT-Synthese-CrossSubstrat (cf Gate 5 irreversibilite) a isole un
axe orthogonal : les **evenements de transition**, pas les niveaux. Ce module
formalise la **triade temporelle** que le capstone teste :

* **beauty event** = saut de compressibilite (``dK/dt``, :mod:`ict.beauty`,
  strand Schmidhuber) -- l'evenement *macro* (grokking, transition de
  structure au cours de l'entrainement).
* **ignition event** = pic persistant de concentration
  (:func:`ict.workspace.ignition_events`, lecture Dehaene) -- l'evenement
  *micro* (un token active durablement un petit sous-ensemble de features).
* **lens-agreement event** = moment ou deux lentilles (SAE / J-Lens)
  co-localisent (:func:`ict.lens_agreement.colocalize_lenses`) -- l'evenement
  *inter-appareils* (un meme texte, deux signatures spatiales).

Hypothese du capstone (issue #7259, decision user 2026-07-18)
-------------------------------------------------------------
Ces trois signatures co-localisent-elles **plus que le hasard** sur les
fixtures 9B-Base (2699 tokens, couche 16) ? Si oui -> un seul evenement latent
("insight" / reorganisation du modele interne) vu par trois lentilles ;
les Phi/F/K statiques sont sous-determines et la jambe temporelle les
complete. Si non -> **dissociation**, tout aussi precieuse, qui reconnecte le
negatif d'ICT-24 (``emergence_gain`` <-> ignition ~17 % creditees) a la
prediction Gate 5 de la synthese : la jambe temporelle discrimine
**orthogonalement** (independante de Phi/F/K).

Ce que ce module fait
---------------------
Etend :func:`ict.workspace.event_colocalization` (deux flux, null par rotation
circulaire, cf PR #7274) au cas **3 flux** :

* :func:`triade_centers` -- orchestre les trois flux par prompt partage (memes
  tokens, memes ``T``) :
  - *beauty* : ``beauty_events`` sur la trajectoire d'etats derivee des
    tokens du prompt (bin par type de token, cf. docstring). Renvoie les
    ``step`` (indices ``[0, T)``) des evenements retenus par le seuil iid.
  - *ignition* : centres de :func:`ignition_events` sur la serie de
    concentration SAE par position.
  - *lens-agreement* : pour chaque paire de flux d'ignition SAE et J-Lens,
    on prend les centres retenus par ``colocalize_lenses`` *du flux
    conjoint* (intersection des deux listes d'ignitions -- un point OU
    les deux lentilles sont allumees est le candidat "lens-agreement").
    Approximation conservative : voir la discussion dans la docstring.
* :func:`triade_colocalization` -- statistique triade : la **distance
  symetrisee au plus proche voisin** sur la triade (moyenne sur les 3 paires
  ``(beauty, ignition)``, ``(beauty, lens)``, ``(ignition, lens)``), z-score
  par null de rotation circulaire **independante** des trois flux (on tourne
  chacun d'un decalage distinct pour preserver l'autocorrelation interne de
  chaque flux). Verdict agrege :
  - ``"colocalized"`` si **les 3 paires** sont individuellement significatives
    (``p_close < 0.05``) ;
  - ``"partial"`` si **>= 1 paire** significative (les autres a chance) --
    une seule jambe alignee, pas une triade ;
  - ``"chance"`` si aucune paire significative ;
  - ``"undefined"`` si un flux est vide.
* :func:`triade_summary` -- agrege les resultats par prompt en un verdict
  global (majorite stricte ``colocalized`` vs ``dissociated`` vs ``chance``
  vs ``partial``).

Honnetement methodologique (a reporter dans le notebook)
---------------------------------------------------------
1. **Trois primitives heterogenes**. Les seuils (quantile 0.9 + persistance 3
   pour ignition ; seuil iid pour beauty ; intersection SAE/JLens pour
   lens-agreement) ne sont **pas** directement comparables ; seule la
   **distance position-level** les met sur un pied d'egalite. C'est volontaire
   : c'est exactement la question du capstone (les evenements tombent-ils aux
   memes positions ?), pas leurs mecanismes.
2. **Lens-agreement approxime**. La definition stricte du lens-agreement
   serait de comparer, prompt par prompt, les distributions de positions des
   deux lentilles et de marquer une position comme "lens-agreement" si les
   deux lentilles sont allumees **a cette position la** (et non au plus
   proche voisin). On approxime par l'intersection ensembliste : une
   position est "lens-agreement candidate" si elle est dans les deux listes
   d'ignitions. Perte : on rate les positions OU les deux lentilles sont
   allumees avec un decalage <= ``persistence``. Gain : primitive reutilisee
   ``colocalize_lenses`` est deja cablee et testee (9 tests, PR #7286). Le
   notebook ICT-26 confrontera cette approximation a une version stricte par
   fenetre glissante.
3. **Triade sur GPU-free**. Toutes les fixtures couche 16 sont deja
   extraites (cf traces/), donc ce module n'importe pas torch et n'invoque
   pas le modele. La 3ᵉ lentille (raw-logit sur l'autre moitie B-A1) reste
   GPU-gatee et n'est pas dans ce module.
4. **Verdict negatif legitime**. ICT-24 a deja trouve dissociation
   ``emergence_gain`` <-> ignition ~17 % creditees. Si la triade rend
   egalement ``chance`` ou ``partial``, c'est un **resultat** -- il confirme
   que la jambe temporelle discrimine orthogonalement aux Phi/F/K, comme
   predit par Gate 5. A rapporter honnetement.

Numpy uniquement (comme le reste du package leger ``ict``).
"""

from __future__ import annotations

from typing import Dict, List, Optional, Sequence, Set, Tuple

import numpy as np

from . import beauty as BTY
from . import lens_agreement as LA
from . import workspace as WS
from .sae_traces import differential_features

__all__ = [
    "token_state_sequence",
    "triade_centers",
    "triade_colocalization",
    "triade_summary",
]


# --------------------------------------------------------------------------- #
# Sequence d'etats pour ``beauty_events`` a partir des tokens
# --------------------------------------------------------------------------- #
def token_state_sequence(
    tokens: Sequence[str],
    *,
    alphabet: str = "type",
) -> List[int]:
    """Discretise une liste de tokens en une trajectoire d'etats pour ``beauty``.

    Le choix de la discretisation est explicite (cf garde-fou #1 du module
    ``synthesis`` : la discretisation est un choix documente, pas une constante
    cachee). Trois strategies, de la plus grossiere a la plus fine :

    * ``"type"`` (defaut) : 4 classes -- *whitespace* (token vide / espaces),
      *punct* (ponctuation isolee), *alpha* (sequence alphabetique),
      *other* (chiffres, symboles, sous-mots speciaux comme ``\\n``, etc.).
      Resolution grossiere suffisante pour la *frontiere de description*
      (zlib local detecte la transition "bruit -> structure"). Recommandee.
    * ``"shape"`` : 6 classes -- ``"whitespace"``, ``"punct"``, ``"lower"``
      (mots en minuscule), ``"upper"`` (au moins une majuscule), ``"digit"``,
      ``"other"``. Distingue "mots" (structure repetitive) de "ponctuation"
      (isolee).
    * ``"unique"`` : un etat par token unique, hashe stable. Resolution fine,
      mais alphabet tres large (longueur ``T``) -- ``local_compressibility``
      souffre (zlib ne peut pas exploiter la repetition quand le nombre de
      symboles >= la fenetre). Reserve aux diagnostics.

    Parametres
    ----------
    tokens : sequence de str
        La liste des tokens du prompt (cf cles ``__tokens`` dans les fixtures
        ``ict21_sae_layer16_*.npz``).
    alphabet : {"type", "shape", "unique"}
        Strategie de discretisation (voir ci-dessus).

    Retour
    ------
    list de int
        Trajectoire d'etats dans ``[0, M)`` (M = 4 / 6 / len(unique_tokens)).
        Peut etre passee directement a :func:`ict.beauty.beauty_events`.
    """
    if alphabet == "type":
        out: List[int] = []
        for tok in tokens:
            if not tok.strip():  # vide ou whitespace pur
                out.append(0)
            elif tok in {",", ".", ";", ":", "!", "?", "-", "(", ")", "[", "]", "{", "}",
                        "'", '"', "/", "\\", "@", "#", "$", "%", "^", "&", "*", "+",
                        "=", "<", ">", "|", "~", "`"}:
                out.append(1)
            elif tok.isalpha():
                out.append(2)
            else:
                out.append(3)
        return out
    if alphabet == "shape":
        out = []
        for tok in tokens:
            if not tok.strip():
                out.append(0)
            elif tok in {",", ".", ";", ":", "!", "?", "-", "(", ")", "[", "]", "{", "}",
                        "'", '"', "/", "\\", "@", "#", "$", "%", "^", "&", "*", "+",
                        "=", "<", ">", "|", "~", "`"}:
                out.append(1)
            elif tok.isalpha():
                out.append(3 if any(c.isupper() for c in tok) else 2)
            elif tok.isdigit():
                out.append(4)
            else:
                out.append(5)
        return out
    if alphabet == "unique":
        # Hash stable pour reproductibilite (defaut Python est salé par session).
        table: Dict[str, int] = {}
        out = []
        next_id = 0
        for tok in tokens:
            if tok not in table:
                table[tok] = next_id
                next_id += 1
            out.append(table[tok])
        return out
    raise ValueError(
        f"alphabet inconnu: {alphabet!r} (attendu 'type', 'shape', 'unique')"
    )


# --------------------------------------------------------------------------- #
#  Centres par prompt pour les 3 flux
# --------------------------------------------------------------------------- #
def triade_centers(
    traces_sae: dict,
    traces_jlens: dict,
    *,
    k: int = 64,
    q: float = 0.9,
    persistence: int = 3,
    metric: str = "gini",
    window: int = 60,
    horizon: int = 40,
    n_control: int = 20,
    n_lens: int = 200,
    rng: Optional[np.random.Generator] = None,
) -> Dict[Tuple[str, int], Dict[str, object]]:
    """Calcule les 3 flux de centres (beauty, ignition SAE, lens-agreement).

    Pour chaque prompt partage entre les deux traces (memes tokens, meme
    longueur ``T``), on retourne :

    * ``beauty`` -- indices des evenements ``beauty_events`` sur la
      discretisation ``type`` des tokens. Le verdict sous-jacent est garde
      (``"beauty"`` vs ``"flat"``) pour permettre une lecture diagnostique.
    * ``ignition_sae`` -- centres des :func:`ignition_events` sur la
      concentration SAE (memes parametres que ``lens_agreement``).
    * ``lens_agreement`` -- intersection ensembliste des centres SAE et
      J-Lens (cf discussion limitee dans la docstring du module). Vide si
      l'une des deux lentilles n'allume rien dans ce prompt.

    Les prompts dont les longueurs ``T`` different entre SAE et J-Lens sont
    exclus (``t_skip`` documente dans le retour). Les prompts ou la SAE
    n'allume aucune ignition (``n_ign_sae == 0``) ou la J-Lens non plus sont
    conserves (les flux vides peuvent etre diagnostiques) mais marques
    ``n_ign_sae == 0`` / ``n_ign_jlens == 0``.

    Parametres (sous-ensemble pertinent ; voir :mod:`ict.workspace`,
    :mod:`ict.lens_agreement`, :mod:`ict.beauty` pour les autres)
    ----------
    traces_sae, traces_jlens : dict
        Traces chargees (``ict.sae_traces.load_traces`` /
        ``ict.jlens_traces.load_traces``).
    k, q, persistence, metric, n_lens
        Cf :func:`ict.lens_agreement.colocalize_lenses`.
    window, horizon, n_control
        Cf :func:`ict.beauty.beauty_events`.

    Retour
    ------
    dict ``{(layer, variant) -> {"T": int, "beauty": [int, ...],
                                   "ignition_sae": [int, ...],
                                   "lens_agreement": [int, ...],
                                   "n_beauty": int, "n_ign_sae": int,
                                   "n_ign_jlens": int, "n_lens_agree": int,
                                   "verdict_beauty": "beauty"|"flat",
                                   "t_skip": bool}}``
        Un dict par prompt partage, dans le meme ordre que
        :func:`ict.lens_agreement.colocalize_lenses`.
    """
    if rng is None:
        rng = np.random.default_rng(0)

    feat_sae = differential_features(traces_sae, k=k)
    feat_jlens = differential_features(traces_jlens, k=k)
    ev_sae = LA.lens_ignition_centers(traces_sae, feat_sae, q=q,
                                      persistence=persistence, metric=metric)
    ev_jlens = LA.lens_ignition_centers(traces_jlens, feat_jlens, q=q,
                                        persistence=persistence, metric=metric)
    shared = sorted(set(ev_sae) & set(ev_jlens))

    out: Dict[Tuple[str, int], Dict[str, object]] = {}
    for key in shared:
        centers_sae, T_sae = ev_sae[key]
        centers_jlens, T_jlens = ev_jlens[key]
        if T_sae != T_jlens:
            out[key] = {
                "T": int(T_sae),
                "beauty": [], "ignition_sae": [], "lens_agreement": [],
                "n_beauty": 0, "n_ign_sae": 0, "n_ign_jlens": 0,
                "n_lens_agree": 0, "verdict_beauty": "flat",
                "t_skip": True,
            }
            continue
        # Tokens : la cle __tokens commune aux deux traces est dans la 1re
        # entree du nom de cle (la SAE et la J-Lens stockent les memes tokens
        # pour un meme prompt, par construction du pipeline d'extraction).
        # On prend la version SAE pour le flux beauty.
        sae_panels = _panels_for_key(traces_sae, key, feat_sae)
        if not sae_panels:
            tokens: List[str] = []
        else:
            tokens = list(sae_panels[0]["tokens"])
        T = int(T_sae)
        if len(tokens) != T:
            # garde-fou : tokens et T doivent coincider (le panel est construit
            # sur les memes positions que la liste de tokens du prompt).
            tokens = tokens[:T] if len(tokens) > T else (
                tokens + [""] * (T - len(tokens))
            )

        seq = token_state_sequence(tokens, alphabet="type")
        # Aligne seq sur T si jamais -- garde-fou.
        if len(seq) < T:
            seq = seq + [3] * (T - len(seq))  # pad "other"
        seq = seq[:T]

        # Beauty events
        rep = BTY.beauty_events(seq, window=window, horizon=horizon,
                                n_control=n_control, rng=rng)
        centers_beauty = [int(step) for step, _ in rep["events"]]
        centers_beauty = [c for c in centers_beauty if 0 <= c < T]

        # Lens-agreement : intersection ensembliste
        sae_set: Set[int] = set(int(c) for c in centers_sae if 0 <= c < T)
        jlens_set: Set[int] = set(int(c) for c in centers_jlens if 0 <= c < T)
        lens_agree = sorted(sae_set & jlens_set)

        out[key] = {
            "T": T,
            "beauty": centers_beauty,
            "ignition_sae": centers_sae,
            "lens_agreement": lens_agree,
            "n_beauty": len(centers_beauty),
            "n_ign_sae": len(centers_sae),
            "n_ign_jlens": len(centers_jlens),
            "n_lens_agree": len(lens_agree),
            "verdict_beauty": rep["verdict"],
            "t_skip": False,
        }
    return out


def _panels_for_key(traces: dict, key: Tuple[str, int],
                    feature_ids: np.ndarray) -> List[dict]:
    """Recupere le panel dense d'un seul prompt (helper interne).

    Les fixtures sont structurees en ``{"meta": ..., "prompts":
    {(name, idx): {"ids", "vals", "tokens"}}}`` (cf :mod:`ict.sae_traces`).
    On cherche le prompt par cle ``(name, idx)`` dans ``traces["prompts"]``.
    Retourne une liste a un element (le panel dense + tokens) ou vide si la
    cle est absente.
    """
    from .sae_traces import densify
    prompts = traces.get("prompts", traces) if isinstance(traces, dict) else {}
    if key not in prompts:
        return []
    entry = prompts[key]
    dense = densify(entry["ids"], entry["vals"], feature_ids)
    return [{"dense": dense, "tokens": entry["tokens"]}]


# --------------------------------------------------------------------------- #
#  Co-localisation triade (3 flux)
# --------------------------------------------------------------------------- #
def _pair_colocalization(
    a: Sequence[int], b: Sequence[int], T: int,
    n_null: int, rng: np.random.Generator,
) -> Dict[str, object]:
    """Sous-routine : appel direct a ``event_colocalization``."""
    return WS.event_colocalization(a, b, T, n_null=n_null, rng=rng)


def triade_colocalization(
    centers: Dict[str, Sequence[int]],
    T: int,
    *,
    n_null: int = 500,
    rng: Optional[np.random.Generator] = None,
) -> Dict[str, object]:
    """Co-localisation triade (3 flux) avec null par rotation circulaire independante.

    Pour chaque paire parmi les 3 flux (``beauty``, ``ignition_sae``,
    ``lens_agreement``), on appelle :func:`ict.workspace.event_colocalization`
    avec un decalage de rotation distinct (tire dans ``[1, T)`` pour chaque
    flux et chaque rotation). Les rotations **independantes** preservent
    l'autocorrelation interne de chaque flux et ne randomisent que la
    **phase** relative aux autres -- c'est le controle adapte au cas
    multi-flux (Grün 2009 etendu).

    Le verdict agrege :

    * ``"colocalized"`` si **les 3 paires** sont individuellement ``p_close < 0.05``.
    * ``"partial"`` si **au moins 1 paire** significative (les autres au
      hasard). Une seule jambe alignee n'est pas une triade.
    * ``"chance"`` si les 3 paires sont au hasard.
    * ``"undefined"`` si **2 flux ou plus** sont vides (pas de triade a
      mesurer).

    Parametres
    ----------
    centers : dict
        Un sous-dict par flux, par exemple ``{"beauty": [...], "ignition_sae":
        [...], "lens_agreement": [...]}``. Les flux absents ou ``None`` sont
        consideres comme vides (verdict ``"undefined"`` si >= 2 flux vides).
    T : int
        Longueur de la sequence porteuse.
    n_null : int
        Nombre de rotations tirees par paire (defaut 500).
    rng : numpy Generator, optionnel

    Retour
    ------
    dict
        ``pairs`` -- dict ``{("beauty","ignition_sae"): dict, ...}`` des 3
        ``event_colocalization`` ;
        ``z_mean`` -- moyenne des ``z`` definis sur les paires ;
        ``n_pairs_close``, ``n_pairs_far`` -- comptes de paires ``colocalized``
        et ``dissociated`` ;
        ``verdict`` -- synthese (voir ci-dessus) ;
        ``per_pair_verdict`` -- dict ``{(flux_a, flux_b): "colocalized" |
        "dissociated" | "chance" | "undefined"}`` ;
        ``n_per_prompt`` -- par flux, le nombre d'evenements utilises (echo
        des ``len(centers[f])``).
    """
    rng = rng or np.random.default_rng(0)
    fluxes = ("beauty", "ignition_sae", "lens_agreement")
    series = {f: [int(x) for x in (centers.get(f) or []) if 0 <= int(x) < T] for f in fluxes}
    n_empty = sum(1 for f in fluxes if not series[f])
    if n_empty >= 2:
        return {
            "pairs": {},
            "z_mean": float("nan"),
            "n_pairs_close": 0,
            "n_pairs_far": 0,
            "verdict": "undefined",
            "per_pair_verdict": {},
            "n_per_prompt": {f: len(series[f]) for f in fluxes},
        }

    pairs = {
        ("beauty", "ignition_sae"): (series["beauty"], series["ignition_sae"]),
        ("beauty", "lens_agreement"): (series["beauty"], series["lens_agreement"]),
        ("ignition_sae", "lens_agreement"): (series["ignition_sae"], series["lens_agreement"]),
    }
    out_pairs: Dict[Tuple[str, str], Dict[str, object]] = {}
    n_close = 0
    n_far = 0
    zs: List[float] = []
    for (fa, fb), (xa, xb) in pairs.items():
        r = _pair_colocalization(xa, xb, T, n_null=n_null, rng=rng)
        out_pairs[(fa, fb)] = r
        if r["verdict"] == "colocalized":
            n_close += 1
        elif r["verdict"] == "dissociated":
            n_far += 1
        if not np.isnan(r["z"]):
            zs.append(float(r["z"]))
    z_mean = float(np.mean(zs)) if zs else float("nan")

    if n_empty == 0 and n_close == 3:
        verdict = "colocalized"
    elif n_close + n_far >= 1:
        verdict = "partial"
    elif n_close == 0 and n_far == 0:
        verdict = "chance"
    else:
        verdict = "chance"  # defense en profondeur

    per_pair = {k: r["verdict"] for k, r in out_pairs.items()}
    return {
        "pairs": out_pairs,
        "z_mean": z_mean,
        "n_pairs_close": int(n_close),
        "n_pairs_far": int(n_far),
        "verdict": verdict,
        "per_pair_verdict": per_pair,
        "n_per_prompt": {f: len(series[f]) for f in fluxes},
    }


# --------------------------------------------------------------------------- #
#  Agregation multi-prompts
# --------------------------------------------------------------------------- #
def triade_summary(
    per_prompt: Dict[Tuple[str, int], Dict[str, object]],
    *,
    n_null: int = 500,
    rng: Optional[np.random.Generator] = None,
) -> Dict[str, object]:
    """Agrege la co-localisation triade sur les prompts partages.

    Pour chaque prompt, appelle :func:`triade_colocalization` puis collecte
    les verdicts et les ``z`` moyens. Le verdict global suit la majorite
    stricte (le verdict le plus frequent parmi les prompts non-undefined),
    avec regle de departage :

    * ``"colocalized"`` -> ``"colocalized"``
    * ``"partial"`` -> ``"partial"``
    * ``"chance"`` majoritaire strict -> ``"chance"``
    * ``"dissociated"`` (zero close, >= 1 dissociated et majoritaire) ->
      ``"dissociated"``
    * sinon -> ``"chance"`` (regle du minoritaire).

    Les prompts ``t_skip`` (T incompatible) sont exclus.

    Retour
    ------
    dict
        ``per_prompt`` -- dict ``{prompt_key: triade_colocalization}`` ;
        ``n_prompts`` -- nombre de prompts evalues ;
        ``n_skipped`` -- nombre de prompts ``t_skip`` ;
        ``verdict_counts`` -- dict des comptes par verdict ;
        ``verdict`` -- verdict global (voir ci-dessus) ;
        ``z_mean`` -- moyenne des ``z_mean`` par prompt (definis) ;
        ``n_colocalized``, ``n_partial``, ``n_chance``, ``n_dissociated`` :
            comptes par verdict (somme par prompt).
    """
    rng = rng or np.random.default_rng(0)
    out: Dict[Tuple[str, int], Dict[str, object]] = {}
    n_skipped = 0
    for key, info in per_prompt.items():
        if info.get("t_skip"):
            n_skipped += 1
            continue
        T = int(info["T"])
        centers = {
            "beauty": info.get("beauty") or [],
            "ignition_sae": info.get("ignition_sae") or [],
            "lens_agreement": info.get("lens_agreement") or [],
        }
        out[key] = triade_colocalization(centers, T, n_null=n_null, rng=rng)

    counts: Dict[str, int] = {"colocalized": 0, "partial": 0, "chance": 0,
                              "dissociated": 0, "undefined": 0}
    for r in out.values():
        counts[r["verdict"]] = counts.get(r["verdict"], 0) + 1

    zs = [r["z_mean"] for r in out.values() if not np.isnan(r["z_mean"])]
    z_mean = float(np.mean(zs)) if zs else float("nan")

    # Verdict global -- majorite stricte parmi les prompts definis.
    defined = {k: v for k, v in counts.items() if k != "undefined"}
    if not defined or all(v == 0 for v in defined.values()):
        global_verdict = "undefined"
    else:
        # Triade stricte d'abord : si tous les prompts definis sont "colocalized".
        if defined.get("colocalized", 0) > 0 and defined.get("colocalized", 0) >= max(
            defined.get("partial", 0), defined.get("chance", 0),
            defined.get("dissociated", 0),
        ):
            global_verdict = "colocalized"
        elif defined.get("dissociated", 0) >= 1 and defined.get("dissociated", 0) > (
            defined.get("colocalized", 0) + defined.get("partial", 0)
        ):
            global_verdict = "dissociated"
        elif defined.get("partial", 0) >= defined.get("chance", 0):
            global_verdict = "partial"
        else:
            global_verdict = "chance"

    return {
        "per_prompt": out,
        "n_prompts": len(out),
        "n_skipped": int(n_skipped),
        "verdict_counts": counts,
        "verdict": global_verdict,
        "z_mean": z_mean,
        "n_colocalized": int(counts.get("colocalized", 0)),
        "n_partial": int(counts.get("partial", 0)),
        "n_chance": int(counts.get("chance", 0)),
        "n_dissociated": int(counts.get("dissociated", 0)),
    }