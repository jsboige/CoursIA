"""Contrat de trace ICT v1 -- manifeste, validation, alignement.

Le **contrat de trace v1** est le format canonique des artefacts ICT-Series
(SAE, J-Lens, et tout futur instrument) qu'echangent les notebooks, les
extracteurs GPU et les loaders numpy-only. Il pose trois regles dures :

1. **Identite d'instrument** : un champ ``meta["instrument"]`` discriminant
   (``"sae"`` / ``"jlens"``) DOIT etre present. Une trace qui le declare
   differemment du module qui la charge est REFUSEE -- c'est l'acceptance #1
   du ticket de fond #15476 (deux traces de meme forme mais d'instruments
   differents ne peuvent plus etre melangees silencieusement).

2. **Alignement explicite** : les champs d'alignement (modele / run / seed /
   prompt set / prompt / token positions / layer / module / tensor space /
   dtype) sont declares dans :data:`ALIGNMENT_KEYS` et valides par
   :func:`check_alignment`. Tout mismatch entre deux traces que l'on souhaite
   comparer doit echouer avec un diagnostic ACTIONNABLE (acceptance #2).

3. **Asymetrie top-k preservee** : la SAE rend zero exact par construction
   (top-k sparse exhaustif) ; la J-Lens rend une valeur NON OBSERVEE pour
   les directions absentes du top-k (troncature rang-k d'une projection).
   Ces deux semantiques sont exposees par :func:`topk_semantics` et
   testees separement -- acceptance #3.

Module **numpy-only** : aucune dependance torch (regle d'architecture de la
serie ICT, GPU confine aux scripts d'extraction). Aucune dependance a
``sae_traces`` / ``jlens_traces`` pour eviter un cycle d'import (la
discrimination par instrument est ici une donnee, pas une politique des
adaptateurs en aval).

References
----------
* #15476 -- ticket de fond du contrat de trace v1.
* #15475 -- epic parente ``ICT toolkit``.
* #8236 -- pipeline SAE 9B/2B (l'instrument SAE).
* #5681 -- tete-a-tete SAE vs J-Lens (l'instrument J-Lens).
* :mod:`ict.sae_traces` -- adaptateur SAE qui consomme ce contrat.
* :mod:`ict.jlens_traces` -- adaptateur J-Lens qui consomme ce contrat.
"""
from __future__ import annotations

import warnings
from typing import Any, Iterable

import numpy as np

__all__ = [
    "CONTRACT_VERSION",
    "INSTRUMENTS",
    "ALIGNMENT_KEYS",
    "REQUIRED_META_KEYS",
    "OPTIONAL_META_KEYS",
    "TraceContractError",
    "validate_manifest",
    "enforce_instrument",
    "check_alignment",
    "topk_semantics",
    "build_manifest",
]


# --------------------------------------------------------------------------- #
# Constantes du contrat v1
# --------------------------------------------------------------------------- #
CONTRACT_VERSION: str = "v1.0.0"

# Instruments reconnus par le contrat v1.
# L'enum est figee : ajouter un instrument = passer en v1.1.0 (avec un test
# d'instrument inconnu qui echoue proprement) pour eviter la proliferation
# silencieuse de forks mal nommes.
INSTRUMENTS: tuple[str, ...] = ("sae", "jlens")

# Champs d'alignement entre deux traces que l'on souhaite comparer.
# Tout couple (trace_a, trace_b) sur lequel on opere (soustraction de
# panneaux, scatter SAE vs J-Lens, etc.) doit partager la valeur de CHACUN
# de ces champs ; sinon, le diagnostic nomme LE champ fautif et les deux
# valeurs observees, pour qu'une correction ciblee soit possible.
ALIGNMENT_KEYS: tuple[str, ...] = (
    "contract_version",
    "instrument",
    "d_sae",
    "k",
    "layer",
    "model",
    "model_revision",
    "model_family",
    "dtype",
    "run",
    "seed",
    "prompt_set",
    "schema",                # structure du npz : <set>__<idx>__<field>
)

# Champs de manifeste obligatoires (en plus de ``instrument`` et
# ``contract_version`` qui sont valides separement par :func:`validate_manifest`).
# Les valeurs peuvent etre None pour les champs de run-time (seed, run) si
# la trace est issue d'un script non-deterministic NON reproductible --
# l'important est que la CLE soit presente et serialisable JSON.
#
# ``d_sae`` est la dimension de l'espace latent (SAE features ou J-Lens
# IDs vocabulaire + logits), c'est ce que les loaders numpy-only
# utilisent reellement pour densifier ; ``d_model`` (dimension du residual
# stream du modele source) est optionnel et releve des champs d'alignement.
REQUIRED_META_KEYS: tuple[str, ...] = (
    "d_sae",
    "k",
    "layer",
)

# Champs recommandes mais non bloquants : le contrat les LIT pour
# l'alignement s'ils sont presents, mais ne les EXIGE pas. C'est la
# liste des champs que les extracteurs GPU devraient ecrire pour
# satisfaire :func:`check_alignment` en mode strict.
OPTIONAL_META_KEYS: tuple[str, ...] = (
    "model",
    "model_revision",
    "model_family",
    "dtype",
    "device",
    "run",
    "seed",
    "prompt_set",
    "prompt_input_hash",
    "capture_point",
    "module",
    "tensor_space",
    "schema_version",
    "n_clamp",
    "sae_repo",
    "sae_k",
    "lens_repo",
    "lens_kind",
    "lens_rank",
)


# --------------------------------------------------------------------------- #
# Erreur explicite : mieux que ValueError pour permettre un try/except cible
# --------------------------------------------------------------------------- #
class TraceContractError(ValueError):
    """Le manifeste d'une trace viole le contrat v1 ou refuse l'alignement.

    Herite de ``ValueError`` pour rester compatible avec le pattern existant
    dans ``sae_traces`` / ``jlens_traces`` (toutes les validations actuelles
    lèvent ``ValueError``) ; le nom specialise permet un ``except`` cible
    côté notebooks si besoin.
    """


# --------------------------------------------------------------------------- #
# Validation de manifeste
# --------------------------------------------------------------------------- #
def validate_manifest(meta: dict, *, strict: bool = False) -> dict:
    """Valide qu'un manifeste respecte le contrat v1.

    Parameters
    ----------
    meta : dict
        Le manifeste (clefs/valeurs JSON-serialisables) charge d'une trace
        ``.npz``.
    strict : bool, default False
        Si ``True``, **chaque** champ de :data:`OPTIONAL_META_KEYS` devient
        obligatoire ; c'est le mode recommandé pour les scripts d'extraction
        neuf. Le défaut ``False`` accepte les traces historiques (qui ne
        portent pas encore tous les champs) -- c'est la migration
        rétro-compatible exigée par l'acceptance #4.

    Returns
    -------
    dict
        Le manifeste valide, complete des champs derives (``contract_version``,
        ``schema``). Copie superficielle pour eviter la mutation du dict
        appelant.

    Raises
    ------
    TraceContractError
        Si ``meta`` n'est pas un dict, si ``contract_version`` est absent
        ou anterieur a v1, si ``instrument`` est absent ou hors
        :data:`INSTRUMENTS`, ou si un champ :data:`REQUIRED_META_KEYS`
        manque (en mode ``strict``, aussi les :data:`OPTIONAL_META_KEYS`).
    """
    if not isinstance(meta, dict):
        raise TraceContractError(
            f"manifeste invalide : type {type(meta).__name__} au lieu de dict. "
            f"Une trace .npz doit embarquer une cle '__meta__' dont la valeur "
            f"est un dict JSON-serialisable.")
    out = dict(meta)

    # 1. Version de schema
    cv = out.get("contract_version")
    if cv is None:
        # Trace historique : on stamp v1.0.0 en retro-compat si le strict
        # n'est pas exige. En strict : refus net, force la migration.
        if strict:
            raise TraceContractError(
                "manifeste sans 'contract_version' en mode strict -- "
                "migration requise (voir OPTIONAL_META_KEYS). Pour accepter "
                "les traces historiques, repasser en strict=False.")
        out["contract_version"] = CONTRACT_VERSION
    elif not isinstance(cv, str):
        raise TraceContractError(
            f"'contract_version' doit être une str (recu {type(cv).__name__}).")
    elif cv != CONTRACT_VERSION:
        # v1.x.y : on accepte. Une migration v1 -> v2 serait signalee ici.
        if not cv.startswith("v1."):
            raise TraceContractError(
                f"'contract_version'={cv} non supportee par ce loader v1. "
                f"Mettre a jour le chargeur ou regenerer la trace.")
        out["contract_version"] = cv

    # 2. Instrument discriminant
    inst = out.get("instrument")
    if inst is None:
        # Champ 'lens' legacy : on mappe vers 'instrument' en retro-compat.
        legacy = out.get("lens")
        if legacy == "sae":
            inst = "sae"
        elif legacy in ("jacobian", "jlens"):
            inst = "jlens"
        if inst is None:
            # Inference pour traces historiques sans discriminant (acceptance
            # #4 retro-compat). On regarde les champs specifiques a chaque
            # instrument : ``sae_repo`` / ``sae_k`` -> "sae" ;
            # ``lens_repo`` / ``lens_kind`` / ``lens_rank`` -> "jlens".
            # Le user est prevenu par warning explicite (visible Papermill +
            # pytest) pour pousser a la migration.
            if "sae_repo" in out or "sae_k" in out:
                inst = "sae"
            elif ("lens_repo" in out or "lens_kind" in out
                  or "lens_rank" in out):
                inst = "jlens"
            if inst is not None:
                warnings.warn(
                    f"trace historique chargee sans 'instrument' ni 'lens' "
                    f"legacy ; infere instrument={inst!r} depuis les champs "
                    f"presents dans le manifeste (acceptance #4 retro-compat). "
                    f"Migrer l'extracteur GPU pour poser meta['instrument'] "
                    f"canoniquement -- le contrat v1 prefere la declaration "
                    f"explicite a l'inference.",
                    UserWarning, stacklevel=2)
                out["instrument"] = inst
            elif strict:
                raise TraceContractError(
                    "manifeste sans 'instrument' en mode strict -- "
                    "champ obligatoire (acceptance #1 anti-melange).")
            # non-strict + aucune inference possible : on laisse instrument=None,
            # l'enforce se fera cote loader et lèvera avec diagnostic.
        else:
            out["instrument"] = inst
    elif inst not in INSTRUMENTS:
        raise TraceContractError(
            f"'instrument'={inst!r} hors enum {INSTRUMENTS}. Le contrat v1 "
            f"limite les instruments a {INSTRUMENTS} -- un fork ajoute une "
            f"valeur hors enum et casse l'acceptance #1.")

    # 3. Champs obligatoires (avec alias d_model <-> d_sae : ``d_sae``
    # est canonique (ce que les loaders numpy-only lisent reellement) ;
    # ``d_model`` est accepte comme alias pour les manifestes qui
    # documentent l'architecture du modele source plutot que la dimension
    # de l'espace latent. Si l'un des deux est present, on pose l'autre
    # par coherence, et la cle canonique ``d_sae`` finit dans le manifeste
    # valide.
    if "d_sae" not in out and "d_model" in out:
        out["d_sae"] = out["d_model"]
    elif "d_model" not in out and "d_sae" in out:
        out["d_model"] = out["d_sae"]

    missing = [k for k in REQUIRED_META_KEYS if k not in out]
    if missing:
        raise TraceContractError(
            f"champs obligatoires manquants : {sorted(missing)}. Le contrat "
            f"v1 exige au minimum {list(REQUIRED_META_KEYS)} (architecture "
            f"du modele, top-k, couche de capture).")

    # 4. Champs stricts (optionnels par defaut)
    if strict:
        missing_opt = [k for k in OPTIONAL_META_KEYS if k not in out]
        if missing_opt:
            raise TraceContractError(
                f"champs stricts manquants : {sorted(missing_opt)}. En mode "
                f"strict le contrat exige les champs d'alignement de "
                f"OPTIONAL_META_KEYS -- migration des extracteurs requise.")

    # 5. Schema derive si absent (retro-compat). Le schema est une clef
    # stable qui nomme la structure du .npz (``<set>__<idx>__<field>``).
    out.setdefault("schema", "<set>__<idx>__<field>")

    return out


def enforce_instrument(meta: dict, expected: str) -> None:
    """Verifie que ``meta['instrument']`` vaut ``expected``, sinon leve.

    C'est le **mecanisme central** de l'acceptance #1 : un chargeur SAE qui
    tente de lire un manifeste ``"jlens"`` (ou un manifeste sans
    ``instrument``) REFUSE avec un diagnostic qui dit quoi utiliser.

    Parameters
    ----------
    meta : dict
        Manifeste valide par :func:`validate_manifest`.
    expected : str
        L'instrument attendu (``"sae"`` ou ``"jlens"``).

    Raises
    ------
    TraceContractError
        Si ``expected`` n'est pas un instrument du contrat, si
        ``meta['instrument']`` est absent (manifeste trop ancien), ou si
        l'instrument observe differe de l'attendu.
    """
    if expected not in INSTRUMENTS:
        raise TraceContractError(
            f"enforce_instrument: attendu={expected!r} hors enum {INSTRUMENTS}")
    inst = meta.get("instrument")
    if inst is None:
        # Retro-compat : pas d'instrument declare. On tente la legacite
        # 'lens' pour ne PAS casser les traces historiques, mais on
        # PRECISE dans le diagnostic que le contrat v1 est preferable.
        legacy = meta.get("lens")
        if legacy == "sae" and expected == "sae":
            return
        if legacy in ("jacobian", "jlens") and expected == "jlens":
            return
        raise TraceContractError(
            f"manifeste sans 'instrument' (legacy meta['lens']={legacy!r}) "
            f"et attendu={expected!r}. Migration requise : poser "
            f"meta['instrument']='{expected}' dans l'extracteur GPU. "
            f"Le contrat v1 refuse les melanges silencieux (acceptance #1).")
    if inst != expected:
        raise TraceContractError(
            f"manifeste declare instrument={inst!r}, attendu={expected!r}. "
            f"Deux lectures possibles : (a) utiliser le chargeur adapte "
            f"a l'instrument declare, ou (b) regenerer la trace avec le bon "
            f"meta['instrument']={expected!r}. Le contrat v1 refuse le "
            f"melange silencieux SAE <-> J-Lens (acceptance #1).")


# --------------------------------------------------------------------------- #
# Alignement entre deux traces
# --------------------------------------------------------------------------- #
def check_alignment(meta_a: dict, meta_b: dict,
                    *, keys: Iterable[str] = ALIGNMENT_KEYS) -> list[str]:
    """Liste les champs d'alignement qui different entre deux manifestes.

    Parameters
    ----------
    meta_a, meta_b : dict
        Manifestes valides par :func:`validate_manifest`.
    keys : iterable of str, default :data:`ALIGNMENT_KEYS`
        Les champs sur lesquels on exige l'egalite. Par defaut, tous les
        champs d'alignement du contrat v1.

    Returns
    -------
    list of str
        Liste vide si les manifestes sont alignes sur tous les champs.
        Sinon, une ligne par champ divergent, formattee
        ``"champ: 'valeur_a' != 'valeur_b'"``. La liste est directement
        utilisable comme message d'erreur : ``raise TraceContractError(
        "traces non alignees:\\n" + "\\n".join(check_alignment(...)))``.
    """
    diffs: list[str] = []
    for k in keys:
        if k not in meta_a:
            diffs.append(f"{k}: absent cote A")
            continue
        if k not in meta_b:
            diffs.append(f"{k}: absent cote B")
            continue
        va, vb = meta_a[k], meta_b[k]
        if isinstance(va, (list, tuple)) or isinstance(vb, (list, tuple)):
            # Alignement structurel : la representation textuelle suffit
            # pour le diagnostic (les listes sont petites -- seeds, layers).
            if list(va) != list(vb):
                diffs.append(f"{k}: {va!r} != {vb!r}")
        else:
            if va != vb:
                diffs.append(f"{k}: {va!r} != {vb!r}")
    return diffs


# --------------------------------------------------------------------------- #
# Asymetrie top-k SAE vs J-Lens (acceptance #3)
# --------------------------------------------------------------------------- #
TOPK_EXACT_ZERO: str = "exact_zero"          # SAE top-k : zero par construction
TOPK_UNOBSERVED: str = "unobserved"         # J-Lens : top-k = troncature rang-k


def topk_semantics(instrument: str) -> str:
    """Renvoie la semantique d'absence d'une cle du top-k.

    * SAE top-k officiel Qwen-Scope : la cle absente du top-k a une
      activation **exactement nulle** (le SAE force la troncature).
    * J-Lens : la cle absente du top-k a une valeur **non observee** (la
      projection tronquee est une approximation rang-k, pas une
      exactitude).

    Cette asymetrie DOIT etre documentee dans tout notebook qui compare
    SAE et J-Lens sur les memes features (cf. :mod:`ict.jlens_traces`,
    section "Divergence semantique honnete vs SAE").

    Parameters
    ----------
    instrument : str
        ``"sae"`` ou ``"jlens"``.

    Returns
    -------
    str
        :data:`TOPK_EXACT_ZERO` ou :data:`TOPK_UNOBSERVED`.

    Raises
    ------
    TraceContractError
        Si ``instrument`` n'est pas un instrument du contrat.
    """
    if instrument == "sae":
        return TOPK_EXACT_ZERO
    if instrument == "jlens":
        return TOPK_UNOBSERVED
    raise TraceContractError(
        f"topk_semantics: instrument={instrument!r} hors enum {INSTRUMENTS}. "
        f"Le contrat v1 ne sait decrire la semantique d'absence que pour "
        f"les instruments reconnus.")


# --------------------------------------------------------------------------- #
# Constructeur de manifeste (pour les tests + les extracteurs a venir)
# --------------------------------------------------------------------------- #
def build_manifest(instrument: str, *, model: str = "", model_revision: str = "",
                   model_family: str = "", dtype: str = "bfloat16",
                   d_model: int | None = None, k: int | None = None,
                   layer: int | None = None, run: str = "",
                   seed: int | None = None, prompt_set: str = "",
                   **extra: Any) -> dict:
    """Fabrique un manifeste conforme au contrat v1.

    Convenience pour les tests et les extracteurs a venir : pose
    ``contract_version``, ``instrument`` et les champs obligatoires
    (``d_model``, ``k``, ``layer``) ; passe les extras via ``**extra``.

    Le manifeste retourne n'est PAS valide : il faut appeler
    :func:`validate_manifest` dessus avant de le poser sur une trace.
    """
    if instrument not in INSTRUMENTS:
        raise TraceContractError(
            f"build_manifest: instrument={instrument!r} hors enum {INSTRUMENTS}")
    manifest: dict[str, Any] = {
        "contract_version": CONTRACT_VERSION,
        "instrument": instrument,
        "dtype": dtype,
    }
    if model:
        manifest["model"] = model
    if model_revision:
        manifest["model_revision"] = model_revision
    if model_family:
        manifest["model_family"] = model_family
    if d_model is not None:
        manifest["d_model"] = int(d_model)
    if k is not None:
        manifest["k"] = int(k)
    if layer is not None:
        manifest["layer"] = int(layer)
    if run:
        manifest["run"] = run
    if seed is not None:
        manifest["seed"] = int(seed)
    if prompt_set:
        manifest["prompt_set"] = prompt_set
    manifest.update(extra)
    return manifest
