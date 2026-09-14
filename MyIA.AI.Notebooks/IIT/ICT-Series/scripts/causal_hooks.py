"""Hooks torch du Causal Intervention Engine (#15479, tranche 2/n, Epic #15475).

Ce module confine torch/transformers (convention de la serie : ``ict/`` reste
numpy-only, les scripts d'extraction et d'application portent le GPU/torch --
cf ``extract_sae_traces.py``). Il relie une :class:`~ict.causal_engine.InterventionSpec`
a un module torch vivant via un **forward pre-hook** : l'activation d'entree du
module designe EST le panneau (T, d) -- ou (B, T, d), lot diffuse -- sur lequel
les cinq operations du contrat v1 s'appliquent.

Correspondance bijective avec le coeur numpy : pour chaque operation unaire
(ablate/clamp/steer/patch), ``apply_spec_to_tensor`` reproduit exactement
``ict.causal_engine.apply_intervention`` (equivalence testee bit a bit en
float64, ``tests/test_causal_hooks.py``). L'operation ``interchange`` exige le
**protocole capture-puis-ecriture** (classe :class:`PairedInterchange`) : un
pre-hook ne voit chaque activation qu'une fois par forward, donc un echange
bilateral ne peut PAS se jouer dans un forward unique -- on capture la tranche
des deux runs apparies (2 forwards), puis on ecrit chacun avec la tranche de
l'autre (2 forwards). En tensor units, l'ecriture d'un cote d'interchange EST
un patch par la tranche empirique du run apparie — c'est litteralement ce que
fait ``interchange_panels`` cote par cote.

Captures : le hook enregistre le panneau complet avant/apres edition (numpy,
CPU) ET la tranche cible (etat). Un forward hook optionnel capte la sortie du
module (point de lecture readout, ex. sortie du LayerNorm vise) — les deux
points de capture pre/post de la decision de design 2026-09-11T12:25Z.
``hook_record`` assemble ensuite un ``InterventionRecord`` sidecar complet
(domage general calcule par le coeur numpy, verdict selectivite, empreintes
avant/apres) sans jamais stocker les panneaux dans l'enregistrement.

Compatibilite transformers : ``attach_intervention`` resout le module par son
nom ``named_modules()`` — n'importe quel ``nn.Module`` (bloc GPT2, couche
LayerNorm interne, sae hook module...) est adressable. La traduction
instrument-space (residual -> latent SAE : encode, editer, decoder) est
explicitement HORS de ce module : elle appartient a la couche lentille
(ex ``extract_sae_traces.py``), le champ ``tensor_space`` de la spec documente
l'espace dans lequel positions/features sont lus.

Determinisme : aucun RNG ici. Les seules nondeterminismes possibles viennent
du modele lui-meme ; les tests s'appuient sur des modeles jouets seeds et des
comparaisons bit a bit en float64.
"""
from __future__ import annotations

import sys
from pathlib import Path
from typing import Any

import numpy as np
import torch

# Le package ``ict/`` reste numpy-only : l'importer ici ne fait PAS entrer torch
# dans la bibliotheque — c'est ce script qui confine torch (cf docstring).
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from ict.causal_engine import (  # noqa: E402  (necessairement apres sys.path)
    InterventionRecord,
    InterventionSpec,
    artifact_sha256,
    damage_metrics,
    selectivity_verdict,
)

__all__ = [
    "InterventionHook",
    "InterventionHandle",
    "PairedInterchange",
    "apply_spec_to_tensor",
    "attach_intervention",
    "forward_with_spec",
    "hook_record",
    "resolve_module",
]


# --------------------------------------------------------------------------- #
# Resolution de cible : nom de module -> nn.Module
# --------------------------------------------------------------------------- #

def resolve_module(model: torch.nn.Module, module_name: str) -> torch.nn.Module:
    """Resout un module par son chemin ``named_modules()`` (compatible transformers).

    Echoue en nommant quelques modules disponibles — jamais un KeyError muet.
    """
    modules = dict(model.named_modules())
    if module_name not in modules:
        available = sorted(name for name in modules if name)
        shown = ", ".join(available[:10]) + ("…" if len(available) > 10 else "")
        raise ValueError(
            f"module {module_name!r} introuvable dans le modele — "
            f"disponibles: {shown}"
        )
    return modules[module_name]


# --------------------------------------------------------------------------- #
# Application tensor : miroir torch du coeur numpy
# --------------------------------------------------------------------------- #

def _validate_shape(t: torch.Tensor, spec: InterventionSpec) -> None:
    if t.dim() not in (2, 3):
        raise ValueError(
            f"activation {tuple(t.shape)} : le moteur edite des panneaux (T, d) "
            f"ou (B, T, d), rien d'autre"
        )
    T, d = t.shape[-2], t.shape[-1]
    if spec.positions:
        bad = min(spec.positions) if min(spec.positions) < 0 else (
            max(spec.positions) if max(spec.positions) >= T else None
        )
        if bad is not None:
            raise ValueError(
                f"position {bad} hors activation T={T} — la spec ne peut pas "
                f"s'appliquer a ce panneau (pas de troncature silencieuse)"
            )
    if spec.features:
        bad = min(spec.features) if min(spec.features) < 0 else (
            max(spec.features) if max(spec.features) >= d else None
        )
        if bad is not None:
            raise ValueError(
                f"feature {bad} hors dimension d={d} — la spec ne peut pas "
                f"s'appliquer a ce panneau (pas de troncature silencieuse)"
            )


def _target_index(t: torch.Tensor, spec: InterventionSpec) -> tuple[Any, ...]:
    rows = torch.tensor(list(spec.positions), dtype=torch.long, device=t.device)
    cols = torch.tensor(list(spec.features), dtype=torch.long, device=t.device)
    if t.dim() == 2:
        return (rows[:, None], cols)
    return (slice(None), rows[:, None], cols)  # (B, T, d) : diffuse sur le lot


def _donor_tensor(
    donor: Any, t: torch.Tensor, spec: InterventionSpec
) -> torch.Tensor:
    """Coerce le donneur (torch / numpy / tuple de lignes) vers (n_positions, n_features)."""
    values = torch.as_tensor(np.asarray(donor), dtype=t.dtype, device=t.device)
    expected = (len(spec.positions), len(spec.features))
    if tuple(values.shape) != expected:
        raise ValueError(
            f"donneur de forme {tuple(values.shape)} != cible {expected} "
            f"(positions x features)"
        )
    return values


def apply_spec_to_tensor(
    t: torch.Tensor, spec: InterventionSpec, *, donor: Any = None
) -> torch.Tensor:
    """Applique la spec au tensor d'activation — clone, ne mute JAMAIS l'entree.

    Miroir torch de ``ict.causal_engine.apply_intervention`` (equivalence bit a
    bit testee). Cible vide (bras intact du Gate 24) : identite PAR LA MEME VOIE
    (clone retourne sans edition). ``interchange`` exige ``donor`` : la tranche
    capturee du run apparie — le protocole bilateral vit dans
    :class:`PairedInterchange`.
    """
    _validate_shape(t, spec)
    out = t.clone()
    if not spec.positions or not spec.features:
        return out  # bras intact : meme voie de code, aucune edition
    idx = _target_index(out, spec)
    if spec.operation == "ablate":
        out[idx] = torch.zeros((), dtype=t.dtype, device=t.device)
    elif spec.operation == "clamp":
        dvec = torch.tensor(spec.direction, dtype=t.dtype, device=t.device)
        out[idx] = spec.dose * dvec
    elif spec.operation == "steer":
        dvec = torch.tensor(spec.direction, dtype=t.dtype, device=t.device)
        unit = dvec / dvec.norm()
        out[idx] = out[idx] + spec.dose * unit
    elif spec.operation == "patch":
        source = donor if donor is not None else spec.donor
        if source is None:
            raise ValueError("patch exige un donneur (valeurs empiriques)")
        out[idx] = _donor_tensor(source, out, spec)
    elif spec.operation == "interchange":
        if donor is None:
            raise ValueError(
                "interchange exige le donneur capture du run apparie — "
                "protocole PairedInterchange.capture puis .write, "
                "jamais une ecriture directe"
            )
        out[idx] = _donor_tensor(donor, out, spec)
    else:  # pragma: no cover - l'enum est ferme, InterventionSpec a deja valide
        raise ValueError(f"operation {spec.operation!r} hors contrat v1")
    return out


# --------------------------------------------------------------------------- #
# Hooks
# --------------------------------------------------------------------------- #

def _first_tensor(args: tuple[Any, ...]) -> torch.Tensor | None:
    for a in args:
        if isinstance(a, torch.Tensor):
            return a
    return None


def _slice_of(panel: np.ndarray, spec: InterventionSpec) -> np.ndarray:
    rows, cols = list(spec.positions), list(spec.features)
    if panel.ndim == 2:
        return panel[rows][:, cols]
    return panel[:, rows][:, :, cols]


class InterventionHook:
    """Forward pre-hook qui applique une spec a l'activation d'entree d'un module.

    A chaque forward : capture le panneau avant (numpy CPU), edite via
    :func:`apply_spec_to_tensor`, capture le panneau/tranche apres, et
    REMPLACE les entrees positionnelles du module par la version editee
    (contrat des pre-hooks torch : un retour non-None remplace ``args``).
    L'entree d'origine n'est jamais mutee.

    Captures (ecrasees a chaque forward) :
      ``panel_before``/``panel_after``  panneaux complets (T, d) ou (B, T, d) ;
      ``state_before``/``state_after``  tranche cible (l'etat du canal etat).
    """

    def __init__(self, spec: InterventionSpec, *, donor: Any = None) -> None:
        self.spec = spec
        self.donor = donor
        self.panel_before: np.ndarray | None = None
        self.panel_after: np.ndarray | None = None
        self.state_before: np.ndarray | None = None
        self.state_after: np.ndarray | None = None
        self.calls = 0

    def __call__(
        self, module: torch.nn.Module, args: tuple[Any, ...]
    ) -> tuple[Any, ...]:
        t = _first_tensor(args)
        if t is None:
            raise RuntimeError(
                f"aucun tensor dans les entrees positionnelles de "
                f"{type(module).__name__} — le hook du moteur causal ne sait "
                f"pas ou editer (appels kwargs uniquement non supportes)"
            )
        _validate_shape(t, self.spec)
        self.panel_before = t.detach().cpu().numpy().copy()
        edited = apply_spec_to_tensor(t, self.spec, donor=self.donor)
        self.panel_after = edited.detach().cpu().numpy().copy()
        if self.spec.positions and self.spec.features:
            self.state_before = _slice_of(self.panel_before, self.spec)
            self.state_after = _slice_of(self.panel_after, self.spec)
        else:
            self.state_before = np.zeros((0, 0))
            self.state_after = np.zeros((0, 0))
        self.calls += 1
        return tuple(edited if a is t else a for a in args)


class _PostCaptureHook:
    """Forward hook passif : capte la sortie du module (point de lecture readout)."""

    def __init__(self) -> None:
        self.readout: np.ndarray | None = None

    def __call__(
        self, module: torch.nn.Module, args: tuple[Any, ...], output: Any
    ) -> None:
        t = output if isinstance(output, torch.Tensor) else _first_tensor(
            output if isinstance(output, tuple) else ()
        )
        self.readout = t.detach().cpu().numpy().copy() if t is not None else None


class InterventionHandle:
    """Poignee de detachement + vues sur les captures d'une intervention attachee."""

    def __init__(
        self,
        module_name: str,
        hook: InterventionHook,
        post: _PostCaptureHook | None = None,
    ) -> None:
        self.module_name = module_name
        self.hook = hook
        self.post = post
        self._removables: list[Any] = []

    @property
    def panel_before(self) -> np.ndarray | None:
        return self.hook.panel_before

    @property
    def panel_after(self) -> np.ndarray | None:
        return self.hook.panel_after

    @property
    def state_before(self) -> np.ndarray | None:
        return self.hook.state_before

    @property
    def state_after(self) -> np.ndarray | None:
        return self.hook.state_after

    @property
    def readout(self) -> np.ndarray | None:
        return self.post.readout if self.post is not None else None

    def remove(self) -> None:
        for removable in self._removables:
            removable.remove()
        self._removables.clear()


def attach_intervention(
    model: torch.nn.Module,
    module_name: str,
    spec: InterventionSpec,
    *,
    donor: Any = None,
    capture_post: bool = True,
) -> InterventionHandle:
    """Attache spec (pre-hook d'edition + post-hook de lecture) sur un module nomme."""
    module = resolve_module(model, module_name)
    hook = InterventionHook(spec, donor=donor)
    handle = InterventionHandle(module_name, hook)
    handle._removables.append(module.register_forward_pre_hook(hook))
    if capture_post:
        post = _PostCaptureHook()
        handle.post = post
        handle._removables.append(module.register_forward_hook(post))
    return handle


def forward_with_spec(
    model: torch.nn.Module,
    module_name: str,
    model_input: torch.Tensor,
    spec: InterventionSpec,
    *,
    donor: Any = None,
    capture_post: bool = True,
) -> tuple[torch.Tensor, InterventionHandle]:
    """Un forward sous ``no_grad`` avec la spec attachee, hooks retires apres.

    Point d'entree independant de l'endpoint : le consommateur (notebook,
    extraction GPU) fournit le modele, le nom de module et l'entree ; le
    moteur applique et capture. Retourne (sortie du modele, poignee dont les
    captures survivent au detachement).
    """
    handle = attach_intervention(
        model, module_name, spec, donor=donor, capture_post=capture_post
    )
    try:
        with torch.no_grad():
            output = model(model_input)
    finally:
        handle.remove()
    return output, handle


# --------------------------------------------------------------------------- #
# Protocole interchange : capture-puis-ecriture
# --------------------------------------------------------------------------- #

class _SliceCaptureHook:
    """Pre-hook passif : stocke panneau + tranche cible d'un run (phase capture)."""

    def __init__(self, parent: "PairedInterchange", which: str) -> None:
        self.parent = parent
        self.which = which

    def __call__(
        self, module: torch.nn.Module, args: tuple[Any, ...]
    ) -> None:
        t = _first_tensor(args)
        if t is None:
            raise RuntimeError(
                f"aucun tensor dans les entrees de {type(module).__name__} "
                f"— capture interchange impossible"
            )
        _validate_shape(t, self.parent.spec)
        panel = t.detach().cpu().numpy().copy()
        self.parent.panels[self.which] = panel
        self.parent.slices[self.which] = _slice_of(panel, self.parent.spec)
        return None  # passthrough : la capture ne change RIEN au forward


class PairedInterchange:
    """Protocole capture-puis-ecriture pour l'operation interchange sur modele vivant.

    Un pre-hook voit chaque activation une fois par forward : un echange
    bilateral ne peut pas se jouer en un forward. Protocole en 4 forwards :

        cap_a = pair.capture("a")   # forward run A -> buffer (passthrough)
        cap_b = pair.capture("b")   # forward run B -> buffer (passthrough)
        wr_a  = pair.write("a")     # forward run A -> ecrit la tranche de B
        wr_b  = pair.write("b")     # forward run B -> ecrit la tranche de A

    Les hooks de capture s'enregistrent comme les autres
    (``module.register_forward_pre_hook(pair.capture("a"))``). Les hooks
    d'ecriture sont des :class:`InterventionHook` complets (panneaux avant/
    apres captes) donc ``hook_record`` fonctionne sur chaque cote de l'echange.
    Ecrire avant d'avoir capture les deux runs echoue avec un diagnostic nomme.
    """

    def __init__(self, spec: InterventionSpec) -> None:
        if spec.operation != "interchange":
            raise ValueError(
                f"PairedInterchange est le protocole d'interchange, pas de "
                f"{spec.operation!r}"
            )
        self.spec = spec
        self.slices: dict[str, np.ndarray] = {}
        self.panels: dict[str, np.ndarray] = {}

    def capture(self, which: str) -> _SliceCaptureHook:
        if which not in ("a", "b"):
            raise ValueError("which doit etre 'a' ou 'b'")
        return _SliceCaptureHook(self, which)

    def write(self, which: str) -> InterventionHook:
        if which not in ("a", "b"):
            raise ValueError("which doit etre 'a' ou 'b'")
        missing = [w for w in ("a", "b") if w not in self.slices]
        if missing:
            raise ValueError(
                f"protocole interchange : capture les DEUX runs avant d'ecrire "
                f"(captures manquantes: {missing})"
            )
        other = "b" if which == "a" else "a"
        return InterventionHook(self.spec, donor=self.slices[other])


# --------------------------------------------------------------------------- #
# Enregistrement sidecar depuis les captures du hook
# --------------------------------------------------------------------------- #

def hook_record(
    handle: InterventionHandle | InterventionHook,
    *,
    verdict: str = "",
    **alignment_extra: str,
) -> InterventionRecord:
    """Assemble un InterventionRecord sidecar depuis les captures d'un hook.

    Le dommage general et le verdict sont calcules par le coeur numpy sur les
    panneaux captes ; les empreintes couvrent les panneaux complets.
    L'enregistrement ne STOCKE pas les panneaux (ils vivent dans le trace store
    du contrat de trace). Requiert un panneau 2-D (T, d) — reduire au lot
    unitaire avant d'enregistrer un forward diffuse (B, T, d).
    """
    hook = handle.hook if isinstance(handle, InterventionHandle) else handle
    if hook.panel_before is None or hook.panel_after is None:
        raise ValueError(
            "aucune capture — attacher le hook et executer un forward AVANT "
            "d'enregistrer"
        )
    if hook.panel_before.ndim != 2:
        raise ValueError(
            f"enregistrement sidecar sur panneau (T, d) — panneau capture de "
            f"{hook.panel_before.ndim} dims : reduire au lot unitaire (B=1) "
            f"avant hook_record"
        )
    damage = damage_metrics(hook.panel_before, hook.panel_after, hook.spec)
    return InterventionRecord(
        spec=hook.spec,
        alignment=hook.spec.alignment(**alignment_extra),
        sha_before=artifact_sha256(hook.panel_before),
        sha_after=artifact_sha256(hook.panel_after),
        damage=damage,
        verdict=verdict or selectivity_verdict(damage),
    )
