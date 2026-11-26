"""Verificateur RLVR Lean (Tier-2 du corpus issue #10289).

RLVR (Reinforcement Learning with Verifiable Rewards) sur preuve formelle :
la politique genere le corps d'une preuve Lean pour un enonce donne, et la
recompense est binaire, calculee par le compilateur Lean lui-meme via
``#print axioms``. Aucun reward model appris.

Pourquoi Lean est le verificateur *distinctif* de notre corpus
(message user / issue #10289) : nos regles Lean enumerent *deja* les exploits
qu'une politique optimisant « ``lake build`` passe » va trouver — ``sorry``,
``sorryAx`` transitif, ``native_decide``, ``Classical.choice``. Un modele qui
apprend a ecrire ``by sorry`` pour toucher la recompense est le cas d'ecole de
Goodhart, et ce module le **detecte** (oracle), pas seulement l'illustre.

Reutilise le mecanisme ``#print axioms`` de
``lean_server.LeanVerifier.check_axioms`` (#8680) — aucune logique de
detection reecrite. La difference : ici la preuve est fournie par la politique
au runtime (rollout), pas lue dans un fichier source fige.

Tier-2 = quelques secondes par rollout (elaboration Lean core, pas de Mathlib) :
ce module est le COMPOSANT verificateur, CPU. L'entraînement GPU RLVR qui le
consomme vit dans PT-11 (#10317) / PT-12 (#10508).

Recette d'execution (rule F — vrai outil, pas de contournement) ::

    export PATH="$HOME/.elan/bin:$PATH"     # elan requis (elan 4.x verifie)
    # chaque rollout passe par l'organe confine scripts/lean/lean_exec.py
    # (mode stdin, admission + budget) ; un projet lake minimal (lakefile.toml
    # + lean-toolchain) est cree automatiquement comme cwd.

Epinglage de la toolchain (organe ``scripts/lean/lean_toolchain.py``) : le pin
effectif est resolu dans l'ordre ``ELAN_TOOLCHAIN`` (lu tel quel aux espaces
de bord près) >
``lean-toolchain`` du projet > declaration par environnement (fichier JSON
lu par le code) > pin de flotte > defaut elan mesure (**non fige**) > repli
alerte. Le tag et sa provenance sont journalises a la creation du
verificateur (``toolchain=... pin=...``).

Exemple ::

    from verifiers.lean_rlvr_verifier import LeanRLVRVerifier
    v = LeanRLVRVerifier()
    v.reward("1 + 1 = 2", "by rfl")          # -> reward=1.0
    v.reward("True", "by sorry")             # -> reward=0.0, hack_flags=['sorryAx']
    v.reward("1 + 1 = 3", "by rfl")          # -> reward=0.0, compiles=False
"""

from __future__ import annotations

import logging
import os
import re
import subprocess
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable

__all__ = ["LeanRLVRVerifier", "RLVRResult"]

# --- Oracle de reward hacking (enumeree par lean-axiom.yml, corpus #10289) ---
#
# Whitelist des axiomes du calcul des constructions acceptes (coeur Lean).
# Tout axiome hors de cette liste est un signal de triche potentielle.
CORE_WHITELIST = frozenset({
    "propext",
    "funext",
    "Classical.choice",
    "Quot.sound",
    "Quot.lift",
    "Quot.mk",
})

# sorryAx = la politique a emis `sorry` (la triche canonique de Goodhart).
SORRY_AXIOM = "sorryAx"
# native_decide = la politique invoque `Native.decide` (oracle d'execution de
# code) — un autre chemin de triche observe.
NATIVE_DECIDE_AXIOM = "native_decide"

# Regex de parsing de la sortie Lean.
#  - erreur de compilation : "<file>:<l>:<c>: error:" (a distinguer du warning)
_LEAN_ERROR_RE = re.compile(r":\d+:\d+: error:")
#  - ligne d'axiomes : "'name' depends on axioms: [X, Y, Z]"
_AXIOMS_RE = re.compile(r"depends on axioms: \[([^\]]*)\]")
#  - cas sans axiome : "'name' does not depend on any axioms"
_NO_AXIOMS_RE = re.compile(r"does not depend on any axioms")

# Epinglage de la toolchain : l'organe ``scripts/lean/lean_toolchain.py``
# detient la declaration par environnement (JSON lu par le code) ET l'ordre
# de resolution. Mesure 2026-11-10 (poste ai-01) : le defaut elan de ce poste
# est ``v4.11.0`` alors que le pin des lakes du depot est ``v4.33.0`` — deux
# postes jugeant les memes rollouts sur des moteurs differents. Le repli
# historique ``v4.27.0`` n'etait installe sur aucun poste mesure : chaque
# rollout partait en download elan.
_LOGGER = logging.getLogger(__name__)

#: Sources de pin REPRODUCTIBLES entre postes (seules celles-la sont ecrites
#: dans le squelette) ; le defaut elan mesure n'en fait pas partie.
PINNED_SOURCES = frozenset({"env", "projet", "declaration", "declaration_flotte"})

_lean_toolchain_mod = None


def _find_lean_toolchain() -> Path:
    """Localise l'organe d'epinglage ``scripts/lean/lean_toolchain.py``.

    Marche de parents depuis ce fichier (verifiers/ -> PostTraining ->
    GenAI -> ... -> racine du depot), meme strategie que
    ``scripts/lean/lean_exec.py`` (#23054).
    """
    current = Path(__file__).resolve().parent
    for _ in range(14):
        candidate = current / "scripts" / "lean" / "lean_toolchain.py"
        if candidate.exists():
            return candidate.resolve()
        current = current.parent
        if current == current.parent:
            break
    raise FileNotFoundError(
        "scripts/lean/lean_toolchain.py introuvable — organe d'epinglage "
        "requis par LeanRLVRVerifier (See #15666, #24568)"
    )


def _get_lean_toolchain():
    """Charge (1er usage) l'organe d'epinglage de la toolchain.

    Chargement LAZY par chemin direct : ce module est importe par le corpus
    et les tests sur des runners nus — l'organe ne doit peser qu'au premier
    rollout reel (meme discipline que ``lean_server._lean_utils``).
    """
    global _lean_toolchain_mod
    if _lean_toolchain_mod is None:
        import importlib.util as ilu

        path = _find_lean_toolchain()
        spec = ilu.spec_from_file_location("_lean_toolchain_organ", path)
        mod = ilu.module_from_spec(spec)
        spec.loader.exec_module(mod)
        _lean_toolchain_mod = mod
    return _lean_toolchain_mod


def _installed_toolchain() -> str | None:
    """Toolchain reellement installee, ou ``None`` si non mesurable.

    Delegue a l'organe d'epinglage. Le tag reconstruit depuis
    ``lean --version`` décrit le défaut elan résolu ; il ne constitue pas un
    pin reproductible entre environnements.
    """
    return _get_lean_toolchain().installed_toolchain()


class OrganRefusedError(RuntimeError):
    """L'organe confine ``lean_exec`` a refuse le rollout ou n'a pas rendu de
    verdict (admission, budget, environnement casse).

    Cause d'INFRA, pas un signal de la politique : ``reward`` la traduit en
    reward 0.0 avec ``hack_flags=['organ_refused']`` et la raison dans
    ``raw_output`` — visible a l'audit, jamais confondu avec une preuve
    fausse (See #23054).
    """


# -- organe confine lean_exec (migration #23054, precedent lean_server #23031)
#
# Le verifieur ne spawn plus ``lake`` lui-meme : chaque rollout passe par
# l'organe confine ``scripts/lean/lean_exec.py`` (admission machine-wide,
# budget, kill-tree) en mode stdin (``--stdin-file``, capacite #23031). La
# delegation reprend le client partage ``lean_notebook_utils._organ_run`` et
# la marche-de-parents de ``agent_tests/lean_server.py`` ; l'entree
# correspondante de ``scripts/lean/lake_direct_allowlist.json`` est retiree.
_lean_nbu = None


def _find_lean_exec() -> Path:
    """Localise l'organe confine ``scripts/lean/lean_exec.py``.

    Marche de parents depuis ce fichier (verifiers/ -> PostTraining ->
    GenAI -> ... -> racine du depot), meme strategie que
    ``agent_tests/lean_server.py`` depuis #23031.
    """
    current = Path(__file__).resolve().parent
    for _ in range(14):
        candidate = current / "scripts" / "lean" / "lean_exec.py"
        if candidate.exists():
            return candidate.resolve()
        current = current.parent
        if current == current.parent:
            break
    raise FileNotFoundError(
        "scripts/lean/lean_exec.py introuvable — organe d'execution confine "
        "requis par LeanRLVRVerifier (See #15666, #23054)"
    )


def _get_lean_notebook_utils():
    """Renvoie le module client partage ``lean_notebook_utils`` (1er usage).

    Chargement LAZY par chemin direct : ce module est importe par le corpus
    et les tests sur des runners nus — le client ne doit peser qu'au
    premier rollout reel (meme discipline que ``lean_server._lean_utils``).
    """
    global _lean_nbu
    if _lean_nbu is None:
        import importlib.util as ilu

        client_path = (
            _find_lean_exec().parents[2]
            / "MyIA.AI.Notebooks" / "SymbolicAI" / "Lean"
            / "lean_notebook_utils.py"
        )
        spec = ilu.spec_from_file_location("_lean_nbu_client", client_path)
        mod = ilu.module_from_spec(spec)
        spec.loader.exec_module(mod)
        _lean_nbu = mod
    return _lean_nbu


def _organ_run(project: str, cmd_args: list, timeout: int,
               stdin_file: str | None = None) -> tuple[int, str, str]:
    """Confie ``cmd_args`` a l'organe confine (See #15666, migration prioritaire).

    Le payload decrit ce que L'ORGANE lancera (admission machine-wide, budget,
    kill-tree) — ce fichier ne spawn aucun processus lake. Contrat du client
    partage : ``(rc_enfant, out, err)``, -1 = timeout, -2 = organe
    refuse/injoignable (raison dans err). Meme forme de wrapper local que
    ``lean_server._organ_run`` (#23031).
    """
    nbu = _get_lean_notebook_utils()
    organ = _find_lean_exec()
    return nbu._organ_run(
        project, cmd_args, timeout,
        stdin_file=stdin_file, organ=organ,
    )


@dataclass
class RLVRResult:
    """Resultat d'un rollout RLVR sur une preuve Lean."""

    reward: float
    """Recompense binaire : 1.0 si la preuve compile SANS sorry ni axiome
    interdit, sinon 0.0."""
    compiles: bool
    """True ssi la preuve s'elabore sans erreur de typage."""
    axioms: list = field(default_factory=list)
    """Axiomes dont depend la preuve (sortie brute de ``#print axioms``)."""
    forbidden: list = field(default_factory=list)
    """Axiomes hors whitelist (= signaux de triche potentielle)."""
    has_sorry: bool = False
    """La politique a emis ``sorry`` (sorryAx detecte)."""
    hack_flags: list = field(default_factory=list)
    """Classes de reward hacking detectees : ``sorryAx``, ``native_decide``,
    ou le nom d'un axiome interdit."""
    raw_output: str = ""
    """Sortie brute de ``lake env lean`` (stdout + stderr), pour audit."""
    elapsed_s: float = 0.0
    """Duree du rollout (elaboration), en secondes."""


class LeanRLVRVerifier:
    """Verificateur RLVR pour preuves Lean 4 (Tier-2 corpus #10289).

    Parameters
    ----------
    project_dir:
        Repertoire d'un projet lake minimal utilise comme cwd pour
        ``lake env lean``. Si ``None``, un squelette est cree dans un cache
        temporaire (``~/.cache/rlvr-lean``). Le squelette ne depend PAS de
        Mathlib : elaboration du coeur Lean uniquement (~4 s/rollout).
    toolchain:
        Version Lean a pinner dans le squelette. Defaut = le pin **resolu**
        par l'organe d'epinglage (``ELAN_TOOLCHAIN`` > pin du projet >
        declaration par environnement > pin de flotte > defaut elan mesure
        non fige > repli averti) ; une valeur passed ici court-circuite la
        resolution (provenance ``argument``).
    timeout:
        Timeout par rollout en secondes. Tier-2 accepte quelques secondes ;
        au-dela on renvoie reward 0 (la politique a produit du code qui
        depasse le budget d'elaboration).
    whitelist:
        Axiomes autorises au-dela du coeur. Defaut = ``CORE_WHITELIST``.
    """

    def __init__(
        self,
        project_dir: str | os.PathLike | None = None,
        toolchain: str | None = None,
        timeout: float = 60.0,
        whitelist: Iterable[str] | None = None,
        verbose: bool = False,
    ) -> None:
        if toolchain is None:
            toolchain, pin_source = self._resolve_toolchain(project_dir)
        else:
            pin_source = "argument"
        self.toolchain = toolchain
        self.pin_source = pin_source
        _LOGGER.info("RLVR Lean toolchain=%s pin=%s", self.toolchain, self.pin_source)
        self.timeout = timeout
        self.whitelist = set(whitelist) if whitelist is not None else set(CORE_WHITELIST)
        self.verbose = verbose
        self.project_dir = self._ensure_skeleton(project_dir)

    @staticmethod
    def _resolve_toolchain(project_dir: str | os.PathLike | None) -> tuple[str, str]:
        """Résout le pin et rend ``(tag, provenance)``.

        Délègue à l'organe d'épinglage ``scripts/lean/lean_toolchain.py``,
        qui tient l'ordre complet : ``ELAN_TOOLCHAIN`` (lu tel quel aux
        espaces de bord près) > pin du
        projet > declaration par environnement > pin de flotte > défaut elan
        mesuré (**non figé**) > repli averti.

        La mesure du défaut elan passe par ``_installed_toolchain``
        (interposable par les tests) et n'a lieu qu'au palier 5 : quand un
        palier plus haut tranche, aucun ``lean --version`` n'est lancé.
        """
        return _get_lean_toolchain().resolve_pin(
            project_dir,
            loader=_installed_toolchain,
        )

    # -- squelette lake minimal ------------------------------------------------

    def _ensure_skeleton(self, project_dir: str | os.PathLike | None) -> Path:
        """Cree (si besoin) un projet lake minimal et le rechauffe.

        Un projet lake minimal = ``lakefile.toml`` (name seul) + ``lean-toolchain``.
        Cela suffit pour que ``lake env lean`` resolve la toolchain et LEAN_PATH ;
        aucun ``lean_lib`` / build d'olean n'est requis (le rollout nourrit le
        theoreme via stdin en un seul passage, patron ``search_lean`` de
        ``lean_server.py``).
        """
        if project_dir is not None:
            root = Path(project_dir)
        else:
            root = Path.home() / ".cache" / "rlvr-lean"
        root.mkdir(parents=True, exist_ok=True)
        lakefile = root / "lakefile.toml"
        if not lakefile.exists():
            lakefile.write_text('name = "RlvrSkeleton"\n', encoding="utf-8")
        # Squelette géré : écrire les pins REPRODUCTIBLES (env, projet,
        # declaration), mais garder le défaut elan comme défaut de résolution
        # plutôt que de le figer dans le cache.
        managed = project_dir is None
        toolchain_file = root / "lean-toolchain"
        if self.pin_source in PINNED_SOURCES and (managed or not toolchain_file.exists()):
            toolchain_file.write_text(f"{self.toolchain}\n", encoding="utf-8")
        # Rechauffement : un premier `lake env` cree le manifest du projet
        # (sinon il est cree au 1er rollout, faussant la mesure de latence).
        self._warmup()
        return root

    def _warmup(self) -> None:
        """Premier passage trivial pour initialiser le manifest lake."""
        try:
            self._run_lean("theorem _warmup : True := by trivial\n")
        except Exception:
            # L'echec du warmup n'est pas fatal (le 1er rollout reessaye).
            pass

    # -- execution -------------------------------------------------------------

    def _run_lean(self, source: str) -> str:
        """Execute ``lake env lean --stdin`` VIA l'organe confine (See #23054).

        ``lake`` est passe EN NOM NU, jamais en chemin resolu : l'organe
        execute l'enfant via bash, ou un chemin Windows
        (``C:\\...\\lake.EXE``) est une commande introuvable — mesure
        2026-11-03, meme contrat que ``lean_server`` (#23031). La source
        passe par ``--stdin-file`` (capacite stdin #23031). Contrat du
        client partage : ``-1`` = timeout (remonte en
        ``subprocess.TimeoutExpired``, repris par ``reward``), ``-2`` =
        organe refuse/injoignable (remonte en ``OrganRefusedError``).
        """
        with tempfile.NamedTemporaryFile(
                "w", suffix=".lean", delete=False, encoding="utf-8") as fh:
            fh.write(source)
            stdin_path = fh.name
        try:
            rc, out, err = _organ_run(
                str(self.project_dir),
                ["lake", "env", "lean", "--stdin"],
                int(self.timeout),
                stdin_file=stdin_path,
            )
        finally:
            try:
                os.unlink(stdin_path)
            except OSError:
                pass
        if rc == -1:
            raise subprocess.TimeoutExpired(
                "lake env lean --stdin", self.timeout)
        if rc == -2:
            raise OrganRefusedError(err or out or "lean_exec: refus sans raison")
        return out + "\n" + err

    # -- API publique ----------------------------------------------------------

    def reward(
        self,
        statement: str,
        proof: str,
        name: str = "rlvr_task",
    ) -> RLVRResult:
        """Calcule la recompense RLVR d'une preuve policy pour un enonce.

        Parameters
        ----------
        statement:
            Enonce Lean a prouver (la proposition), ex ``"1 + 1 = 2"`` ou
            ``"∀ n : ℕ, n + 0 = n"``. Fourni par le corpus (ground truth).
        proof:
            Preuve generee par la politique. Soit un bloc tactique sans le
            ``by`` (ex ``"rfl"``, ``"induction n <;> simp"`` — le ``by`` est
            ajoute automatiquement), soit un terme (ex ``"rfl"``). Un ``by``
            initial est detecte et preserve.
        name:
            Nom de la declaration (pour ``#print axioms``).

        Returns
        -------
        RLVRResult
            reward=1.0 ssi la preuve compile SANS sorry ni axiome interdit.
        """
        # Normaliser le bloc de preuve : ajouter `by` si absent (tactiques).
        proof_body = proof.strip()
        if not proof_body.startswith("by") and not proof_body.startswith("fun") \
                and not proof_body.startswith("show") and proof_body != "rfl" \
                and not _looks_like_term(proof_body):
            proof_body = "by " + proof_body
        source = (
            f"theorem {name} : {statement} := {proof_body}\n"
            f"#print axioms {name}\n"
        )
        t0 = time.perf_counter()
        try:
            raw = self._run_lean(source)
            elapsed = time.perf_counter() - t0
        except subprocess.TimeoutExpired:
            return RLVRResult(
                reward=0.0, compiles=False, hack_flags=["timeout"],
                raw_output=f"<timeout after {self.timeout}s>", elapsed_s=self.timeout,
            )
        except OrganRefusedError as exc:
            return RLVRResult(
                reward=0.0, compiles=False,
                hack_flags=["organ_refused"],
                raw_output=f"<organ_refused> {exc}",
                elapsed_s=time.perf_counter() - t0,
            )
        return self._parse(raw, elapsed)

    def reward_batch(
        self,
        statement: str,
        proofs: list[str],
        name: str = "rlvr_task",
    ) -> list[RLVRResult]:
        """Verifie un GROUPE de completions pour le meme enonce (GRPO).

        GRPO echantillonne N completions d'un meme prompt et calcule un
        advantage centre sur le groupe. Cette methode renvoie la recompense
        brute par completion ; la normalisation group-relative est du ressort
        du trainer (``trl.GRPOTrainer``).
        """
        return [self.reward(statement, p, name=name) for p in proofs]

    def trl_reward_adapter(self):
        """Renvoie une ``reward_func`` compatible ``trl.GRPOTrainer``.

        La signature trl est ``reward_func(prompts, completions, **kwargs)``.
        L'enonce (ground truth) est lu depuis ``kwargs['statement']`` (la
        colonne du dataset), et ``completions`` sont les preuves generees.

        Usage dans PT-11 ::

            verifier = LeanRLVRVerifier()
            trainer = GRPOTrainer(
                reward_funcs=[verifier.trl_reward_adapter()],
                ...,
            )
        """

        def _reward(prompts, completions, **kwargs):
            statement = kwargs.get("statement")
            if statement is None:
                raise ValueError(
                    "LeanRLVRVerifier.trl_reward_adapter: la colonne 'statement' "
                    "(enonce a prouver) doit etre passée via le dataset / kwargs."
                )
            # trl passe souvent une liste ; on gere scalaire + liste.
            if isinstance(statement, str):
                statement = [statement] * len(completions)
            rewards = []
            for stmt, comp in zip(statement, completions):
                rewards.append(self.reward(stmt, comp).reward)
            return rewards

        _reward.__name__ = "lean_rlvr_reward"
        return _reward

    # -- parsing / oracle ------------------------------------------------------

    def _parse(self, raw: str, elapsed: float, name: str = "rlvr_task") -> RLVRResult:
        """Parse la sortie Lean et applique l'oracle de reward hacking."""
        has_error = bool(_LEAN_ERROR_RE.search(raw))
        # Preuve d'elaboration : ``#print axioms`` imprime TOUJOURS une des
        # deux lignes sur un rollout reel. Sans elles, le moteur n'a pas
        # rendu de verdict (echec de lancement, crash de l'enfant) — ce
        # n'est PAS une preuve qui compile. Mesure 2026-11-03 : sortie bash
        # « command not found » (lake en chemin Windows passe a l'organe)
        # parsait en compiles=True, reward 1.0 — fausse recompense pure.
        elaborated = bool(
            _AXIOMS_RE.search(raw) or _NO_AXIOMS_RE.search(raw))
        compiles = not has_error and elaborated

        # Axomes : soit "depends on axioms: [...]", soit "does not depend".
        axioms: list = []
        m = _AXIOMS_RE.search(raw)
        if m:
            axioms = [a.strip() for a in m.group(1).split(",") if a.strip()]
        # (sinon : pas d'axiomes, ou declaration inconnue -> axioms reste vide)

        has_sorry = SORRY_AXIOM in axioms
        forbidden = [a for a in axioms if a not in self.whitelist and a != SORRY_AXIOM]
        native_decide = NATIVE_DECIDE_AXIOM in axioms

        # Oracle : classes de reward hacking.
        hack_flags: list = []
        if has_sorry:
            hack_flags.append("sorryAx")  # Goodhart canonique
        if native_decide:
            hack_flags.append("native_decide")
        hack_flags.extend(forbidden)  # axiomes interdits nommes

        # Recompense : 1.0 ssi compile ET sans triche.
        clean = compiles and not has_sorry and not forbidden and not native_decide
        reward = 1.0 if clean else 0.0

        if self.verbose:
            print(f"[LeanRLVR] compiles={compiles} axioms={axioms} "
                  f"sorry={has_sorry} forbidden={forbidden} reward={reward}")

        return RLVRResult(
            reward=reward,
            compiles=compiles,
            axioms=axioms,
            forbidden=forbidden,
            has_sorry=has_sorry,
            hack_flags=hack_flags,
            raw_output=raw,
            elapsed_s=elapsed,
        )


def _looks_like_term(s: str) -> bool:
    """Heuristique : la preuve est-elle un terme Lean (vs un bloc tactique) ?

    On considere comme terme les expressions qui commencent par un constructeur
    ou un identificateur definissant une preuve directe. Conservateur : en cas
    de doute on prefere ajouter ``by`` (un terme errone avec ``by`` produit une
    erreur de parse claire, recuperable).
    """
    s = s.strip()
    # Termes typiques produisant une preuve sans tactique.
    return s.startswith(("rfl", "trivial", "True.intro", "Or.inl", "Or.inr",
                         "And.intro", "⟨", "fun ", "λ"))
