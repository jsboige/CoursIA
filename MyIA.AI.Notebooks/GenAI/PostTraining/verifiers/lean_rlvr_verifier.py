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

Execution (rule F — vrai outil, pas de contournement) : chaque rollout est
confie a l'organe canonique ``scripts/lean/lean_exec.py`` (See #15666, case
1/7 de l'epic) via le client partage ``lean_notebook_utils._organ_run`` —
admission machine-wide, budget, kill-tree, backend epingle par lake. Un
projet lake minimal (lakefile.toml + lean-toolchain) est cree automatiquement
comme cwd ; chaque rollout nourrit un theoreme via ``lake env lean --stdin``.
elan reste requis (elan 4.x verifie), natif ou WSL selon l'epinglage de
l'organe pour le squelette.

Exemple ::

    from verifiers.lean_rlvr_verifier import LeanRLVRVerifier
    v = LeanRLVRVerifier()
    v.reward("1 + 1 = 2", "by rfl")          # -> reward=1.0
    v.reward("True", "by sorry")             # -> reward=0.0, hack_flags=['sorryAx']
    v.reward("1 + 1 = 3", "by rfl")          # -> reward=0.0, compiles=False
"""

from __future__ import annotations

import os
import re
import subprocess
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable

__all__ = ["LeanRLVRVerifier", "RLVRResult"]

# --- Client partage de l'organe confine (#15666, case 1/7) ------------------
#
# Charge LAZILY par chemin direct, meme discipline que lean_server.py (#8722) :
# aucun import de package au chargement du module, le client ne pese qu'au
# premier rollout reel. La serie SymbolicAI/Lean possede le client
# (organ-first : on l'invoque, on ne le reimplante pas).
_lean_nbu = None
_LEAN_NOTEBOOK_UTILS_PATH = (
    Path(__file__).resolve().parents[3]
    / "SymbolicAI" / "Lean" / "lean_notebook_utils.py"
)


def _get_lean_client():
    """Return le module client ``lean_notebook_utils``, charge au 1er usage."""
    global _lean_nbu
    if _lean_nbu is None:
        import importlib.util as ilu

        spec = ilu.spec_from_file_location(
            "_lean_nbu_client", _LEAN_NOTEBOOK_UTILS_PATH)
        mod = ilu.module_from_spec(spec)
        spec.loader.exec_module(mod)
        _lean_nbu = mod
    return _lean_nbu


def _find_lean_exec() -> Path:
    """Localise l'organe canonique ``scripts/lean/lean_exec.py``.

    Marche des parents depuis ce fichier (verifiers/ -> PostTraining -> GenAI
    -> ... -> racine du depot), meme strategie que lean_server.py.
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
        "requis par LeanRLVRVerifier (See #15666)"
    )


def _organ_run(project_path: str, cmd_args: list, timeout: float,
               stdin_file: str | None = None) -> tuple:
    """Confie ``cmd_args`` a l'organe confine (See #15666, case 1/7).

    Le payload decrit ce que L'ORGANE lancera (admission machine-wide, budget,
    kill-tree, backend epingle) — ce fichier ne spawn aucun processus lake.
    Contrat du client partage : ``(rc_enfant, out, err)``, -1 = timeout, -2 =
    organe refuse/injoignable (raison dans err).
    """
    return _get_lean_client()._organ_run(
        project_path, cmd_args, timeout,
        stdin_file=stdin_file, organ=_find_lean_exec(),
    )

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

# Toolchain pinnee (presente sur po-2025 ; regle F verifiee firsthand).
DEFAULT_TOOLCHAIN = "leanprover/lean4:v4.27.0"


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
        Version Lean a pinner dans le squelette. Defaut = toolchain presente
        sur le runner (regle F : on pinne ce qui est installe, pas un tag
        qui forcerait un download).
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
        toolchain: str = DEFAULT_TOOLCHAIN,
        timeout: float = 60.0,
        whitelist: Iterable[str] | None = None,
        verbose: bool = False,
    ) -> None:
        self.toolchain = toolchain
        self.timeout = timeout
        self.whitelist = set(whitelist) if whitelist is not None else set(CORE_WHITELIST)
        self.verbose = verbose
        self._elan_bin = str(Path.home() / ".elan" / "bin")
        self.project_dir = self._ensure_skeleton(project_dir)

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
        toolchain_file = root / "lean-toolchain"
        if not toolchain_file.exists():
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
        """Execute ``lake env lean --stdin`` sur une source, retourne la sortie.

        Migration #15666 (case 1/7) : le lancement est confie a l'organe
        confine via le client partage (``_organ_run``) — admission
        machine-wide, budget, kill-tree, backend epingle par lake. La source
        passe par un fichier branche sur l'entree standard de l'enfant confine
        (capacite stdin de l'organe, meme mecanisme que ``check_axioms`` de
        lean_server.py).

        Timeout organe -> ``subprocess.TimeoutExpired``, contrat historique de
        ``reward()``. Refus organe (cap sature, telemetrie illisible, backend
        indisponible) -> ``RuntimeError`` visible : une panne d'infrastructure
        n'est JAMAIS un reward 0.0 — ce serait enseigner a la politique qu'une
        preuve valide ne vaut rien (empoisonnement du gradient, #10289).
        """
        snippet_f = tempfile.NamedTemporaryFile(
            "w", delete=False, suffix=".lean", encoding="utf-8")
        snippet_f.write(source)
        snippet_f.close()
        try:
            # Backend natif : l'organe herite de l'environ de CE processus (le
            # client n'a pas de pass-through d'env), donc elan doit etre visible
            # ici pour l'etre la-bas. Mutation scopee, restauree ; sous WSL le
            # shell de login voit deja ~/.elan/bin (mesure po-2026, lean_exec.py).
            old_path = os.environ.get("PATH", "")
            if self._elan_bin not in old_path:
                os.environ["PATH"] = self._elan_bin + os.pathsep + old_path
            try:
                rc, out, err = _organ_run(
                    str(self.project_dir), ["lake", "env", "lean", "--stdin"],
                    self.timeout, stdin_file=snippet_f.name,
                )
            finally:
                os.environ["PATH"] = old_path
        finally:
            try:
                Path(snippet_f.name).unlink()
            except OSError:
                pass
        if rc == -1:
            raise subprocess.TimeoutExpired(
                cmd="lake env lean --stdin", timeout=self.timeout)
        if rc == -2:
            raise RuntimeError(
                f"lean_exec refused rollout: {err or '(no reason)'} (See #15666)"
            )
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
        compiles = not has_error

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
