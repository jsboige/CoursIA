"""Pont Python des preuves Lean AMD et Groves (jalon 3 de #22381).

Ce que ce module relie
----------------------

Deux jalons de #22381 existent separement :

- **jalon 1** (`amd_synthesis.py`) : une synthese globale DSIC-IR par CP-SAT et un
  **verificateur independant** (`verify`) qui ne partage ni utilite ni contraintes
  avec le constructeur ;
- **jalon 2** (`game_theory_lean/SocialChoice/Groves.lean`) : les theoremes de
  Groves et de Clarke, plus un temoin negatif, prouves par le noyau Lean sur un
  domaine abstrait.

Aucun des deux ne dit ce que l'autre fait. Ce module est le pont : il **extrait**
les declarations du `.lean` (le fichier Lean reste la source de verite), il
**rejoue** les instances formelles en Python, et il **compare** le verdict du
verificateur independant a l'enonce transcrit. Le pont est **verrouille** sur
l'etat du `.lean` : une transcription dont l'empreinte ne correspond plus est
signalee comme derive, jamais silencieusement acceptee.

Ce que le pont n'est pas
------------------------

Ce n'est **pas** une preuve. Une preuve Lean certifie son enonce sur son domaine,
pour toujours ; le pont rejoue une **instance** et constate qu'elle est coherente
avec l'enonce. Un ecart entre les deux fait echouer `ensure_conforms` — c'est un
detecteur de divergence, pas un certificat. Chaque instance porte explicitement,
dans `BridgeInstance.not_certified`, ce que le theoreme cite **ne certifie pas**.

La convention de signe, qui n'est pas la meme dans les deux modules Lean
-----------------------------------------------------------------------

- `AMD.lean` : `u = thetaVal t * issueVal (o r) - p r`, le paiement est **paye**
  par l'agent. C'est exactement la convention de `amd_synthesis`
  (`u = values - payments`), donc la traduction est directe.
- `Groves.lean` : `payoff = v + grovesPayment`, le transfert est **recu** par
  l'agent. Pour l'exprimer dans `amd_synthesis`, il faut inverser le signe :
  `payment_i(r) = -grovesPayment_i(r)`. Ce n'est pas une commodite d'ecriture,
  c'est le point ou une traduction naive se tromperait de signe : les tests
  mesurent l'inversion profil par profil, et le temoin negatif reproduit
  **exactement** les nombres de `Groves.lean` (utilite sincere 0, deviation 2)
  qui ne tombent juste que sous cette convention.

Voir #22381 (critere 6 : reproduire le temoin booleen et les memes utilites ;
critere 7 : tests reproductibles et resultats falsifiables), jalon 1 PR #22391,
jalon 2 PR #22686.
"""

from __future__ import annotations

import hashlib
import itertools
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Iterable, Mapping, Sequence

sys.path.insert(0, str(Path(__file__).resolve().parent))

from amd_synthesis import (  # noqa: E402
    FiniteDomain,
    Mechanism,
    Violation,
    amd_domain,
    amd_star_mechanism,
    best_by_enumeration,
    synthesize,
    verify,
    verify_dsic_sincere_anchored,
    verify_ir_sincere,
    verify_utility,
)

LEAN_DIR = Path(__file__).resolve().parent / "game_theory_lean" / "SocialChoice"
AMD_LEAN = LEAN_DIR / "AMD.lean"
GROVES_LEAN = LEAN_DIR / "Groves.lean"


# ---------------------------------------------------------------------------
# Extraction structurelle des declarations Lean
#
# Un analyseur complet de Lean n'est ni disponible ni necessaire : ce dont le
# pont a besoin, c'est le texte normalise de chaque declaration et l'enonce qui
# la termine. Trois operations suffisent, et chacune est verifiee par un test :
# retirer les commentaires (blocs imbriques compris), suivre la pile de
# namespaces, decouper aux mots-cles de declaration.
# ---------------------------------------------------------------------------

_DECL_START = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:(?:noncomputable|private|protected|partial|unsafe)\s+)*"
    r"(theorem|lemma|def|abbrev)\s+([A-Za-z_][A-Za-z0-9_'.]*)"
)
_NAMESPACE = re.compile(r"^namespace\s+(\S+)\s*$")
_END = re.compile(r"^end(?:\s+(\S+))?\s*$")


def strip_lean_comments(source: str) -> str:
    """Retire les commentaires Lean en conservant la structure de lignes.

    Les blocs `/- ... -/` sont **imbriques** en Lean (`/-! ... /- ... -/ ... -/`),
    d'ou le compteur de profondeur. Les sauts de ligne traverses sont recopies
    tels quels : sans cela, retirer un commentaire collerait deux declarations
    sur une meme ligne et fausserait le decoupage.

    **Limite connue** : les litteraux de chaine (`"..."`) ne sont pas traites —
    un `--` ou un `/-` a l'interieur d'une chaine casserait le decoupage.
    Mesure sur le corpus vise : `AMD.lean` ne contient aucune chaine (0
    occurrence de `"`), et un fichier de preuves n'a pas de raison d'en
    introduire.
    """
    out: list[str] = []
    depth = 0
    i = 0
    n = len(source)
    while i < n:
        if depth == 0 and source.startswith("/-", i):
            depth = 1
            i += 2
            continue
        if depth > 0:
            if source.startswith("/-", i):
                depth += 1
                i += 2
                continue
            if source.startswith("-/", i):
                depth -= 1
                i += 2
                continue
            if source[i] == "\n":
                out.append("\n")
            i += 1
            continue
        if source.startswith("--", i):
            j = source.find("\n", i)
            i = n if j == -1 else j
            continue
        out.append(source[i])
        i += 1
    if depth != 0:
        raise ValueError("commentaire de bloc non ferme dans la source Lean")
    return "".join(out)


def _normalise(text: str) -> str:
    """Normalise les espaces : la transcription ne depend pas du formatage ni du CRLF."""
    return " ".join(text.split())


_OPENERS = "([{⟨"
_CLOSERS = ")]}⟩"


def _statement_of(declaration: str) -> str:
    """Enonce d'une declaration : ce qui suit le `:` de tete, ou le corps d'un `:=` nu.

    Pour `theorem foo (h : P) : Q := by ...`, l'enonce est `Q`. La detection du
    `:` de tete se fait par profondeur de parentheses : les `:` des binders sont
    a une profondeur strictement positive, et un `:=` n'est jamais confondu avec
    un `:`.

    Pour `abbrev X := Y` (sans type annonce), l'enonce est `Y`.
    """
    depth = 0
    colon = -1
    i = 0
    while i < len(declaration):
        ch = declaration[i]
        if ch in _OPENERS:
            depth += 1
        elif ch in _CLOSERS:
            depth = max(0, depth - 1)
        elif ch == ":" and depth == 0:
            if declaration.startswith(":=", i):
                body = declaration[i + 2 :]
                if colon < 0:
                    return _normalise(body)
                return _normalise(declaration[colon + 1 : i])
            if colon < 0:
                colon = i
        i += 1
    if colon < 0:
        return ""
    return _normalise(declaration[colon + 1 :])


@dataclass(frozen=True)
class LeanDeclaration:
    """Une declaration extraite d'un fichier Lean, avec son empreinte."""

    kind: str
    name: str
    namespace: str
    text: str
    statement: str

    @property
    def qualified_name(self) -> str:
        return f"{self.namespace}.{self.name}" if self.namespace else self.name

    @property
    def digest(self) -> str:
        return hashlib.sha256(_normalise(self.text).encode("utf-8")).hexdigest()


def parse_lean_declarations(source: str) -> dict[str, LeanDeclaration]:
    """Decoupe une source Lean en declarations, indexees par nom qualifie.

    Le decoupage est volontairement minimal : une declaration court du mot-cle
    jusqu'a la prochaine declaration, ou jusqu'a un changement de namespace. Un
    fichier qui imbriquerait des declarations (Lean ne le permet pas) serait
    mal lu — c'est une limite assumee, verifiee par le test des instances
    attendues.
    """
    cleaned = strip_lean_comments(source)
    namespace: list[str] = []
    found: dict[str, LeanDeclaration] = {}
    pending: list[str] = []
    pending_kind = ""
    pending_name = ""
    pending_ns = ""

    def flush() -> None:
        nonlocal pending, pending_kind, pending_name, pending_ns
        if not pending_kind:
            return
        text = "\n".join(pending)
        declaration = LeanDeclaration(
            kind=pending_kind,
            name=pending_name,
            namespace=pending_ns,
            text=text,
            statement=_statement_of(text),
        )
        if declaration.qualified_name in found:
            raise ValueError(f"declaration dupliquee : {declaration.qualified_name}")
        found[declaration.qualified_name] = declaration
        pending = []
        pending_kind = ""

    for raw in cleaned.splitlines():
        stripped = raw.strip()
        match = _DECL_START.match(raw)
        ns = _NAMESPACE.match(stripped)
        end = _END.match(stripped)
        if ns:
            flush()
            namespace.append(ns.group(1))
            continue
        if end:
            flush()
            if namespace:
                namespace.pop()
            continue
        if match:
            flush()
            pending_kind = match.group(1)
            pending_name = match.group(2)
            pending_ns = ".".join(namespace)
            pending = [raw]
            continue
        if pending_kind:
            pending.append(raw)
    flush()
    return found


# ---------------------------------------------------------------------------
# Transcription verrouillee sur l'etat du .lean
#
# Les empreintes ci-dessous ne sont pas une seconde source de verite : elles
# sont la photographie de la source au moment ou le pont a ete ecrit. Un ecart
# signifie « la preuve a bouge, la transcription doit etre mise a jour et le
# pont revalide » — jamais « la preuve est fausse ». Regeneration :
#
#     python amd_lean_bridge.py --dump-transcription AMD
#     python amd_lean_bridge.py --dump-transcription Groves
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class TranscriptionEntry:
    """Enonce transcrit et empreinte de la declaration dont il vient."""

    kind: str
    digest: str
    statement: str


TRANSCRIPTION_AMD: Mapping[str, TranscriptionEntry] = {
    "SocialChoice.AMD.AgentType": TranscriptionEntry(
        kind="abbrev",
        digest="91eadb9ad5f7042db138678ba40cf67ee030fc88b9055e3c0fe2e7787748d083",
        statement="Bool",
    ),
    "SocialChoice.AMD.Profile": TranscriptionEntry(
        kind="abbrev",
        digest="c3a6c233765ccd1877c50d51244c9af76df08de0ae47b0788effc34f0458644b",
        statement="Bool × Bool",
    ),
    "SocialChoice.AMD.thetaVal": TranscriptionEntry(
        kind="def",
        digest="92e3f25c4d557ab60047935103c720a2f526d88bf62603808589b3b4348f7e7a",
        statement="ℤ",
    ),
    "SocialChoice.AMD.issueVal": TranscriptionEntry(
        kind="def",
        digest="4377a62b5ac90c0f13f8e91516aacbecb57100fc0bc71afe69c16af683b83524",
        statement="ℤ",
    ),
    "SocialChoice.AMD.u0": TranscriptionEntry(
        kind="def",
        digest="542a688c5fcfa523b758ebeaf1ba39eaae62abbc1e9e614ab637bb37491986bb",
        statement="ℤ",
    ),
    "SocialChoice.AMD.u1": TranscriptionEntry(
        kind="def",
        digest="8b0ce11c551431ebea1cdc6bfbfc9f6ad7067f71be77bf5f006a5dc3a5a8c18a",
        statement="ℤ",
    ),
    "SocialChoice.AMD.DSIC": TranscriptionEntry(
        kind="def",
        digest="697c8eb1cf6076a786a5af41db0885fe160570949dc9e477c7b936bad305ffa6",
        statement="Prop",
    ),
    "SocialChoice.AMD.IR": TranscriptionEntry(
        kind="def",
        digest="590057f2a3fc25ff18cd1d446990a49e859f3ea6c11fea3ed4f4cd7436e6119c",
        statement="Prop",
    ),
    "SocialChoice.AMD.J": TranscriptionEntry(
        kind="def",
        digest="099a1d952fadf231c284fc5367b55d339fd13c433b540dde5c82e129adcd271f",
        statement="ℤ",
    ),
    "SocialChoice.AMD.o_star": TranscriptionEntry(
        kind="def",
        digest="98feb24be29c9fac58b5e35247dca39bb7ec11231b42d2e9ac2a4bf2bc3ab5fa",
        statement="Bool",
    ),
    "SocialChoice.AMD.p_star": TranscriptionEntry(
        kind="def",
        digest="f56b6f64f37f051ede80b5732aa4e7ec74edf4a5485a8283dc7f19b7dec96420",
        statement="ℤ",
    ),
    "SocialChoice.AMD.amd_star_DSIC": TranscriptionEntry(
        kind="theorem",
        digest="c2de941fdbf3d0081384d2ead26884d665eab1635e5c72cfd95d05078687c511",
        statement="DSIC o_star p_star p_star",
    ),
    "SocialChoice.AMD.amd_star_IR": TranscriptionEntry(
        kind="theorem",
        digest="8db28dc622ddb14481cb83076f312c81d367dae6ee4a42b58727fac4ad503c3b",
        statement="IR o_star p_star p_star",
    ),
    "SocialChoice.AMD.amd_star_J": TranscriptionEntry(
        kind="theorem",
        digest="ebbe0f57c3be4767295acbb1f867066e190e89de67fa9bfb800dd92cb445abee",
        statement="J o_star true true = 2",
    ),
    "SocialChoice.AMD.amd_star_J_optimal": TranscriptionEntry(
        kind="theorem",
        digest="d6d1e22660d192aba8a1ccf3869ddc2c6aff7aefb736054196a3e81a08671040",
        statement="J o true true ≤ 2",
    ),
    "SocialChoice.AMD.impossibility_strict_payments": TranscriptionEntry(
        kind="theorem",
        digest="e2ef1d86f5a8a2d6665bfb44724ddb7427877ac40be6bd9585003c55f8f6051a",
        statement="¬ IR o p0 p1",
    ),
}

# Etat epingle : `Groves.lean` n'est pas encore sur `main` (PR #22686 ouverte).
# Les empreintes ci-dessous sont celles du blob b47b6a4f581fdec04e550f43b5873d35ef2030b7
# de la branche `feature/22381-groves-clarke-lean` (tete dc55b39b2d6b). Tant que le
# fichier est absent de l'arbre, `check_transcription` rend un unique
# `module-absent` et les tests du pont Groves se declarent non applicables — ils
# ne passent pas au vert par defaut. Des que le fichier arrive, la comparaison
# s'applique et une divergence fait echouer la suite.
TRANSCRIPTION_GROVES: Mapping[str, TranscriptionEntry] = {
    "SocialChoice.Groves.welfare": TranscriptionEntry(
        kind="def",
        digest="8553d13054369cf4f0f17f52b5b20642735dfe374dd366944baafe6804a961dc",
        statement="ℤ",
    ),
    "SocialChoice.Groves.othersWelfare": TranscriptionEntry(
        kind="def",
        digest="0ef2c2152c52fa8b9c5858d21a023836034da4857ce4097085eb85406eefe9aa",
        statement="ℤ",
    ),
    "SocialChoice.Groves.grovesPayment": TranscriptionEntry(
        kind="def",
        digest="61ba121d6154b478066b9b78d08e8c7aec6e80c4746bc918e5e40fa9145024d9",
        statement="ℤ",
    ),
    "SocialChoice.Groves.payoff": TranscriptionEntry(
        kind="def",
        digest="0d6e9de2f249843df5e557b3f8f140db204eb7489513d6afaad9ad0fef24e5ff",
        statement="ℤ",
    ),
    "SocialChoice.Groves.othersWelfare_add_own": TranscriptionEntry(
        kind="lemma",
        digest="070bfde7c41690859db4b86fbf31beb059d6c46c23a998886ab45043d8e5f460",
        statement="othersWelfare v θ a i + v i (θ i) a = welfare v θ a",
    ),
    "SocialChoice.Groves.othersWelfare_update": TranscriptionEntry(
        kind="lemma",
        digest="3d1313a829e8c8ab05739e394a1fff06405b45515bbfa4350df473b0d1973341",
        statement="othersWelfare v (Function.update θ i t') a i = othersWelfare v θ a i",
    ),
    "SocialChoice.Groves.othersMax": TranscriptionEntry(
        kind="def",
        digest="4a62e80128af8829e08d6aab5bb8cd78331468d8c1a7dbdeaaa47a5bbcd2871c",
        statement="ℤ",
    ),
    "SocialChoice.Groves.clarkeTransfer": TranscriptionEntry(
        kind="def",
        digest="88797c0091307bab469296e1b777d991d24705522dfa737ee80e8e7f64ff0b8e",
        statement="N → (N → T) → ℤ",
    ),
    "SocialChoice.Groves.groves_DSIC": TranscriptionEntry(
        kind="theorem",
        digest="1384c1a527bf1ea2eb404b4ce5e727b1e6a3b3dcfe876d0c8067476a37e8e7d8",
        statement="payoff v aStar g i (θ i) θ ≥ payoff v aStar g i (θ i) (Function.update θ i t')",
    ),
    "SocialChoice.Groves.clarke_DSIC": TranscriptionEntry(
        kind="theorem",
        digest="4999825219e648ca86b953adb9a876b5152b54056aeea20872072ffc5c499d4e",
        statement="payoff v aStar (clarkeTransfer v) i (θ i) θ ≥ payoff v aStar (clarkeTransfer v) i (θ i) (Function.update θ i t')",
    ),
    "SocialChoice.Groves.clarke_IR": TranscriptionEntry(
        kind="theorem",
        digest="d3768781c3a20e371023bdee92ade450fc7c2640e97d81f7df6e852a2ab58e77",
        statement="0 ≤ payoff v aStar (clarkeTransfer v) i (θ i) θ",
    ),
    "SocialChoice.Groves.Counterexample.val": TranscriptionEntry(
        kind="def",
        digest="b39e090fba46f5babf506e8a0bf377be6acaefa99c86f5d47667fb29c4417957",
        statement="ℤ",
    ),
    "SocialChoice.Groves.Counterexample.badAlloc": TranscriptionEntry(
        kind="def",
        digest="3d9bed234cbaa29168c8f5aecc1f55cc58a5c460bbdb6c8cf29332e18e79cecc",
        statement="Bool",
    ),
    "SocialChoice.Groves.Counterexample.zeroTransfer": TranscriptionEntry(
        kind="def",
        digest="2c02c410174df4328a1dec3cbcce36e1701e22b4701b3346f52e1c06ec50a470",
        statement="ℤ",
    ),
    "SocialChoice.Groves.Counterexample.badAlloc_not_efficient": TranscriptionEntry(
        kind="theorem",
        digest="ac754d0fc126f0eeebdd048b92be4e9545fae0c79cd942cde00d957868cb8f3c",
        statement="¬ ∀ θ a, welfare val θ a ≤ welfare val θ (badAlloc θ)",
    ),
    "SocialChoice.Groves.Counterexample.badAlloc_violates_DSIC": TranscriptionEntry(
        kind="theorem",
        digest="551fe1757e4cc45ec5886a17745716f6b41e20d6f9a1b85347136a5350ddf55f",
        statement="∃ (i : Bool) (θ : Bool → Bool) (t' : Bool), payoff val badAlloc zeroTransfer i (θ i) θ < payoff val badAlloc zeroTransfer i (θ i) (Function.update θ i t')",
    ),
}

TRANSCRIPTION_TARGETS_AMD: tuple[str, ...] = (
    "SocialChoice.AMD.AgentType",
    "SocialChoice.AMD.Profile",
    "SocialChoice.AMD.thetaVal",
    "SocialChoice.AMD.issueVal",
    "SocialChoice.AMD.u0",
    "SocialChoice.AMD.u1",
    "SocialChoice.AMD.DSIC",
    "SocialChoice.AMD.IR",
    "SocialChoice.AMD.J",
    "SocialChoice.AMD.o_star",
    "SocialChoice.AMD.p_star",
    "SocialChoice.AMD.amd_star_DSIC",
    "SocialChoice.AMD.amd_star_IR",
    "SocialChoice.AMD.amd_star_J",
    "SocialChoice.AMD.amd_star_J_optimal",
    "SocialChoice.AMD.impossibility_strict_payments",
)

TRANSCRIPTION_TARGETS_GROVES: tuple[str, ...] = (
    "SocialChoice.Groves.welfare",
    "SocialChoice.Groves.othersWelfare",
    "SocialChoice.Groves.grovesPayment",
    "SocialChoice.Groves.payoff",
    "SocialChoice.Groves.othersWelfare_add_own",
    "SocialChoice.Groves.othersWelfare_update",
    "SocialChoice.Groves.othersMax",
    "SocialChoice.Groves.clarkeTransfer",
    "SocialChoice.Groves.groves_DSIC",
    "SocialChoice.Groves.clarke_DSIC",
    "SocialChoice.Groves.clarke_IR",
    "SocialChoice.Groves.Counterexample.val",
    "SocialChoice.Groves.Counterexample.badAlloc",
    "SocialChoice.Groves.Counterexample.zeroTransfer",
    "SocialChoice.Groves.Counterexample.badAlloc_not_efficient",
    "SocialChoice.Groves.Counterexample.badAlloc_violates_DSIC",
)


@dataclass(frozen=True)
class TranscriptionDrift:
    """Un ecart entre la source Lean et la transcription du pont."""

    kind: str  # "module-absent" | "declaration-absente" | "empreinte" | "enonce"
    name: str
    detail: str

    def __str__(self) -> str:
        return f"[{self.kind}] {self.name} : {self.detail}"


def check_transcription(
    source: Path, transcription: Mapping[str, TranscriptionEntry]
) -> tuple[TranscriptionDrift, ...]:
    """Compare la source Lean a la transcription ; rend les derives, sans lever.

    Un module **absent** est signale par un seul `module-absent` : c'est l'etat
    normal tant que la PR qui ajoute le `.lean` n'est pas mergee, et ce n'est
    pas un echec du pont. Une declaration absente ou une empreinte differente
    sont des derives : le `.lean` a bouge sous la transcription.
    """
    if not source.is_file():
        return (
            TranscriptionDrift(
                kind="module-absent",
                name=str(source.name),
                detail=f"fichier introuvable : {source}",
            ),
        )
    declarations = parse_lean_declarations(source.read_text(encoding="utf-8"))
    drifts: list[TranscriptionDrift] = []
    for name, entry in transcription.items():
        declaration = declarations.get(name)
        if declaration is None:
            drifts.append(
                TranscriptionDrift(
                    kind="declaration-absente",
                    name=name,
                    detail="la declaration a disparu ou a ete renommee dans la source Lean",
                )
            )
            continue
        if declaration.kind != entry.kind:
            drifts.append(
                TranscriptionDrift(
                    kind="empreinte",
                    name=name,
                    detail=f"nature {declaration.kind!r} != {entry.kind!r}",
                )
            )
        if declaration.digest != entry.digest:
            drifts.append(
                TranscriptionDrift(
                    kind="empreinte",
                    name=name,
                    detail=(
                        f"empreinte {declaration.digest[:12]} != {entry.digest[:12]} — "
                        "regenerer la transcription (--dump-transcription) et revalider le pont"
                    ),
                )
            )
        if declaration.statement != entry.statement:
            drifts.append(
                TranscriptionDrift(
                    kind="enonce",
                    name=name,
                    detail=(
                        f"enonce {declaration.statement!r} != {entry.statement!r} — "
                        "la preuve a change d'ENONCE, pas seulement de forme"
                    ),
                )
            )
    return tuple(drifts)


def build_transcription(
    source: Path, names: Sequence[str]
) -> dict[str, TranscriptionEntry]:
    """Construit la transcription depuis la source : outil de regeneration."""
    declarations = parse_lean_declarations(source.read_text(encoding="utf-8"))
    missing = [name for name in names if name not in declarations]
    if missing:
        raise ValueError(f"declarations introuvables dans {source.name} : {missing}")
    return {
        name: TranscriptionEntry(
            kind=declarations[name].kind,
            digest=declarations[name].digest,
            statement=declarations[name].statement,
        )
        for name in names
    }


def dump_transcription(module: str) -> str:
    """Rend la transcription sous forme de litteral Python, a coller dans ce fichier."""
    if module == "AMD":
        source, names = AMD_LEAN, TRANSCRIPTION_TARGETS_AMD
        variable = "TRANSCRIPTION_AMD"
    elif module == "Groves":
        source, names = GROVES_LEAN, TRANSCRIPTION_TARGETS_GROVES
        variable = "TRANSCRIPTION_GROVES"
    else:
        raise ValueError(f"module inconnu : {module!r} (attendu 'AMD' ou 'Groves')")
    entries = build_transcription(source, names)
    lines = [f"{variable}: Mapping[str, TranscriptionEntry] = {{"]
    for name in names:
        entry = entries[name]
        lines.append(f'    "{name}": TranscriptionEntry(')
        lines.append(f'        kind="{entry.kind}",')
        lines.append(f'        digest="{entry.digest}",')
        lines.append(f'        statement="{entry.statement}",')
        lines.append("    ),")
    lines.append("}")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Reproduction des utilites d'AMD.lean (critere 6)
#
# Traduction litterale de `AMD.lean:49-60`, dans l'ordre du fichier : thetaVal,
# issueVal, u0, u1. Elles servent de temoin lisible, et les tests mesurent
# qu'elles coincident avec `verify_utility` du verificateur independant sur tout
# le domaine — c'est la seule chose qui les empeche de deriver en silence.
# ---------------------------------------------------------------------------

BoolProfile = tuple[bool, bool]


def theta_val(t: bool) -> int:
    """`AMD.lean:49` — valeur numerique d'un type (T = 1, F = 0)."""
    return 1 if t else 0


def issue_val(o: bool) -> int:
    """`AMD.lean:52` — valeur numerique d'une issue (T = 1, F = 0)."""
    return 1 if o else 0


def lean_u0(
    o: Callable[[BoolProfile], bool],
    p0: Callable[[BoolProfile], int],
    t: bool,
    r: BoolProfile,
) -> int:
    """`AMD.lean:55-56` — utilite de l'agent 0, type vrai `t`, profil REPORTE `r`."""
    return theta_val(t) * issue_val(o(r)) - p0(r)


def lean_u1(
    o: Callable[[BoolProfile], bool],
    p1: Callable[[BoolProfile], int],
    t: bool,
    r: BoolProfile,
) -> int:
    """`AMD.lean:59-60` — utilite de l'agent 1 (symetrique)."""
    return theta_val(t) * issue_val(o(r)) - p1(r)


def o_star(r: BoolProfile) -> bool:
    """`AMD.lean:89` — table d'issues de M* : l'issue vaut T au seul profil (T, T)."""
    return r[0] and r[1]


def p_star(_r: BoolProfile) -> int:
    """`AMD.lean:92` — table de paiements de M* : nulle partout."""
    return 0


BOOL_PROFILES: tuple[BoolProfile, ...] = tuple(itertools.product((False, True), repeat=2))


def to_int_profile(profile: BoolProfile) -> tuple[int, int]:
    """Profil booleen Lean -> profil entier de `amd_synthesis` (T = 1, F = 0)."""
    return (1 if profile[0] else 0, 1 if profile[1] else 0)


# ---------------------------------------------------------------------------
# Cadre de Groves en Python
#
# Traduction de `Groves.lean` (welfare, othersWelfare, grovesPayment, payoff).
# La convention de transfert RECU est conservee telle quelle ici ; c'est
# `payments_from_groves` qui l'inverse pour le verificateur.
# ---------------------------------------------------------------------------


def groves_welfare(values: Sequence[Sequence[Sequence[int]]], reported: Sequence[int], outcome: int) -> int:
    """`Groves.lean` `welfare` : somme des valorisations reportees a l'issue."""
    return sum(values[j][reported[j]][outcome] for j in range(len(reported)))


def groves_others_welfare(
    values: Sequence[Sequence[Sequence[int]]],
    reported: Sequence[int],
    outcome: int,
    agent: int,
) -> int:
    """`Groves.lean` `othersWelfare` : bien-etre des agents autres que `agent`."""
    return sum(
        values[j][reported[j]][outcome] for j in range(len(reported)) if j != agent
    )


def groves_payment(
    values: Sequence[Sequence[Sequence[int]]],
    a_star: Callable[[Sequence[int]], int],
    g: Callable[[int, Sequence[int]], int],
    reported: Sequence[int],
    agent: int,
) -> int:
    """`Groves.lean` `grovesPayment` : part des autres a l'issue retenue, plus `g`."""
    return groves_others_welfare(values, reported, a_star(reported), agent) + g(agent, reported)


def groves_payoff(
    values: Sequence[Sequence[Sequence[int]]],
    a_star: Callable[[Sequence[int]], int],
    g: Callable[[int, Sequence[int]], int],
    agent: int,
    true_type: int,
    reported: Sequence[int],
) -> int:
    """`Groves.lean` `payoff` : valorisation a l'issue retenue PLUS transfert recu."""
    return values[agent][true_type][a_star(reported)] + groves_payment(
        values, a_star, g, reported, agent
    )


def clarke_transfer(
    values: Sequence[Sequence[Sequence[int]]],
    reported: Sequence[int],
    agent: int,
) -> int:
    """`Groves.lean` `clarkeTransfer` : oppose du maximum des autres (l'externalite)."""
    n_outcomes = len(values[0][0])
    return -max(
        groves_others_welfare(values, reported, outcome, agent)
        for outcome in range(n_outcomes)
    )


def welfare_maximiser(
    values: Sequence[Sequence[Sequence[int]]], n_outcomes: int
) -> Callable[[Sequence[int]], int]:
    """Selectionne l'issue de bien-etre maximal, plus petit indice en cas d'egalite.

    C'est l'hypothese `hStar` du theoreme de Groves : la regle doit MAXIMISER le
    bien-etre reporte. Le departage n'a pas d'importance pour le theoreme, mais
    il doit etre deterministe pour que le pont soit reproductible.
    """

    def a_star(reported: Sequence[int]) -> int:
        best_outcome = 0
        best_welfare = groves_welfare(values, reported, 0)
        for outcome in range(1, n_outcomes):
            value = groves_welfare(values, reported, outcome)
            if value > best_welfare:
                best_outcome, best_welfare = outcome, value
        return best_outcome

    return a_star


def payments_from_groves(
    values: Sequence[Sequence[Sequence[int]]],
    a_star: Callable[[Sequence[int]], int],
    g: Callable[[int, Sequence[int]], int],
    profiles: Sequence[Sequence[int]],
) -> tuple[tuple[int, ...], ...]:
    """Traduit les transferts RECUS de `Groves.lean` en paiements PAYES.

    `payment_i(r) = -grovesPayment_i(r)`. Sans cette inversion, l'utilite du
    verificateur (`valeur - paiement`) aurait le signe oppose de `payoff`
    (`valeur + transfert`), et un mecanisme DSIC passerait pour fautif.
    """
    return tuple(
        tuple(-groves_payment(values, a_star, g, reported, agent) for agent in range(len(reported)))
        for reported in profiles
    )


# ---------------------------------------------------------------------------
# Instances du pont : le verdict formel et le verdict mesure, cote a cote
# ---------------------------------------------------------------------------


class BridgeMismatch(AssertionError):
    """Le verdict mesure contredit l'enonce formel transcrit."""


@dataclass(frozen=True)
class BridgeCheck:
    """Une proposition : ce que l'enonce Lean affirme, et ce que Python mesure."""

    name: str
    expected: str
    measured: str

    @property
    def ok(self) -> bool:
        return self.expected == self.measured


@dataclass(frozen=True)
class BridgeInstance:
    """Une instance formelle rejouee en Python.

    `theorems` nomme les enonces Lean cites, `hypotheses` leurs hypotheses,
    et `not_certified` dit ce que ces enonces **n'etablissent pas** — c'est une
    exigence du critere 6 de #22381, pas une precaution de style.
    """

    name: str
    lean_module: str
    theorems: tuple[str, ...]
    hypotheses: tuple[str, ...]
    formal_claim: str
    checks: tuple[BridgeCheck, ...]
    not_certified: str

    @property
    def conforms(self) -> bool:
        return all(check.ok for check in self.checks)

    @property
    def failed(self) -> tuple[BridgeCheck, ...]:
        return tuple(check for check in self.checks if not check.ok)

    def summary(self) -> str:
        head = f"{'CONFORME' if self.conforms else 'DIVERGENT'} {self.name} [{self.lean_module}]"
        body = [f"    {c.name} : attendu {c.expected!r}, mesure {c.measured!r}" for c in self.checks]
        return "\n".join([head, *body, f"    limite : {self.not_certified}"])


def ensure_conforms(*instances: BridgeInstance) -> None:
    """Leve `BridgeMismatch` des qu'une instance contredit son enonce forme."""
    problems = [
        (instance.name, check)
        for instance in instances
        for check in instance.failed
    ]
    if not problems:
        return
    detail = "; ".join(
        f"{name}/{check.name} : attendu {check.expected!r}, mesure {check.measured!r}"
        for name, check in problems
    )
    raise BridgeMismatch(f"pont divergent — {detail}")


def _violations_text(violations: Iterable[Violation]) -> str:
    items = list(violations)
    return "aucune violation" if not items else f"{len(items)} violation(s)"


def amd_witness_instance() -> BridgeInstance:
    """Temoin booleen d'`AMD.lean` : M* est DSIC, IR, J = 2, J optimal, utilites reproduites.

    Trois mesures independantes du noyau Lean sont confrontees a l'enonce :
    le verificateur de `amd_synthesis`, l'enumeration exhaustive des 16
    allocations au profil (1, 1), et la traduction litterale de `u0`/`u1`.
    """
    domain = amd_domain()
    mechanism = amd_star_mechanism(domain)
    report = verify(domain, mechanism)

    true_profile = (1, 1)
    r = domain.profiles.index(true_profile)
    point_welfare = sum(domain.values[a][true_profile[a]][mechanism.allocation[r]] for a in range(2))

    best_point = max(
        sum(domain.values[a][1][allocation[r]] for a in range(2))
        for allocation in itertools.product(range(2), repeat=len(domain.profiles))
    )

    mismatches = 0
    for true_type in (False, True):
        for profile in BOOL_PROFILES:
            int_profile = to_int_profile(profile)
            if lean_u0(o_star, p_star, true_type, profile) != verify_utility(
                domain, mechanism, 0, int(true_type), int_profile
            ):
                mismatches += 1
            if lean_u1(o_star, p_star, true_type, profile) != verify_utility(
                domain, mechanism, 1, int(true_type), int_profile
            ):
                mismatches += 1

    return BridgeInstance(
        name="amd_witness",
        lean_module="SocialChoice/AMD.lean",
        theorems=(
            "SocialChoice.AMD.amd_star_DSIC",
            "SocialChoice.AMD.amd_star_IR",
            "SocialChoice.AMD.amd_star_J",
            "SocialChoice.AMD.amd_star_J_optimal",
        ),
        hypotheses=(
            "aucune : le domaine est fini et explicite (2 agents, types booleens, issue booleenne)",
            "o_star (r) = r1 ET r2 ; p_star (r) = 0 (AMD.lean:89-92)",
        ),
        formal_claim=(
            "M* = (o_star, paiements nuls) est DSIC et IR sur tout le domaine fini, "
            "J o_star true true = 2, et aucun mecanisme ne depasse J = 2 au profil (T, T)."
        ),
        checks=(
            BridgeCheck(
                name="DSIC (amd_star_DSIC)",
                expected="aucune violation",
                measured=_violations_text(report.dsic_violations),
            ),
            BridgeCheck(
                name="IR (amd_star_IR)",
                expected="aucune violation",
                measured=_violations_text(report.ir_violations),
            ),
            BridgeCheck(
                name="J au profil vrai (1, 1) (amd_star_J)",
                expected="2",
                measured=str(point_welfare),
            ),
            BridgeCheck(
                name="optimalite J <= 2 (amd_star_J_optimal)",
                expected="2",
                measured=str(best_point),
            ),
            BridgeCheck(
                name="utilites u0/u1 reproduites (AMD.lean:55-60)",
                expected="0 ecart(s)",
                measured=f"{mismatches} ecart(s)",
            ),
        ),
        not_certified=(
            "La preuve certifie le TEMOIN M* sur ce domaine fini de 4 profils ; elle ne certifie "
            "aucun mecanisme produit par le solveur CP-SAT, ni un domaine a plus de deux agents, "
            "plus de deux types ou plus de deux issues."
        ),
    )


def amd_impossibility_instance() -> BridgeInstance:
    """`impossibility_strict_payments` : paiements >= 1 partout rendent IR impossible.

    Le theoreme est general (tout mecanisme). Le pont ne peut reproduire qu'une
    instance : le verdict CP-SAT et l'enumeration exhaustive sur la grille {1, 2}.
    """
    constrained = synthesize(amd_domain(payment_bounds=(1, 4)), payments_at_least=1)
    enumerated = best_by_enumeration(amd_domain(payment_bounds=(1, 2)), (1, 2))

    return BridgeInstance(
        name="amd_impossibility_strict_payments",
        lean_module="SocialChoice/AMD.lean",
        theorems=("SocialChoice.AMD.impossibility_strict_payments",),
        hypotheses=(
            "h0 : pour tout profil r, 1 <= p0 r (tout paiement de l'agent 0 est >= 1)",
            "_h1 : la meme hypothese pour l'agent 1 (declaree, non utilisee par la preuve)",
        ),
        formal_claim=(
            "Si tout paiement est >= 1, alors IR est viole, pour TOUT mecanisme et toute table d'issues."
        ),
        checks=(
            BridgeCheck(
                name="CP-SAT, paiements >= 1 (instance)",
                expected="INFEASIBLE",
                measured=constrained.status,
            ),
            BridgeCheck(
                name="enumeration exhaustive, grille {1, 2}",
                expected="0 admissibles",
                measured=f"{enumerated.n_admissible} admissibles",
            ),
            BridgeCheck(
                name="aucun mecanisme rendu",
                expected="aucun",
                measured="aucun" if constrained.mechanism is None else "un mecanisme",
            ),
        ),
        not_certified=(
            "Le theoreme est general, mais le pont n'en rejoue que l'instance booleenne : l'etat "
            "INFEASIBLE de CP-SAT est une mesure du solveur, pas une preuve. Elle ne certifie donc "
            "ni le domaine a 3 agents / 3 types, ni l'exactitude du modele lineaire transmis au "
            "solveur."
        ),
    )


CLARKE_VALUES: tuple[tuple[tuple[int, ...], ...], ...] = (
    ((0, 1), (0, 3)),  # agent 0 : type 0 valorise (o0=0, o1=1) ; type 1 (0, 3)
    ((2, 0), (1, 0)),  # agent 1 : type 0 valorise (o0=2, o1=0) ; type 1 (1, 0)
)


def clarke_domain() -> FiniteDomain:
    """Domaine a deux issues ou le pivot de Clarke n'est **pas** degenere.

    Les valeurs sont choisies pour qu'un agent soit pivot : au profil (1, 0),
    l'agent 0 fait basculer l'issue de 0 a 1 et impose a l'agent 1 une perte de
    2, qu'il paie. Une instance ou tous les pivots seraient nuls ne testerait
    rien (les paiements seraient tous nuls et DSIC trivialement vrai).
    """
    return FiniteDomain(
        n_agents=2,
        n_types=2,
        n_outcomes=2,
        values=CLARKE_VALUES,
        weights=tuple((profile, 1) for profile in itertools.product(range(2), repeat=2)),
        payment_bounds=(0, 4),
    )


def clarke_g(values: Sequence[Sequence[Sequence[int]]]) -> Callable[[int, Sequence[int]], int]:
    """Terme `g` du pivot de Clarke : `g i θ = - max_a othersWelfare θ a i`.

    C'est l'instance de Groves retenue par `clarke_DSIC` — et non `g = 0`, qui
    donnerait le mecanisme de bien-etre (DSIC lui aussi, mais a transferts
    strictement negatifs, donc sans pivot a mesurer).
    """

    def g(agent: int, reported: Sequence[int]) -> int:
        return clarke_transfer(values, reported, agent)

    return g


def clarke_mechanism(domain: FiniteDomain) -> Mechanism:
    """Mecanisme de Clarke construit depuis les formules de `Groves.lean`.

    L'allocation est `aStar` (bien-etre maximal), les transferts sont
    `clarkeTransfer`. Le paiement PAYE est l'oppose du transfert RECU — voir
    `payments_from_groves`.
    """
    a_star = welfare_maximiser(domain.values, domain.n_outcomes)
    payments = payments_from_groves(domain.values, a_star, clarke_g(domain.values), domain.profiles)
    allocation = tuple(a_star(profile) for profile in domain.profiles)
    return Mechanism(allocation=allocation, payments=payments)


def clarke_pivot_instance() -> BridgeInstance:
    """Pivot de Clarke : DSIC (via Groves), IR sous valorisations positives, pivots reels."""
    domain = clarke_domain()
    mechanism = clarke_mechanism(domain)
    report = verify(domain, mechanism)

    a_star = welfare_maximiser(domain.values, domain.n_outcomes)
    g = clarke_g(domain.values)
    utility_errors = 0
    for profile in domain.profiles:
        for agent in range(domain.n_agents):
            for true_type in range(domain.n_types):
                if verify_utility(domain, mechanism, agent, true_type, profile) != groves_payoff(
                    domain.values, a_star, g, agent, true_type, profile
                ):
                    utility_errors += 1

    negatives = sum(
        1
        for agent in range(domain.n_agents)
        for true_type in range(domain.n_types)
        for outcome in range(domain.n_outcomes)
        if domain.values[agent][true_type][outcome] < 0
    )
    max_payment = max(p for row in mechanism.payments for p in row)

    return BridgeInstance(
        name="clarke_pivot",
        lean_module="SocialChoice/Groves.lean",
        theorems=(
            "SocialChoice.Groves.groves_DSIC",
            "SocialChoice.Groves.clarke_DSIC",
            "SocialChoice.Groves.clarke_IR",
        ),
        hypotheses=(
            "hStar : pour tout profil reporte θ et toute issue a, welfare θ a <= welfare θ (aStar θ)",
            "hg (Groves) : g i θ ne depend que du report des agents autres que i — verifiee par construction (g = 0)",
            "hv (IR) : pour tout agent i, type t et issue a, 0 <= v i t a",
        ),
        formal_claim=(
            "Tout mecanisme de Groves est DSIC ; le pivot de Clarke, qui en est une instance, est "
            "DSIC et — sous valorisations positives — individuellement rationnel."
        ),
        checks=(
            BridgeCheck(
                name="DSIC (clarke_DSIC, via groves_DSIC)",
                expected="aucune violation",
                measured=_violations_text(report.dsic_violations),
            ),
            BridgeCheck(
                name="IR (clarke_IR)",
                expected="aucune violation",
                measured=_violations_text(report.ir_violations),
            ),
            BridgeCheck(
                name="hypothese hv : valorisations positives",
                expected="0 negative(s)",
                measured=f"{negatives} negative(s)",
            ),
            BridgeCheck(
                name="identite d'utilite : u_verificateur = payoff Lean",
                expected="0 ecart(s)",
                measured=f"{utility_errors} ecart(s)",
            ),
            BridgeCheck(
                name="pivot non degenere",
                expected="un agent paie strictement plus que 0",
                measured=(
                    "un agent paie strictement plus que 0"
                    if max_payment > 0
                    else "tous les paiements sont nuls"
                ),
            ),
        ),
        not_certified=(
            "Les theoremes supposent hStar (aStar maximise le bien-etre REPORTE) et, pour IR, des "
            "valorisations positives ; ils ne certifient ni que le solveur trouve ce mecanisme, ni "
            "l'equilibre budgetaire, ni l'optimalite en revenu (Myerson-Satterthwaite), ni un "
            "domaine a plus de deux issues ou a types correles."
        ),
    )


BAD_ALLOC_VALUES: tuple[tuple[tuple[int, ...], ...], ...] = (
    ((0, 0), (0, 1)),
    ((0, 0), (0, 1)),
)


def bad_alloc_mechanism() -> Mechanism:
    """Temoin negatif de `Groves.lean` : allocation `badAlloc`, transferts nuls.

    `badAlloc θ = non (θ 0)` — l'allocation ignore deliberement le second agent.
    Les transferts gardent la forme de Groves (`g = 0`), mais l'allocation ne
    maximise plus le bien-etre : c'est la premisse de `groves_DSIC` qui tombe.
    """
    values = BAD_ALLOC_VALUES
    profiles = tuple(itertools.product(range(2), repeat=2))
    a_star = lambda reported: 0 if reported[0] else 1  # noqa: E731 — badAlloc, non efficace
    payments = payments_from_groves(values, a_star, lambda _agent, _reported: 0, profiles)
    allocation = tuple(a_star(profile) for profile in profiles)
    return Mechanism(allocation=allocation, payments=payments)


def bad_alloc_domain() -> FiniteDomain:
    """Domaine du temoin negatif : bornes ouvertes aux transferts negatifs."""
    return FiniteDomain(
        n_agents=2,
        n_types=2,
        n_outcomes=2,
        values=BAD_ALLOC_VALUES,
        weights=tuple((profile, 1) for profile in itertools.product(range(2), repeat=2)),
        payment_bounds=(-2, 2),
    )


def bad_alloc_instance() -> BridgeInstance:
    """`badAlloc_violates_DSIC` : sincere 0, deviation 2 — les nombres de la preuve."""
    domain = bad_alloc_domain()
    mechanism = bad_alloc_mechanism()
    dsic = verify_dsic_sincere_anchored(domain, mechanism)
    ir = verify_ir_sincere(domain, mechanism)

    sincere = (1, 1)
    hit = [
        violation
        for violation in dsic
        if violation.agent == 0
        and violation.profile == sincere
        and violation.deviation == 0
    ]
    if hit:
        measured = (
            f"agent 0, profil {sincere}, deviation 0 : "
            f"{hit[0].sincere_utility} -> {hit[0].deviating_utility}"
        )
    else:
        measured = "aucune violation pour (agent 0, profil (1, 1), deviation 0)"

    r = domain.profiles.index(sincere)
    point_alloc = sum(
        domain.values[a][sincere[a]][mechanism.allocation[r]] for a in range(domain.n_agents)
    )
    point_best = max(
        sum(domain.values[a][sincere[a]][o] for a in range(domain.n_agents))
        for o in range(domain.n_outcomes)
    )

    return BridgeInstance(
        name="bad_alloc",
        lean_module="SocialChoice/Groves.lean",
        theorems=(
            "SocialChoice.Groves.Counterexample.badAlloc_not_efficient",
            "SocialChoice.Groves.Counterexample.badAlloc_violates_DSIC",
        ),
        hypotheses=(
            "aucune hypothese de bonne conduite : c'est precisement hStar qui est retiree",
            "badAlloc θ = non (θ 0) ; transferts nuls (Groves.lean, namespace Counterexample)",
        ),
        formal_claim=(
            "badAlloc ne maximise pas le bien-etre, et sous cette allocation les transferts de "
            "Groves cessent d'etre DSIC : l'agent 0 obtient 0 en rapportant (T, T) et 2 en deviant "
            "vers (F, T)."
        ),
        checks=(
            BridgeCheck(
                name="hStar violee (badAlloc_not_efficient)",
                expected="0 < 2",
                measured=f"{point_alloc} < {point_best}"
                if point_alloc < point_best
                else f"{point_alloc} >= {point_best} — badAlloc est efficace ici",
            ),
            BridgeCheck(
                name="DSIC viole (badAlloc_violates_DSIC)",
                expected="agent 0, profil (1, 1), deviation 0 : 0 -> 2",
                measured=measured,
            ),
            BridgeCheck(
                name="IR tenue — contraste (le temoin ne viole que DSIC)",
                expected="aucune violation",
                measured=_violations_text(ir),
            ),
        ),
        not_certified=(
            "Le temoin est un enonce d'EXISTENCE sur une instance de deux agents : il ne prouve pas "
            "qu'aucune allocation non efficace n'est DSIC, et il ne certifie aucune instance "
            "produite par le solveur CP-SAT."
        ),
    )


def all_instances() -> tuple[BridgeInstance, ...]:
    """Les quatre instances du pont, dans l'ordre du rapport."""
    return (
        amd_witness_instance(),
        amd_impossibility_instance(),
        clarke_pivot_instance(),
        bad_alloc_instance(),
    )


def transcription_status() -> tuple[tuple[str, tuple[TranscriptionDrift, ...]], ...]:
    """Etat de la transcription des deux modules Lean, sans lever."""
    return (
        ("AMD", check_transcription(AMD_LEAN, TRANSCRIPTION_AMD)),
        ("Groves", check_transcription(GROVES_LEAN, TRANSCRIPTION_GROVES)),
    )


def main(argv: Sequence[str] | None = None) -> int:
    """Rapport du pont : transcription, instances, conformite. Code 0 si tout tient."""
    args = list(sys.argv[1:] if argv is None else argv)
    if args and args[0] == "--dump-transcription":
        if len(args) != 2:
            print("usage : --dump-transcription {AMD|Groves}")
            return 2
        print(dump_transcription(args[1]))
        return 0

    failed = 0
    print("== transcription ==")
    for module, drifts in transcription_status():
        if not drifts:
            print(f"{module:8s}: conforme a la source Lean")
            continue
        for drift in drifts:
            print(f"{module:8s}: {drift}")
            if drift.kind != "module-absent":
                failed += 1

    print("\n== instances ==")
    instances = all_instances()
    for instance in instances:
        print(instance.summary())
        if not instance.conforms:
            failed += 1
    print(f"\n{sum(1 for i in instances if i.conforms)}/{len(instances)} instances conformes")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
