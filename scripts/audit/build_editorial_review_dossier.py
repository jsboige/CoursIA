#!/usr/bin/env python3
"""Dossier de revue editoriale -- couche INSTRUMENTS (acceptance 2 de #11259).

Entree : le SEUL chemin du notebook. Sortie : les 7 axes instrumentaux nommes
par l'acceptance 2 de #11259 -- execution, outputs authentiques, densite
pedagogique, ordre des cellules, citations verifiees, parite jumeau, i18n --
chacun en PASS/WARN/NA/ERROR avec sa provenance (organe, argv, code de retour,
extrait), puis les 3 questions de jugement humain que les instruments ne
tranchent pas.

Le contrat qui donne sa valeur au dossier : **aucun verdict n'est fabrique**.
Chaque ligne vient d'un organe reel, cite dans la colonne de provenance. Un
organe injoignable ou muet sort en ERROR -- jamais en PASS : un instrument qu'on
n'a pas su lire est un instrument dont on ne sait rien, et le confondre avec un
instrument vert est exactement la complaisance que ce dossier existe pour
empecher (G.1, H.1).

Ce que ce script ne fait PAS, et ne pretend pas faire : les *constats* et les
*correctifs proposes* de l'acceptance 2 sont un jugement d'agent (lire la
cellule, decider ce qui ne va pas, rediger le diff) -- ils ne sont pas
scriptables et ne sont pas revendiques ici. Le dossier livre les instruments,
leur provenance et les questions ; l'agent remplit le reste.

Usage :
    python scripts/audit/build_editorial_review_dossier.py \\
        --notebook MyIA.AI.Notebooks/Sudoku/Sudoku-01-Backtracking-Python.ipynb
    ... --json          # sortie machine
    ... --out dossier.md

Code de retour : 0 si tous les instruments ont rendu un verdict lisible (PASS,
WARN ou NA) ; 1 si au moins un axe est en ERROR (organe injoignable ou muet).
Un WARN est un constat sur le notebook, pas une panne de l'outil : il ne rougit
pas le script.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, Sequence

REPO_ROOT = Path(__file__).resolve().parents[2]
NOTEBOOK_ROOT = "MyIA.AI.Notebooks"
DEFAULT_TIMEOUT = 300

PASS = "PASS"
WARN = "WARN"
NA = "NA"
ERROR = "ERROR"


# ---------------------------------------------------------------------------
# Runner injectable
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class RunResult:
    """Resultat brut d'un organe. `rc` porte le verdict de l'organe."""

    rc: int
    stdout: str = ""
    stderr: str = ""


def run_organ(argv: Sequence[str], cwd: Path | None = None,
              timeout: int = DEFAULT_TIMEOUT) -> RunResult:
    """Execute un organe et capture sa sortie. Injectable dans les tests."""
    proc = subprocess.run(
        [str(a) for a in argv], cwd=str(cwd) if cwd else None,
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        timeout=timeout,
    )
    return RunResult(proc.returncode, proc.stdout or "", proc.stderr or "")


# ---------------------------------------------------------------------------
# Lecture de charge utile
# ---------------------------------------------------------------------------

def parse_json(text: str) -> Any | None:
    """JSON du premier objet/accolade ouvrante au dernier fermant.

    Les organes bavards preparent leur JSON de lignes de log ; on ne veut pas
    dependre de l'absence de preambule. Rend None si rien ne parse -- l'appelant
    en fait un ERROR, jamais un PASS.
    """
    if not text:
        return None
    start = text.find("{")
    end = text.rfind("}")
    if start == -1 or end == -1 or end < start:
        return None
    try:
        return json.loads(text[start:end + 1])
    except json.JSONDecodeError:
        return None


def count_at(payload: Any, path: Sequence[str]) -> int:
    """Compte a un chemin pointe : entier tel quel, liste par sa longueur."""
    node = payload
    for key in path:
        if not isinstance(node, dict) or key not in node:
            return 0
        node = node[key]
    if isinstance(node, bool):
        return 0
    if isinstance(node, int):
        return node
    if isinstance(node, (list, tuple, dict)):
        return len(node)
    return 0


def excerpt(text: str, limit: int = 200) -> str:
    """Premiere ligne utile, tronquee -- la provenance reste lisible.

    Une ligne reduite a une ponctuation ouvrante (`{`, `[`) est la premiere ligne
    d'un JSON : la montrer n'apprend rien et laisserait croire que l'organe n'a
    rien dit. On passe a la suivante.
    """
    for line in (text or "").splitlines():
        line = line.strip()
        if line and line not in ("{", "[", "(", "{"):
            return line[:limit]
    return ""


def portable_command(argv: Sequence[str], outfile: str | None = None) -> str:
    """Commande relisible : interpreteur par son basename, temporaire masque.

    Le dossier est lu par un humain, souvent sur une autre machine que celle qui
    l'a produit. Un chemin d'interpreteur absolu (`C:\\Python313\\python.exe`)
    n'y apporte rien et y fait entrer un chemin machine ; le fichier de charge
    utile temporaire, lui, change a chaque execution.
    """
    parts: list[str] = []
    for index, arg in enumerate(argv):
        if index == 0:
            parts.append(Path(str(arg)).name)
        elif outfile and str(arg) == str(outfile):
            parts.append("<tmp>/charge-utile.json")
        else:
            parts.append(str(arg))
    return " ".join(parts)


# ---------------------------------------------------------------------------
# Juges -- fonctions pures (payload, rc, notebook) -> (verdict, detail)
# ---------------------------------------------------------------------------

Judge = Callable[[Any, int, str], "tuple[str, str]"]


def judge_rc(payload: Any, rc: int, notebook: str) -> tuple[str, str]:
    """Organe binaire : rc 0 = sain, rc 1 = defaut, au-dela = organe muet."""
    if rc == 0:
        return PASS, "aucun defaut"
    if rc == 1:
        return WARN, "defaut(s) detecte(s)"
    return ERROR, f"organe non concluant (rc={rc})"


def judge_counts(*paths: Sequence[str]) -> Judge:
    """Organe advisory : le signal est dans des compteurs JSON, pas dans le rc.

    Ces organes sortent toujours 0 (un seuil mutable changerait ce que le label
    signifie d'une invocation a l'autre, cf #10479) -- lire le rc seul les
    declare donc tous verts. On somme les compteurs nommes.
    """
    def _judge(payload: Any, rc: int, notebook: str) -> tuple[str, str]:
        if rc not in (0, 1):
            return ERROR, f"organe non concluant (rc={rc})"
        if payload is None:
            return ERROR, "sortie JSON illisible -- verdict impossible"
        counts = {p[-1]: count_at(payload, p) for p in paths}
        total = sum(counts.values())
        rendered = ", ".join(f"{k}={v}" for k, v in counts.items())
        if total == 0:
            return PASS, rendered
        return WARN, rendered
    return _judge


def judge_citations(payload: Any, rc: int, notebook: str) -> tuple[str, str]:
    """Citations arXiv du notebook, croisees avec le delta non couvert.

    L'organe balaie une famille : on ne retient que les occurrences qui nomment
    CE notebook, sinon le verdict porterait sur les voisins.
    """
    if rc not in (0, 1):
        return ERROR, f"organe non concluant (rc={rc})"
    if payload is None:
        return ERROR, "sortie JSON illisible -- verdict impossible"
    wanted = Path(str(notebook).replace("\\", "/")).name
    mine: list[str] = []
    occurrences = payload.get("occurrences") or {}
    if not isinstance(occurrences, dict):
        return ERROR, "charge utile 'occurrences' inattendue"
    for arxiv_id, hits in occurrences.items():
        for hit in hits or []:
            if not isinstance(hit, dict):
                continue
            if Path(str(hit.get("notebook", ""))).name == wanted:
                mine.append(str(arxiv_id))
                break
    if not mine:
        return PASS, "0 citation arXiv"
    uncovered = {str(x) for x in (payload.get("delta_not_covered") or [])}
    holes = sorted(i for i in mine if i in uncovered)
    if holes:
        return WARN, f"{len(mine)} citation(s), non couverte(s) : {', '.join(holes)}"
    return PASS, f"{len(mine)} citation(s), toutes couvertes"


def judge_na(reason: str) -> Judge:
    """Axe declare sans objet pour un .ipynb -- la raison fait partie du verdict."""
    def _judge(payload: Any, rc: int, notebook: str) -> tuple[str, str]:
        return NA, reason
    return _judge


# ---------------------------------------------------------------------------
# Registre des instruments -- les 7 axes nommes par l'acceptance 2
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Instrument:
    axis: str
    label: str
    scope: str          # "notebook" | "family" | "none"
    argv: tuple[str, ...]
    payload: str        # "stdout" | "outfile" | "none"
    judge: Judge
    note: str = ""
    # Un organe dont on PARSE la charge utile n'a pas d'extrait de stdout a
    # montrer : sa premiere ligne est l'accolade ouvrante du JSON, et le fait
    # utile est deja dans la colonne « detail ». On garde l'extrait pour les
    # organes a verdict binaire, ou il porte le message de l'organe.
    show_excerpt: bool = True


INSTRUMENTS: tuple[Instrument, ...] = (
    Instrument(
        axis="execution",
        label="Execution reelle",
        scope="notebook",
        argv=("{python}", "scripts/notebook_tools/check_null_exec.py", "{notebook}"),
        payload="stdout",
        judge=judge_rc,
        note="H.3 -- refuse une cellule de code non executee (execution_count null + sorties vides).",
    ),
    Instrument(
        axis="outputs",
        label="Outputs authentiques",
        scope="notebook",
        argv=("{python}", "scripts/notebook_tools/check_notebook_outputs_required.py",
              "--path", "{notebook}"),
        payload="stdout",
        judge=judge_rc,
        note=("C.2 -- sorties presentes et coherentes. La ligne de resume de l'organe "
              "compte les notebooks AVEC defauts, pas les notebooks scannes."),
    ),
    Instrument(
        axis="density",
        label="Densite pedagogique",
        scope="notebook",
        argv=("{python}", "scripts/notebook_tools/pedagogy_density.py",
              "{notebook}", "--json"),
        payload="stdout",
        judge=judge_counts(("summary", "below_threshold"), ("summary", "unmeasured")),
        show_excerpt=False,
        note=("Advisory -- plancher verrouille a 1200 par calibration (#10479) ; "
              "l'organe sort toujours 0, le signal est dans les compteurs."),
    ),
    Instrument(
        axis="cell_order",
        label="Ordre des cellules",
        scope="notebook",
        argv=("{python}", "scripts/notebook_tools/scan_cell_ordering.py",
              "{notebook}", "--json"),
        payload="stdout",
        judge=judge_counts(("reports",)),
        show_excerpt=False,
        note=("Une cellule d'interpretation placee avant la cellule qu'elle interprete "
              "est un defaut d'ordre (cell-interpretation-ordering)."),
    ),
    Instrument(
        axis="citations",
        label="Citations verifiees",
        scope="family",
        argv=("{python}", "scripts/notebook_tools/scan_arxiv_citations.py",
              "--workspace", "{family_dir}", "--out", "{outfile}"),
        payload="outfile",
        judge=judge_citations,
        show_excerpt=False,
        note=("Balaie la famille puis ne retient que les occurrences de ce notebook ; "
              "une reference arXiv hors du CSV couvert ressort en WARN."),
    ),
    Instrument(
        axis="twin_parity",
        label="Parite jumeau",
        scope="family",
        argv=("{python}", "scripts/notebook_tools/check_twin_parity.py",
              "--check", "--family", "{family}", "--json"),
        payload="stdout",
        judge=judge_counts(("drift",), ("missing",), ("numbering_drift",)),
        show_excerpt=False,
        note=("Registre twin_pairs.d -- un jumeau C#/Python dont la contrepartie "
              "derive, manque ou se renumeroie."),
    ),
    Instrument(
        axis="i18n",
        label="i18n (siblings FR/EN)",
        scope="none",
        argv=(),
        payload="none",
        judge=judge_na(
            "sans objet pour un .ipynb -- la convention sibling-pair porte sur les "
            "*.lean (code-style.md section Lean i18n, #4980)"
        ),
        note="Axe nomme par l'acceptance 2 ; declare NA ici, avec sa raison, plutot qu'omis.",
    ),
)

AXES: tuple[str, ...] = tuple(i.axis for i in INSTRUMENTS)

# Les 3 questions de l'acceptance 2, litteralement, chacune reliee aux axes
# dont la lecture doit nourrir la reponse.
QUESTIONS: tuple[tuple[str, tuple[str, ...]], ...] = (
    ("Est-ce que ca s'enseigne bien ?", ("execution", "outputs", "density")),
    ("Est-ce que l'exemple porte ?", ("cell_order", "citations")),
    ("Est-ce que je signe ?", ("twin_parity", "i18n")),
)


# ---------------------------------------------------------------------------
# Localisation du notebook
# ---------------------------------------------------------------------------

def normalize_notebook(notebook: str, repo_root: Path) -> str:
    """Chemin POSIX relatif au depot -- c'est la forme que les organes attendent."""
    text = str(notebook).replace("\\", "/")
    path = Path(text)
    if path.is_absolute():
        try:
            return path.resolve().relative_to(repo_root.resolve()).as_posix()
        except ValueError:
            return text
    return text


def family_of(notebook: str, root: str = NOTEBOOK_ROOT) -> str | None:
    """Premier composant sous <root>/ ('Sudoku', 'SymbolicAI'). None si hors racine."""
    nb = str(notebook).replace("\\", "/")
    prefix = root + "/"
    if not nb.startswith(prefix):
        return None
    head = nb[len(prefix):].split("/", 1)[0]
    return head or None


# ---------------------------------------------------------------------------
# Construction du dossier
# ---------------------------------------------------------------------------

@dataclass
class Row:
    axis: str
    label: str
    verdict: str
    detail: str
    provenance: str
    note: str = ""


@dataclass
class Dossier:
    notebook: str
    family: str | None
    rows: list[Row] = field(default_factory=list)

    @property
    def errors(self) -> list[Row]:
        return [r for r in self.rows if r.verdict == ERROR]


def _provenance(instrument: Instrument, argv: Sequence[str],
                result: RunResult | None, outfile: str | None = None) -> str:
    if instrument.scope == "none":
        return "sans objet (voir constat)"
    cmd = portable_command(argv, outfile)
    if result is None:
        return f"`{cmd}` -> non execute"
    if instrument.show_excerpt:
        seen = excerpt(result.stdout) or excerpt(result.stderr)
    else:
        seen = ""
    tail = f" -- {seen}" if seen else ""
    return f"`{cmd}` -> rc={result.rc}{tail}"


def build_dossier(notebook: str, repo_root: Path = REPO_ROOT,
                  runner: Callable[..., RunResult] = run_organ,
                  python_exe: str | None = None) -> Dossier:
    """Interroge chaque instrument et rend le dossier. Le notebook est la SEULE entree."""
    nb = normalize_notebook(str(notebook), repo_root)
    family = family_of(nb)
    python_exe = python_exe or sys.executable
    dossier = Dossier(notebook=nb, family=family)

    with tempfile.TemporaryDirectory(prefix="dossier-") as tmp:
        for instrument in INSTRUMENTS:
            if instrument.scope == "none":
                verdict, detail = instrument.judge(None, 0, nb)
                dossier.rows.append(Row(instrument.axis, instrument.label, verdict,
                                        detail, "sans objet (voir constat)",
                                        instrument.note))
                continue

            if instrument.scope == "family" and not family:
                dossier.rows.append(Row(
                    instrument.axis, instrument.label, NA,
                    f"hors de {NOTEBOOK_ROOT}/ : portee famille indeterminee",
                    "non execute (portee indeterminee)", instrument.note))
                continue

            outfile = str(Path(tmp) / f"{instrument.axis}.json")
            fields = {
                "python": python_exe,
                "notebook": nb,
                "family": family or "",
                "family_dir": f"{NOTEBOOK_ROOT}/{family}" if family else "",
                "outfile": outfile,
            }
            argv = [a.format(**fields) for a in instrument.argv]
            try:
                result = runner(argv, cwd=repo_root)
            except Exception as exc:  # organe injoignable = ERROR, jamais PASS
                dossier.rows.append(Row(
                    instrument.axis, instrument.label, ERROR,
                    f"organe non invocable : {type(exc).__name__}: {exc}",
                    f"`{portable_command(argv, outfile)}` -> non execute",
                    instrument.note))
                continue

            if instrument.payload == "outfile":
                try:
                    payload = json.loads(Path(outfile).read_text(encoding="utf-8"))
                except (OSError, json.JSONDecodeError):
                    payload = None
            elif instrument.payload == "stdout":
                payload = parse_json(result.stdout)
            else:
                payload = None

            verdict, detail = instrument.judge(payload, result.rc, nb)
            dossier.rows.append(Row(instrument.axis, instrument.label, verdict, detail,
                                    _provenance(instrument, argv, result, outfile),
                                    instrument.note))

    return dossier


# ---------------------------------------------------------------------------
# Rendu
# ---------------------------------------------------------------------------

def render_questions(dossier: Dossier) -> str:
    """Les 3 questions, chacune annotee de l'etat des axes dont elle depend."""
    by_axis = {r.axis: r for r in dossier.rows}
    lines = ["## Questions (jugement humain -- aucun instrument ne les tranche)", ""]
    for index, (question, axes) in enumerate(QUESTIONS, start=1):
        lines.append(f"{index}. **{question}**")
        for axis in axes:
            row = by_axis.get(axis)
            if row is None:
                continue
            lines.append(f"   - `{axis}` = **{row.verdict}** -- {row.detail}")
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def render_dossier(dossier: Dossier) -> str:
    counts = {v: 0 for v in (PASS, WARN, NA, ERROR)}
    for row in dossier.rows:
        counts[row.verdict] = counts.get(row.verdict, 0) + 1
    summary = ", ".join(f"{counts[v]} {v}" for v in (PASS, WARN, NA, ERROR) if counts[v])

    lines = [
        "# Dossier de revue editoriale -- instruments",
        "",
        f"- **Notebook** : `{dossier.notebook}`",
        f"- **Famille** : {dossier.family or '_(hors ' + NOTEBOOK_ROOT + ')_'}",
        f"- **Axes** : {summary}",
        "",
        "Chaque ligne vient d'un organe reel, cite dans la provenance. Un organe "
        "illisible sort en ERROR, jamais en PASS.",
        "",
        "| Axe | Instrument | Verdict | Provenance |",
        "|---|---|---|---|",
    ]
    for row in dossier.rows:
        lines.append(f"| `{row.axis}` | {row.label} | **{row.verdict}** -- {row.detail} "
                     f"| {row.provenance} |")
    lines += ["", render_questions(dossier)]
    return "\n".join(lines)


def dossier_to_json(dossier: Dossier) -> str:
    return json.dumps({
        "notebook": dossier.notebook,
        "family": dossier.family,
        "axes": [
            {"axis": r.axis, "label": r.label, "verdict": r.verdict,
             "detail": r.detail, "provenance": r.provenance}
            for r in dossier.rows
        ],
        "questions": [
            {"question": q, "axes": list(axes)} for q, axes in QUESTIONS
        ],
    }, indent=2, ensure_ascii=False)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Dossier de revue editoriale -- couche instruments (#11259).")
    parser.add_argument("--notebook", required=True,
                        help="SEUL chemin du notebook (relatif au depot ou absolu)")
    parser.add_argument("--repo", default=str(REPO_ROOT), help="racine du depot")
    parser.add_argument("--json", action="store_true", dest="as_json",
                        help="sortie machine")
    parser.add_argument("--out", default=None, help="ecrire le dossier dans ce fichier")
    args = parser.parse_args(argv)

    repo_root = Path(args.repo).resolve()
    dossier = build_dossier(args.notebook, repo_root=repo_root)
    rendered = dossier_to_json(dossier) if args.as_json else render_dossier(dossier)

    if args.out:
        Path(args.out).write_text(rendered, encoding="utf-8")
        print(f"dossier ecrit : {args.out}")
    else:
        print(rendered)

    for row in dossier.errors:
        print(f"ERROR {row.axis}: {row.detail}", file=sys.stderr)
    return 1 if dossier.errors else 0


if __name__ == "__main__":
    sys.exit(main())
