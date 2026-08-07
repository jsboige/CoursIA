"""Detecteur Phase 1 EPIC #9768 -- degeneration numerique sur commits non-substantiels.

Cible 4 categories documentees dans l'EPIC #9768 (parent issue de l'audit
forensic Phase 0 tranche ICT/IIT, issue #9787) :

  D1  Provenance orpheline
      Un nombre publie dans la prose (cellule markdown ou commentaire) n'est
      PAS reproductible depuis les outputs Jupyter actuellement commits sur
      la meme branche. Cas-type : un mainteneur ecrivant "Phi = 0.69" en prose
      alors que l'execution produit Phi = 0.42, sans mise a jour conjointe.

  D3  Restauration partielle
      Un commit dont le sujet mentionne "restore" / "revert" retablit des
      outputs numeriques QUI DIFFERENT des valeurs d'avant la perte.
      Cas-type : un git checkout sur un commit anterieur suivi d'un commit
      "restore" qui ne pointe pas exactement sur le meme contenu.

  D4  Rename transportant une valeur
      Un rename/move (git log --follow) qui deplace une valeur numerique
      d'un contexte a un autre. Cas-type : un notebook deplace de
      `recherche/` vers `production/` conserve les outputs mais le lecteur
      attend la rigueur de production alors que les resultats etaient
      exploratoires.

  D5  Coquille silencieuse
      Delta numerique IMPORTANT (seuil 20% relatif sur la mediane de sortie)
      sur un diff de source MINUSCULE (e.g. 1 caractere corrige) qui ne leve
      aucune exception mais degrade silencieusement le resultat.
      Cas-type : `np.linspace(0, 1, 100)` -> `np.linspace(0, 1, 10)` change
      la granularite sans prevenir ; `range(100)` -> `range(10)` pareil.

Conception
----------
Le detecteur combine 3 signaux :

  1. **Signature numerique** : mediane + ecart-type + count des nombres
     extraits des outputs Jupyter (texte plain). Toute modification de la
     signature au-dela de 5% entre 2 revisions consecutives est un saut.

  2. **Classification du commit** : `git log --format=%s` permet d'identifier
     les commits "non-substantiels" (prefixe fix/, docs/, chore/, etc.) qui
     ne sont PAS censes modifier les outputs.

  3. **Provenance HEAD** : pour D1, le verdict exige que les nombres cites
     en prose soient presents dans les outputs HEAD avec une tolerance.

Le verdict final est l'union des 4 detecteurs : SAIN si aucun signal,
D1+/D3+/D4+/D5+ si un seul signal, MIXED si plusieurs, INDETERMINE si
donnees insuffisantes (notebook jamais execute, ou <2 revisions).

Note methodologique
-------------------
Ce script ne **declare jamais** ce qu'il faut corriger -- chaque verdict
D1+/D3+/D4+/D5+ est un **point de depart d'investigation**. Un D3+ peut
etre un artefact de git filter-branch, un D5+ peut etre une correction
volontaire documentee ailleurs. Le jugement reste humain / review-bot.

Mode CI
-------
    python scan_d1_d3_d4_d5.py MyIA.AI.Notebooks/IIT/ICT-Series/ --check

Exit 1 si au moins un verdict D1+/D3+/D4+/D5+ (mode CI strict).
Exit 0 sinon (verdict SAIN ou INDETERMINE uniquement).

Conformite harnais
------------------
- Regle F (env repair not bypass) : 0 dependance externe (Python 3.10+ stdlib).
- audit-cross-source-distillation R1 : verdict stdout/JSON, JAMAIS de rapport
  AUDIT-D*.md commite dans l'arbre.
- catalog-pr-hygiene R1 : 0 modification catalogue (le script lit, n'ecrit pas).
- C.1 : 0 erreur volontaire (pas de `raise NotImplementedError` etc.).

Voir aussi
----------
- EPIC #9768 : taxonomie complete de la degeneration
- Issue #9787 (Phase 0 tranche ICT/IIT) : calibration empirique du seuil
- scripts/notebook_tools/forensic_scan.py : orthogonal (cat. A/B/C/D/E execution)
- scripts/notebook_tools/regression_scan.py : orthogonal (axis-2 SOFT markers)
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Iterable, Sequence


# --------------------------------------------------------------------------- #
#  Configuration
# --------------------------------------------------------------------------- #

# Prefixes de commit consideres "non-substantiels" -- ne sont PAS censes
# modifier les outputs numeriques. Heuristique conservatrice : si tu changes
# du code ou des donnees, le prefixe est feat()/fix(major)/perf() etc.,
# JAMAIS docs/chore/style/...
NON_SUBSTANTIAL_PREFIXES: tuple[str, ...] = (
    "docs(",
    "chore(",
    "refactor(",
    "style(",
    "test(",
    "build(",
    "ci(",
)

# Verbes "restore" / "revert" identifies comme declencheurs D3 (restauration
# partielle). On regarde le sujet du commit (lowercase, premiere ligne).
RESTORE_VERBS: tuple[str, ...] = (
    "restore",
    "revert",
    "rollback",
    "resurrect",
)

# Verbes "rename" / "move" identifies comme declencheurs D4.
RENAME_VERBS: tuple[str, ...] = (
    "relocate",
    "rename",
    "reorganize",
    "move",
    "homogenize",
    "repackage",
)

# Seuil de saut relatif sur la mediane des outputs pour D5.
RELATIVE_JUMP_THRESHOLD: float = 0.20  # 20%

# Tolerance signature numerique entre 2 revisions consecutives (median+std+count).
SIGNATURE_CHANGE_THRESHOLD: float = 0.05  # 5%

# Bornes des nombres extraits : en-dessous c'est trivial (0, indices de boucle),
# au-dessus c'est probablement un timestamp Unix ou un numero de build.
MIN_NUMBER_VALUE: float = 1e-6
MAX_NUMBER_VALUE: float = 1e9

# Pour le detecteur D1 : seuil en-dessous duquel un nombre de prose est
# considere comme non-candidat (identifiants, indices, references comme
# "ICT-1", "#4588", "-1"). On vise les nombres "mesurables" -- typiquement
# entre 1e-3 et 1000.
D1_PROSE_MIN: float = 1e-3
D1_PROSE_MAX: float = 1e3

# Tolerance de proximite prose <-> outputs pour D1. 5% relatif OU exactement
# egal (pour gerer les cas ou la prose arrondit a 1e-2 et l'output a 1e-3).
D1_PROXIMITY_REL: float = 0.05
D1_PROXIMITY_ABS: float = 1e-6

# Ratio minimal d'orphelins pour classer D1+. En-dessous, on considere que
# les "orphelins" sont des references croisees (#4588, ICT-3, etc.) et non
# des mesures -- le bruit depasse le signal.
D1_ORPHAN_RATIO_THRESHOLD: float = 0.30

# Taille minimale de la mediane pour considerer un saut relatif (evite les
# divisions par ~zero sur des sorties tres petites).
MEDIAN_FLOOR_FOR_JUMP: float = 1e-6


# --------------------------------------------------------------------------- #
#  Dataclasses
# --------------------------------------------------------------------------- #


@dataclass
class NotebookRevision:
    """Une revision (= un commit) d'un notebook."""
    sha: str
    subject: str
    is_non_substantial: bool
    numbers_in_outputs: list[float] = field(default_factory=list)
    cells_count: int = 0


@dataclass
class NumericSignature:
    """Signature compacte des outputs numeriques d'un notebook."""
    median: float = 0.0
    std: float = 0.0
    count: int = 0

    @classmethod
    def from_numbers(cls, numbers: Sequence[float]) -> "NumericSignature":
        if not numbers:
            return cls()
        sorted_n = sorted(numbers)
        median = sorted_n[len(sorted_n) // 2]
        if len(sorted_n) > 1:
            mean = sum(sorted_n) / len(sorted_n)
            var = sum((x - mean) ** 2 for x in sorted_n) / len(sorted_n)
            std = var ** 0.5
        else:
            std = 0.0
        return cls(median=float(median), std=float(std), count=len(sorted_n))

    def changed_from(self, prev: "NumericSignature") -> bool:
        """Vrai si la signature a change au-dela de SIGNATURE_CHANGE_THRESHOLD."""
        if prev.count == 0 or self.count == 0:
            return False
        # Mediane
        if prev.median != 0 and abs(self.median - prev.median) / abs(prev.median) > SIGNATURE_CHANGE_THRESHOLD:
            return True
        if prev.median == 0 and self.median != 0:
            return True
        # Ecart-type
        if prev.std > 0 and abs(self.std - prev.std) / abs(prev.std) > SIGNATURE_CHANGE_THRESHOLD:
            return True
        return False


@dataclass
class ForensicFinding:
    """Un finding individuel d'un des 4 detecteurs."""
    category: str  # "D1" / "D3" / "D4" / "D5"
    sha: str
    subject: str
    detail: str


@dataclass
class NotebookForensic:
    """Verdict complet d'un notebook sur l'ensemble de ses revisions."""
    path: str
    total_revisions: int
    verdict: str  # "SAIN" / "D1+" / "D3+" / "D4+" / "D5+" / "MIXED" / "INDETERMINE"
    findings: list[ForensicFinding] = field(default_factory=list)
    notes: str = ""

    @property
    def is_pathological(self) -> bool:
        """Vrai si le verdict signale une degeneration.

        D1+ (provenance orpheline) est pathologique MEME sur verdict global
        INDETERMINE, car il ne depend pas de l'historique du notebook -- un
        seul commit suffit pour le signaler.
        """
        if self.verdict in ("D3+", "D4+", "D5+", "MIXED"):
            return True
        if any(f.category == "D1" for f in self.findings):
            return True
        return False


# --------------------------------------------------------------------------- #
#  Git plumbing
# --------------------------------------------------------------------------- #


def _run_git(args: Sequence[str], cwd: str) -> str:
    """Execute une commande git dans cwd, retourne stdout."""
    result = subprocess.run(
        ["git", *args],
        cwd=cwd,
        capture_output=True,
        text=True,
        check=False,
        encoding="utf-8",
        errors="replace",
    )
    if result.returncode != 0:
        raise RuntimeError(
            f"git {' '.join(args)} failed ({result.returncode}): {result.stderr[:300]}"
        )
    return result.stdout


def get_revisions(notebook: str, repo: str) -> list[tuple[str, str]]:
    """Retourne [(sha, subject)] pour un notebook, en suivant les renames."""
    fmt = "%H%x1f%s"  # SHA + subject, separateur unit (0x1f)
    out = _run_git(
        ["log", "--follow", f"--format={fmt}", "--", notebook],
        cwd=repo,
    )
    revs: list[tuple[str, str]] = []
    for line in out.splitlines():
        line = line.strip()
        if not line:
            continue
        parts = line.split("\x1f", 1)
        if len(parts) != 2:
            continue
        revs.append((parts[0], parts[1]))
    return revs


def read_notebook_at_revision(notebook: str, sha: str, repo: str) -> str:
    """Retourne le contenu JSON d'un notebook a une revision donnee."""
    return _run_git(["show", f"{sha}:{notebook}"], cwd=repo)


def get_current_outputs(notebook: str, repo: str) -> str:
    """Retourne le contenu brut de la version actuelle (HEAD) du notebook."""
    return _run_git(["show", f"HEAD:{notebook}"], cwd=repo)


# --------------------------------------------------------------------------- #
#  Extraction des nombres depuis les outputs Jupyter
# --------------------------------------------------------------------------- #


_NUMBER_RE = re.compile(r"[-+]?\d*\.?\d+(?:[eE][-+]?\d+)?")


def _extract_numbers_from_text(text: str) -> list[float]:
    """Extrait tous les nombres d'une chaine. Filtre les valeurs triviales."""
    nums: list[float] = []
    for m in _NUMBER_RE.finditer(text):
        try:
            v = float(m.group(0))
        except ValueError:
            continue
        if abs(v) < MIN_NUMBER_VALUE or abs(v) > MAX_NUMBER_VALUE:
            continue
        nums.append(v)
    return nums


def extract_output_numbers(notebook_json: str) -> tuple[int, list[float]]:
    """Parse un notebook Jupyter, retourne (n_cells_code, liste_nombres_outputs).

    Couvre les formats de sortie varies :
    - outputs[*].text : str directe
    - outputs[*].data."text/plain" : str OU liste de str
    Les erreurs (output_type == "error") sont ignorees (l'erreur ne produit
    pas de nombre significatif).
    """
    try:
        nb = json.loads(notebook_json)
    except json.JSONDecodeError:
        return 0, []
    cells = nb.get("cells", [])
    code_cells = [c for c in cells if c.get("cell_type") == "code"]
    nums: list[float] = []
    for c in code_cells:
        outputs = c.get("outputs") or []
        for out in outputs:
            if not isinstance(out, dict):
                continue
            if out.get("output_type") == "error":
                continue
            if "text" in out and isinstance(out["text"], str):
                nums.extend(_extract_numbers_from_text(out["text"]))
            elif "data" in out and isinstance(out["data"], dict):
                t = out["data"].get("text/plain")
                if isinstance(t, str):
                    nums.extend(_extract_numbers_from_text(t))
                elif isinstance(t, list):
                    for item in t:
                        if isinstance(item, str):
                            nums.extend(_extract_numbers_from_text(item))
    return len(code_cells), nums


def extract_prose_numbers(notebook_json: str) -> list[tuple[int, float]]:
    """Extrait les nombres publies dans les cellules markdown d'un notebook.

    Retourne [(cell_index, valeur), ...]. Sert au detecteur D1 (provenance
    orpheline) : comparer la prose aux outputs de la version actuelle.

    Note : on ne tente PAS de comprendre le contexte semantique du nombre
    (label "Phi = 0.69" vs "alpha = 0.69"). Cette detection est DELIBEREMENT
    conservatrice -- on extrait les nombres "mesurables" de toutes les cellules
    md (dans la plage [D1_PROSE_MIN, D1_PROSE_MAX]), et on verifie la presence
    dans les outputs avec tolerance D1_PROXIMITY_REL.
    """
    try:
        nb = json.loads(notebook_json)
    except json.JSONDecodeError:
        return []
    cells = nb.get("cells", [])
    out: list[tuple[int, float]] = []
    for i, c in enumerate(cells):
        if c.get("cell_type") != "markdown":
            continue
        src = c.get("source", "")
        if isinstance(src, list):
            src = "".join(src)
        for m in _NUMBER_RE.finditer(src):
            try:
                v = float(m.group(0))
            except ValueError:
                continue
            if abs(v) < D1_PROSE_MIN or abs(v) > D1_PROSE_MAX:
                continue
            # D1 vise les valeurs mesurables positives. Les nombres negatifs
            # (-1, -2) sont generalement des sentinelles / indices / erreurs
            # codes, pas des mesures publiees.
            if v <= 0:
                continue
            out.append((i, v))
    return out


# --------------------------------------------------------------------------- #
#  Classification d'un commit
# --------------------------------------------------------------------------- #


def _is_non_substantial(subject: str) -> bool:
    s = subject.lower().strip()
    return any(s.startswith(p) for p in NON_SUBSTANTIAL_PREFIXES)


def _has_restore_verb(subject: str) -> bool:
    s = subject.lower().strip()
    return any(v in s for v in RESTORE_VERBS)


def _has_rename_verb(subject: str) -> bool:
    s = subject.lower().strip()
    return any(v in s for v in RENAME_VERBS)


# --------------------------------------------------------------------------- #
#  Detecteurs (D1, D3, D4, D5)
# --------------------------------------------------------------------------- #


def detect_d1(notebook: str, repo: str) -> list[ForensicFinding]:
    """D1 : provenance orpheline.

    Un nombre publie dans la prose (cellule markdown) n'est PAS present dans
    les outputs HEAD. Strategie : extraire (a) tous les nombres des cellules
    markdown HEAD, (b) tous les nombres des outputs code HEAD, puis verifier
    que chaque nombre prose a un candidat proche dans outputs ( tolerance 1%
    relatif ou absolu 1e-6).
    """
    findings: list[ForensicFinding] = []
    try:
        head_json = get_current_outputs(notebook, repo)
    except RuntimeError:
        return findings

    prose_numbers = extract_prose_numbers(head_json)
    if not prose_numbers:
        return findings

    _, output_numbers = extract_output_numbers(head_json)
    if not output_numbers:
        # Pas d'output du tout : tous les nombres prose sont orphelins.
        findings.append(
            ForensicFinding(
                category="D1",
                sha="HEAD",
                subject="<current>",
                detail=(
                    f"{len(prose_numbers)} nombre(s) dans la prose, "
                    f"0 nombre dans les outputs (notebook non execute ?)"
                ),
            )
        )
        return findings

    # Ensemble des outputs pour recherche rapide (tolerance D1_PROXIMITY_REL).
    orphans: list[tuple[int, float]] = []
    for cell_idx, v in prose_numbers:
        candidate_found = False
        for ov in output_numbers:
            if abs(ov) < D1_PROXIMITY_ABS:
                # Output quasi-nul : n'est PAS un candidat raisonnable pour
                # un nombre "mesurable" de la prose. On ignore cette branche.
                continue
            if abs(v) < D1_PROXIMITY_ABS:
                # Nombre de prose quasi-nul : candidat uniquement si un output
                # est egalement quasi-nul.
                candidate_found = True
                break
            if abs(v - ov) / abs(ov) <= D1_PROXIMITY_REL:
                candidate_found = True
                break
        if not candidate_found:
            orphans.append((cell_idx, v))

    if not orphans:
        return findings

    # Garde-fou : on ne signale D1 QUE si la proportion d'orphelins est
    # substantielle. Sinon les "orphelins" sont probablement des references
    # croisees (#4588, ICT-3, ...) et non des mesures -- bruit > signal.
    orphan_ratio = len(orphans) / len(prose_numbers) if prose_numbers else 0
    if orphan_ratio < D1_ORPHAN_RATIO_THRESHOLD:
        return findings

    # Limite le bruit : on signale les 5 premiers orphelins.
    sample = orphans[:5]
    findings.append(
        ForensicFinding(
            category="D1",
            sha="HEAD",
            subject="<current>",
            detail=(
                f"{len(orphans)}/{len(prose_numbers)} ({orphan_ratio:.0%}) nombre(s) "
                f"mesurables de la prose sans candidat proche dans les outputs. "
                f"Exemples : "
                + ", ".join(f"cell[{c}]={v:.4g}" for c, v in sample)
            ),
        )
    )
    return findings


def detect_d3(revisions: list[NotebookRevision]) -> list[ForensicFinding]:
    """D3 : restauration partielle.

    Un commit dont le sujet contient un verbe "restore/revert" ET dont la
    signature numerique differe de la revision precedente (donc ne retablit
    pas exactement l'etat anterieur).
    """
    findings: list[ForensicFinding] = []
    for i in range(1, len(revisions)):
        r = revisions[i]
        if not _has_restore_verb(r.subject):
            continue
        prev = revisions[i - 1]
        prev_sig = NumericSignature.from_numbers(prev.numbers_in_outputs)
        cur_sig = NumericSignature.from_numbers(r.numbers_in_outputs)
        if cur_sig.changed_from(prev_sig):
            findings.append(
                ForensicFinding(
                    category="D3",
                    sha=r.sha,
                    subject=r.subject,
                    detail=(
                        f"Restore numerique : mediane {prev_sig.median:.4g} -> "
                        f"{cur_sig.median:.4g} (n {prev_sig.count} -> {cur_sig.count})"
                    ),
                )
            )
    return findings


def detect_d4(revisions: list[NotebookRevision]) -> list[ForensicFinding]:
    """D4 : rename/move transportant une valeur.

    Un commit dont le sujet contient un verbe "relocate/rename/reorganize" ET
    dont la signature numerique a change (donc le contenu numerique a ete
    transporte ou modifie en parallele du rename).
    """
    findings: list[ForensicFinding] = []
    for i in range(1, len(revisions)):
        r = revisions[i]
        if not _has_rename_verb(r.subject):
            continue
        prev = revisions[i - 1]
        prev_sig = NumericSignature.from_numbers(prev.numbers_in_outputs)
        cur_sig = NumericSignature.from_numbers(r.numbers_in_outputs)
        if cur_sig.changed_from(prev_sig):
            findings.append(
                ForensicFinding(
                    category="D4",
                    sha=r.sha,
                    subject=r.subject,
                    detail=(
                        f"Relocate numerique : mediane {prev_sig.median:.4g} -> "
                        f"{cur_sig.median:.4g}"
                    ),
                )
            )
    return findings


def detect_d5(revisions: list[NotebookRevision]) -> list[ForensicFinding]:
    """D5 : saut numerique sous commit non-substantiel.

    Un commit classifie non-substantiel (docs/chore/style/...) sous lequel la
    mediane des outputs a bouge de plus de RELATIVE_JUMP_THRESHOLD (20%).
    """
    findings: list[ForensicFinding] = []
    for i in range(1, len(revisions)):
        cur = revisions[i]
        if not cur.is_non_substantial:
            continue
        prev = revisions[i - 1]
        prev_nums = prev.numbers_in_outputs
        cur_nums = cur.numbers_in_outputs
        if not prev_nums or not cur_nums:
            continue
        prev_median = sorted(prev_nums)[len(prev_nums) // 2]
        cur_median = sorted(cur_nums)[len(cur_nums) // 2]
        if abs(prev_median) < MEDIAN_FLOOR_FOR_JUMP:
            continue
        rel = abs(cur_median - prev_median) / abs(prev_median)
        if rel >= RELATIVE_JUMP_THRESHOLD:
            findings.append(
                ForensicFinding(
                    category="D5",
                    sha=cur.sha,
                    subject=cur.subject,
                    detail=(
                        f"Saut mediane {prev_median:.4g} -> {cur_median:.4g} "
                        f"(relatif {rel:.1%}) sous commit non-substantiel"
                    ),
                )
            )
    return findings


# --------------------------------------------------------------------------- #
#  Orchestration
# --------------------------------------------------------------------------- #


def _build_revisions(notebook: str, repo: str) -> list[NotebookRevision]:
    """Construit la liste des NotebookRevision pour un notebook."""
    revs_meta = get_revisions(notebook, repo)
    revs: list[NotebookRevision] = []
    for sha, subject in revs_meta:
        try:
            nb_json = read_notebook_at_revision(notebook, sha, repo)
            cells_count, nums = extract_output_numbers(nb_json)
        except RuntimeError:
            cells_count, nums = 0, []
        revs.append(
            NotebookRevision(
                sha=sha,
                subject=subject,
                is_non_substantial=_is_non_substantial(subject),
                numbers_in_outputs=nums,
                cells_count=cells_count,
            )
        )
    return revs


def forensic_scan(notebook: str, repo: str) -> NotebookForensic:
    """Verdict complet pour un notebook : D1 + D3 + D4 + D5."""
    revs = _build_revisions(notebook, repo)
    findings: list[ForensicFinding] = []
    findings.extend(detect_d1(notebook, repo))
    findings.extend(detect_d3(revs))
    findings.extend(detect_d4(revs))
    findings.extend(detect_d5(revs))

    if not revs:
        verdict = "INDETERMINE"
        notes = "Aucune revision accessible"
    elif len(revs) < 2:
        verdict = "INDETERMINE"
        notes = "Une seule revision -- comparaison impossible"
    elif not findings:
        verdict = "SAIN"
        notes = (
            f"{len(revs)} revision(s), aucune degenerescence detectee "
            f"(D1, D3, D4, D5)"
        )
    else:
        # Determine verdict : MIXED si plusieurs categories, sinon la categorie unifie.
        cats = sorted({f.category for f in findings})
        if len(cats) > 1:
            verdict = "MIXED"
        else:
            verdict = f"{cats[0]}+"
        notes = f"{len(findings)} finding(s) sur categorie(s) {', '.join(cats)}"

    return NotebookForensic(
        path=notebook,
        total_revisions=len(revs),
        verdict=verdict,
        findings=findings,
        notes=notes,
    )


def forensic_scan_paths(notebooks: Iterable[str], repo: str) -> list[NotebookForensic]:
    """Verdict pour une liste de notebooks."""
    return [forensic_scan(nb, repo) for nb in notebooks]


def forensic_scan_directory(directory: str, repo: str) -> list[NotebookForensic]:
    """Verdict pour tous les notebooks d'un repertoire (recursive).

    Couvre les fichiers *.ipynb. Les sous-repertoires archives (commencant
    par `_` ou nommes `archive`/`_archive`) sont exclus par convention.
    """
    base = Path(repo) / directory
    if not base.exists():
        return []
    notebooks = sorted(
        str(p.relative_to(repo)).replace("\\", "/")
        for p in base.rglob("*.ipynb")
        if not any(part.startswith("_") or part in ("archive", "node_modules")
                   for part in p.relative_to(base).parts)
    )
    return forensic_scan_paths(notebooks, repo)


# --------------------------------------------------------------------------- #
#  Sortie texte / JSON
# --------------------------------------------------------------------------- #


def render_text(results: list[NotebookForensic]) -> str:
    """Format texte : table + detail par notebook."""
    lines: list[str] = []
    lines.append("| Notebook | Revisions | Verdict | Findings | Note |")
    lines.append("|---|---|---|---|---|")
    for r in results:
        nb_name = Path(r.path).name
        n_findings = len(r.findings)
        first_cat = r.findings[0].category if r.findings else "-"
        lines.append(
            f"| `{nb_name}` | {r.total_revisions} | **{r.verdict}** | "
            f"{n_findings} ({first_cat}) | {r.notes[:60]} |"
        )
    lines.append("")
    lines.append("## Detail")
    for r in results:
        if not r.findings:
            continue
        lines.append(f"### `{Path(r.path).name}` -- verdict **{r.verdict}**")
        for f in r.findings[:5]:
            lines.append(
                f"- **{f.category}** `{f.sha[:8]}` {f.subject[:70]}\n"
                f"  {f.detail}"
            )
        lines.append("")
    return "\n".join(lines)


# --------------------------------------------------------------------------- #
#  CLI
# --------------------------------------------------------------------------- #


def _build_arg_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        description="Detecteur Phase 1 EPIC #9768 : D1/D3/D4/D5 sur notebooks Jupyter."
    )
    p.add_argument(
        "targets",
        nargs="*",
        help="Fichiers .ipynb ou repertoires (recursive). Vide = stdin interactif.",
    )
    p.add_argument(
        "--repo",
        default=".",
        help="Chemin du worktree git (defaut : cwd).",
    )
    p.add_argument(
        "--format",
        choices=["text", "json"],
        default="text",
        help="Format de sortie (defaut : text).",
    )
    p.add_argument(
        "--check",
        action="store_true",
        help="Mode CI : exit 1 si au moins un verdict D1+/D3+/D4+/D5+/MIXED.",
    )
    return p


def main(argv: Iterable[str] | None = None) -> int:
    parser = _build_arg_parser()
    args = parser.parse_args(list(argv) if argv is not None else None)

    if not args.targets:
        parser.error("au moins un fichier .ipynb ou repertoire requis")

    repo = args.repo
    all_results: list[NotebookForensic] = []
    for target in args.targets:
        target_path = Path(repo) / target
        if target_path.is_dir():
            all_results.extend(forensic_scan_directory(target, repo))
        elif target_path.is_file() and target.endswith(".ipynb"):
            all_results.append(forensic_scan(target, repo))
        else:
            print(f"[warn] cible ignoree (pas un .ipynb ni repertoire) : {target}",
                  file=sys.stderr)

    if args.format == "json":
        out = json.dumps(
            [asdict(r) for r in all_results],
            indent=2,
            ensure_ascii=False,
        )
        print(out)
    else:
        print(render_text(all_results))

    if args.check:
        n_pathological = sum(1 for r in all_results if r.is_pathological)
        return 1 if n_pathological > 0 else 0
    return 0


if __name__ == "__main__":
    sys.exit(main())
