"""Lean file utilities: sorry extraction, goal probing, sorry replacement verification."""

import re
from pathlib import Path
from typing import Optional, Tuple


# Patterns marking an intentionally-honest sorry (theoretical impossibility,
# not a TODO). When any of these appear in the comments immediately above a
# sorry, the prover MUST refuse to attack it.
_HONEST_SORRY_PATTERNS = [
    r"\bFIXME\b",
    r"cannot\s+be\s+proved",
    r"unprovable",
    r"not\s+derivable",
    r"counter-?example",
    r"needs?\s+a?\s*stronger\s+hypothes",
    r"requires?\s+a?\s*stronger\s+hypothes",
    r"impossible\s+with",
    r"DO\s+NOT\s+TOUCH",
]
_HONEST_SORRY_RE = re.compile(
    "|".join(_HONEST_SORRY_PATTERNS), re.IGNORECASE,
)


def is_honest_sorry(filepath: str, sorry_line: int,
                    lookback: int = 12) -> Tuple[bool, str]:
    """Check whether the sorry at `sorry_line` is documented as intentionally
    unprovable.

    Scans up to `lookback` consecutive comment lines (`--` or `/-` … `-/`)
    immediately above the sorry. If any contain HONEST patterns (FIXME,
    "cannot be proved", "counter-example", "needs a stronger hypothesis",
    etc.), the sorry is HONEST and must NOT be attacked.

    Returns (is_honest, reason). The reason is the matched comment block.
    """
    try:
        content = Path(filepath).read_text(encoding="utf-8")
    except OSError as e:
        return False, f"file read error: {e}"

    lines = content.split("\n")
    if sorry_line < 1 or sorry_line > len(lines):
        return False, f"line {sorry_line} out of range"

    # Collect contiguous comment block above the sorry
    comments = []
    for i in range(sorry_line - 2, max(sorry_line - 2 - lookback, -1), -1):
        stripped = lines[i].strip()
        if stripped.startswith("--") or stripped.startswith("/-") or stripped.endswith("-/"):
            comments.insert(0, stripped)
        elif not stripped:
            # Allow one blank line within comment block
            if comments:
                continue
            break
        else:
            break

    if not comments:
        return False, ""

    block = "\n".join(comments)
    if _HONEST_SORRY_RE.search(block):
        return True, block
    return False, ""


def extract_sorry_block(filepath: str, sorry_line: int, context_lines: int = 15) -> dict:
    """Extract the sorry context from a .lean file.

    Returns dict with:
      - full_file: complete file content
      - sorry_line: 1-based line number of sorry
      - context_before: lines before sorry (indented proof context)
      - context_after: lines after sorry (continuation)
      - proof_block: the full proof block containing the sorry
      - indentation: indentation level of the sorry
      - goal_hint: extracted from comments before sorry
    """
    content = Path(filepath).read_text(encoding="utf-8")
    lines = content.split("\n")

    if sorry_line < 1 or sorry_line > len(lines):
        return {"error": f"sorry_line {sorry_line} out of range (1-{len(lines)})"}

    sorry_text = lines[sorry_line - 1]
    indent = len(sorry_text) - len(sorry_text.lstrip())
    indent_str = sorry_text[:indent]

    # Extract goal hints from comments before sorry
    goal_hints = []
    for i in range(sorry_line - 2, max(sorry_line - 20, -1), -1):
        line = lines[i].strip()
        if line.startswith("--"):
            goal_hints.insert(0, line)
        elif line and not line.startswith("--"):
            break

    # Find the start of the proof block (theorem/lemma line)
    proof_start = sorry_line - 1
    for i in range(sorry_line - 2, -1, -1):
        stripped = lines[i].strip()
        if stripped.startswith("theorem ") or stripped.startswith("lemma ") or \
           stripped.startswith("private theorem ") or stripped.startswith("private lemma "):
            proof_start = i
            break
        if stripped.startswith("def ") or stripped.startswith("noncomputable def "):
            proof_start = i
            break

    # Find the next top-level declaration after sorry to bound the proof
    proof_end = sorry_line
    for i in range(sorry_line, min(sorry_line + 30, len(lines))):
        stripped = lines[i].strip()
        if stripped.startswith("theorem ") or stripped.startswith("lemma ") or \
           stripped.startswith("/-!") or stripped.startswith("end ") or \
           (stripped and not stripped.startswith("--") and not stripped.startswith("·")
            and not stripped.startswith("have ") and not stripped.startswith("rw ")
            and not stripped.startswith("simp") and not stripped.startswith("exact")
            and not stripped.startswith("intro") and not stripped.startswith("apply")
            and not stripped.startswith("cases") and not stripped.startswith("obtain")
            and not stripped.startswith("by_cases") and not stripped.startswith("refine")
            and not stripped.startswith("fun") and not stripped.startswith("ext")
            and not stripped.startswith("constructor") and indent > 0
            and lines[i][:1] not in (" ", "\t")):
            proof_end = i
            break

    context_before_lines = lines[max(0, sorry_line - 1 - context_lines):sorry_line - 1]
    context_after_lines = lines[sorry_line:min(len(lines), sorry_line + context_lines)]

    return {
        "filepath": filepath,
        "sorry_line": sorry_line,
        "sorry_text": sorry_text.strip(),
        "indentation": indent,
        "indent_str": indent_str,
        "goal_hints": "\n".join(goal_hints),
        "context_before": "\n".join(context_before_lines),
        "context_after": "\n".join(context_after_lines),
        "proof_block": "\n".join(lines[proof_start:proof_end + 1]),
        "full_file": content,
    }


def get_goal_state(filepath: str, sorry_line: int) -> Optional[str]:
    """Extract the actual Lean goal state at a sorry by provoking a type-mismatch error.

    Tries multiple probes in sequence: exact (), exact rfl.
    Only considers errors at the EXACT sorry line to avoid cascade errors.
    For deeply nested sorries (indent >= 8), skips probing and uses heuristics.
    """
    from .verifier import get_verifier

    content = Path(filepath).read_text(encoding="utf-8")
    lines = content.split("\n")

    if sorry_line < 1 or sorry_line > len(lines):
        return None

    sorry_text = lines[sorry_line - 1]
    indent = len(sorry_text) - len(sorry_text.lstrip())
    indent_str = " " * indent

    # Skip probing for deeply nested sorries — cascade errors make it unreliable
    if indent >= 8:
        print(f"  [GoalExtract] Deeply nested sorry (indent={indent}), using heuristic")
        return _heuristic_goal_extract(lines, sorry_line)

    project_dir = Path(filepath).parent.parent
    verifier = get_verifier(str(project_dir))
    subdir = Path(filepath).parent.name
    relative_path = f"{subdir}/_GoalExtract.lean"
    tmp_path = Path(filepath).parent / "_GoalExtract.lean"

    # Try multiple probes to extract goal state
    probes = [
        "exact ()",    # Works for Unit goals; also produces type mismatch for others
        "exact rfl",   # Works for equality goals (a = b)
        "exact (0 : Nat)",  # Produces type mismatch for most non-Nat goals
        "exact True.intro",  # Produces type mismatch for non-Prop goals
        "exact 42",    # Last resort: almost always type-mismatches
    ]

    for probe in probes:
        new_lines = lines[:sorry_line - 1] + [indent_str + probe] + lines[sorry_line:]
        new_content = "\n".join(new_lines)
        tmp_path.write_text(new_content, encoding="utf-8")

        result = verifier.verify_project_file(relative_path)

        raw_output = result.get("raw_output", "")

        # Accept errors within ±3 lines of the sorry — nested tactic blocks
        # can shift error reporting to adjacent lines.
        # For unsolved goals (bullet-point sorrys), allow much wider tolerance
        # since the unsolved case can be far from the sorry line.
        LINE_TOLERANCE = 3
        UNSOLVED_GOAL_TOLERANCE = 25
        target_errors = []
        collecting = False
        for line in raw_output.split("\n"):
            # Match both "file:line:col: error: msg" and "error: file:line:col: msg"
            m_err = re.match(r".*?(\d+):\d+: error: (.*)", line)
            if not m_err:
                m_err = re.match(r"error: .*?(\d+):\d+: (.*)", line)
            if m_err:
                err_line = int(m_err.group(1))
                if abs(err_line - sorry_line) <= LINE_TOLERANCE:
                    target_errors.append(line)
                    collecting = True
                else:
                    collecting = False
            elif collecting:
                if line.strip() == "" or re.match(r".*?\d+:\d+: ", line):
                    collecting = False
                else:
                    target_errors.append(line)

        if not target_errors:
            print(f"  [GoalExtract] Probe '{probe}': no error at exact line {sorry_line}")
            # Check for unsolved goals errors — use wider tolerance for bullet-point sorrys
            # where the unsolved case may be far from the actual sorry line.
            unsolved_matches = list(re.finditer(
                r"(\d+):\d+: error: unsolved goals", raw_output))
            if not unsolved_matches:
                unsolved_matches = list(re.finditer(
                    r"error: .*?(\d+):\d+: unsolved goals", raw_output))
            # Pick the best unsolved goals match: prefer one at or after sorry_line,
            # within UNSOLVED_GOAL_TOLERANCE
            best_unsolved = None
            best_dist = UNSOLVED_GOAL_TOLERANCE + 1
            for um in unsolved_matches:
                uline = int(um.group(1))
                dist = abs(uline - sorry_line)
                if dist <= UNSOLVED_GOAL_TOLERANCE:
                    # Prefer matches at or after sorry_line (bullet-point cases)
                    if uline >= sorry_line or dist < best_dist:
                        if best_unsolved is None or dist < best_dist:
                            best_unsolved = um
                            best_dist = dist
            if best_unsolved:
                unsolved_line = int(best_unsolved.group(1))
                # Probe was accepted but left open goals — the goal type IS compatible
                # Try to extract the goal from the unsolved goals error context
                after_idx = raw_output.find(best_unsolved.group(0))
                after_text = raw_output[after_idx:after_idx+1000]
                goal_match = re.search(r"⊢ (.*?)(?:\n\n|\n\d+:)", after_text, re.DOTALL)
                if goal_match:
                    goal = goal_match.group(1).strip()
                    print(f"  [GoalExtract] Extracted from unsolved goals: {goal[:200]}")
                    try:
                        tmp_path.unlink()
                    except OSError:
                        pass
                    return goal
            else:
                if unsolved_matches:
                    closest = int(unsolved_matches[0].group(1))
                    print(f"  [GoalExtract] Unsolved goals at line {closest}, "
                          f"too far from sorry at {sorry_line} "
                          f"(tolerance={UNSOLVED_GOAL_TOLERANCE})")
            # Check for ANY error in the output (not just near sorry line)
            any_error = re.search(r"error:", raw_output)
            if any_error:
                print(f"  [GoalExtract] Errors found but not at line {sorry_line}. "
                      f"First error: {raw_output[any_error.start():any_error.start()+300]}")
            continue

        target_error_text = "\n".join(target_errors)
        print(f"  [GoalExtract] Probe '{probe}': {target_error_text[:300]}")

        goal = _parse_goal_from_error(target_error_text)
        if goal:
            try:
                tmp_path.unlink()
            except OSError:
                pass
            return goal

    # Cleanup
    try:
        tmp_path.unlink()
    except OSError:
        pass

    # All probes failed to produce parseable goal — try heuristic from context
    return _heuristic_goal_extract(lines, sorry_line)


def _parse_goal_from_error(error_text: str) -> Optional[str]:
    """Parse Lean error text to extract the goal type."""
    # Pattern 1: "but is expected to have type ..."
    m = re.search(
        r"but is expected to have type\n?(.*?)(?:\n\n|\n[a-z]|\Z)",
        error_text, re.DOTALL,
    )
    if m:
        goal = m.group(1).strip()
        return re.sub(r'\s+', ' ', goal)

    # Pattern 2: "expected to have type ..."
    m = re.search(r"expected to have type\n?(.*?)(?:\n\n|\Z)", error_text, re.DOTALL)
    if m:
        goal = m.group(1).strip()
        return re.sub(r'\s+', ' ', goal)

    # Pattern 3: "type mismatch" followed by term and expected type
    m = re.search(
        r"type mismatch\n.*?has type\n.*?\nbut is expected to have type\n?(.*?)(?:\n\n|\Z)",
        error_text, re.DOTALL,
    )
    if m:
        goal = m.group(1).strip()
        return re.sub(r'\s+', ' ', goal)

    # Pattern 4: "⊢ ..." (goal display in error context)
    m = re.search(r"⊢ (.*?)$", error_text, re.MULTILINE)
    if m:
        return m.group(1).strip()

    return None


def extract_hypotheses(filepath: str, sorry_line: int) -> list:
    """Extract available hypotheses from the proof context before a sorry.

    Parses have-statements, intro'd variables, case-pattern variables,
    split_ifs hypotheses, let-bindings, and theorem parameters.
    """
    content = Path(filepath).read_text(encoding="utf-8")
    lines = content.split("\n")

    hypotheses = []
    indent_at_sorry = 0

    if 1 <= sorry_line <= len(lines):
        sorry_text = lines[sorry_line - 1]
        indent_at_sorry = len(sorry_text) - len(sorry_text.lstrip())

    for i in range(max(0, sorry_line - 2), -1, -1):
        stripped = lines[i].strip()
        line_indent = len(lines[i]) - len(lines[i].lstrip())

        # Stop at top-level declarations or equal/lower indent at proof start
        if line_indent == 0 and (stripped.startswith("theorem ")
                                  or stripped.startswith("lemma ")
                                  or stripped.startswith("def ")
                                  or stripped.startswith("noncomputable def ")):
            # Extract theorem parameters before stopping
            m = re.match(
                r'(?:private\s+)?(?:theorem|lemma|def|noncomputable\s+def)\s+\w+\s+(.+?)(?::=|\Z)',
                stripped, re.DOTALL,
            )
            if m:
                params_str = m.group(1)
                # Parse (name : Type) blocks
                for pm in re.finditer(r'\((\w+)\s*:\s*([^)]+)\)', params_str):
                    hypotheses.append(f"{pm.group(1)} : {pm.group(2).strip()}")
                # Parse {name : Type} blocks
                for pm in re.finditer(r'\{(\w+)\s*:\s*([^}]+)\}', params_str):
                    hypotheses.append(f"{pm.group(1)} : {pm.group(2).strip()}")
                # Parse [name : Type] blocks (instance implicit)
                for pm in re.finditer(r'\[(\w+)\s*:\s*([^\]]+)\]', params_str):
                    hypotheses.append(f"[{pm.group(1)} : {pm.group(2).strip()}]")
            break
        if stripped.startswith("end ") and line_indent == 0:
            break

        # Only consider lines at or outside the sorry's indentation level
        if line_indent > indent_at_sorry:
            continue

        # have h : statement := by ...
        m = re.match(r'\s*have\s+(\w+)\s*(?::\s*(.+?))?\s*:=', stripped)
        if m:
            name = m.group(1)
            typ = m.group(2) or ""
            hypotheses.append(f"{name} : {typ.strip()}" if typ else name)

        # intro x / intro h
        m = re.match(r'\s*intro\s+(\w+)', stripped)
        if m:
            hypotheses.append(m.group(1))

        # intros x y z
        m = re.match(r'\s*intros\s+(.+)', stripped)
        if m:
            for var in m.group(1).split():
                hypotheses.append(var.strip())

        # split_ifs with h1 h2
        m = re.match(r'\s*split_ifs\s+with\s+(.+)', stripped)
        if m:
            for var in m.group(1).split():
                v = var.strip()
                if v:
                    hypotheses.append(f"split_ifs: {v}")

        # obtain ⟨h1, h2⟩ := ...
        m = re.match(r'\s*obtain\s*[⟨<](.+?)[⟩>]', stripped)
        if m:
            for var in m.group(1).split(","):
                v = var.strip()
                if v:
                    hypotheses.append(v)

        # case name => ...
        m = re.match(r'\s*case\s+(\w+)', stripped)
        if m:
            hypotheses.append(f"case: {m.group(1)}")

    return hypotheses


def extract_local_lemmas(filepath: str, sorry_lines: set = None) -> list:
    """Extract lemma/theorem/def names from a .lean file that have NO sorry.

    Returns list of names that the agent can reference as already-proven helpers.
    """
    content = Path(filepath).read_text(encoding="utf-8")
    lines = content.split("\n")
    sorry_lines = sorry_lines or set()

    names = []
    for i, line in enumerate(lines, 1):
        if i in sorry_lines:
            continue
        m = re.match(r'\s*(?:private\s+)?(?:theorem|lemma|def|noncomputable\s+def)\s+(\w+)', line)
        if m:
            names.append(m.group(1))

    # Filter: keep only those whose proof block doesn't contain sorry
    clean = []
    for name in names:
        pattern = re.compile(
            rf'(?:theorem|lemma|def)\s+{re.escape(name)}\b', re.MULTILINE
        )
        match = pattern.search(content)
        if not match:
            continue
        start_line = content[:match.start()].count("\n") + 1
        # Check next 50 lines for sorry
        block = "\n".join(lines[start_line - 1:min(start_line + 50, len(lines))])
        if "sorry" not in block:
            clean.append(name)

    return clean


def _heuristic_goal_extract(lines: list, sorry_line: int) -> Optional[str]:
    """Extract goal heuristically from proof context when Lean probing fails."""
    # Look backwards for the proof statement (theorem/lemma/have)
    proof_start = sorry_line - 1
    for i in range(sorry_line - 1, max(0, sorry_line - 60), -1):
        line = lines[i].strip()
        if line.startswith("theorem ") or line.startswith("lemma ") or line.startswith("have "):
            proof_start = i
            break
        if line.startswith("by ") and i < sorry_line - 3:
            proof_start = i
            break

    # Look for the most recent goal-transforming tactic before sorry
    last_show = None
    for i in range(sorry_line - 1, max(0, sorry_line - 20), -1):
        stripped = lines[i].strip()
        if stripped.startswith("show "):
            last_show = stripped[5:].rstrip(" :=")
        if stripped.startswith("·") or stripped.startswith("case "):
            break

    if last_show:
        print(f"  [GoalExtract] Heuristic: found 'show' → {last_show[:200]}")
        return last_show

    # Build a hint from the enclosing proof and recent tactics
    hints = []
    last_rw = None
    for i in range(sorry_line - 1, max(0, sorry_line - 20), -1):
        stripped = lines[i].strip()
        if stripped.startswith("rw [") or stripped.startswith("rewrite "):
            last_rw = stripped
        if stripped.startswith("·") or stripped.startswith("case "):
            break

    if last_rw:
        hints.append(f"After rewrite: {last_rw}")

    for i in range(sorry_line - 1, max(0, sorry_line - 8), -1):
        stripped = lines[i].strip()
        if stripped.startswith("have ") and " := " in stripped:
            hints.append(stripped)
        if stripped.startswith("by_cases "):
            hints.append(stripped)

    if hints:
        hint_str = " | ".join(hints[-3:])
        print(f"  [GoalExtract] Heuristic hints: {hint_str[:200]}")

    return None


def classify_definitions(filepath: str, goal_identifiers: list = None) -> list:
    """Classify definitions in the file as def/inductive/noncomputable for prover guidance.

    Returns list of dicts with:
      - name: definition name
      - kind: "inductive" | "def" | "noncomputable_def"
      - is_unfoldable: True if `unfold` will work, False if not
      - signature: first line of the definition (truncated)
      - reason: why unfold may fail (if applicable)
    """
    content = Path(filepath).read_text(encoding="utf-8")
    lines = content.split("\n")
    results = []

    # If specific identifiers given, only classify those; otherwise classify all
    target_names = set(goal_identifiers) if goal_identifiers else None

    for i, line in enumerate(lines):
        stripped = line.strip()

        # Inductive types
        m = re.match(r'^(inductive|structure)\s+(\w+)', stripped)
        if m:
            name = m.group(2)
            if target_names and name not in target_names:
                continue
            results.append({
                "name": name,
                "kind": "inductive",
                "is_unfoldable": True,
                "signature": stripped[:200],
                "reason": None,
            })
            continue

        # Noncomputable def
        m = re.match(r'^noncomputable\s+def\s+(\w+)', stripped)
        if m:
            name = m.group(1)
            if target_names and name not in target_names:
                continue
            # Check if body starts with `by` (tactic mode) — can't unfold
            rest_of_line = stripped[len(m.group(0)):]
            is_tactic_body = ":= by" in rest_of_line
            # Check next few lines for := by
            if not is_tactic_body:
                for j in range(i + 1, min(i + 5, len(lines))):
                    if ":= by" in lines[j]:
                        is_tactic_body = True
                        break
                    if ":=" in lines[j]:
                        break
            results.append({
                "name": name,
                "kind": "noncomputable_def",
                "is_unfoldable": not is_tactic_body,
                "signature": stripped[:200],
                "reason": "unfold fails on `noncomputable def ... by classical; exact ...`"
                          if is_tactic_body else None,
            })
            continue

        # Regular def
        m = re.match(r'^def\s+(\w+)', stripped)
        if m:
            name = m.group(1)
            if target_names and name not in target_names:
                continue
            # def can usually be unfolded, but anonymous constructors need care
            results.append({
                "name": name,
                "kind": "def",
                "is_unfoldable": True,
                "signature": stripped[:200],
                "reason": "Use `show` or explicit type ascription for anonymous constructors",
            })
            continue

    return results


def build_def_type_warnings(filepath: str, goal_state: str) -> str:
    """Build a warning string for the prover about def type handling.

    Scans the goal for custom identifiers, classifies their definitions,
    and returns actionable guidance.
    """
    if not goal_state:
        return ""

    # Extract identifiers from goal
    skip = {"by", "exact", "sorry", "have", "obtain", "intro", "fun", "lambda",
            "forall", "exists", "and", "or", "not", "true", "false", "unit",
            "prop", "type", "Finset", "Nat", "Int", "Real", "Bool", "List",
            "Set", "Option", "Sum", "Prod", "Sigma", "PSigma", "Subtype",
            "PSubtype", "Nonempty", "Classical", "Decidable", "Fintype"}
    identifiers = set(re.findall(r'\b([a-z_]\w*)\b', goal_state))
    identifiers -= skip

    # Also check for Capitalized identifiers that might be custom types
    cap_identifiers = set(re.findall(r'\b([A-Z]\w*)\b', goal_state))
    all_ids = identifiers | cap_identifiers

    defs = classify_definitions(filepath, list(all_ids))
    if not defs:
        return ""

    warnings = []
    for d in defs:
        if not d["is_unfoldable"]:
            warnings.append(
                f"  - {d['name']} ({d['kind']}): {d['reason']}. "
                f"Use `show <expanded_type>` instead of `unfold {d['name']}`"
            )
        elif d["kind"] == "def":
            warnings.append(
                f"  - {d['name']} ({d['kind']}): not an inductive type. "
                f"Avoid anonymous `⟨⟩` with inline lambdas. Use `constructor` + `by` blocks or `show`."
            )

    if not warnings:
        return ""

    header = "AVERTISSEMENT TYPES PERSONNALISES (def vs inductive):"
    return header + "\n" + "\n".join(warnings)


def verify_sorry_replacement(filepath: str, sorry_line: int, replacement: str,
                             imports: Optional[str] = None) -> dict:
    """Verify a sorry replacement by writing modified file to disk and checking Lean.

    Args:
        filepath: Path to .lean file
        sorry_line: 1-based line number of the sorry
        replacement: Tactic(s) to replace the sorry (will be indented to match)
        imports: Unused (file already has imports)

    Returns: dict with success, errors, time_s
    """
    from .verifier import get_verifier

    content = Path(filepath).read_text(encoding="utf-8")
    lines = content.split("\n")

    if sorry_line < 1 or sorry_line > len(lines):
        return {"success": False, "errors": f"Line {sorry_line} out of range"}

    sorry_text = lines[sorry_line - 1]
    indent = len(sorry_text) - len(sorry_text.lstrip())
    indent_str = " " * indent

    # Build replacement lines with correct indentation
    replacement_lines = []
    for line in replacement.strip().split("\n"):
        if line.strip():
            replacement_lines.append(indent_str + line.strip())

    # Replace the sorry line in the full file
    new_lines = lines[:sorry_line - 1] + replacement_lines + lines[sorry_line:]
    new_content = "\n".join(new_lines)

    # Write modified file to disk (Lean project directory)
    tmp_path = Path(filepath).parent / "_SorryVerify.lean"
    tmp_path.write_text(new_content, encoding="utf-8")

    # Verify using verify_project_file (no command-line length limit)
    verifier = get_verifier(str(Path(filepath).parent.parent))
    subdir = Path(filepath).parent.name
    relative_path = f"{subdir}/_SorryVerify.lean"
    result = verifier.verify_project_file(relative_path, force=True)

    # Clean up temp file
    try:
        tmp_path.unlink()
    except OSError:
        pass

    # Filter errors to only those near the target sorry line.
    n_replacement_lines = len(replacement_lines)
    line_shift = max(0, n_replacement_lines - 1)
    raw_output = result.get("raw_output", "")

    # Collect ALL error locations first
    all_error_lines = []
    current_error = []
    for line in raw_output.split("\n"):
        m_err = re.match(r".*?(\d+):\d+: error: (.*)", line)
        if not m_err:
            m_err = re.match(r"error: .*?(\d+):\d+: (.*)", line)
        if m_err:
            if current_error:
                all_error_lines.append(current_error)
            current_error = [(int(m_err.group(1)), line)]
        elif current_error:
            current_error.append((current_error[0][0], line))
    if current_error:
        all_error_lines.append(current_error)

    # Separate: direct errors vs cascade errors vs distant errors
    # P2 (Epic #1453): distant errors (outside nearby_range) were silently
    # ignored, causing false successes where errors existed in the file but
    # outside the ±5 line window. Now collected and included in the result.
    direct_errors = []
    cascade_errors = []
    distant_errors = []
    nearby_range = 5 + line_shift

    for err_block in all_error_lines:
        first_line_num = err_block[0][0]
        text = "\n".join(line_text for _, line_text in err_block)
        if first_line_num == sorry_line:
            direct_errors.append(text)
        elif abs(first_line_num - sorry_line) <= nearby_range:
            cascade_errors.append(text)
        else:
            distant_errors.append(text)

    # Build result
    has_direct_error = len(direct_errors) > 0
    has_cascade_error = len(cascade_errors) > 0
    # P2: require absence of ALL errors in _SorryVerify.lean, not just nearby.
    # Distant errors indicate the replacement broke something elsewhere.
    has_distant_error = len(distant_errors) > 0
    is_success = (not has_direct_error and not has_cascade_error
                  and not has_distant_error)

    # Extract residual goals from cascade errors (lines starting with ⊢)
    residual_goals = []
    cascade_text = "\n".join(cascade_errors)
    for line in cascade_text.split("\n"):
        stripped = line.strip()
        if stripped.startswith("⊢ ") or stripped.startswith("| ⊢ "):
            goal = stripped.lstrip("| ").lstrip("⊢ ").strip()
            if goal and goal not in residual_goals:
                residual_goals.append(goal)

    # Build error message with context
    if has_direct_error:
        error_msg = "\n".join(direct_errors)
        error_type = "tactic_failed"
    elif has_cascade_error:
        error_msg = (
            "Tactic left UNSOLVED GOALS. The tactic at line "
            f"{sorry_line} executed but did not close all goals. "
            "Cascade error:\n" + "\n".join(cascade_errors[:2])
        )
        error_type = "unsolved_goals"
    elif has_distant_error:
        # P2: errors outside the nearby window mean the replacement broke
        # something elsewhere in the file. Report first 2 distant errors.
        error_msg = (
            f"Tactic at line {sorry_line} compiles locally but introduced "
            f"errors at distant lines. File may be broken elsewhere:\n"
            + "\n".join(distant_errors[:2])
        )
        error_type = "distant_errors"
    else:
        error_msg = ""
        error_type = None

    return {
        "success": is_success,
        "errors": error_msg,
        "raw_error": error_msg[:500],
        "error_type": error_type,
        "residual_goals": residual_goals,
        "distant_errors": distant_errors,  # P2: expose for caller inspection
        "all_errors": result.get("errors", ""),
        "time_s": result.get("time_s", 0),
        "backend": result.get("backend", ""),
    }


def suggest_decomposition(goal: str) -> list:
    """Suggest top-down decomposition steps for complex goals.

    Returns a list of 'have' sub-goals to break the proof into manageable steps.
    Used by B.4 to force decomposition for ∀/∃/∧/↔ goals.

    Returns:
        list of dicts with 'name', 'type', 'hint' for each suggested have-step
    """
    suggestions = []

    if not goal:
        return suggestions

    # Universal quantifier: ∀ x, P x → decompose into intro + separate claim
    if "∀" in goal or "forall" in goal.lower():
        suggestions.append({
            "name": "h_forall",
            "type": "intro the universally quantified variable(s), then prove the body",
            "hint": "Use `intro` or `intros` first, then focus on the body goal",
        })

    # Existential: ∃ x, P x → decompose into `use` + proof of property
    if "∃" in goal or "Exists" in goal:
        suggestions.append({
            "name": "h_exists",
            "type": "provide a witness with `use`, then prove the property holds",
            "hint": "Use `use <witness>` to provide the existential witness, then prove P witness",
        })

    # Conjunction: P ∧ Q → decompose into two separate sub-proofs
    if "∧" in goal or ("And" in goal and "(" in goal):
        suggestions.append({
            "name": "h_and_left",
            "type": "prove the left conjunct first",
            "hint": "Use `constructor` or `exact And.intro` to split into two goals",
        })

    # Biconditional: P ↔ Q → decompose into two implications
    if "↔" in goal or "Iff" in goal:
        suggestions.append({
            "name": "h_iff_fwd",
            "type": "prove the forward direction P → Q",
            "hint": "Use `constructor` or `Iff.intro` to split into fwd and bwd",
        })

    # Implication chain: nested → → →
    arrow_count = goal.count("→") + goal.count("->")
    if arrow_count >= 2:
        suggestions.append({
            "name": "h_impl_chain",
            "type": "decompose implication chain with `intro` step by step",
            "hint": "Use `intro` repeatedly to name each hypothesis, then prove conclusion",
        })

    # Negation: ¬ P → usually needs intro + absurdum or specific lemma
    if "¬" in goal or "Not " in goal:
        suggestions.append({
            "name": "h_neg",
            "type": "prove by contradiction: assume P and derive False",
            "hint": "Use `intro h` to get h : P, then derive False from h and existing hypotheses",
        })

    return suggestions
