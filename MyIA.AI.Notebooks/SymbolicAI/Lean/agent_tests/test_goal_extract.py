#!/usr/bin/env python3
"""Test goal state extraction from Shapley.lean."""
import os, re
from pathlib import Path
from dotenv import load_dotenv

_parent = Path(__file__).parent.parent
load_dotenv(_parent / ".env")

from lean_server import LeanVerifier

proj = os.getenv("LEAN_PROJECT_DIR")
v = LeanVerifier(proj, verbose=True)

filepath = Path(proj) / "CooperativeGames" / "Shapley.lean"
content = filepath.read_text(encoding="utf-8")
lines = content.split("\n")
sorry_line = 292
sorry_text = lines[sorry_line - 1]
indent = len(sorry_text) - len(sorry_text.lstrip())
indent_str = " " * indent

new_lines = lines[:sorry_line - 1] + [indent_str + "exact ()"] + lines[sorry_line:]
new_content = "\n".join(new_lines)

tmp_path = filepath.parent / "_GoalExtract.lean"
tmp_path.write_text(new_content, encoding="utf-8")

print("Verifying _GoalExtract.lean...")
result = v.verify_project_file("CooperativeGames/_GoalExtract.lean")
print(f"Success: {result['success']}")
print(f"Errors: {result.get('errors', '')[:1000]}")
print(f"Raw output (first 500): {result.get('raw_output', '')[:500]}")

# Cleanup
try:
    tmp_path.unlink()
except Exception:
    pass
