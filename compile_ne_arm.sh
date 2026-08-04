#!/bin/bash
export PATH="/home/jesse/.elan/bin:$PATH"
cd /mnt/c/dev/CoursIA-c6724-c31-p4nw/MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean
lake env lean Conway/Life/HashlifeCorrectness.lean 2>&1 | tail -80
