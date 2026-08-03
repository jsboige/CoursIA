#!/bin/bash
export PATH=/home/jesse/.elan/bin:$PATH
cd /mnt/c/dev/CoursIA-c6724-c31-p4nw/MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean
lake env lean Conway/Life/HashlifeCorrectness.lean > /tmp/build_p4ne_v6.log 2>&1
echo "EXIT=$?"
wc -l /tmp/build_p4ne_v6.log
