#!/usr/bin/env python3
"""Mini-validator pour proof gauntlet (#15067).

Lit un fichier (sys.argv[1]) et :
  - exit 0 si le contenu NE contient PAS le marqueur "@FAIL_HELD"
  - exit 1 si le contenu CONTIENT le marqueur
N'inspecte PAS la longueur du fichier (=> ESCAPED sous fault=truncate).
"""
import sys
TARGET = b"@FAIL_HELD"
try:
    data = open(sys.argv[1], "rb").read()
except Exception as exc:
    print(f"validator error: {exc}", file=sys.stderr)
    sys.exit(2)
sys.exit(1 if TARGET in data else 0)
