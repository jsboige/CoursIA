#!/usr/bin/env python3
"""Extract slide titles from a PPTX-exported content.md file.

The extractor expects `<!-- Slide number: N -->` markers; the first `# Heading`
after each marker is taken as the slide title. If no heading is present before
the next marker, the first non-empty content line is used, prefixed with
`[no-h1]`.
"""

import sys
import re
import pathlib

SLIDE_MARKER = re.compile(r"^<!--\s*Slide number:\s*(\d+)\s*-->")


def extract(path: pathlib.Path):
    lines = path.read_text(encoding="utf-8").splitlines()
    current_num = None
    current_block = []
    slides = []

    def flush():
        nonlocal current_block, current_num
        if current_num is None:
            return
        title = None
        for line in current_block:
            s = line.strip()
            if s.startswith("# "):
                title = s[2:].strip()
                break
        if title is None:
            for line in current_block:
                s = line.strip()
                if s and not s.startswith("<!--"):
                    title = f"[no-h1] {s[:80]}"
                    break
        slides.append((current_num, title or "[empty]"))
        current_block = []

    for line in lines:
        m = SLIDE_MARKER.match(line)
        if m:
            flush()
            current_num = int(m.group(1))
            continue
        current_block.append(line)
    flush()

    for num, title in slides:
        print(f"{num}: {title}")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print(__doc__)
        sys.exit(1)
    extract(pathlib.Path(sys.argv[1]))
