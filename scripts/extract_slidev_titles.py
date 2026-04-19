#!/usr/bin/env python3
"""Extract slide titles from a Slidev slides.md file.

A slide in Slidev is delimited by `---` lines. The first `---...---` block is
the root frontmatter; subsequent slides may begin with their own per-slide
frontmatter (`---...---`) before the content.

Algorithm: split the file by `---` lines into blocks. Discard block 0 (root
frontmatter). Then walk remaining blocks: a block that starts with a YAML-like
key line (e.g. `layout: default`) and has no `# ` heading is a per-slide
frontmatter belonging to the next block. Otherwise the block is a slide.
Emit the first `# ` title of each slide (or `[no-h1] <first line>` if absent).
"""

import sys
import re
import pathlib

YAML_KEY = re.compile(r"^[A-Za-z_][A-Za-z0-9_-]*\s*:")


def split_blocks(lines):
    blocks, current = [], []
    for line in lines:
        if line.strip() == "---":
            blocks.append(current)
            current = []
        else:
            current.append(line)
    blocks.append(current)
    return blocks


def is_frontmatter(block):
    non_empty = [line for line in block if line.strip()]
    if not non_empty:
        return False
    if any(line.strip().startswith("# ") for line in block):
        return False
    return bool(YAML_KEY.match(non_empty[0]))


def title_of(block):
    for line in block:
        s = line.strip()
        if s.startswith("# "):
            return s[2:].strip()
    for line in block:
        s = line.strip()
        if s:
            return f"[no-h1] {s[:80]}"
    return "[empty]"


def extract(path: pathlib.Path):
    lines = path.read_text(encoding="utf-8").splitlines()
    blocks = split_blocks(lines)

    # Drop root frontmatter (blocks[0] is before the first `---`; blocks[1]
    # is the root FM content). After the first `---`...`---` pair, the next
    # block is slide 1.
    if not blocks:
        return
    # blocks[0] = "" before the opening ---
    # blocks[1] = root FM content (between opening --- and closing ---)
    # blocks[2..] = slide content, possibly interleaved with per-slide FM
    slide_blocks = blocks[2:]

    slides = []
    i = 0
    while i < len(slide_blocks):
        b = slide_blocks[i]
        if is_frontmatter(b) and i + 1 < len(slide_blocks):
            slides.append(slide_blocks[i + 1])
            i += 2
        else:
            slides.append(b)
            i += 1

    for idx, content in enumerate(slides, start=1):
        print(f"{idx}: {title_of(content)}")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print(__doc__)
        sys.exit(1)
    extract(pathlib.Path(sys.argv[1]))
