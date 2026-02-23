"""
Convert Marp slides.md to Slidev format.

Key conversions:
- Marp frontmatter → Slidev frontmatter
- <!-- _class: title --> → layout: cover
- <!-- _class: section --> → layout: section
- <!-- _class: dense --> → layout: dense
- <!-- _class: columns-layout --> → layout: two-cols
- ![bg right:X%](img) → layout: image-right with image prop
- ![bg right:X% vertical] + ![bg] patterns → layout: image-right with v-click images
- Animations from animations.json → v-click directives
"""

import json
import re
import sys
from pathlib import Path

SLIDES_DIR = Path(__file__).parent.parent


def read_animations(deck_dir: Path) -> dict:
    """Read animations.json for a deck."""
    anim_path = deck_dir / 'extracted' / 'animations.json'
    if anim_path.exists():
        with open(anim_path, encoding='utf-8') as f:
            return json.load(f)
    return {}


def split_slides(marp_content: str) -> list:
    """Split markdown content by --- separators."""
    slides = []
    current = []
    for line in marp_content.split('\n'):
        if line.strip() == '---':
            slides.append('\n'.join(current))
            current = []
        else:
            current.append(line)
    if current:
        slides.append('\n'.join(current))
    return slides


def parse_frontmatter(slide: str) -> tuple:
    """Parse frontmatter (YAML between ---). Returns (frontmatter, content)."""
    lines = slide.split('\n')
    if lines[0].strip() == '---' and '---' in '\n'.join(lines[1:]):
        end_idx = lines[1:].index('---') + 2
        frontmatter = '\n'.join(lines[1:end_idx])
        content = '\n'.join(lines[end_idx + 1:])
        return frontmatter, content
    return '', slide


def convert_slide_content(content: str, slide_num: int, animations: dict) -> str:
    """Convert Marp content to Slidev format."""
    lines = content.split('\n')
    result = []
    i = 0

    while i < len(lines):
        line = lines[i]

        # Class directives
        if '<!-- _class: title -->' in line:
            result.append('layout: cover')
        elif '<!-- _class: section -->' in line:
            result.append('layout: section')
        elif '<!-- _class: dense -->' in line:
            result.append('layout: dense')
        elif '<!-- _class: columns-layout -->' in line:
            result.append('layout: two-cols')
            # Skip empty lines that followed
            i += 1
            while i < len(lines) and lines[i].strip() == '':
                i += 1
            continue
        # Image background patterns
        elif re.match(r'^!\[bg right:\d+%\]?\(images/[^\)]+\)', line):
            match = re.match(r'^!\[bg right:(\d+)%\]?\(([^)]+)\)', line)
            if match:
                width = match.group(1)
                img_path = match.group(2)
                result.append(f'layout: image-right')
                result.append(f'image: ./{img_path}')
        # Regular image (inline)
        elif line.strip().startswith('![') and '](' in line:
            # Keep inline images as-is
            result.append(line)
        else:
            result.append(line)
        i += 1

    return '\n'.join(result)


def convert_marp_to_slidev(marp_path: Path, slidev_path: Path, deck_name: str):
    """Convert a Marp slides.marp.md to Slidev slides.md."""
    with open(marp_path, encoding='utf-8') as f:
        marp_content = f.read()

    animations = read_animations(marp_path.parent)

    # Parse global frontmatter
    global_fm, rest = parse_frontmatter('\n'.join(['---'] + marp_content.split('\n')[1:]))

    # Build Slidev frontmatter
    slidev_fm = f"""---
theme: ../theme-ia101
title: "{deck_name}"
info: Cours Intelligence Artificielle
paginate: true
drawings:
  persist: false
transition: slide-left
mdc: true
---

"""

    # Split into slides and convert each
    marp_slides = split_slides(rest)
    converted_slides = []

    for i, slide in enumerate(marp_slides):
        slide_num = i + 1
        # Skip frontmatter slides
        if slide.strip().startswith('marp:') or slide.strip().startswith('theme:'):
            continue
        converted = convert_slide_content(slide, slide_num, animations)
        converted_slides.append(converted)

    slidev_content = slidev_fm + '\n---\n\n'.join(converted_slides)

    slidev_path.parent.mkdir(parents=True, exist_ok=True)
    with open(slidev_path, 'w', encoding='utf-8') as f:
        f.write(slidev_content)

    print(f"Converted: {marp_path.name} → {slidev_path.name} ({len(converted_slides)} slides)")


def main():
    if len(sys.argv) < 2:
        print("Usage: python marp_to_slidev.py <deck_name>")
        print("Example: python marp_to_slidev.py 01-introduction")
        sys.exit(1)

    deck_name = sys.argv[1]
    deck_dir = SLIDES_DIR / deck_name

    marp_path = deck_dir / 'slides.marp.md'
    slidev_path = deck_dir / 'slides.md'

    if not marp_path.exists():
        print(f"Error: {marp_path} not found")
        sys.exit(1)

    convert_marp_to_slidev(marp_path, slidev_path, deck_name.replace('-', ' ').title())


if __name__ == '__main__':
    main()
