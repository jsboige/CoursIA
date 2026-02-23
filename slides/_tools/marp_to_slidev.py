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


def apply_click_animations(content: str, slide_animations: dict) -> str:
    """Apply v-click directives based on PPTX click_groups."""
    if not slide_animations.get('has_animations', False):
        return content

    click_groups = slide_animations.get('click_groups', [])
    if not click_groups or len(click_groups) <= 1:
        return content

    # Build mapping of level 0 text to click index
    level0_to_click = {}
    for group in click_groups[1:]:  # Skip click 0 (visible by default)
        click_idx = group['click']
        for item in group.get('items', []):
            if item.get('type') == 'paragraph' and item.get('level', 0) == 0:
                text = item.get('text', '').strip()
                if text:
                    key = text[:40].lower()
                    level0_to_click[key] = click_idx

    lines = content.split('\n')
    result = []
    parent_click = 0  # Track click for current level 0 parent

    for line in lines:
        # Detect indentation level
        indent_match = re.match(r'^(\s*)-', line)
        if indent_match:
            indent = len(indent_match.group(1))
            level = indent // 2 if indent else 0
            stripped = line.strip()

            if level == 0:
                # Level 0 bullet - find its click
                bullet_text = stripped[2:].strip()
                parent_click = 0
                for key, click_idx in level0_to_click.items():
                    if key in bullet_text.lower() or bullet_text.lower() in key:
                        parent_click = click_idx
                        break

                if parent_click > 0:
                    result.append(f'<v-click="{parent_click}">{stripped}</v-click>')
                else:
                    result.append(line)
            else:
                # Level 1+ bullet - inherit parent's click
                if parent_click > 0:
                    result.append(f'<v-click="{parent_click}">{stripped}</v-click>')
                else:
                    result.append(line)
        else:
            result.append(line)

    return '\n'.join(result)


def convert_slide_content(content: str, slide_num: int, animations: dict) -> str:
    """Convert Marp content to Slidev format."""
    lines = content.split('\n')
    result = []
    i = 0

    # Track animations for this slide
    slide_animations = animations.get('slides', [{}])[slide_num - 1] if slide_num <= len(animations.get('slides', [])) else {}
    has_animations = slide_animations.get('has_animations', False)
    click_groups = slide_animations.get('click_groups', [])

    # Collect multi-image vertical patterns first
    vertical_images = []
    in_vertical_block = False

    # Track two-cols layout
    in_two_cols = False
    in_right_col = False

    while i < len(lines):
        line = lines[i]

        # Detect vertical multi-image pattern start
        if re.match(r'^!\[bg right:\d+% vertical\]\(images/[^\)]+\)', line):
            in_vertical_block = True
            match = re.match(r'^!\[bg right:\d+% vertical\]\(([^)]+)\)', line)
            if match:
                vertical_images.append(match.group(1))
            i += 1
            # Collect following ![bg] patterns
            while i < len(lines) and re.match(r'^!\[bg\]\(images/[^\)]+\)', lines[i]):
                bg_match = re.match(r'^!\[bg\]\(([^)]+)\)', lines[i])
                if bg_match:
                    vertical_images.append(bg_match.group(1))
                i += 1
            continue

        # If we collected vertical images, output them
        if vertical_images:
            result.append('layout: image-right')
            result.append(f'image: ./{vertical_images[0]}')
            # Additional images as inline markdown with v-click if animated
            for idx, img in enumerate(vertical_images[1:], 1):
                if has_animations:
                    result.append(f'<div v-click="{idx}"><img src="./{img}" style="max-height:300px; margin-top:8px;"></div>')
                else:
                    result.append(f'<img src="./{img}" style="max-height:300px; margin-top:8px;">')
            vertical_images = []
            in_vertical_block = False
            continue

        # Class directives
        if '<!-- _class: title -->' in line:
            result.append('layout: cover')
        elif '<!-- _class: section -->' in line:
            result.append('layout: section')
        elif '<!-- _class: dense -->' in line:
            result.append('layout: dense')
        elif '<!-- _class: columns-layout -->' in line:
            result.append('layout: two-cols')
            in_two_cols = True
            # Skip empty lines that followed
            i += 1
            while i < len(lines) and lines[i].strip() == '':
                i += 1
            continue
        # Image background patterns (single, non-vertical)
        elif re.match(r'^!\[bg right:\d+%\]?\(images/[^\)]+\)', line):
            match = re.match(r'^!\[bg right:(\d+)%\]?\(([^)]+)\)', line)
            if match:
                width = match.group(1)
                img_path = match.group(2)
                result.append(f'layout: image-right')
                result.append(f'image: ./{img_path}')
        # Img-grid div pattern
        elif '<div class="img-grid"' in line:
            # Extract images from grid until closing div
            result.append('<div class="image-grid">')
            i += 1
            while i < len(lines) and '</div>' not in lines[i]:
                img_match = re.search(r'<img src="([^"]+)"', lines[i])
                if img_match:
                    img_src = img_match.group(1)
                    # Ensure path starts with ./
                    if not img_src.startswith('./'):
                        img_src = f'./{img_src}'
                    result.append(f'<img src="{img_src}">')
                i += 1
            result.append('</div>')
        # Columns div pattern - map to two-cols layout
        elif '<div class="columns">' in line:
            # We're already in two-cols layout, just skip the div wrapper
            i += 1
            continue
        elif '<div class="col-left">' in line:
            i += 1
            continue
        elif '<div class="col-right">' in line:
            in_right_col = True
            result.append('::right::')
            i += 1
            continue
        elif '</div>' in line and (in_two_cols or in_right_col):
            # End of column content
            if in_right_col:
                in_right_col = False
            i += 1
            continue
        # Regular image (inline) - fix path
        elif line.strip().startswith('![') and '](' in line:
            # Keep as-is, will be fixed in post-process
            result.append(line)
        # Skip standalone ![bg] patterns (already handled in vertical block)
        elif re.match(r'^!\[bg\]\(images/[^\)]+\)', line):
            i += 1
            continue
        else:
            result.append(line)
        i += 1

    # Post-process: fix all image paths to start with ./
    content = '\n'.join(result)
    # Fix HTML img tags: src="images/xxx" -> src="./images/xxx"
    content = re.sub(r' src="(images/[^"]+)"', r' src="./\1"', content)
    # Fix markdown images: ](images/xxx) -> ](./images/xxx)
    content = re.sub(r'\]\((images/[^)]+)\)', r'](./\1)', content)
    # Apply v-click animations from PPTX
    content = apply_click_animations(content, slide_animations)
    return content


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
