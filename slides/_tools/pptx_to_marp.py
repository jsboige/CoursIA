"""Convert extracted PowerPoint decks to Marp Markdown format.

Reads the already-extracted artifacts (content.md, inventory.json, images/)
and generates a Marp-compatible slides.md file per deck.

Usage:
    python pptx_to_marp.py slides/08-ia-generative
    python pptx_to_marp.py --all
"""

import argparse
import json
import os
import re
import shutil
import sys
from pathlib import Path


# Footers to strip from slide content
FOOTER_PATTERNS = [
    r'^IA 101$',
    r'^CS 405$',
    r'^Intelligence\(s\)$',
    r'^CS405$',
    r'^IA101$',
]

# Layout name -> Marp class mapping
LAYOUT_CLASS_MAP = {
    'Title Slide': 'title',
    'Section Header': 'section',
    'Blank': None,  # will detect Questions? slides separately
}


def parse_content_md(content_path: str) -> dict[int, dict]:
    """Parse content.md into a dict of {slide_num: {title, body, notes}}."""
    with open(content_path, 'r', encoding='utf-8') as f:
        text = f.read()

    slides = {}
    # Split by slide markers
    parts = re.split(r'<!-- Slide number: (\d+) -->', text)
    # parts[0] is before first marker (usually empty)
    # parts[1] = slide number, parts[2] = content, parts[3] = number, parts[4] = content, ...
    for i in range(1, len(parts), 2):
        slide_num = int(parts[i])
        raw_content = parts[i + 1].strip() if i + 1 < len(parts) else ''

        # Split notes
        notes_match = re.split(r'###\s*Notes:\s*', raw_content, maxsplit=1)
        body = notes_match[0].strip()
        notes = notes_match[1].strip() if len(notes_match) > 1 else ''

        # Extract title (first # line)
        title = ''
        lines = body.split('\n')
        body_lines = []
        title_found = False
        for line in lines:
            if not title_found and line.startswith('# '):
                title = line[2:].strip()
                title_found = True
            else:
                body_lines.append(line)

        body = '\n'.join(body_lines).strip()

        slides[slide_num] = {
            'title': title,
            'body': body,
            'notes': notes,
        }

    return slides


def clean_slide_body(body: str, slide_num: int) -> str:
    """Clean up slide body text: remove noise, format bullets."""
    lines = body.split('\n')
    cleaned = []

    for line in lines:
        stripped = line.strip()

        # Skip standalone slide numbers
        if stripped == str(slide_num):
            continue

        # Skip footer patterns
        skip = False
        for pattern in FOOTER_PATTERNS:
            if re.match(pattern, stripped):
                skip = True
                break
        if skip:
            continue

        # Skip ALL markitdown image references (they point to internal PPTX names
        # like Image6.jpg which don't exist in our structure - we use extracted images instead)
        if re.match(r'^!\[.*\]\(.*\)$', stripped):
            continue

        cleaned.append(line)

    # Remove leading/trailing blank lines
    text = '\n'.join(cleaned).strip()

    return text


def map_images(deck_dir: str) -> dict[int, list[str]]:
    """Map each slide number to its extracted image files."""
    images_dir = os.path.join(deck_dir, 'extracted', 'images')
    if not os.path.isdir(images_dir):
        return {}

    mapping = {}
    for fname in sorted(os.listdir(images_dir)):
        match = re.match(r'slide_(\d+)_img_\d+\.(png|jpg|jpeg|gif|bmp|svg)', fname, re.IGNORECASE)
        if match:
            slide_num = int(match.group(1))
            mapping.setdefault(slide_num, []).append(fname)

    return mapping


def copy_images(deck_dir: str, image_map: dict[int, list[str]]) -> dict[str, str]:
    """Copy images from extracted/images/ to deck/images/ with simplified names.

    Returns a mapping of old_name -> new_name.
    """
    src_dir = os.path.join(deck_dir, 'extracted', 'images')
    dst_dir = os.path.join(deck_dir, 'images')
    os.makedirs(dst_dir, exist_ok=True)

    name_map = {}
    counter = 1

    for slide_num in sorted(image_map.keys()):
        for old_name in image_map[slide_num]:
            ext = os.path.splitext(old_name)[1]
            new_name = f'img_{counter:03d}{ext}'
            src = os.path.join(src_dir, old_name)
            dst = os.path.join(dst_dir, new_name)

            if os.path.isfile(src):
                shutil.copy2(src, dst)

            name_map[old_name] = new_name
            counter += 1

    return name_map


def load_inventory(deck_dir: str) -> dict:
    """Load inventory.json and return slide metadata."""
    inv_path = os.path.join(deck_dir, 'extracted', 'inventory.json')
    if not os.path.isfile(inv_path):
        return {}

    with open(inv_path, 'r', encoding='utf-8') as f:
        data = json.load(f)

    # Index by slide number
    slides_meta = {}
    for slide in data.get('slides', []):
        slides_meta[slide['number']] = slide

    return slides_meta


def detect_questions_slide(title: str, body: str) -> bool:
    """Detect if a slide is a Questions? breathing slide."""
    t = (title + ' ' + body).strip().lower()
    return t in ('questions?', 'questions ?', 'questions', '?')


def build_body_from_inventory(slide_meta: dict, slide_num: int) -> str | None:
    """Try to build structured body from inventory text_content.

    The inventory text_content preserves vertical tabs (\x0b) for sub-bullets
    which gives us better hierarchy than content.md.
    Returns None if inventory not available.
    """
    text_content = slide_meta.get('text_content', '')
    if not text_content:
        return None

    title = slide_meta.get('title', '')
    lines = text_content.split('\n')
    result = []

    for line in lines:
        stripped = line.strip()
        if not stripped:
            continue
        # Skip the title (already handled separately)
        if stripped == title:
            continue
        # Skip slide number
        if stripped == str(slide_num):
            continue
        # Skip footers
        skip = False
        for pattern in FOOTER_PATTERNS:
            if re.match(pattern, stripped):
                skip = True
                break
        if skip:
            continue

        # Detect sub-bullets: lines containing vertical tab (\x0b) are sub-items
        if '\x0b' in line:
            # Split by vertical tab, each part after first is a sub-bullet
            parts = line.split('\x0b')
            for j, part in enumerate(parts):
                p = part.strip()
                if not p:
                    continue
                if j == 0:
                    result.append(f'- **{p}**')
                else:
                    result.append(f'  - {p}')
        else:
            result.append(f'- {stripped}')

    return '\n'.join(result) if result else None


def generate_marp_slide(slide_num: int, slide_data: dict, slide_meta: dict,
                         image_map: dict[int, list[str]], name_map: dict[str, str],
                         deck_name: str) -> str:
    """Generate Marp markdown for a single slide."""
    title = slide_data['title']
    body = clean_slide_body(slide_data['body'], slide_num)
    notes = slide_data['notes']

    layout_name = slide_meta.get('layout_name', 'Title and Content')
    images = image_map.get(slide_num, [])

    lines = []

    # Determine slide class
    marp_class = LAYOUT_CLASS_MAP.get(layout_name)

    # Override: detect Questions? slides
    if detect_questions_slide(title, body):
        marp_class = 'questions'

    # Add class directive if needed
    if marp_class:
        lines.append(f'<!-- _class: {marp_class} -->')
        lines.append('')

    # Title
    if title:
        lines.append(f'# {title}')
        lines.append('')

    # Body content
    if marp_class != 'questions':
        # Try inventory first (better hierarchy), fall back to content.md
        inv_body = build_body_from_inventory(slide_meta, slide_num)
        if inv_body:
            lines.append(inv_body)
            lines.append('')
        elif body:
            body_formatted = format_body_text(body)
            lines.append(body_formatted)
            lines.append('')

    # Images
    if images:
        if len(images) == 1:
            new_name = name_map.get(images[0], images[0])
            if marp_class == 'title':
                # Background image for title slides
                lines.insert(0, f'![bg opacity:0.2](images/{new_name})')
                lines.insert(1, '')
            else:
                # Side image for content slides
                lines.append(f'![bg right:35%](images/{new_name})')
                lines.append('')
        elif len(images) == 2:
            # Two images: one right, one below or both as bg
            for img in images:
                new_name = name_map.get(img, img)
                lines.append(f'![w:400](images/{new_name})')
            lines.append('')
        else:
            # Multiple images: inline with width
            for img in images:
                new_name = name_map.get(img, img)
                lines.append(f'![w:250](images/{new_name})')
            lines.append('')

    # Notes
    if notes:
        lines.append(f'<!-- notes: {notes} -->')
        lines.append('')

    return '\n'.join(lines).rstrip()


def format_body_text(body: str) -> str:
    """Format body text: detect bullet structures, clean up."""
    lines = body.split('\n')
    result = []

    for line in lines:
        stripped = line.strip()
        if not stripped:
            result.append('')
            continue

        # Already has markdown formatting
        if stripped.startswith(('- ', '* ', '> ', '1.', '2.', '3.', '4.', '5.',
                                '6.', '7.', '8.', '9.', '#', '|', '```', '![',
                                '<!--')):
            result.append(line)
            continue

        # Detect indented lines (sub-bullets in extracted text)
        leading_spaces = len(line) - len(line.lstrip())
        if leading_spaces >= 4:
            result.append(f'  - {stripped}')
        elif leading_spaces >= 2:
            result.append(f'  - {stripped}')
        else:
            # Top-level text: add as bullet
            result.append(f'- {stripped}')

    return '\n'.join(result)


def generate_frontmatter(deck_name: str, total_slides: int) -> str:
    """Generate Marp frontmatter."""
    return f"""---
marp: true
theme: ia101
paginate: true
header: 'IA 101'
footer: '{deck_name}'
---"""


# Mapping directory name -> clean display name for footer
DECK_DISPLAY_NAMES = {
    '01-introduction': 'I - Introduction',
    '02-resolution-problemes': 'II - Resolution de problemes',
    '03-logique': 'III - Logique',
    '04-probabilites': 'IV - Probabilites',
    '05-theorie-des-jeux': 'V - Theorie des jeux',
    '06-apprentissage': 'VI - Apprentissage',
    '07-elargissements': 'VII - Elargissements',
    '08-ia-generative': 'VIII - IA Generative',
    'S1-argumentation': 'S1 - Argumentation',
    'S2-ia-exploratoire-symbolique': 'S2 - IA Exploratoire et Symbolique',
    'S3-acculturation': 'S3 - Acculturation',
    'S4-trading-algorithmique': 'S4 - Trading Algorithmique',
}


def convert_deck(deck_dir: str, verbose: bool = True) -> str:
    """Convert a full deck to Marp format. Returns path to generated slides.md."""
    deck_dir = os.path.normpath(deck_dir)
    dir_name = os.path.basename(deck_dir)
    deck_name = DECK_DISPLAY_NAMES.get(dir_name, dir_name.replace('-', ' ').title())

    if verbose:
        print(f"Converting: {deck_dir}")

    # Load data
    content_path = os.path.join(deck_dir, 'extracted', 'content.md')
    if not os.path.isfile(content_path):
        print(f"  ERROR: {content_path} not found")
        return ''

    slides_data = parse_content_md(content_path)
    slides_meta = load_inventory(deck_dir)
    image_map = map_images(deck_dir)

    if verbose:
        print(f"  Slides: {len(slides_data)}, Images: {sum(len(v) for v in image_map.values())}")

    # Copy images
    name_map = copy_images(deck_dir, image_map)
    if verbose and name_map:
        print(f"  Copied {len(name_map)} images to images/")

    # Generate Marp markdown
    output_lines = [generate_frontmatter(deck_name, len(slides_data))]

    for slide_num in sorted(slides_data.keys()):
        slide_data = slides_data[slide_num]
        meta = slides_meta.get(slide_num, {})

        slide_md = generate_marp_slide(
            slide_num, slide_data, meta,
            image_map, name_map, deck_name
        )

        output_lines.append('')
        output_lines.append('---')
        output_lines.append('')
        output_lines.append(slide_md)

    # Write output
    output_path = os.path.join(deck_dir, 'slides.md')
    content = '\n'.join(output_lines) + '\n'

    with open(output_path, 'w', encoding='utf-8') as f:
        f.write(content)

    if verbose:
        print(f"  Generated: {output_path}")

    return output_path


def find_all_decks(slides_root: str) -> list[str]:
    """Find all deck directories under slides/."""
    decks = []
    for entry in sorted(os.listdir(slides_root)):
        deck_dir = os.path.join(slides_root, entry)
        content_path = os.path.join(deck_dir, 'extracted', 'content.md')
        if os.path.isdir(deck_dir) and os.path.isfile(content_path):
            decks.append(deck_dir)
    return decks


def main():
    parser = argparse.ArgumentParser(description='Convert extracted PPTX to Marp Markdown')
    parser.add_argument('deck_dir', nargs='?', help='Path to a deck directory')
    parser.add_argument('--all', action='store_true', help='Convert all decks under slides/')
    parser.add_argument('--slides-root', default=None, help='Root slides directory')
    parser.add_argument('-q', '--quiet', action='store_true', help='Suppress output')
    args = parser.parse_args()

    # Determine slides root
    if args.slides_root:
        slides_root = args.slides_root
    else:
        # Auto-detect: look for slides/ relative to script location
        script_dir = os.path.dirname(os.path.abspath(__file__))
        slides_root = os.path.dirname(script_dir)  # parent of _tools/

    verbose = not args.quiet

    if args.all:
        decks = find_all_decks(slides_root)
        if not decks:
            print(f"No decks found under {slides_root}")
            sys.exit(1)
        print(f"Converting {len(decks)} decks...")
        for deck_dir in decks:
            convert_deck(deck_dir, verbose)
        print(f"\nDone. {len(decks)} decks converted.")
    elif args.deck_dir:
        path = convert_deck(args.deck_dir, verbose)
        if not path:
            sys.exit(1)
    else:
        parser.print_help()
        sys.exit(1)


if __name__ == '__main__':
    main()
