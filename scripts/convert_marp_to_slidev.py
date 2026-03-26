#!/usr/bin/env python3
"""Convert Marp slides to Slidev format."""

import re
import sys
from pathlib import Path


def convert_marp_to_slidev(input_path: Path, output_path: Path, title: str) -> None:
    """Convert a Marp markdown file to Slidev format."""
    content = input_path.read_text(encoding='utf-8')

    # Extract footer for title suffix
    footer_match = re.search(r"footer: '(.+?)'", content)
    footer = footer_match.group(1) if footer_match else ""

    # Replace frontmatter
    old_frontmatter = re.search(r'^---\nmarp: true.*?^---', content, re.DOTALL | re.MULTILINE)
    if old_frontmatter:
        new_frontmatter = f'''---
theme: ../theme-ia101
title: "{title}"
info: Cours Intelligence Artificielle
paginate: true
drawings:
  persist: false
transition: slide-left
mdc: true
layout: cover
---'''
        content = content[:old_frontmatter.start()] + new_frontmatter + content[old_frontmatter.end():]

    # Remove <!-- _class: title --> comments
    content = re.sub(r'<!-- _class: title -->\n*', '', content)

    # Convert <!-- _class: questions --> to layout: center
    content = re.sub(
        r'---\n\n<!-- _class: questions -->\n\n',
        '---\nlayout: center\n---\n\n',
        content
    )

    # Convert ![bg right:XX%](images/xxx.png) to layout: image-right
    def convert_image(match):
        percentage = match.group(1)
        image_path = match.group(2)
        # Add ./ prefix if not present
        if not image_path.startswith('./') and not image_path.startswith('../'):
            image_path = './' + image_path

        # Map percentage to prop
        if percentage:
            return f'---\nlayout: image-right\nimage: {image_path}\n---\n'
        else:
            return f'---\nlayout: image-right\nimage: {image_path}\n---\n'

    # Match ![bg right:30%](images/xxx.png) or ![bg right](images/xxx.png)
    content = re.sub(
        r'!\[bg right(?::(\d+))?%\]\(([^)]+)\)',
        convert_image,
        content
    )

    # Also handle ![bg left:XX%](...)
    content = re.sub(
        r'!\[bg left(?::(\d+))?%\]\(([^)]+)\)',
        lambda m: f'---\nlayout: image-left\nimage: ./{m.group(2) if not m.group(2).startswith("./") else m.group(2)}\n---\n',
        content
    )

    # Write output
    output_path.write_text(content, encoding='utf-8')
    print(f"Converted: {input_path} -> {output_path} ({len(content.splitlines())} lines)")


DECKS = [
    ("02-resolution-problemes", "02 Resolution de Problemes"),
    ("03-logique", "03 Logique"),
    ("04-probabilites", "04 Probabilites"),
    ("05-theorie-des-jeux", "05 Theorie des Jeux"),
    ("06-apprentissage", "06 Apprentissage"),
    ("07-elargissements", "07 Elargissements"),
    ("08-ia-generative", "08 IA Generative"),
    ("S1-argumentation", "S1 Argumentation"),
    ("S2-ia-exploratoire-symbolique", "S2 IA Exploratoire et Symbolique"),
    ("S3-acculturation", "S3 Acculturation IA"),
]


def main():
    slides_dir = Path("slides")

    for deck_dir, title in DECKS:
        deck_path = slides_dir / deck_dir
        marp_file = deck_path / "slides.marp.md"
        slidev_file = deck_path / "slides.md"

        if not marp_file.exists():
            # Try alternate naming
            marp_file = deck_path / "slides.md"
            if not marp_file.exists():
                print(f"SKIP: {deck_dir} - no slides.marp.md found")
                continue

        if slidev_file.exists():
            print(f"EXISTS: {deck_dir}/slides.md already exists")
            continue

        convert_marp_to_slidev(marp_file, slidev_file, title)


if __name__ == "__main__":
    main()
