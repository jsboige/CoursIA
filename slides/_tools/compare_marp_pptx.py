#!/usr/bin/env python3
"""
Automated comparison tool for Marp vs PPTX slide decks.

Compares:
- Slide counts
- Content structure
- Image references
- Layout differences

Usage:
    python compare_marp_pptx.py <deck_directory>
"""

import os
import re
import json
from pathlib import Path
from typing import Dict, List, Tuple


def parse_markdown_slides(md_path: str) -> List[Dict]:
    """Parse markdown file into slides separated by ---."""
    with open(md_path, 'r', encoding='utf-8') as f:
        content = f.read()

    # Split by slide separator
    raw_slides = re.split(r'^---$', content, flags=re.MULTILINE)

    slides = []
    slide_number = 1  # Start numbering from 1

    for slide_content in raw_slides:
        # Skip empty slides (before first --- or after last ---)
        if not slide_content.strip():
            continue

        # Skip Marp metadata section (contains marp: true, theme, etc.)
        if 'marp:' in slide_content and 'theme:' in slide_content:
            continue

        # Extract title
        title_match = re.search(r'^#\s+(.+)$', slide_content, re.MULTILINE)
        title = title_match.group(1).strip() if title_match else f"Slide {slide_number}"

        # Extract image references
        images = re.findall(r'!\[.*?\]\((.*?)\)', slide_content)

        # Check for layout classes
        layout_match = re.search(r'<!--\s*_class:\s*(\w+)\s*-->', slide_content)
        layout = layout_match.group(1) if layout_match else 'default'

        slides.append({
            'number': slide_number,
            'title': title,
            'images': images,
            'layout': layout,
            'content_length': len(slide_content)
        })

        slide_number += 1  # Increment for next slide

    return slides


def parse_extracted_content(content_path: str) -> List[Dict]:
    """Parse extracted content.md into slides."""
    with open(content_path, 'r', encoding='utf-8') as f:
        content = f.read()

    # Split by slide markers
    slide_blocks = re.split(r'<!-- Slide number:', content)

    slides = []
    for block in slide_blocks[1:]:  # Skip first empty split
        lines = block.strip().split('\n')
        if not lines:
            continue

        # Extract slide number
        num_match = re.match(r'(\d+)\s*-->', lines[0])
        if not num_match:
            continue

        slide_num = int(num_match.group(1))

        # Extract title (first line starting with #)
        title = f"Slide {slide_num}"
        for line in lines[1:]:
            if line.strip().startswith('#'):
                title = line.strip().lstrip('#').strip()
                break

        # Extract image references
        images = re.findall(r'!\[\]\((.*?)\)', block)

        slides.append({
            'number': slide_num,
            'title': title,
            'images': images
        })

    return sorted(slides, key=lambda x: x['number'])


def compare_slides(marp_slides: List[Dict], pptx_slides: List[Dict]) -> Dict:
    """Compare Marp and PPTX slides."""

    comparison = {
        'marp_count': len(marp_slides),
        'pptx_count': len(pptx_slides),
        'title_matches': [],
        'title_mismatches': [],
        'missing_in_pptx': [],
        'missing_in_marp': [],
        'image_issues': []
    }

    # Create lookup dicts
    marp_by_num = {s['number']: s for s in marp_slides}
    pptx_by_num = {s['number']: s for s in pptx_slides}

    # Compare titles
    all_numbers = sorted(set(marp_by_num.keys()) | set(pptx_by_num.keys()))

    for num in all_numbers:
        marp_slide = marp_by_num.get(num)
        pptx_slide = pptx_by_num.get(num)

        if marp_slide and pptx_slide:
            # Normalize titles for comparison
            marp_title = marp_slide['title'].lower().strip()
            pptx_title = pptx_slide['title'].lower().strip()

            # Check for key match (ignore parentheticals, numbering)
            marp_key = re.sub(r'\(.*?\)|\d+/\d+', '', marp_title).strip()
            pptx_key = re.sub(r'\(.*?\)|\d+/\d+', '', pptx_title).strip()

            if marp_key == pptx_key or marp_key in pptx_key or pptx_key in marp_key:
                comparison['title_matches'].append({
                    'number': num,
                    'marp_title': marp_slide['title'],
                    'pptx_title': pptx_slide['title']
                })
            else:
                comparison['title_mismatches'].append({
                    'number': num,
                    'marp_title': marp_slide['title'],
                    'pptx_title': pptx_slide['title']
                })

            # Check image issues
            if marp_slide['images']:
                for img_ref in marp_slide['images']:
                    img_path = Path(marp_slide.get('base_path', '')) / img_ref
                    if not img_path.exists():
                        comparison['image_issues'].append({
                            'slide': num,
                            'image': img_ref,
                            'issue': 'File not found'
                        })

        elif marp_slide and not pptx_slide:
            comparison['missing_in_pptx'].append({
                'number': num,
                'marp_title': marp_slide['title']
            })

        elif pptx_slide and not marp_slide:
            comparison['missing_in_marp'].append({
                'number': num,
                'pptx_title': pptx_slide['title']
            })

    return comparison


def generate_report(comparison: Dict, output_path: str):
    """Generate markdown comparison report."""

    report_lines = [
        "# Rapport de Comparaison Marp vs PPTX",
        "",
        f"**Marp slides**: {comparison['marp_count']}",
        f"**PPTX slides**: {comparison['pptx_count']}",
        f"**Différence**: {comparison['marp_count'] - comparison['pptx_count']} slides",
        "",
        "---",
        "",
        "## Correspondance des Titres",
        ""
    ]

    # Title matches
    if comparison['title_matches']:
        report_lines.append("### Slides Correspondantes")
        report_lines.append("")
        for match in comparison['title_matches']:
            report_lines.append(f"- **Slide {match['number']}**: {match['marp_title']}")
        report_lines.append("")

    # Title mismatches
    if comparison['title_mismatches']:
        report_lines.append("### Slides avec Différences")
        report_lines.append("")
        for mismatch in comparison['title_mismatches']:
            report_lines.append(f"- **Slide {mismatch['number']}**:")
            report_lines.append(f"  - Marp: {mismatch['marp_title']}")
            report_lines.append(f"  - PPTX: {mismatch['pptx_title']}")
        report_lines.append("")

    # Missing slides
    if comparison['missing_in_pptx']:
        report_lines.append("### Slides Absentes du PPTX")
        report_lines.append("")
        for missing in comparison['missing_in_pptx']:
            report_lines.append(f"- Slide {missing['number']}: {missing['marp_title']}")
        report_lines.append("")

    if comparison['missing_in_marp']:
        report_lines.append("### Slides Absentes du Marp")
        report_lines.append("")
        for missing in comparison['missing_in_marp']:
            report_lines.append(f"- Slide {missing['number']}: {missing['pptx_title']}")
        report_lines.append("")

    # Image issues
    if comparison['image_issues']:
        report_lines.append("## Problèmes d'Images")
        report_lines.append("")
        for issue in comparison['image_issues']:
            report_lines.append(f"- **Slide {issue['slide']}**: `{issue['image']}` - {issue['issue']}")
        report_lines.append("")

    # Summary
    report_lines.extend([
        "---",
        "",
        "## Résumé",
        "",
        f"- **Correspondances**: {len(comparison['title_matches'])} slides",
        f"- **Différences**: {len(comparison['title_mismatches'])} slides",
        f"- **Absentes PPTX**: {len(comparison['missing_in_pptx'])} slides",
        f"- **Absentes Marp**: {len(comparison['missing_in_marp'])} slides",
        f"- **Images manquantes**: {len(comparison['image_issues'])}",
        ""
    ])

    with open(output_path, 'w', encoding='utf-8') as f:
        f.write('\n'.join(report_lines))


def main():
    import argparse

    parser = argparse.ArgumentParser(description='Compare Marp and PPTX slide decks')
    parser.add_argument('deck_dir', help='Path to deck directory (e.g., 07-elargissements)')
    parser.add_argument('--output', '-o', help='Output report path')
    args = parser.parse_args()

    deck_path = Path(args.deck_dir)
    if not deck_path.is_absolute():
        deck_path = Path.cwd() / deck_path

    # File paths
    md_path = deck_path / 'slides.md'
    content_path = deck_path / 'extracted' / 'content.md'

    if not md_path.exists():
        print(f"Error: {md_path} not found")
        return 1

    if not content_path.exists():
        print(f"Error: {content_path} not found")
        return 1

    # Parse files
    print(f"Parsing {md_path}...")
    marp_slides = parse_markdown_slides(str(md_path))

    # Set base path for image validation
    assets_path = deck_path / '_assets' / 'images'
    for slide in marp_slides:
        slide['base_path'] = str(assets_path)

    print(f"Parsing {content_path}...")
    pptx_slides = parse_extracted_content(str(content_path))

    print(f"Marp slides: {len(marp_slides)}")
    print(f"PPTX slides: {len(pptx_slides)}")

    # Compare
    print("Comparing...")
    comparison = compare_slides(marp_slides, pptx_slides)

    # Generate report
    output_path = args.output or str(deck_path / 'analysis' / 'comparison_report.md')
    os.makedirs(os.path.dirname(output_path), exist_ok=True)

    print(f"Generating report: {output_path}")
    generate_report(comparison, output_path)

    print("Done!")
    return 0


if __name__ == '__main__':
    exit(main())
