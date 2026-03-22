#!/usr/bin/env python3
"""
Audit pédagogique des READMEs QuantConnect.

Analyse la structure, la cohérence et la qualité pédagogique des READMEs.
"""

import os
import re
from pathlib import Path
from dataclasses import dataclass, field
from typing import List, Dict, Optional
from collections import Counter


@dataclass
class ReadmeStats:
    """Statistiques d'un README."""
    path: str
    lines: int = 0
    words: int = 0
    has_title: bool = False
    has_description: bool = False
    has_examples: bool = False
    has_requirements: bool = False
    has_usage: bool = False
    has_links: bool = False
    sections: List[str] = field(default_factory=list)
    broken_links: List[str] = field(default_factory=list)
    missing_sections: List[str] = field(default_factory=list)


class ReadmeAuditor:
    """Auditeur de READMEs QuantConnect."""

    # Sections attendues selon le type de README
    MAIN_SECTIONS = [
        "Vue d'Ensemble",
        "Démarrage Rapide",
        "Structure de la Série",
        "Configuration",
        "Ressources Complémentaires"  # Plus flexible que "Ressources" seul
    ]

    PROJECT_SECTIONS = [
        "Description",
        "Stratégie",
        "Performance",
        "Installation",
        "Utilisation"
    ]

    ESGF_EXAMPLE_SECTIONS = [
        "Objectif",
        "Stratégie",
        "Résultats",
        "Installation",
        "Utilisation"
    ]

    def __init__(self, root_dir: str):
        self.root_dir = Path(root_dir)
        self.readmes: List[ReadmeStats] = []

    def find_readmes(self) -> List[Path]:
        """Trouve tous les READMEs du projet."""
        all_readmes = list(self.root_dir.rglob("README.md"))
        # Exclure les READMEs du dossier data/ (fichiers LEAN par défaut)
        return [r for r in all_readmes if 'data/' not in r.parts and r != self.root_dir / 'data' / 'README.md']

    def classify_readme(self, path: Path) -> str:
        """Classifie le type de README."""
        parts = path.parts
        if "ESGF-2026/examples" in parts:
            return "ESGF_EXAMPLE"
        elif "ESGF-2026/templates" in parts:
            return "ESGF_TEMPLATE"
        elif "ESGF-2026" in parts:
            return "ESGF_MAIN"
        elif "projects" in parts:
            return "PROJECT"
        elif path.name == "README.md" and len(parts) <= 7:
            return "MAIN"
        return "OTHER"

    def extract_sections(self, content: str) -> List[str]:
        """Extrait les titres de sections du markdown."""
        # Matches ## Titre
        return re.findall(r'^##\s+(.+)$', content, re.MULTILINE)

    def check_links(self, content: str, base_path: Path) -> List[str]:
        """Vérifie les liens relatifs brisés."""
        broken = []
        # Matches [](path) ou [text](path)
        links = re.findall(r'\[([^\]]+)\]\(([^)]+)\)', content)

        for text, link in links:
            if link.startswith('http'):
                continue  # Liens externes non vérifiés
            if link.startswith('#'):
                continue  # Ancres internes ignorées
            # Lien relatif
            target = base_path.parent / link
            if not target.exists():
                broken.append(link)

        return broken

    def analyze_readme(self, path: Path) -> ReadmeStats:
        """Analyse un README."""
        content = path.read_text(encoding='utf-8')
        lines = content.split('\n')

        stats = ReadmeStats(path=str(path.relative_to(self.root_dir)))
        stats.lines = len(lines)
        stats.words = sum(len(line.split()) for line in lines)

        # Détection basique
        stats.has_title = any(line.strip().startswith('# ') for line in lines[:10])
        stats.has_description = stats.words > 50
        stats.sections = self.extract_sections(content)
        stats.broken_links = self.check_links(content, path)

        # Détection de sections
        content_lower = content.lower()
        stats.has_examples = any('example' in s.lower() for s in stats.sections)
        stats.has_requirements = any(kw in content_lower for kw in ['requirement', 'dépendance', 'prérequis'])
        stats.has_usage = any('usage' in s.lower() or 'util' in s.lower() for s in stats.sections)
        stats.has_links = len(re.findall(r'\[([^\]]+)\]\(', content)) > 0

        # Vérification sections attendues (recherche partielle, plus flexible)
        readme_type = self.classify_readme(path)
        if readme_type == "MAIN":
            expected = self.MAIN_SECTIONS
        elif readme_type == "PROJECT":
            expected = self.PROJECT_SECTIONS
        elif readme_type == "ESGF_EXAMPLE":
            expected = self.ESGF_EXAMPLE_SECTIONS
        else:
            expected = []

        # Vérification flexible : cherche les mots-clés dans les sections
        missing = []
        for exp in expected:
            # Extrait les mots-clés de la section attendue (ex: "Vue d'Ensemble" -> "ensemble")
            keywords = exp.lower().replace('-', ' ').split()
            # Vérifie si au moins un mot-clé est présent dans une section
            found = any(
                any(kw in s.lower() for kw in keywords if len(kw) > 3)
                for s in stats.sections
            )
            if not found:
                missing.append(exp)

        stats.missing_sections = missing

        return stats

    def audit_all(self) -> Dict[str, List[ReadmeStats]]:
        """Audit tous les READMEs et renvoie les résultats par catégorie."""
        readme_paths = self.find_readmes()
        results = {}

        for path in readme_paths:
            stats = self.analyze_readme(path)
            self.readmes.append(stats)

            category = self.classify_readme(path)
            if category not in results:
                results[category] = []
            results[category].append(stats)

        return results

    def print_report(self, results: Dict[str, List[ReadmeStats]]):
        """Affiche le rapport d'audit."""
        total = len(self.readmes)
        print(f"\n{'='*70}")
        print(f"AUDIT PÉDAGOGIQUE README - QuantConnect")
        print(f"{'='*70}")
        print(f"Total READMEs analysés : {total}\n")

        # Résumé par catégorie
        for category, items in sorted(results.items()):
            print(f"\n{category} : {len(items)} fichiers")
            print("-" * 70)

            for stats in items:
                status_icon = "✅" if not stats.missing_sections and not stats.broken_links else "⚠️"
                print(f"  {status_icon} {stats.path}")
                print(f"      {stats.lines} lignes | {len(stats.sections)} sections")

                if stats.missing_sections:
                    print(f"      Sections manquantes: {', '.join(stats.missing_sections)}")
                if stats.broken_links:
                    print(f"      Liens brisés: {', '.join(stats.broken_links)}")

        # Statistiques globales
        print(f"\n{'='*70}")
        print("STATISTIQUES GLOBALES")
        print(f"{'='*70}")

        with_title = sum(1 for r in self.readmes if r.has_title)
        with_desc = sum(1 for r in self.readmes if r.has_description)
        with_examples = sum(1 for r in self.readmes if r.has_examples)
        with_reqs = sum(1 for r in self.readmes if r.has_requirements)
        with_usage = sum(1 for r in self.readmes if r.has_usage)
        with_links = sum(1 for r in self.readmes if r.has_links)

        print(f"Avec titre : {with_title}/{total} ({100*with_title//total}%)")
        print(f"Avec description (>50 mots) : {with_desc}/{total} ({100*with_desc//total}%)")
        print(f"Avec exemples : {with_examples}/{total} ({100*with_examples//total}%)")
        print(f"Avec prérequis : {with_reqs}/{total} ({100*with_reqs//total}%)")
        print(f"Avec utilisation : {with_usage}/{total} ({100*with_usage//total}%)")
        print(f"Avec liens : {with_links}/{total} ({100*with_links//total}%)")

        total_broken = sum(len(r.broken_links) for r in self.readmes)
        total_missing = sum(len(r.missing_sections) for r in self.readmes)

        print(f"\nLiens brisés : {total_broken}")
        print(f"Sections manquantes : {total_missing}")

        # Recommandations
        if total_broken > 0:
            print(f"\n⚠️  RECOMMANDATION : Corriger les {total_broken} liens brisés")

        if total_missing > 10:
            print(f"\n⚠️  RECOMMANDATION : Standardiser les sections manquantes")


def main():
    """Point d'entrée."""
    root_dir = Path(__file__).parent.parent
    auditor = ReadmeAuditor(str(root_dir))
    results = auditor.audit_all()
    auditor.print_report(results)


if __name__ == "__main__":
    main()
