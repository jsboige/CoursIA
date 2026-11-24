#!/usr/bin/env python3
"""Insere les boutons de lancement sur les pages de carnets du site rendu.

Pli 2.3 de l'Epic #27543 : une page de carnet doit offrir les lancements
auxquels le carnet a droit -- **Codespaces** (via le devcontainer du pli 1.4),
**Colab** (carnets Python, recette de #23276) et **JupyterLite** (carnets
publies dans le bundle du pli 2.2).

Trois principes, tous verifiables :

1. **L'eligibilite est CALCULEE, jamais posee a la main.** Un bouton n'est
   emis que si la condition qui le justifie est measurable sur l'arbre :
   Codespaces exige ``.devcontainer/devcontainer.json`` a la racine du depot ;
   Colab exige un carnet Python ; JupyterLite exige que le carnet figure
   dans le **manifeste publie du bundle** (``_site/jupyterlite/manifest.json``).
   Un carnet qui n'a pas droit a un bouton ne l'a **pas** -- le bouton est
   absent, jamais grise sans explication.
2. **Aucune URL de lien mort.** L'URL JupyterLite est celle du manifeste
   (le bundle la publie), l'URL Colab est la forme Colab du chemin du
   carnet dans le depot, l'URL Codespaces est celle du devcontainer publie.
   La page n'affiche que des liens dont la cible existe.
3. **La passe est post-rendu et idempotente.** Elle agit sur ``_site/``,
   jamais sur les sources du depot ; un marqueur
   (``data-coursia-launch-buttons``) rend une seconde execution sans effet.

Le site publie est produit par la CI (comme la passe de reecriture des
liens, #10921) : les boutons sont inseres **apres** le rendu, dans le
pipeline de publication.

Usage
-----
    python scripts/notebook_tools/launch_buttons.py --site-dir _site --repo-root .
    python scripts/notebook_tools/launch_buttons.py --site-dir _site --check
    python scripts/notebook_tools/launch_buttons.py --site-dir _site --rapport rapport.json

Sorties : 0 rien a faire (ou ecrit), 1 insertions dues en --check,
2 instrument casse (repertoire _site/ illisible, manifeste illisible).
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple

#: Depot de reference : la navigation du site est celle de github.com.
DEPOT = "jsboige/CoursIA"
#: Branche visee par les liens « ouvrir le carnet » : le site publie `main`.
BRANCHE = "main"
#: Origine du site publie (le manifeste porte des URL relatives a la base).
ORIGINE_SITE = "https://jsboige.github.io"
#: Devcontainer du pli 1.4 : son absence retire le bouton Codespaces.
CHEMIN_DEVCONTAINER = ".devcontainer/devcontainer.json"
#: Type de machine Codespaces : celui du badge publie (pli's devcontainer).
MACHINE_CODESPACES = "basicLinux32gb"
#: Marqueur d'identite : rend l'injection idempotente.
MARQUEUR = 'data-coursia-launch-buttons="1"'

EXIT_OK = 0
EXIT_PENDING = 1
EXIT_INSTRUMENT = 2

#: Ancre d'insertion preferentielle : le titre de la page (les boutons se
#: placent sous le titre, comme le fait la navigation de Quarto).
_ANCRE_TITRE = re.compile(
    r'(<h1[^>]*class="(?:[^"]* )?title(?: [^"]*)?"[^>]*>.*?</h1>)', re.IGNORECASE | re.DOTALL)
#: Ancre de repli (Quarto 1.7) : le contenu de la page.
_ANCRE_CONTENU = re.compile(r'(<div id="quarto-document-content"[^>]*>)', re.IGNORECASE)
#: Repli : le corps de la page.
_ANCRE_BODY = re.compile(r'(<body[^>]*>)', re.IGNORECASE)
#: Taille de la queue lue dans un .ipynb : le bloc ``metadata`` est en fin de
#: fichier, on lit donc la queue plutot que les 1 400 carnets entiers.
TAILLE_QUEUE = 16384


class ErreurInstrument(Exception):
    """Le repertoire du site ou le manifeste est illisible (sortie 2)."""


@dataclass(frozen=True)
class Bouton:
    """Un bouton de lancement, avec la condition qui l'a justifie."""

    genre: str          # codespaces | colab | jupyterlite
    libelle: str
    url: str
    condition: str      # la mesure qui autorise ce bouton


# --------------------------------------------------------------------------
# Les URL
# --------------------------------------------------------------------------

def url_codespaces(depot: str = DEPOT, ref: str = BRANCHE) -> str:
    """URL d'ouverture d'un Codespace sur le devcontainer du depot."""
    from urllib.parse import quote

    return (
        "https://github.com/codespaces/new?hide_repo_select=true"
        "&repo=%s&ref=%s&machine=%s&devcontainer_path=%s"
        % (quote(depot, safe=""), quote(ref, safe=""),
           MACHINE_CODESPACES, quote(CHEMIN_DEVCONTAINER, safe=""))
    )


def url_colab(chemin: str, depot: str = DEPOT, ref: str = BRANCHE) -> str:
    """URL d'ouverture d'un carnet Python dans Colab (recette de #23276).

    La forme est celle que le depot sait deja lire
    (``scripts/notebook_tools/check_external_consumer_links.py``) :
    ``https://colab.research.google.com/github/<depot>/blob/<branche>/<chemin>``.
    """
    return "https://colab.research.google.com/github/%s/blob/%s/%s" % (
        depot, ref, chemin.lstrip("/"))


# --------------------------------------------------------------------------
# Les mesures d'eligibilite
# --------------------------------------------------------------------------

@dataclass(frozen=True)
class Langage:
    """La langue declaree par un carnet, et son noyau.

    ``language`` est ``metadata.language_info.name`` (la langue du document,
    declaree par le noyau qui l'a execute) ; ``kernel`` est
    ``metadata.kernelspec.name`` (le nom de l'environnement, pas une langue :
    ``ict-py313``, ``py310-gpu`` ou ``.net-csharp`` sont des noyaux dont le
    nom ne commence pas par « python »).
    """

    language: str = ""
    kernel: str = ""


def est_python(langage: Langage) -> bool:
    """Le carnet est-il de la famille Python ?

    La regle est **celle du critere d'eligibilite** (pli 2.1,
    ``pyodide_eligibility.is_python_notebook``) : ``language_info.name`` fait
    foi, le nom du kernelspec n'est qu'un repli ; le premier marqueur non vide
    decide, et un carnet qui ne declare ni l'un ni l'autre n'est pas compte
    comme Python. Les deux lectures sont comparees mecaniquement par un test
    sur un echantillon de carnets reels.
    """
    for marqueur in (langage.language, langage.kernel):
        if marqueur:
            return marqueur.lower().startswith("python")
    return False


def _objet_json(texte: str, cle: str) -> Optional[str]:
    """Le corps de l'objet JSON ``cle`` (accolades appairees), ou None.

    Les metadonnees d'un carnet contiennent des objets imbriques
    (``codemirror_mode``) : une expression reguliere ne suffit pas -- on
    apparie les accolades.
    """
    cible = '"%s"' % cle
    debut = 0
    while True:
        idx = texte.find(cible, debut)
        if idx == -1:
            return None
        debut = idx + len(cible)
        ouverture = texte.find("{", idx)
        if ouverture == -1:
            return None
        profondeur = 0
        for i in range(ouverture, len(texte)):
            char = texte[i]
            if char == "{":
                profondeur += 1
            elif char == "}":
                profondeur -= 1
                if profondeur == 0:
                    corps = texte[ouverture:i + 1]
                    try:
                        json.loads(corps)
                    except ValueError:
                        continue
                    return corps
        return None


def _nom_de(texte: str, cle: str) -> str:
    corps = _objet_json(texte, cle)
    if corps is None:
        return ""
    try:
        valeur = json.loads(corps).get("name")
    except ValueError:
        return ""
    return str(valeur) if valeur else ""


def langage_du_carnet(chemin: Path, taille_queue: int = TAILLE_QUEUE) -> Langage:
    """La langue et le noyau du carnet, lus dans ses metadonnees.

    Lecture de la **queue** du fichier (le bloc ``metadata`` est en fin de
    .ipynb) ; si la lecture rapide ne dit rien, on retombe sur une lecture
    complete du carnet.
    """
    try:
        taille = chemin.stat().st_size
        with chemin.open("rb") as fh:
            if taille > taille_queue:
                fh.seek(-taille_queue, 2)
            blob = fh.read().decode("utf-8", errors="replace")
    except OSError:
        return Langage()
    langage = _nom_de(blob, "language_info")
    noyau = _nom_de(blob, "kernelspec")
    if langage or noyau:
        return Langage(language=langage, kernel=noyau)
    try:
        donnees = json.loads(chemin.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return Langage()
    meta = donnees.get("metadata") or {}
    info = meta.get("language_info") or {}
    spec = meta.get("kernelspec") or {}
    return Langage(language=str(info.get("name") or ""),
                    kernel=str(spec.get("name") or ""))


def lire_manifeste(chemin: Path) -> Dict[str, Dict[str, str]]:
    """Le manifeste publie du bundle : {chemin du depot -> entree du carnet}.

    Le manifeste est l'artefact de verite du pli 2.2 : un carnet absent du
    manifeste n'a **pas** de page JupyterLite publiee -- son bouton ne doit
    donc pas etre emis.
    """
    if not chemin.is_file():
        return {}
    try:
        donnees = json.loads(chemin.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        raise ErreurInstrument("manifeste illisible : %s (%s)" % (chemin, exc))
    entrees: Dict[str, Dict[str, str]] = {}
    for carnet in donnees.get("carnets") or []:
        rel = str(carnet.get("chemin") or "")
        if rel:
            entrees[rel.replace("\\", "/")] = carnet
    return entrees


def boutons_pour_carnet(rel: str, chemin_source: Path, manifeste: Dict[str, Dict[str, str]],
                        racine: Path, depot: str = DEPOT, ref: str = BRANCHE) -> List[Bouton]:
    """Les boutons du carnet, chacun avec la mesure qui l'autorise.

    L'ordre est stable (Codespaces, Colab, JupyterLite) : la page rendue
    est ainsi deterministe d'un build a l'autre. Aucune condition n'est un
    drapeau pose a la main : le devcontainer est **recherche** dans l'arbre.
    """
    boutons: List[Bouton] = []
    if (racine / CHEMIN_DEVCONTAINER).is_file():
        boutons.append(Bouton(
            genre="codespaces",
            libelle="Codespaces",
            url=url_codespaces(depot, ref),
            condition="devcontainer present : %s" % CHEMIN_DEVCONTAINER))
    langage = langage_du_carnet(chemin_source)
    if est_python(langage):
        boutons.append(Bouton(
            genre="colab",
            libelle="Colab",
            url=url_colab(rel, depot, ref),
            condition="carnet Python (noyau lu dans les metadonnees)"))
    entree = manifeste.get(rel.replace("\\", "/"))
    if entree is not None:
        lab = str(entree.get("lab") or "")
        if lab:
            boutons.append(Bouton(
                genre="jupyterlite",
                libelle="JupyterLite",
                url=_url_absolue(lab),
                condition="carnet publie dans le bundle (manifeste)"))
    return boutons


def _url_absolue(lab: str) -> str:
    """Le manifeste porte une URL relative a la base du site : on la rend absolue."""
    if lab.startswith("http://") or lab.startswith("https://"):
        return lab
    return ORIGINE_SITE + "/" + lab.lstrip("/")


# --------------------------------------------------------------------------
# L'injection
# --------------------------------------------------------------------------

def bloc_html(boutons: Sequence[Bouton]) -> str:
    """Le bloc HTML des boutons (marqueur d'identite compris)."""
    liens = "".join(
        '\n  <a class="btn coursia-launch-button" href="%s" title="%s">%s</a>'
        % (b.url, _echapper(b.condition), _echapper(b.libelle))
        for b in boutons)
    return ('\n<div class="coursia-launch-buttons" %s>'
            '<span class="coursia-launch-label">Lancer :</span>%s\n</div>\n'
            % (MARQUEUR, liens))


def _echapper(texte: str) -> str:
    return (texte.replace("&", "&amp;").replace("<", "&lt;")
            .replace(">", "&gt;").replace('"', "&quot;"))


def injecter(html: str, boutons: Sequence[Bouton]) -> Optional[str]:
    """Le HTML avec le bloc insere, ou None si rien a faire.

    ``None`` signifie soit « deja injecte » (idempotence), soit « aucune ancre
    trouvee » (page d'une forme inattendue -- le cas est compte et signale).
    """
    if MARQUEUR in html or not boutons:
        return None
    bloc = bloc_html(boutons)
    for motif in (_ANCRE_TITRE, _ANCRE_CONTENU, _ANCRE_BODY):
        trouve = motif.search(html)
        if trouve:
            return html[:trouve.end()] + bloc + html[trouve.end():]
    return None


# --------------------------------------------------------------------------
# La passe
# --------------------------------------------------------------------------

@dataclass
class Rapport:
    """Ce que la passe a fait, page par page."""

    pages_carnet: int = 0
    injectees: int = 0
    deja_injectees: int = 0
    sans_bouton: int = 0
    ancre_introuvable: int = 0
    source_introuvable: int = 0
    boutons: Dict[str, int] = None  # type: ignore[assignment]

    def __post_init__(self) -> None:
        if self.boutons is None:
            self.boutons = {}

    def compte(self, genre: str) -> None:
        self.boutons[genre] = self.boutons.get(genre, 0) + 1

    def resume(self) -> str:
        return ("%d pages de carnet ; %d injectees (%s) ; %d deja injectees ; "
                "%d sans bouton ; %d ancre introuvable ; %d source introuvable"
                % (self.pages_carnet, self.injectees,
                   ", ".join("%s %d" % (k, v) for k, v in sorted(self.boutons.items())) or "aucun bouton",
                   self.deja_injectees, self.sans_bouton, self.ancre_introuvable,
                   self.source_introuvable))


def pages_de_carnets(site: Path, racine: Path) -> List[Tuple[Path, str]]:
    """Les pages du site qui correspondent a un carnet du depot.

    Le rendu de Quarto preserve l'arborescence : ``X.ipynb`` est rendu en
    ``X.html``. On ne retient que les pages dont le carnet **existe** dans le
    depot -- c'est ce qui distingue une page de carnet d'une page de README.
    """
    trouves: List[Tuple[Path, str]] = []
    for page in sorted(site.rglob("*.html")):
        rel = page.relative_to(site).with_suffix(".ipynb")
        if (racine / rel).is_file():
            trouves.append((page, rel.as_posix()))
    return trouves


def passer(site: Path, racine: Path, manifeste: Dict[str, Dict[str, str]],
           ecrire: bool = True) -> Rapport:
    """La passe : calcule les boutons et les insere dans les pages de carnets."""
    rapport = Rapport()
    for page, rel in pages_de_carnets(site, racine):
        rapport.pages_carnet += 1
        source = racine / rel
        if not source.is_file():
            rapport.source_introuvable += 1
            continue
        boutons = boutons_pour_carnet(rel, source, manifeste, racine)
        if not boutons:
            rapport.sans_bouton += 1
            continue
        for b in boutons:
            rapport.compte(b.genre)
        html = page.read_text(encoding="utf-8", errors="replace")
        if MARQUEUR in html:
            rapport.deja_injectees += 1
            continue
        nouveau = injecter(html, boutons)
        if nouveau is None:
            rapport.ancre_introuvable += 1
            continue
        if ecrire:
            page.write_text(nouveau, encoding="utf-8", newline="")
        rapport.injectees += 1
    return rapport


def main(argv: Optional[Sequence[str]] = None) -> int:
    parseur = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parseur.add_argument("--site-dir", default="_site")
    parseur.add_argument("--repo-root", default=".")
    parseur.add_argument("--manifest", default=None,
                         help="manifeste publie du bundle (defaut : <site>/jupyterlite/manifest.json)")
    parseur.add_argument("--check", action="store_true",
                         help="ne rien ecrire ; rc 1 si des insertions sont dues")
    parseur.add_argument("--rapport", default=None, help="ecrit le rapport en JSON")
    args = parseur.parse_args(argv)

    site = Path(args.site_dir)
    racine = Path(args.repo_root)
    if not site.is_dir():
        print("instrument casse : repertoire de site illisible : %s" % site,
              file=sys.stderr)
        return EXIT_INSTRUMENT
    manifeste_path = Path(args.manifest) if args.manifest else site / "jupyterlite" / "manifest.json"
    try:
        manifeste = lire_manifeste(manifeste_path)
    except ErreurInstrument as exc:
        print("instrument casse : %s" % exc, file=sys.stderr)
        return EXIT_INSTRUMENT

    rapport = passer(site, racine, manifeste, ecrire=not args.check)
    print("launch-buttons : %s" % rapport.resume())
    if args.rapport:
        Path(args.rapport).write_text(
            json.dumps({
                "pages_carnet": rapport.pages_carnet,
                "injectees": rapport.injectees,
                "deja_injectees": rapport.deja_injectees,
                "sans_bouton": rapport.sans_bouton,
                "ancre_introuvable": rapport.ancre_introuvable,
                "source_introuvable": rapport.source_introuvable,
                "boutons": rapport.boutons,
            }, indent=1, sort_keys=True) + "\n", encoding="utf-8")
    if args.check and rapport.injectees:
        return EXIT_PENDING
    return EXIT_OK


if __name__ == "__main__":
    sys.exit(main())
