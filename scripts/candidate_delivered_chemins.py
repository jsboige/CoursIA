#!/usr/bin/env python3
"""Le CHEMIN CIBLE d'un grain, et ce que `main` en dit.

Le dispatch `c0035b` du coordinateur (24/11) : « les issues livrees sont
encore servies ; "le chemin cible est sur main" ne doit que **soupconner**
une livraison, jamais la conclure ; le grain passe a l'urne avec un label
candidat ».

Ce module porte ce signal, et lui seul :

- `nommes` -- les chemins du depot qu'une issue nomme (titre + corps) ;
- `touches_main` -- ce que `origin/main` en dit : un seul appel git pour
  tout le balayage, donc un cout **independant du nombre de grains** ;
- `suspects` -- les chemins dont le dernier mouvement sur `main` est
  **posterieur au dernier mouvement de l'issue**.

Un soupcon n'est **jamais** une preuve : il ne clot rien, il ne retire
rien. Il route le grain vers l'urne (le label `candidate-delivered`), dont
le Coordinateur et l'adjoint sont les gestionnaires. La grammaire du label
et le retrait par verdict humain restent dans `candidate_delivered.py` --
ce module ne fait qu'un calcul, il ne decide de rien.
"""
from __future__ import annotations

import re
import subprocess
from datetime import datetime, timezone

#: Les prefixes de chemins qu'une issue peut nommer (les repertoires du depot).
PREFIXES = ("MyIA.AI.Notebooks", "scripts", "docs", "dotnet", "slides",
            "config", ".claude")

#: Un chemin nomme : un prefixe connu, puis un nom de fichier avec une extension.
_CHEMIN_RE = re.compile(
    r"(?:MyIA\.AI\.Notebooks|scripts|docs|dotnet|slides|config|\.claude)/"
    r"[A-Za-z0-9_./+\-]+\.[A-Za-z0-9]{1,8}")

#: Le nombre de chemins retenus par grain : le signal est un indice, pas un dossier.
MAX_CHEMINS = 12

#: La fenetre de balayage de l'historique (jours). Un chemin touche recemment
#: suffit ; au-dela, le mouvement ne dit plus rien de l'issue d'aujourd'hui.
FENETRE_J = 365

#: Le separateur de records de `git log --format=%x1e`.
_SEP = "\x1e"

#: Le MARQUEUR de la suspicion, pose dans le fil de l'issue par l'organe qui
#: a compare le chemin cible au contenu de `main`. C'est une **donnee** : le
#: poseur de label (CI) et le tapis la lisent sans repayer la sonde.
#:
#: La forme est distincte de `[INFO] candidate-delivered` : celle-la dit
#: « les criteres sont couverts » (un verdict de livraison), celle-ci dit
#: « le chemin cible a bouge sur main, ce n'est peut-etre pas un travail a
#: refaire ». La distinction est lue par l'oeil, pas par une machine.
SUSPICION_MARKER_RE = re.compile(
    r"^\s*(?:#{1,6}\s*)?\[INFO\]\s+suspicion-livraison(?![-_\w])",
    re.IGNORECASE | re.MULTILINE,
)


def suspicion_dans_le_fil(bodies: list[str]) -> str | None:
    """La suspicion portee par le fil de l'issue, ou None.

    Le fil est la **donnee** qui survit a la machine qui l'a produite : le
    poseur de label tourne en CI sur un sparse-checkout sans historique, et
    ne peut pas refaire le calcul -- il lit le marqueur.
    """
    for body in bodies or []:
        if SUSPICION_MARKER_RE.search(body or ""):
            return "marqueur [INFO] suspicion-livraison dans le fil"
    return None


def nommes(texte: str) -> list[str]:
    """Les chemins du depot nommes dans un texte (titre + corps).

    L'ordre du texte est preserve, les doublons tombes : le premier nom
    d'un chemin est celui que l'ecrivain avait en tete.
    """
    vus: set[str] = set()
    out: list[str] = []
    for m in _CHEMIN_RE.finditer(texte or ""):
        chemin = m.group(0).rstrip(".,;:)`'\"")
        if chemin in vus:
            continue
        vus.add(chemin)
        out.append(chemin)
        if len(out) >= MAX_CHEMINS:
            break
    return out


def instant(texte: str | None) -> datetime | None:
    """Un instant ISO 8601 -> datetime (naif si la date n'a pas de fuseau)."""
    if not texte:
        return None
    try:
        return datetime.fromisoformat(str(texte).strip().replace("Z", "+00:00"))
    except ValueError:
        return None


def _comparable(dt: datetime | None) -> datetime:
    """Un datetime comparable : en UTC, et sans fuseau si l'original n'en a pas."""
    if dt is None:
        return datetime.min.replace(tzinfo=timezone.utc)
    if dt.tzinfo is None:
        return dt.replace(tzinfo=timezone.utc)
    return dt.astimezone(timezone.utc)


_ANCRE_CACHE: dict[int, re.Pattern[str]] = {}


def _ancre_re(numero: int) -> re.Pattern[str]:
    """La reference **entiere** a l'issue : `#7` ne vaut pas pour `#70`.

    Le test par sous-chaine faisait soupconner l'issue 7 sur un commit qui ne
    citait que `#70` (defaut mesure le 25/11, revue du coordinateur sur
    #28454). On exige un numero entier : pas de chiffre avant le `#`, pas de
    chiffre apres.
    """
    motif = _ANCRE_CACHE.get(numero)
    if motif is None:
        motif = re.compile(r"(?<!\d)#%d(?!\d)" % numero)
        _ANCRE_CACHE[numero] = motif
    return motif


def touches_main(depot: str | None = None,
                 jours: int = FENETRE_J) -> dict[str, tuple[str, str, str]] | None:
    """`origin/main` : chemin -> (date ISO, added/modified, sujet du commit).

    **Un** appel git pour tout le balayage. Une erreur Git rend None ; un
    historique lu sans mouvement rend un dictionnaire vide.

    Le **sujet** du commit est lu avec : c'est lui qui dit si le mouvement
    cite l'issue. Un commit de masse (une renommage de masse, une mise a jour
    transversale) touche beaucoup de chemins et ne prouve rien pour une
    issue donnee -- le sujet est ce qui distingue le commit de la
    livraison du commit de passage.
    """
    argv = ["git", "-C", str(depot or "."), "log", "origin/main",
            f"--since={jours}.days", "--diff-filter=AM",
            "--name-status", "--format=%x1e%cI %s"]
    try:
        proc = subprocess.run(argv, capture_output=True, text=True, check=False,
                              encoding="utf-8", errors="replace")
    except OSError:
        return None
    if proc.returncode != 0:
        return None
    out: dict[str, tuple[str, str, str]] = {}
    for record in (proc.stdout or "").split(_SEP):
        lignes = [l.strip() for l in record.splitlines() if l.strip()]
        if not lignes:
            continue
        entete = lignes[0]
        date, _, sujet = entete.partition(" ")
        for ligne in lignes[1:]:
            parts = ligne.split("\t")
            if len(parts) < 2:
                continue
            statut, chemin = parts[0][0], parts[-1].strip()
            if not chemin:
                continue
            # Le commit **le plus recent** gagne. L'historique est parcouru du
            # plus recent au plus ancien : ecraser garderait l'ANCIEN (defaut
            # mesure le 25/11, revue du coordinateur sur #28454). On compare
            # donc les dates -- et sur date egale, le premier lu (le plus
            # recent dans l'ordre de `git log`) reste.
            precedent = out.get(chemin)
            if precedent is None or (_comparable(instant(date))
                                      > _comparable(instant(precedent[0]))):
                out[chemin] = (date, statut, sujet)
    return out


def suspects(chemins: list[str], touches: dict[str, tuple[str, str, str]],
             cree_le: str | None, dernier_commentaire: str | None = None,
             numero: int | None = None) -> list[dict]:
    """Les chemins nommes dont le mouvement sur `main` est POSTERIEUR au
    dernier mouvement de l'issue, et **cite l'issue**.

    C'est la **suspicion**, et sa forme est stricte :

    - le depot a bouge sur le chemin cible *apres* que l'issue s'est tuee
      (une issue commenter apres le mouvement n'est pas suspecte :
      quelqu'un travaille encore) ;
    - et le commit qui l'a bouge **cite l'issue** (`#N` dans son sujet, comme
      une reference **entiere** : `#7` ne vaut pas pour `#70`).
      Sans cette seconde condition, un commit de masse suffirait a
      soupçonner n'importe quelle issue ancienne qui nomme un fichier
      touche par ce commit -- mesure du premier balayage : 21 soupcons
      sur 488 issues ouvertes, dont 9 portaient la meme date (un commit
      de masse du 15/11).

    `numero` absent : la seconde condition ne s'applique pas (le signal
    est alors le seul « le chemin a bouge »).
    """
    moments = [d for d in (instant(cree_le), instant(dernier_commentaire)) if d]
    if not moments:
        # Sans date de creation, le seuil est inconnu : fail-OPEN, aucune
        # suspicion (le signal ne s'applique pas, il ne devine pas).
        return []
    seuil = _comparable(max(moments))
    ancre = _ancre_re(numero) if numero else None
    out: list[dict] = []
    for chemin in chemins:
        info = touches.get(chemin)
        if not info:
            continue
        date, statut, sujet = info
        moment = instant(date)
        if moment is None or _comparable(moment) <= seuil:
            continue
        if ancre and not ancre.search(sujet or ""):
            continue
        out.append({"chemin": chemin, "date": date, "statut": statut,
                    "sujet": sujet})
    return out
