"""Les PRs ouvertes, lues **par le cache partage** (#22630, residuel).

Le tirage (`tapis_rapide.py`) lit deja les PRs ouvertes : son cache de lecture
`lecture-<N>j.json` est partage par machine, verrouille, et il les contient.
La qualification (`tapis_prise_en_charge.py`) relisait la meme liste depuis le
reseau a chaque invocation -- le credit gh etait paye deux fois pour le meme
contenu, et la qualification, qui est la seconde passe, echouait quand le seau
etait court.

Mesure du 28/11/2026, siege `myia-ai-01`, 09:52Z : le tirage de 10:14Z etait
passe (provenance `qualifie`, 527 issues, 15,7 s / 48 s) ; la qualification de
six grains, lancee dans la minute, a echoue sur `rate limit exceeded` a l'appel
`gh api repos/jsboige/CoursIA/pulls?state=open&per_page=100&page=1` -- la page
1 d'une pagination que le tirage venait de payer 20 secondes plus tot.

Ce module decide **ou** la liste est lue, pas **ce qu'elle contient** :
`gh_bulk.lire_prs_ouvertes` reste la seule source de verite du contenu.

Trois chemins, du moins cher au plus cher :

1. le cache de lecture du tapis, s'il est frais : les PRs y sont deja ;
2. le cache PRs dedie (`prs-ouvertes.json`), ecrit sous le meme verrou partage ;
3. le reseau, une fois -- puis le cache PRs est ecrit.

Aucun chemin n'est bloquant : un cache absent, perime ou illisible rebascule
sur le reseau, comme le protocole de `coordination.gh_cache`.

Le **tirage** garde sa lecture fraiche et la **publie** (`publier_prs`) : il
n'est jamais servi une liste plus ancienne que celle qu'il lit lui-meme. C'est
la qualification, qui vient apres et sur le meme contenu, qui evite le
doublon.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from datetime import UTC, datetime
from pathlib import Path

from coordination import gh_bulk, gh_cache

try:
    from .gh_cache_fichier import ecrire, frais
except ImportError:  # pragma: no cover - import direct, hors paquet
    from gh_cache_fichier import ecrire, frais

_ISO = "%Y-%m-%dT%H:%M:%SZ"
#: Le TTL par defaut, aligne sur celui du cache de lecture du tapis
#: (`gh_bulk.lire_tout`) : une qualification lancee juste apres un tirage lit
#: le cache que le tirage vient d'ecrire.
CACHE_S = 300


@dataclass
class LecturePrs:
    """Les PRs ouvertes, et l'instant de leur lecture."""

    prs: list[dict] = field(default_factory=list)
    lu_a: str = ""


def _depuis_cache(brut: dict) -> LecturePrs:
    """Le cache deserialise ; la forme invalide leve (repli sur le reseau)."""
    return LecturePrs(prs=list(brut["prs"]), lu_a=str(brut.get("lu_a") or ""))


def _reseau(run, depot: str, echeance: float | None) -> LecturePrs:
    """La lecture reseau -- le contenu vient de `gh_bulk`, jamais d'ici."""
    return LecturePrs(
        prs=gh_bulk.lire_prs_ouvertes(run, depot, echeance),
        lu_a=datetime.now(UTC).strftime(_ISO),
    )


def publier_prs(prs: list[dict], dossier_cache: Path | None = None) -> None:
    """Publie la liste des PRs lue, pour que la qualification la relise.

    Le tirage **ecrit** ce qu'il a paye ; la qualification **relit** ce
    cache au lieu de payer la meme pagination une seconde fois.

    Le tirage garde sa lecture fraiche : il n'est pas.question de lui servir
    une liste plus ancienne que ce qu'il lit lui-meme. C'est la qualification,
    qui vient apres et sur le meme contenu, qui evite le doublon.
    """
    dossier = dossier_cache or gh_bulk.dossier_cache_defaut()
    ecrire(dossier / "prs-ouvertes.json",
           LecturePrs(prs=list(prs), lu_a=datetime.now(UTC).strftime(_ISO)))


def lire_prs_partagees(run=gh_bulk.run_defaut, depot: str = gh_bulk.DEPOT_GH,
                       cache_s: int = CACHE_S, dossier_cache: Path | None = None,
                       jours: int = 45, echeance: float | None = None) -> list[dict]:
    """Les PRs ouvertes, lues une seule fois par machine et par instant.

    Le cache de lecture du tapis est lu **en premier** : il porte deja les
    PRs, et le tirage vient de l'ecrire -- une qualification lancee dans la
    minute ne paie donc aucun appel gh.

    Ensuite le cache PRs dedie, sous le meme verrou partage ; et seulement en
    dernier resort le reseau, dont le resultat est ecrit dans ce cache.
    """
    dossier = dossier_cache or gh_bulk.dossier_cache_defaut()

    brut = frais(dossier / f"lecture-{jours}j.json", cache_s)
    if brut is not None and isinstance(brut.get("prs"), list):
        return list(brut["prs"])

    chemin = dossier / "prs-ouvertes.json"
    return gh_cache.lire_unique(
        chemin, cache_s,
        lambda: _reseau(run, depot, echeance),
        _depuis_cache,
    ).prs
