#!/usr/bin/env python3
"""La LECTURE : son conteneur, son echec, et la mise a plat d'une issue.

Trois choses qui etaient dans `coordination.gh_bulk`, extraites le 19/11 :
`gh_bulk` etait exactement a son plafond de lignes, et l'honnetete du
`comments_total` (un total **INCONNU** ne vaut pas 0) n'y tient plus.

- `LectureIncomplete` : l'echec qui interdit de servir une liste a moitie ;
- `Lecture` : le conteneur des trois lectures, et ce qu'elles ont coute ;
- `issue()` : la mise a plat d'une issue GraphQL aux champs de `issues.json`.

Le module ne depend de rien : `gh_bulk` les reintroduit, donc tous les
consommateurs (`gh_bulk.Lecture`, `gh_bulk.LectureIncomplete`) continuent de
fonctionner, et le tiroir de la lecture garde une seule adresse.
"""
from __future__ import annotations

from dataclasses import dataclass, field


class LectureIncomplete(RuntimeError):
    """Une lecture n'a pas abouti : rien ne doit etre servi."""

    def __init__(self, lecture: str, page: object, cause: str) -> None:
        super().__init__(f"lecture {lecture} incomplete (page {page}) : {cause}")
        self.lecture, self.page, self.cause = lecture, page, cause


@dataclass
class Lecture:
    """Les trois lectures d'un tirage, et ce qu'elles ont coute."""

    issues: list[dict]
    prs: list[dict]
    citations: dict[int, list[dict]] = field(default_factory=dict)
    lu_a: str = ""
    appels: int = 0
    secondes: float = 0.0
    depuis_cache: bool = False
    fetch_note: str | None = None  # fetch d'origin/main tente et echoue (sinon None)

    @property
    def origin_main_le(self) -> str | None:
        """Dernier commit de la fenetre : chaque commit de squash cite sa PR."""
        return max((c["date"] for cs in self.citations.values() for c in cs), default=None)


def issue(node: dict) -> dict:
    """Une issue GraphQL a plat, aux champs de `issues.json`.

    `comments_total` reste **INCONNU** quand la lecture ne l'a pas donne : un
    absent ne vaut pas 0 -- il vaut « la taille de la fenetre est inconnue »,
    donc la fenetre n'est pas prouvee complete (fail-CLOSED,
    `coordination.tapis_fenetre`).
    """
    com = node.get("comments") or {}
    return {"number": node["number"], "title": node.get("title") or "",
            "body": node.get("body") or "", "created_at": node.get("createdAt") or "",
            "updated_at": node.get("updatedAt") or "",
            "labels": [lab["name"] for lab in (node.get("labels") or {}).get("nodes") or []],
            "comments_total": com.get("totalCount"),
            "comments": [{"created_at": c.get("createdAt") or "",
                          "author": (c.get("author") or {}).get("login") or "",
                          "body": (c.get("body") or "")[:600]} for c in com.get("nodes") or []]}
