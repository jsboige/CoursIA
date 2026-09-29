#!/usr/bin/env python3
r"""Definition PARTAGEE des campagnes gelees par un veto user (#17040).

Deux organes lisent ce veto : ``merge_ready`` (skip de perimetre, etape 2)
et le gate d'entree ``check_adjoint_prevalidation.py`` (refus rc=3 d'un
dossier READY porte par une PR gelee). Une seule definition pour les deux,
jamais deux qui derivent -- le gate ne peut pas importer merge_ready
(merge_ready importe deja le gate), donc les deux importent ce module.
"""
from __future__ import annotations

import re

# Parapluies GELES par un veto user : une PR qui s'en reclame (titre ou body)
# sort du perimetre (b), quel que soit son dossier. Ni le gate d'entree ni B.0
# ne lisent un veto pose sur une issue : l'organe le lit ici, fail-closed.
# 13410 = campagne densite, gelee par le veto #17040 (mandat user 2026-09-20).
# #17021 y a ete mergee le 2026-09-22 sur un dossier READY et un B.0 vert :
# c'est l'incident qui fonde cette liste.
# 11601 = densite QC round 2 (« 1200->2000+ »), gelee au meme titre le
# 2026-09-23 (#11601 c.5786602361) : sa cible EST un seuil, ce que le point 4
# de #17040 interdit.
FROZEN_UMBRELLAS = {"13410": "17040", "11601": "17040"}

# Branches d'une campagne gelee dont les PRs ne citent PAS le parapluie : les
# relais g-XX de #13410 (`wt/vibe-g62-...`) n'ont #13410 ni dans le titre ni
# dans le body. 17 d'entre eux etaient ouverts et invisibles au filtre
# ci-dessus le 2026-09-23 (fermes au titre du veto, solde markdown net > 0).
FROZEN_BRANCH_PREFIXES = {"wt/vibe-": "13410"}

# Campagnes AUTORISEES apres le veto qui reutilisent les memes relais
# ``wt/vibe-*`` : le prefixe de branche ne dit plus a lui seul « campagne
# gelee ». 17636 = resorption des mesures d'artefact en prose markdown (GO
# ai-01 du 2026-09-27, recette #17636 c.5860054240) : elle RETIRE des chiffres,
# elle ne vise aucun seuil. Mesure fondatrice (2026-09-28) : #18252, #18283 et
# #18316 portaient `fix(prose,#17636)` en titre et aucun #13410, et restaient
# gelees par leur seule branche. La levee se lit sur le TITRE (le body peut
# citer n'importe quoi) et tombe des qu'un parapluie gele est cite.
BRANCH_PREFIX_RELEASES = {"wt/vibe-": ("17636",)}

# Redressements EXEMPTES du gel, sur le TITRE seul (insensible a la casse) :
# une PR qui REPREARE les degats d'une campagne gelee cite le parapluie comme
# n'importe quelle PR de la campagne -- le filtre par citation la gelerait
# aussi, et le retour a l'etat d'avant ne serait plus mergeable. Trois
# signatures suffisent (titre reels mesures) : le numero du veto lui-meme,
# le type conventionnel ``revert(`` et le mot ``redressement``.
# Sans effet sur les branches ``wt/vibe-*`` : ce sont des relais de campagne,
# jamais des redressements.
FROZEN_EXEMPT_TITLE_PATTERNS = tuple(
    re.compile(pattern, re.IGNORECASE)
    for pattern in (r"#17040(?!\d)", r"^revert\(", r"\bredressement\b")
)


def frozen_umbrella_exclusion(
    title: str | None, body: str | None, head_ref: str | None = None
) -> str | None:
    """Raison d'exclusion si la PR se reclame d'un parapluie gele, sinon None.

    Une reference ``#<numero>`` dans le titre ou le body suffit (fail-closed) ;
    un TITRE de redressement exempte (``FROZEN_EXEMPT_TITLE_PATTERNS``), pour
    que les PRs qui reparerent les degats restent mergeables malgre la
    citation. ``#134100`` ne vaut pas ``#13410``. Une branche d'une famille
    gelee (``FROZEN_BRANCH_PREFIXES``) suffit aussi, meme muette -- sauf si
    le TITRE nomme une campagne autorisee sur ces relais
    (``BRANCH_PREFIX_RELEASES``) et qu'aucun parapluie gele n'est cite.
    """
    text = " ".join((title or "", body or ""))
    cites_frozen = any(
        re.search(rf"#{umbrella}(?!\d)", text) for umbrella in FROZEN_UMBRELLAS
    )
    for prefix, umbrella in FROZEN_BRANCH_PREFIXES.items():
        if (head_ref or "").startswith(prefix):
            released = not cites_frozen and any(
                re.search(rf"#{campaign}(?!\d)", title or "")
                for campaign in BRANCH_PREFIX_RELEASES.get(prefix, ())
            )
            if not released:
                return f"frozen:#{umbrella}(veto #{FROZEN_UMBRELLAS[umbrella]},branch {prefix}*)"
    if title and any(p.search(title) for p in FROZEN_EXEMPT_TITLE_PATTERNS):
        return None
    for umbrella, veto in FROZEN_UMBRELLAS.items():
        if re.search(rf"#{umbrella}(?!\d)", text):
            return f"frozen:#{umbrella}(veto #{veto})"
    return None
