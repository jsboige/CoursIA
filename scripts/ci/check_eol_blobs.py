"""Garde les PRs contre les blobs CRLF ou mixtes sous attribut eol=lf (#19374).

Un blob CRLF ou mixte sous un attribut ``eol=lf`` fait paraitre le fichier
modifie apres chaque checkout, sur toutes les machines : git renormalise
a la lecture mais ne reecrit jamais le blob. Tout organe qui exige un
arbre propre s'arrete alors : ``merge_ready`` (``git status --porcelain``
dans ``sync_repo``) refuse son tour, ``check_clean_cycle_exit.py`` voit
sale le clone principal.

Source de la classe : #19287 a merge 7 fichiers EPITA en promettant
l'identite octet a octet avec l'amont, dont 2 etaient CRLF chez l'amont
et sont sortis en blob mixte (en-tete LF, corps CRLF). ``merge_ready``
a refuse tous ses tours de 18:16Z a 21:10Z. Le correctif ponctuel est
#19373 (``git add --renormalize``). Cette garde empeche la prochaine
de la classe.

Detection : ``git diff --name-only --diff-filter=AM origin/main...HEAD``
puis ``git ls-files --eol -- <path>`` par chemin. Un fichier AM est
rouge si ``i/crlf`` ou ``i/mixed`` ET ``eol=lf``. Un blob CRLF voulu
(fichier ``.bat``, fixture de test) se declare par un attribut
``eol=crlf`` ou ``-text`` dans ``.gitattributes``, jamais par une
exemption dans la garde.

Sortie de rouge : nom de fichier + commande de reparation
``git add --renormalize <fichier>``.

Architecture testable : la matrice pure vit dans `_classify(i_attr, attr)`
et le parsing de la ligne `git ls-files --eol` dans `_parse_ls_files_line`.
Les tests `scripts/tests/test_check_eol_blobs.py` couvrent les 7 cas
de la matrice (cf. revue 5421649286 du coordinateur).

Critere d'acceptance #19374 :
- rougit sur le blob mixte de #19287 (controle positif)
- vert sur main apres #19373 et sur une PR ordinaire
- mesure main : ``git ls-files --eol | awk '($1=="i/crlf"||$1=="i/mixed") && /eol=lf/'``
  rend 0 ligne
"""

from __future__ import annotations

import re
import subprocess
import sys


# Indices `i_eol` qui signalent un blob non-stable (git renormalisera le
# worktree sans reecrire le blob -> "modifie apres chaque checkout").
BAD_INDEX = ("crlf", "mixed")

# Attributs `.gitattributes` qui declarent le fichier comme "text" sans
# proteger le blob CRLF. Un fichier declare `-text` est binaire et n'est
# PAS renormalise -- la garde ne le rougit pas. Un attribut vide
# (aucune entree `.gitattributes`) laisse le defaut `text`, qui
# renormalise egalement ; mais sans declaration explicite, l'auteur n'a
# pas CLAIM le format CRLF, le cas est "non declare" et reste hors du
# filet (cf `_classify` et `test_decision_*`).
LF_ATTRS = ("text", "lf")

# Format de la sortie `git ls-files --eol` :
#   <i_eol> <w_eol> <attr> eol=<X> \t<path>
# `attr` est vide si le fichier n'a aucune entree `.gitattributes` (vu
# comme `attr/ ` avec un espace final). `eol=` est absent si aucun
# attribut EOL n'est pose (uniquement l'attribut text). On capture
# l'attribut brut ; la decision le `.strip()` avant test d'appartenance.
EOL_LINE_RE = re.compile(
    r"(?P<i_eol>i/(?P<i_attr>\w+))\s+"
    r"w/(?P<w_attr>\w+)\s+"
    r"attr/(?P<attr>[^\t]*?)\s+"
    r"eol=(?P<eol_attr>\S+)"
    r"\s+(?P<path>.+)"
)


def _run(cmd: list[str], cwd: str | None = None) -> subprocess.CompletedProcess:
    return subprocess.run(
        cmd, capture_output=True, text=True, encoding="utf-8",
        errors="replace", cwd=cwd,
    )


def _classify(i_attr: str, attr: str) -> bool:
    """Matrice de decision (pure, testable hors subprocess).

    Le strip() de `attr` couvre l'attribut vide (sortie `git ls-files
    --eol` avec `attr/ ` espace final). La garde rougit UNIQUEMENT les
    cas declares `text` ou `eol=lf` -- un blob CRLF sans declaration
    `.gitattributes` (attribut vide) reste hors du filet, l'auteur n'a
    pas CLAIM le format et la renormalisation depend de la config
    locale (core.autocrlf), pas d'un contrat commite."""
    return i_attr in BAD_INDEX and attr.strip() in LF_ATTRS


def _parse_ls_files_line(line: str) -> tuple[str, str, str] | None:
    """Parse une ligne `git ls-files --eol` -> (i_attr, attr, path).
    None si la ligne n'est pas au format attendu."""
    m = EOL_LINE_RE.match(line)
    if m is None:
        return None
    return m.group("i_attr"), m.group("attr"), m.group("path")


def main() -> int:
    diff_proc = _run(
        ["git", "diff", "--name-only", "--diff-filter=AM",
         "origin/main...HEAD"],
    )
    if diff_proc.returncode != 0:
        print(
            "eol-guard: git diff a echoue : "
            f"{diff_proc.stderr.strip()}",
            file=sys.stderr,
        )
        return 2

    changed = [f for f in diff_proc.stdout.splitlines() if f.strip()]
    if not changed:
        return 0

    eol_proc = _run(["git", "ls-files", "--eol", "--", *changed])
    if eol_proc.returncode != 0:
        print(
            "eol-guard: git ls-files --eol a echoue : "
            f"{eol_proc.stderr.strip()}",
            file=sys.stderr,
        )
        return 2

    bad: list[tuple[str, str]] = []
    for line in eol_proc.stdout.splitlines():
        if not line.strip():
            continue
        parsed = _parse_ls_files_line(line)
        if parsed is None:
            continue
        i_attr, attr, path = parsed
        if _classify(i_attr, attr):
            bad.append((i_attr, path))

    if not bad:
        return 0

    print(
        f"eol-guard: {len(bad)} fichier(s) avec blob CRLF ou mixte sous "
        "eol=lf -- le clone de chaque lane paraitra modifie apres "
        "chaque checkout :",
        file=sys.stderr,
    )
    for i_attr, path in bad:
        print(f"  i/{i_attr}  {path}", file=sys.stderr)
        print(
            f"    -> git add --renormalize {path}",
            file=sys.stderr,
        )
    print(
        "\nUn blob CRLF voulu (fichier .bat, fixture de test) se declare\n"
        "par un attribut eol=crlf ou -text dans .gitattributes, jamais\n"
        "par une exemption dans cette garde.",
        file=sys.stderr,
    )
    return 1


if __name__ == "__main__":
    sys.exit(main())