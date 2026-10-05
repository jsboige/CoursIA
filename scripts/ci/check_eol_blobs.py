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

Critere d'acceptance #19374 :
- rougit sur le blob mixte de #19287 (controle positif)
- vert sur main apres #19373 et sur une PR ordinaire
- mesure main : ``git ls-files --eol | awk '($1=="i/crlf"||$1=="i/mixed") && /eol=lf/'``
  rend 0 ligne
"""

from __future__ import annotations

import subprocess
import sys


def _run(cmd: list[str], cwd: str | None = None) -> subprocess.CompletedProcess:
    return subprocess.run(
        cmd, capture_output=True, text=True, encoding="utf-8",
        errors="replace", cwd=cwd,
    )


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
        # Format : "<i_eol> <w_eol> <attr> eol=<X> \t<path>"
        parts = line.split(None, 4)
        if len(parts) < 5:
            continue
        i_eol, _w_eol, _attr, eol_attr, path = parts
        if (i_eol in ("i/crlf", "i/mixed")) and eol_attr.startswith("eol=") \
                and eol_attr != "eol=crlf":
            bad.append((i_eol, path))

    if not bad:
        return 0

    print(
        f"eol-guard: {len(bad)} fichier(s) avec blob CRLF ou mixte sous "
        "eol=lf -- le clone de chaque lane paraitra modifie apres "
        "chaque checkout :",
        file=sys.stderr,
    )
    for i_eol, path in bad:
        print(f"  {i_eol}  {path}", file=sys.stderr)
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
