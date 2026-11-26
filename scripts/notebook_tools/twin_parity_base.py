#!/usr/bin/env python3
"""Base du squash et orphelin A VENIR (#28122) -- module frere de check_twin_parity.

`check_twin_parity.py` est epingle (plafond de lignes) : la decision de no-op
d'`--update` vit ici, dans un module frere, comme la scission T7 de #26364 l'a
fait pour les modes d'ecriture (cf `twin_parity_attest.py`). L'organe est
injecte en parametre (`organ`) : ce module ne l'importe pas, donc aucun cycle.

Deux notions distinctes, souvent confondues :

- **orphelin DEJA constate** (#11919) : le blob enregistre n'est plus joignable
  depuis HEAD -- le squash a re-hashe, l'ancien blob a disparu du depot. Le
  rebaseline doit le corriger ;
- **orphelin A VENIR** (#28122) : le blob enregistre est encore joignable
  depuis HEAD (c'est un commit de la BRANCHE qui le porte) mais il n'est pas
  dans `main`, la destination du squash. Apres la fusion, l'arbre portera le
  blob courant : l'attestation decrirait un blob que `main` n'a jamais eu.

Le no-op d'`--update` compare les `content_*_sha` (metadata-immunes) : un
tampon de metadata seul ne justifie pas de re-attester (design-gate #9399
critere 2, cas Sudoku-08/14 BDD). Mais cette comparaison voit les DEUX cas
ci-dessus de la meme facon -- la discrimination se fait sur les git blob SHA,
et c'est elle qui doit interroger la BASE du squash, pas la tete de la branche.
"""
from __future__ import annotations


def est_documentation_registre(nom: str) -> bool:
    """Une entree `_`-prefixee du registre est de la DOCUMENTATION.

    Regle du lecteur canonique (`check_twin_parity.load_registry`) : dans
    `twin_pairs.d/`, chaque `*.yaml` ne commencant pas par `_` est le
    descripteur d'UNE paire ; les `_`-prefixes (`_schema.yaml`) sont ignores.

    La regle vit ici parce que `check_twin_parity.py` est epingle (plafond de
    lignes) : les modules freres partagent la decision sans la dupliquer.
    """
    return nom.startswith("_")


def squash_base_ref(organ, repo_root) -> str:
    """Base du squash : `origin/main` si elle se resout, sinon `HEAD`.

    Repli sur `HEAD` quand `origin/main` n'est pas resolvable (depot de test,
    clone sans remote) : le comportement d'avant est conserve.
    """
    r = organ._run_git(
        ["git", "rev-parse", "--verify", "--quiet", "origin/main^{commit}"],
        cwd=str(repo_root),
    )
    return "origin/main" if r.returncode == 0 else "HEAD"


def orphan_a_venir(organ, repo_root, latest: dict, cur_py, cur_cs,
                   cur_ru=None) -> bool:
    """Vrai ssi l'attestation decrit un blob que la base du squash ne porte pas.

    `latest` est la derniere attestation de la paire (`_latest_audit`), et
    `cur_py` / `cur_cs` les git blob SHA courants. Un blob enregistre qui
    differe du blob courant ET qui n'est pas joignable depuis la base sera
    ecrase par le squash : l'attestation doit etre rafraichie.

    `cur_ru` (facultatif) est le git blob SHA du cote rust optionnel
    (#27098). Il n'est interroge que si la paire declare ce cote : une paire
    binaire passe `None` et ne consulte jamais la cle `rust_sha`.

    Le no-op metadata-only reste preserve quand le blob enregistre est DEJA sur
    la base (Sudoku-08/14 BDD) : c'est le meme contenu, et `main` porte deja
    ce blob -- il n'y a rien a re-attester.
    """
    base = squash_base_ref(organ, repo_root)
    cotes = [("python_sha", cur_py), ("csharp_sha", cur_cs)]
    if cur_ru is not None:
        cotes.append(("rust_sha", cur_ru))
    for cle, courant in cotes:
        rec = latest.get(cle)
        if rec is None or rec == courant:
            continue
        if not organ._blob_ancestor_in(repo_root, rec, base):
            return True
    return False
