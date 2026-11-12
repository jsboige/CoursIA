"""Inventaire factuel de la soumission Lean `yang-mills-group/OpenAI-YM-20261028`.

Ce module ne compile rien et n'exige pas Lean : il **rejoue** les affirmations
auto-declarees par la soumission (integrite des sources, cloisonnement des imports
du referentiel, absence de `sorry`/`axiom` hors placeholder, controles negatifs)
a partir d'un clone local, et rend un rapport falsifiable : un controle qui
echoue est un echec, pas une note.

Usage :
    python scripts/ym_openai_20261028/inventory.py --repo D:/tmp/ym-src
    python scripts/ym_openai_20261028/inventory.py --repo D:/tmp/ym-src --json

Code de sortie : 0 si tous les controles passent, 1 sinon, 2 si le clone est
illisible (obstacle d'environnement, jamais un resultat de recherche).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path

# Racine du referentiel : le statement du defi, reference non implantee.
REFERENCE_MODULE = "Challenge"
# Module portant la preuve de la soumission.
SOLUTION_MODULE = "Solution"
# Modules de la specification *publique* : ils definissent le vocabulaire du
# defi (groupes de jauge, Wilson, Wightman) sans contenir de travail
# d'implementation. Le referentiel doit s'y limiter.
SPECIFICATION_MODULES = ("Challenge", "ChallengeSpec", "PublicWilson", "PublicTheory")

# Motifs releves dans les sources Lean. Les occurrences sont rapportees avec
# leur ligne ; seules les declarations `axiom`/`opaque` sont bloquantes.
PATTERNS: dict[str, re.Pattern[str]] = {
    "sorry": re.compile(r"(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])"),
    "axiom": re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?axiom\s"),
    "opaque": re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?opaque\s"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "classical_choice": re.compile(r"\bClassical\.choice\b"),
    "partial_def": re.compile(
        r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*partial\s+def\s"
    ),
    "unsafe_decl": re.compile(
        r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*unsafe\s"
    ),
}

IMPORT_LINE = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)", re.MULTILINE)


@dataclass
class Check:
    """Un controle binaire, avec la preuve qui le fonde."""

    key: str
    titre: str
    statut: str
    preuve: str
    details: dict = field(default_factory=dict)


def _sha256_bytes(donnees: bytes) -> str:
    return hashlib.sha256(donnees).hexdigest()


def _sha256_fichier(chemin: Path) -> str:
    empreinte = hashlib.sha256()
    with chemin.open("rb") as handle:
        for bloc in iter(lambda: handle.read(1 << 20), b""):
            empreinte.update(bloc)
    return empreinte.hexdigest()


def _fichiers_lean(racine: Path) -> list[Path]:
    return sorted(p for p in racine.rglob("*.lean") if p.is_file())


def _index_modules(racine: Path, fichiers: list[Path]) -> dict[str, Path]:
    """Table `nom de module Lean` -> fichier, deduite des chemins du clone.

    `Challenge.lean` -> `Challenge` ; `YM/Ac/Foo.lean` -> `YM.Ac.Foo`.
    """
    index: dict[str, Path] = {}
    for fichier in fichiers:
        relatif = fichier.relative_to(racine).as_posix()
        if relatif.endswith(".lean"):
            sans_ext = relatif[: -len(".lean")]
        else:
            continue
        index[sans_ext.replace("/", ".")] = fichier
    return index


def _closure_imports(
    racine: Path, index: dict[str, Path], module: str
) -> tuple[set[str], set[str]]:
    """Cloisonnement transitif des imports : (modules projet, modules externes)."""
    vus: set[str] = set()
    projet: set[str] = set()
    externes: set[str] = set()
    pile = [module]
    while pile:
        courant = pile.pop()
        if courant in vus:
            continue
        vus.add(courant)
        fichier = index.get(courant)
        if fichier is None:
            externes.add(courant)
            continue
        projet.add(courant)
        texte = fichier.read_text(encoding="utf-8", errors="replace")
        for importee in IMPORT_LINE.findall(texte):
            pile.append(importee)
    return projet, externes


def _occurrences(racine: Path, fichiers: list[Path]) -> dict[str, list[str]]:
    """Occurrences par motif, au format `chemin:ligne` (relatives a la racine)."""
    trouves: dict[str, list[str]] = {nom: [] for nom in PATTERNS}
    for fichier in fichiers:
        texte = fichier.read_text(encoding="utf-8", errors="replace")
        for numero, ligne in enumerate(texte.splitlines(), start=1):
            for nom, motif in PATTERNS.items():
                if motif.search(ligne):
                    trouves[nom].append(f"{fichier.relative_to(racine).as_posix()}:{numero}")
    return trouves


def _hors_reference(occurrences: dict[str, list[str]]) -> dict[str, list[str]]:
    """Occurrences hors du fichier de reference (qui porte le `sorry` du defi)."""
    return {
        nom: [o for o in valeurs if not o.startswith("Challenge.lean:")]
        for nom, valeurs in occurrences.items()
    }


def _empreintes_blobs(racine: Path, chemins: list[str]) -> dict[str, str | None]:
    """SHA-256 des blobs `HEAD:<chemin>`, lus par `git cat-file --batch`.

    Indispensable sur un poste Windows : `core.autocrlf = true` convertit les
    fins de ligne au checkout, donc le fichier **de travail** ne porte plus
    l'empreinte du blob committe. C'est la normalisation du checkout qui est
    en cause, pas la soumission.
    """
    if not (racine / ".git").exists():
        return {}
    requete = "\n".join(f"HEAD:{chemin}" for chemin in chemins)
    try:
        processus = subprocess.run(
            ["git", "-C", str(racine), "cat-file", "--batch"],
            input=requete.encode("utf-8"),
            capture_output=True,
            check=True,
        )
    except (OSError, subprocess.CalledProcessError):
        return {}
    donnees = processus.stdout
    resultat: dict[str, str | None] = {}
    position = 0
    for chemin in chemins:
        fin = donnees.find(b"\n", position)
        if fin < 0:
            resultat[chemin] = None
            break
        entete = donnees[position:fin].decode("utf-8", errors="replace").split()
        position = fin + 1
        if len(entete) < 3 or entete[1] != "blob":
            resultat[chemin] = None
            continue
        taille = int(entete[2])
        contenu = donnees[position : position + taille]
        position += taille + 1
        resultat[chemin] = _sha256_bytes(contenu)
    return resultat


def _verifie_manifeste(racine: Path) -> dict:
    """Recalcule le SHA-256 de chaque fichier annonce par `SOURCES.sha256`."""
    manifeste = racine / "SOURCES.sha256"
    if not manifeste.is_file():
        return {
            "present": False,
            "verifies": 0,
            "manquants": [],
            "differents": [],
            "normalises_par_checkout": [],
            "hors_manifeste": [],
        }
    attendus: dict[str, str] = {}
    for ligne in manifeste.read_text(encoding="utf-8", errors="replace").splitlines():
        ligne = ligne.strip()
        if not ligne:
            continue
        empreinte, _, chemin = ligne.partition("  ")
        if not chemin:
            empreinte, _, chemin = ligne.partition(" ")
        attendus[chemin.strip()] = empreinte.strip()

    blobs = _empreintes_blobs(racine, sorted(attendus))
    manquants: list[str] = []
    differents: list[str] = []
    normalises: list[str] = []
    for chemin, empreinte in sorted(attendus.items()):
        cible = racine / chemin
        if not cible.is_file():
            manquants.append(chemin)
            continue
        empreinte_blob = blobs.get(chemin)
        if empreinte_blob is None:
            # Pas de blob lisible : on compare le fichier de travail.
            if _sha256_fichier(cible) != empreinte:
                differents.append(chemin)
            continue
        if empreinte_blob == empreinte:
            if _sha256_fichier(cible) != empreinte:
                normalises.append(chemin)
            continue
        differents.append(chemin)

    declares = set(attendus)
    presents = {
        p.relative_to(racine).as_posix()
        for p in racine.rglob("*")
        if p.is_file() and ".git" not in p.relative_to(racine).parts
    }
    hors = sorted(presents - declares - {"SOURCES.sha256"})
    return {
        "present": True,
        "verifies": len(attendus) - len(manquants) - len(differents),
        "manquants": sorted(manquants),
        "differents": sorted(differents),
        "normalises_par_checkout": normalises,
        "hors_manifeste": hors,
    }


def _inventaire_volume(racine: Path, fichiers: list[Path]) -> dict:
    """Volume par repertoire, et part des repertoires repetitifs `ANNULUS_*`."""
    par_repertoire: Counter[str] = Counter()
    lignes: Counter[str] = Counter()
    lignes_annulus = 0
    for fichier in fichiers:
        relatif = fichier.relative_to(racine).as_posix()
        premier = relatif.split("/", 1)[0] if "/" in relatif else "(racine)"
        par_repertoire[premier] += 1
        nombre = fichier.read_text(encoding="utf-8", errors="replace").count("\n")
        lignes[premier] += nombre
        if "/ANNULUS" in "/" + relatif:
            lignes_annulus += nombre
    total = sum(lignes.values()) or 1
    return {
        "fichiers_lean": len(fichiers),
        "lignes_lean": total,
        "fichiers_par_repertoire": dict(sorted(par_repertoire.items())),
        "lignes_par_repertoire": dict(sorted(lignes.items())),
        "lignes_annulus": lignes_annulus,
        "part_annulus_pct": round(100.0 * lignes_annulus / total, 2),
    }


def _extrait_enonce(racine: Path) -> str:
    """Extrait l'enonce `JointExistence` de `ChallengeSpec.lean`."""
    chemin = racine / "ChallengeSpec.lean"
    if not chemin.is_file():
        return ""
    texte = chemin.read_text(encoding="utf-8", errors="replace")
    position = texte.find("def JointExistence")
    if position < 0:
        return ""
    fin = texte.find("\nend ", position)
    return texte[position : fin if fin > 0 else len(texte)].strip()


def _versions(racine: Path) -> dict:
    """Version de Lean, pin de Mathlib, et pins du manifeste Lake."""
    versions: dict[str, str] = {}
    outil = racine / "lean-toolchain"
    if outil.is_file():
        versions["lean_toolchain"] = outil.read_text(encoding="utf-8", errors="replace").strip()
    lakefile = racine / "lakefile.toml"
    if lakefile.is_file():
        texte = lakefile.read_text(encoding="utf-8", errors="replace")
        for nom in ("mathlib", "batteries", "Qq", "aesop", "proofwidgets"):
            correspondance = re.search(
                rf'name\s*=\s*"{nom}"(.{{0,400}}?)rev\s*=\s*"([0-9a-f]{{40}})"', texte, re.DOTALL
            )
            if correspondance:
                versions[f"lakefile_{nom}"] = correspondance.group(2)
    manifeste = racine / "lake-manifest.json"
    if manifeste.is_file():
        donnees = json.loads(manifeste.read_text(encoding="utf-8", errors="replace"))
        for paquet in donnees.get("packages", []):
            if paquet.get("name") == "mathlib":
                versions["manifest_mathlib_rev"] = str(paquet.get("rev", ""))
    return versions


def _controles_negatifs(racine: Path) -> dict:
    """Relit le journal des controles negatifs de la soumission."""
    chemin = racine / "verification" / "negative-controls.log"
    if not chemin.is_file():
        return {"present": False, "lignes": []}
    lignes = [
        l.strip()
        for l in chemin.read_text(encoding="utf-8", errors="replace").splitlines()
        if l.strip()
    ]
    return {
        "present": True,
        "lignes": lignes,
        "rejets_attendus": sum(1 for l in lignes if l.startswith("REJECTED_AS_EXPECTED")),
        "succes": any(l.startswith("NEGATIVE_CONTROLS_PASS") for l in lignes),
    }


def _headlines(racine: Path) -> dict:
    """Recense les resultats « headlines » annonces par la soumission."""
    chemin = racine / "verification" / "joint-headlines.txt"
    if not chemin.is_file():
        return {"present": False, "noms": [], "nombre": 0}
    lignes = [
        l.strip()
        for l in chemin.read_text(encoding="utf-8", errors="replace").splitlines()
        if l.strip()
    ]
    return {"present": True, "noms": lignes, "nombre": len(lignes)}


def _construit_controles(racine: Path) -> tuple[list[Check], dict]:
    """Execute tous les controles sur le clone et rend la liste et le contexte."""
    fichiers = _fichiers_lean(racine)
    index = _index_modules(racine, fichiers)
    occurrences = _occurrences(racine, fichiers)
    hors_reference = _hors_reference(occurrences)
    manifest = _verifie_manifeste(racine)
    projet_ref, externes_ref = _closure_imports(racine, index, REFERENCE_MODULE)
    implementation_ref = sorted(projet_ref - set(SPECIFICATION_MODULES))
    projet_sol, externes_sol = _closure_imports(racine, index, SOLUTION_MODULE)
    volume = _inventaire_volume(racine, fichiers)
    volume["lignes_specification"] = sum(
        (racine / f"{nom}.lean")
        .read_text(encoding="utf-8", errors="replace")
        .count("\n")
        for nom in SPECIFICATION_MODULES
        if (racine / f"{nom}.lean").is_file()
    )
    versions = _versions(racine)
    controles_neg = _controles_negatifs(racine)
    headlines = _headlines(racine)

    total_manifeste = (
        manifest.get("verifies", 0)
        + len(manifest.get("manquants", []))
        + len(manifest.get("differents", []))
    )
    controles_liste = [
        Check(
            "integrite_manifeste",
            "Integrite des sources (SOURCES.sha256 recalcule sur les blobs committe)",
            "PASS" if manifest["present"] and not manifest["manquants"] and not manifest["differents"] else "FAIL",
            f"{manifest.get('verifies', 0)} fichiers verifies sur {total_manifeste} annonces",
            {
                "manquants": manifest.get("manquants", [])[:20],
                "differents": manifest.get("differents", [])[:20],
                "normalises_par_checkout": len(manifest.get("normalises_par_checkout", [])),
            },
        ),
        Check(
            "cloisonnement_reference",
            "Le referentiel (Challenge.lean) n'atteint aucun module d'implementation",
            "PASS" if not implementation_ref else "FAIL",
            f"closure = {len(projet_ref)} module(s) de specification "
            f"({', '.join(sorted(projet_ref))}) + {len(externes_ref)} externe(s) ; "
            f"{len(implementation_ref)} module(s) d'implementation atteint(s)",
            {
                "modules_projet": sorted(projet_ref)[:20],
                "modules_externes": sorted(externes_ref)[:20],
                "modules_implementation": implementation_ref[:20],
            },
        ),
        Check(
            "travail_dans_la_solution",
            "La solution importe bien des modules d'implementation",
            "PASS" if projet_sol else "FAIL",
            f"{len(projet_sol)} module(s) projet et {len(externes_sol)} module(s) externe(s) dans la closure",
            {"modules_projet": sorted(projet_sol)[:20]},
        ),
        Check(
            "placeholder_unique",
            "Le seul `sorry` du depot est celui du referentiel",
            "PASS" if not hors_reference["sorry"] else "FAIL",
            f"{len(occurrences['sorry'])} occurrence(s) au total, {len(hors_reference['sorry'])} hors referentiel",
            {"hors_reference": hors_reference["sorry"][:20]},
        ),
        Check(
            "admissions_declarees",
            "Aucune declaration `axiom`/`opaque` hors referentiel",
            "PASS" if not hors_reference["axiom"] and not hors_reference["opaque"] else "FAIL",
            f"axiom={len(hors_reference['axiom'])}, opaque={len(hors_reference['opaque'])}",
            {
                "axiom": hors_reference["axiom"][:20],
                "opaque": hors_reference["opaque"][:20],
            },
        ),
        Check(
            "reduction_naturelle",
            "Aucun `native_decide` hors referentiel (reduction sans preuve)",
            "PASS" if not hors_reference["native_decide"] else "FAIL",
            f"{len(hors_reference['native_decide'])} occurrence(s)",
            {"occurrences": hors_reference["native_decide"][:20]},
        ),
        Check(
            "controles_negatifs",
            "Le journal des controles negatifs est present et concluant",
            "PASS" if controles_neg["present"] and controles_neg["succes"] else "FAIL",
            f"{controles_neg.get('rejets_attendus', 0)} rejet(s) attendu(s), succes={controles_neg.get('succes')}",
            {"lignes": controles_neg.get("lignes", [])},
        ),
        Check(
            "headlines",
            "Les resultats headlines sont enumeres",
            "PASS" if headlines["present"] else "FAIL",
            f"{headlines.get('nombre', 0)} headline(s) annonce(s)",
            {"noms": headlines.get("noms", [])[:20]},
        ),
        Check(
            "versions",
            "Les versions (Lean, Mathlib) sont epinglees",
            "PASS" if versions.get("lean_toolchain") and versions.get("lakefile_mathlib") else "FAIL",
            f"lean={versions.get('lean_toolchain', '?')} mathlib={versions.get('lakefile_mathlib', '?')}",
            versions,
        ),
    ]

    contexte = {
        "racine": str(racine),
        "volume": volume,
        "versions": versions,
        "enonce_joint_existence": _extrait_enonce(racine),
        "occurrences_hors_reference": {
            nom: valeurs[:50] for nom, valeurs in hors_reference.items() if valeurs
        },
        "totaux_occurrences": {nom: len(valeurs) for nom, valeurs in occurrences.items()},
        "manifeste": {
            "present": manifest["present"],
            "verifies": manifest.get("verifies", 0),
            "manquants": len(manifest.get("manquants", [])),
            "differents": len(manifest.get("differents", [])),
            "normalises_par_checkout": len(manifest.get("normalises_par_checkout", [])),
            "hors_manifeste": len(manifest.get("hors_manifeste", [])),
        },
        "headlines": headlines,
        "controles_negatifs": controles_neg,
    }
    return controles_liste, contexte


def _rend_texte(controles: list[Check], contexte: dict) -> str:
    lignes = [
        "Inventaire de la soumission OpenAI-YM-20261028",
        f"Racine analysee : {contexte['racine']}",
        "",
    ]
    for controle in controles:
        lignes.append(f"[{controle.statut}] {controle.key} -- {controle.titre}")
        lignes.append(f"        {controle.preuve}")
    volume = contexte["volume"]
    manifeste = contexte["manifeste"]
    lignes += [
        "",
        "Volume",
        f"  fichiers .lean : {volume['fichiers_lean']} ; lignes : {volume['lignes_lean']}",
        f"  part des repertoires repetitifs ANNULUS_* : {volume['part_annulus_pct']} % "
        f"({volume['lignes_annulus']} lignes)",
        f"  specification publique (Challenge/ChallengeSpec/PublicWilson/PublicTheory) : "
        f"{volume['lignes_specification']} lignes",
        "",
        "Manifeste",
        f"  verifies : {manifeste['verifies']} ; manquants : {manifeste['manquants']} ; "
        f"differents : {manifeste['differents']} ; "
        f"normalises par le checkout (fins de ligne) : {manifeste['normalises_par_checkout']}",
        "",
        "Occurrences par motif",
    ]
    for nom, total in sorted(contexte["totaux_occurrences"].items()):
        lignes.append(f"  {nom} : {total}")
    lignes += [
        "",
        "Enonce `YangMills.JointExistence` (ChallengeSpec.lean)",
        contexte["enonce_joint_existence"] or "  (absent)",
    ]
    return "\n".join(lignes)


def main(argv: list[str] | None = None) -> int:
    analyseur = argparse.ArgumentParser(description=__doc__)
    analyseur.add_argument("--repo", required=True, help="racine du clone local de la soumission")
    analyseur.add_argument("--json", action="store_true", help="sortie structuree JSON")
    args = analyseur.parse_args(argv)

    # La sortie contient des symboles Lean (quantificateurs, `ℕ`) : la console
    # Windows par defaut (cp1252) ne sait pas les ecrire.
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")

    racine = Path(args.repo).expanduser()
    if not racine.is_dir():
        print(f"Clone introuvable : {racine}", file=sys.stderr)
        return 2

    controles, contexte = _construit_controles(racine)
    if args.json:
        print(
            json.dumps(
                {
                    "controles": [
                        {
                            "key": c.key,
                            "titre": c.titre,
                            "statut": c.statut,
                            "preuve": c.preuve,
                            "details": c.details,
                        }
                        for c in controles
                    ],
                    "contexte": contexte,
                },
                ensure_ascii=False,
                indent=2,
            )
        )
    else:
        print(_rend_texte(controles, contexte))

    return 0 if all(c.statut == "PASS" for c in controles) else 1


if __name__ == "__main__":
    raise SystemExit(main())
