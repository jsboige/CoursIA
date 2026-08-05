"""Integrite structurelle du registre twin_pairs.d/ (#8057, file-per-entry #8542 Option C).

Historique : le registre etait un mono-fichier YAML `twin_pairs.yaml` (liste
append-only) sur lequel un merge driver `union` etait declare dans
`.gitattributes`. Les lanes y ajoutaient des entrees disjointes en fin de
fichier, ce qui produisait un conflit serie systematique (une seule PR
mergeable a la fois -- recurrences #8415 consolidation, #8476 re-apply, #8499
recovery tranche, #8505, #8526, #8492, toutes resolues a la main).

#8542 Option C supprime cette classe de conflit a la source : **un fichier par
paire** sous `twin_pairs.d/`. Deux PRs enregistrant des paires differentes
touchent des fichiers differents -- plus rien a fusionner. Cette suite de tests
est portee du mono-fichier vers le file-per-entry : les garanties
(comptage, doublons, schema, SHAs) sont preserves, le mode de defaillance
qu'elles couvraient (corruption silencieuse du merge union) disparait, et deux
nouveaux tests valident la structure file-per-entry elle-meme.

Le registre utilise des git blob SHAs (pas des hashes de contenu) : un notebook
edite (meme markdown-only) deplace son blob et doit etre re-audite via
`check_twin_parity.py --update --pair "<name>" --by "<lane>"`.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

import pytest

yaml = pytest.importorskip("yaml")

# Source unique de verite : le loader de check_twin_parity (evite de dupliquer
# la logique d'agregation du repertoire file-per-entry).
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_twin_parity import load_registry, _slug, _latest_audit  # noqa: E402

REGISTRY_DIR = Path(__file__).resolve().parents[1] / "twin_pairs.d"
SCHEMA = REGISTRY_DIR / "_schema.yaml"
SHA_RE = re.compile(r"^[0-9a-f]{40}$")
# Cles structurelles qu'une entree doit POSSEDER (sous-ensemble). L'enregistrement
# d'audit n'est pas liste ici : depuis #9399 volet (a) il peut prendre deux formes
# -- le singleton legacy `last_audit:` ou la liste append-only `audits:` -- et une
# entree valide possede l'UN des deux (cf `_has_audit_record` / `test_has_audit_record`).
REQUIRED_KEYS = {"name", "family", "python", "csharp", "parity_level"}
ALLOWED_KEYS = {
    "name", "family", "python", "csharp", "parity_level",
    "last_audit", "audits", "known_differences",
}
# Plancher d'entrees (post-migration #8542 : 116 paires sur origin/main). En
# mode file-per-entry, une entree perdue = un fichier supprime ; ce plancher le
# transforme en echec CI bruyant. A LEVER au fur et a mesure que le registre
# grossit (jamais baisser sans investiguer une perte, cf #8542 Constat 2).
MIN_ENTRIES = 116


def _entries() -> list:
    return load_registry(REGISTRY_DIR)


def _has_audit_record(entry: dict) -> bool:
    """Une entree valide possede un enregistrement d'audit sous l'une des deux
    formes (#9399) : le singleton legacy `last_audit:` ou la liste append-only
    `audits:` (non vide, chaque element un dict)."""
    if "last_audit" in entry and isinstance(entry["last_audit"], dict):
        return True
    audits = entry.get("audits")
    return isinstance(audits, list) and len(audits) > 0 and all(
        isinstance(a, dict) for a in audits
    )


def _all_audit_records(entry: dict) -> list:
    """Tous les enregistrements d'audit d'une entree (last_audit + chaque
    element de audits:). Sert a valider les SHAs PARTOUT, pas seulement le
    dernier -- un ancien enregistrement migre doit garder des SHAs valides
    (anti-regression : on ne jette pas l'historique, cf #9399 critere 4)."""
    records = []
    if isinstance(entry.get("last_audit"), dict):
        records.append(entry["last_audit"])
    for a in (entry.get("audits") or []):
        if isinstance(a, dict):
            records.append(a)
    return records


def _pair_files() -> list[Path]:
    """Tous les fichiers *.yaml non `_`-prefixes (un fichier = une paire)."""
    return sorted(p for p in REGISTRY_DIR.glob("*.yaml") if not p.name.startswith("_"))


class _DupKeyLoader(yaml.SafeLoader):
    """SafeLoader qui refuse les cles dupliquees au lieu de garder la derniere.

    Signaturait historique d'un merge union mal tombe (deux `python_sha:` dans
    un meme bloc) ; en file-per-entry c'est le signe d'une main-edit corrompue
    d'un fichier d'entree. PyYAML l'accepte silencieusement par defaut.
    """


def _no_duplicate_keys(loader, node, deep=False):
    mapping = {}
    for key_node, value_node in node.value:
        key = loader.construct_object(key_node, deep=deep)
        if key in mapping:
            raise yaml.constructor.ConstructorError(
                None, None, f"cle dupliquee dans le registre : {key!r}", key_node.start_mark
            )
        mapping[key] = loader.construct_object(value_node, deep=deep)
    return mapping


_DupKeyLoader.add_constructor(
    yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, _no_duplicate_keys
)


# --- Tests portes du mono-fichier (garanties preservees) ---


def test_registry_parses_as_list():
    assert len(_entries()) > 0


def test_no_duplicate_keys_anywhere():
    """Une cle dupliquee dans un fichier d'entree = structure corrompue."""
    for p in _pair_files():
        yaml.load(p.read_text(encoding="utf-8"), Loader=_DupKeyLoader)


def test_no_duplicate_pair_names():
    names = [e.get("name") for e in _entries()]
    dupes = sorted({n for n in names if names.count(n) > 1})
    assert not dupes, f"noms de paires dupliques : {dupes}"


def test_no_duplicate_notebook_paths():
    """Un notebook ne doit apparaitre que dans une seule paire."""
    seen: dict[str, str] = {}
    collisions = []
    for entry in _entries():
        for side in ("python", "csharp"):
            path = entry.get(side)
            if path in seen:
                collisions.append(f"{path} : {seen[path]} et {entry.get('name')}")
            else:
                seen[path] = entry.get("name", "?")
    assert not collisions, "notebooks enregistres deux fois : " + "; ".join(collisions)


def test_required_keys_present():
    missing = [
        f"{e.get('name', '?')} -> {sorted(REQUIRED_KEYS - set(e))}"
        for e in _entries()
        if not REQUIRED_KEYS.issubset(e)
    ]
    assert not missing, f"entrees incompletes : {missing}"


def test_has_audit_record():
    """Chaque entree porte un enregistrement d'audit (last_audit OU audits:, #9399).

    Les deux formes coexistent pendant la migration paresseuse a la volee : une
    entree n'en avoir AUCUNE est une corruption (paire enregistree sans jamais
    etre auditee -> DRIFT permanent non trace).
    """
    no_record = [
        e.get("name", "?") for e in _entries() if not _has_audit_record(e)
    ]
    assert not no_record, f"entrees sans enregistrement d'audit : {no_record}"


def test_audit_shas_are_git_blob_shas():
    """Les shas sont des blob SHA git (40 hex), pas des hashes de contenu.

    Valide les SHAs de TOUS les enregistrements (singleton last_audit + chaque
    element de la liste audits:) : un ancien enregistrement migre doit conserver
    des SHAs valides (#9399 critere 4 : on ne jette pas l'historique).
    """
    bad = []
    for entry in _entries():
        for audit in _all_audit_records(entry):
            for key in ("python_sha", "csharp_sha"):
                sha = audit.get(key)
                if not isinstance(sha, str) or not SHA_RE.match(sha):
                    bad.append(f"{entry.get('name', '?')}.{key} = {sha!r}")
    assert not bad, f"shas invalides : {bad}"


def test_registered_notebooks_exist_on_disk():
    repo_root = REGISTRY_DIR.resolve().parents[2]
    missing = [
        f"{e.get('name', '?')} -> {p}"
        for e in _entries()
        for p in (e.get("python"), e.get("csharp"))
        if p and not (repo_root / p).exists()
    ]
    assert not missing, f"notebooks introuvables : {missing}"


def test_entries_have_exact_key_set():
    """Chaque entree possede EXACTEMENT l'ensemble de cles canonique (ni plus, ni moins)."""
    bad = []
    for entry in _entries():
        keys = set(entry.keys())
        extra = keys - ALLOWED_KEYS
        missing = REQUIRED_KEYS - keys
        if extra or missing:
            name = entry.get("name", "?")
            if extra:
                bad.append(f"{name} -> cles inattendues: {sorted(extra)}")
            if missing:
                bad.append(f"{name} -> cles manquantes: {sorted(missing)}")
    assert not bad, "entrees au schema corrompu : " + "; ".join(bad)


def test_entry_count_floor():
    """Plancher anti-perte-silencieuse (une entree supprimee = un fichier manquant)."""
    n = len(_entries())
    assert n >= MIN_ENTRIES, (
        f"le registre a perdu des entrees : {n} < {MIN_ENTRIES} "
        f"(fichier d'entree supprime ou fusion accidentee ? cf #8542)"
    )


# --- Forme append-only `audits:` (#9399 volet a) ---


def test_audit_form_is_exclusive():
    """Une entree ne porte pas BOTH `last_audit` ET `audits` (source de verite unique).

    La migration (#9399) REMPLACE le singleton par la liste (l'ecrivain retire
    `last_audit:` quand il migre). Coexistence = main-edit corrompue ou migration
    a moitie faite -> le reader `_latest_audit` privilegierait `audits` et le
    `last_audit` residuel mentirait (SHAs potentiellement perimes).
    """
    both = [
        e.get("name", "?") for e in _entries()
        if "last_audit" in e and "audits" in e
    ]
    assert not both, f"entrees avec les deux formes d'audit : {both}"


def test_latest_audit_resolves_for_every_entry():
    """`_latest_audit` resout en un enregistrement a SHAs pour CHAQUE entree.

    Valide le reader polyvalent (#9399) sur le registre reel : quelle que soit la
    forme (legacy `last_audit` ou append-only `audits`), le dernier enregistrement
    porte des SHAs exploitables par le gate. Une entree dont le reader renvoie
    `{}` ou des SHAs absents -> DRIFT silencieux si la paire n'est pas checkee.
    """
    unresolved = []
    for entry in _entries():
        latest = _latest_audit(entry)
        if not isinstance(latest, dict) or not latest.get("python_sha") or not latest.get("csharp_sha"):
            unresolved.append(entry.get("name", "?"))
    assert not unresolved, f"entrees sans dernier audit resolu : {unresolved}"


def test_append_only_entries_well_formed():
    """Toute entree `audits:` est une liste non vide de dicts a SHAs valides.

    Un enregistrement d'audit (ancien ou nouveau) sans python_sha/csharp_sha est
    inutilisable par le gate (le reader renverrait None -> DRIFT bruyant, mais
    silencieux si la paire n'est pas checkee). On valide a l'inscription.
    """
    bad = []
    for entry in _entries():
        audits = entry.get("audits")
        if not isinstance(audits, list):
            continue
        for idx, rec in enumerate(audits):
            if not isinstance(rec, dict):
                bad.append(f"{entry.get('name', '?')}[{idx}] n'est pas un dict")
                continue
            for key in ("python_sha", "csharp_sha"):
                sha = rec.get(key)
                if not isinstance(sha, str) or not SHA_RE.match(sha):
                    bad.append(f"{entry.get('name', '?')}[{idx}].{key} = {sha!r}")
    assert not bad, f"entrees audits: mal formees : {bad}"


# --- Nouveaux tests : validation de la structure file-per-entry (#8542) ---


def test_one_file_per_pair_and_slug_roundtrip():
    """Chaque paire a son propre fichier `<slug(name)>.yaml`, contenant exactement
    cette paire (round-trip name -> slug -> fichier -> name)."""
    files = _pair_files()
    assert len(files) == len(_entries()), (
        f"{len(files)} fichiers pour {len(_entries())} entrees (un fichier par paire attendu)"
    )
    seen_files = set()
    for entry in _entries():
        name = entry.get("name", "?")
        expected = REGISTRY_DIR / f"{_slug(name)}.yaml"
        assert expected.exists(), f"fichier attendu manquant pour {name!r} : {expected.name}"
        seen_files.add(expected.name)
    assert len(seen_files) == len(files), "doublon de fichiers de paires"


def test_schema_file_present_and_excluded_from_pairs():
    """`_schema.yaml` est la documentation du repertoire (schema + provenance) :
    present, et correctement exclu du decompte de paires (parse a None/non-dict)."""
    assert SCHEMA.exists(), "_schema.yaml (doc schema + provenance) doit survivre (#8542)"
    data = yaml.safe_load(SCHEMA.read_text(encoding="utf-8"))
    assert not isinstance(data, dict), (
        "_schema.yaml doit etre de la documentation (comments), pas une paire ; "
        "sinon le loader `_`-skip doit etre durci."
    )


# --- Verification d'integrite des sha attestes (#9399 volet b) ---


def _repo_root() -> Path:
    # scripts/notebook_tools/tests/<file> -> repo root.
    return Path(__file__).resolve().parents[3]


def _build_blob_history(repo_root: Path) -> tuple[dict, dict]:
    """Map ``(path_blobs, blob_paths)`` pour tous les fichiers, ancetres de HEAD.

    Un seul appel ``git log HEAD --raw --abbrev=40`` (perf CI : ~1 appel pour
    tout le repo, lookup O(1) ensuite). #9399 volet (b) : un sha atteste qui
    n'est JAMAIS apparu comme blob du fichier = fabrication/typo/cross-file ->
    doit rougir, or ``test_audit_shas_are_git_blob_shas`` ne valide que le format.

    On parcourt l'historique des ancetres de HEAD (pas ``--all``) : ``--all`` est
    non-deterministe entre un clone local (qui voit les branches distantes) et un
    checkout CI (qui ne fetch que la branche de la PR), ce qui ferait varier le
    verdit du test. Les audits se font sur la ligne principale, donc un sha
    d'audit valide doit etre un blob apparu dans les ancetres de HEAD.

    Deux index derives du MEME flux ``--raw`` (determinisme preserve, pas de
    detection heuristique de renommage) :

    - ``path_blobs`` : ``{rel_path: set(blob sha)}`` -- les blobs qu'un path a eus.
    - ``blob_paths`` : ``{blob sha: set(rel_path)}`` -- les paths sous lesquels un
      blob est apparu. Sert a distinguer un carnet RENOMME (sha apparu sous un
      ancien path, legitime) d'une fabrication (sha apparu sous aucun path) -- cf
      ``_classify_attested_sha`` et le residuel note par ai-01 sur #9471.
    """
    import subprocess

    proc = subprocess.run(
        ["git", "log", "HEAD", "--raw", "--no-renames", "--abbrev=40", "--format="],
        cwd=repo_root, capture_output=True, text=True,
    )
    path_blobs: dict[str, set[str]] = {}
    blob_paths: dict[str, set[str]] = {}
    for line in proc.stdout.splitlines():
        if not line.startswith(":"):
            continue
        parts = line.split("\t")
        if len(parts) < 2:
            continue
        meta = parts[0].split()
        path = parts[-1].strip()
        if len(meta) < 5:
            continue
        for sha in (meta[2], meta[3]):  # old blob, new blob (40 hex ou zeros)
            if len(sha) == 40 and not sha.startswith("0" * 7):
                path_blobs.setdefault(path, set()).add(sha)
                blob_paths.setdefault(sha, set()).add(path)
    return path_blobs, blob_paths


def _declared_paths() -> set[str]:
    """Ensemble des paths de carnets declares dans le registre (python + csharp),
    normalises en ``/``. Sert a distinguer un cross-file (sha d'un AUTRE carnet
    enregistre) d'un renommage (sha d'un ancien path non declare -- ex. carnet
    renomme avant d'etre enregistre sous son nom courant)."""
    out: set[str] = set()
    for entry in _entries():
        for side in ("python", "csharp"):
            rel = entry.get(side)
            if rel:
                out.add(str(rel).replace("\\", "/"))
    return out


def _classify_attested_sha(
    sha: str,
    path: str,
    path_blobs: dict,
    blob_paths: dict,
    declared: set,
) -> tuple[str, str]:
    """Classe un sha atteste sous ``path`` en exactement un verdict.

    Retourne ``(verdict, detail)`` ou ``verdict`` est l'un de :

    - ``"ok"`` : le sha est un blob du carnet sous son path declare -> conforme.
    - ``"renamed"`` : le sha fut un blob sous un path ANTERIEUR non declare
      (carnet renomme/deplace). Legitime : on ne faille pas, mais on le signale
      pour diagnostic (residuel ai-01 #9471 : ``--no-renames`` dissocie
      l'historique du path courant -> faux positif « fabrique » sans ceci).
    - ``"fabricated"`` : le sha n'apparait sous AUCUN path -> fabrication/typo
      (le seul vrai defaut que ce gate doit rougir, #9399 4e manifestation).
    - ``"crossfile"`` : le sha apparait sous le path d'un AUTRE carnet enregistre
      -> copie cross-file (on garde la detection que ai-01 a valide sur #9471).

    ``detail`` est un message humain (path ancien / path voisin) pour l'assertion.
    """
    if sha in path_blobs.get(path, set()):
        return "ok", ""
    others = blob_paths.get(sha, set()) - {path}
    if not others:
        return "fabricated", f"jamais blob d'aucun fichier (ni {path})"
    # Le sha fut un blob, mais sous d'autres paths. Cross-file si l'un de ces
    # paths est un carnet declare d'une autre paire ; sinon c'est un ancien path
    # du carnet (renomme) -- legitime.
    cross = sorted(others & declared)
    if cross:
        return "crossfile", f"sha d'un autre carnet enregistre : {cross}"
    return "renamed", f"sha apparu sous ancien(s) path(s) (renommage ?) : {sorted(others)}"


def test_audit_shas_exist_in_file_history():
    """Ferme la faille #9399 (4e manifestation) : le sha du DERNIER audit d'une
    paire doit etre un blob que le carnet a REELLEMENT eu dans son historique git
    (sous son path declare).

    `test_audit_shas_are_git_blob_shas` ne valide que le FORMAT (40 hex). Un sha
    fabrique, typo, ou copie du carnet voisin -- 40 hex valides mais n'ayant
    JAMAIS correspond au fichier -- passait silencieusement : « rien ne verifie
    qu'elle est vraie » (#9399). Ce test verifie l'assertion reelle sur le
    dernier enregistrement (celui qui atteste l'etat de parite courant) :
    python_sha / csharp_sha existent dans l'historique des blobs du carnet declare.

    Scope = dernier audit uniquement (pas les audits historiques migres) : un
    audit ancien peut legitiment porter le sha d'un path ANTERIEUR (carnet
    renomme/deplace, ex. restructuration Search/Applications). ``--no-renames``
    dissocie l'historique du path courant, donc la classification 3-branches
    (``_classify_attested_sha``) distingue ce cas (``renamed``, legitime) d'une
    fabrication (``fabricated``) ou d'une copie cross-file (``crossfile``) -- cf
    residuel note par ai-01 sur #9471. Le FORMAT des sha historiques reste couvert
    par ``test_audit_shas_are_git_blob_shas``.

    Distinction avec le drift (sha != HEAD) : un sha qui fut vrai a un commit
    passe ce test (il est dans l'historique) mais reste detecte comme drift par
    ``check_twin_parity --check`` au moment d'une PR. Ce test cible exclusivement
    les sha qui ne correspondent JAMAIS au carnet (fabrication), qui ne
    rougiraient nulle part autrement. La reserve de drifts legittimes
    (Sudoku-8/14-BDD/9, ai-01) reste donc verte ici.
    """
    import subprocess

    repo_root = _repo_root()
    # Skip defensif si git absent / hors work-tree (env degrade non-CI).
    try:
        subprocess.run(
            ["git", "rev-parse", "--is-inside-work-tree"],
            cwd=repo_root, capture_output=True, check=True,
        )
    except Exception:
        pytest.skip("hors d'un work-tree git (git indisponible) -- test d'historique saute")

    path_blobs, blob_paths = _build_blob_history(repo_root)
    declared = _declared_paths()
    fabricated, crossfile, renamed = [], [], []
    for entry in _entries():
        latest = _latest_audit(entry)
        if not isinstance(latest, dict):
            continue
        for sha_key, path_key in (("python_sha", "python"), ("csharp_sha", "csharp")):
            rel = entry.get(path_key)
            sha = latest.get(sha_key)
            if not rel or not isinstance(sha, str) or not SHA_RE.match(sha):
                continue
            relf = str(rel).replace("\\", "/")
            verdict, detail = _classify_attested_sha(
                sha, relf, path_blobs, blob_paths, declared
            )
            label = f"{entry.get('name', '?')}.{sha_key} = {sha[:12]} ({detail})"
            if verdict == "fabricated":
                fabricated.append(label)
            elif verdict == "crossfile":
                crossfile.append(label)
            elif verdict == "renamed":
                renamed.append(label)
    assert not fabricated, (
        f"sha(s) du dernier audit jamais apparu(s) comme blob : {fabricated}"
    )
    assert not crossfile, (
        f"sha(s) du dernier audit emprunte(s) a un autre carnet enregistre : {crossfile}"
    )
    # ``renamed`` est legitime (carnet renomme) -> on ne faille pas, mais on le
    # rend visible (warning pytest) pour prevenir qu'un faux rename masque un
    # futur cross-file. Vide sur le registre courant.
    if renamed:
        import warnings
        warnings.warn(
            "sha attestes sous un ancien path (carnet renomme ?) : " + "; ".join(renamed)
        )


def test_classify_attested_sha_ok_fabricated_crossfile_renamed():
    """Unitarise la classification 3-branches (pas de git, dicts factices).

    Couvre les 4 verdicts de ``_classify_attested_sha`` : ``ok`` (sha sous le
    path declare), ``fabricated`` (sha absent de tout path), ``crossfile`` (sha
    sous le path d'un autre carnet enregistre), ``renamed`` (sha sous un ancien
    path non declare). Garantit que le durcissement rename-aware (residuel ai-01
    #9471) ne regresse pas la detection de fabrication ni de cross-file.
    """
    declared = {"A/X.ipynb", "B/Y.ipynb"}
    path_blobs = {
        "A/X.ipynb": {"shaX_ok"},
        "B/Y.ipynb": {"shaY_ok"},
        "A/X_old.ipynb": {"shaX_renamed"},  # ancien path (renomme), non declare
    }
    blob_paths = {
        "shaX_ok": {"A/X.ipynb"},
        "shaY_ok": {"B/Y.ipynb"},
        "shaX_renamed": {"A/X_old.ipynb"},
        "sha_crossfile": {"B/Y.ipynb"},  # blob d'un autre carnet declare
    }
    v, _ = _classify_attested_sha("shaX_ok", "A/X.ipynb", path_blobs, blob_paths, declared)
    assert v == "ok"
    v, d = _classify_attested_sha("e" * 39 + "f", "A/X.ipynb", path_blobs, blob_paths, declared)
    assert v == "fabricated"
    assert "jamais blob" in d
    v, d = _classify_attested_sha("sha_crossfile", "A/X.ipynb", path_blobs, blob_paths, declared)
    assert v == "crossfile"
    assert "B/Y.ipynb" in d
    v, d = _classify_attested_sha("shaX_renamed", "A/X.ipynb", path_blobs, blob_paths, declared)
    assert v == "renamed"
    assert "X_old" in d
