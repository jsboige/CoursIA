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
from check_twin_parity import (
    load_registry, _slug, _latest_audit, verify_recorded_sha, update_pair,
)  # noqa: E402

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


# --- tests verify_recorded_sha (#9399 volet b) ------------------------------
#
# Le mode CI --verify-recorded-sha detecte un SHA enregistre dans le YAML qui
# ne correspond pas au SHA reel du carnet a HEAD. Cible l'acceptance verbatim
# « la CI calcule python_sha/csharp_sha/content_*_sha et echoue si le YAML
# committé diverge ». On unitarise les 4 branches (OK/PY-NOPE/CS-NOPE/BOTH-NOPE)
# en mockant _git_blob_sha et _content_sha pour controler les valeurs
# calculees, sans dependre de l'etat du repo.


def test_verify_recorded_sha_ok_when_recorded_matches_calculated(tmp_path, monkeypatch):
    """Recorded == calculated -> OK, pas de mismatch."""
    fake_pair = {
        "name": "Test-OK",
        "family": "Test",
        "python": "X.ipynb",
        "csharp": "Y.ipynb",
        "parity_level": "surface",
        "last_audit": {
            "date": "2026-08-05",
            "by": "test",
            "python_sha": "a" * 40,
            "csharp_sha": "b" * 40,
            "content_python_sha": "c" * 64,
            "content_csharp_sha": "d" * 64,
        },
    }
    # Mock les helpers de hash pour retourner des valeurs connues.
    import check_twin_parity as ct
    monkeypatch.setattr(ct, "_git_blob_sha", lambda *a, **kw: "a" * 40 if kw.get("git_ref") is None or "Y" not in str(a[1] if len(a) > 1 else "") else "b" * 40)
    # Mock plus precis : return different sha based on path.
    def _hash_blob(repo_root, path, git_ref="HEAD"):
        return "a" * 40 if path == "X.ipynb" else "b" * 40
    def _hash_content(repo_root, path, git_ref="HEAD"):
        return "c" * 64 if path == "X.ipynb" else "d" * 64
    monkeypatch.setattr(ct, "_git_blob_sha", _hash_blob)
    monkeypatch.setattr(ct, "_content_sha", _hash_content)

    r = verify_recorded_sha(tmp_path, fake_pair)
    assert r["status"] == "OK"
    assert r["mismatches"] == []
    assert r["name"] == "Test-OK"


def test_verify_recorded_sha_mismatch_on_python_sha(tmp_path, monkeypatch):
    """Recorded python_sha diverge du SHA reel -> MISMATCH sur python_sha."""
    fake_pair = {
        "name": "Test-Mismatch-Py",
        "family": "Test",
        "python": "X.ipynb",
        "csharp": "Y.ipynb",
        "parity_level": "surface",
        "last_audit": {
            "date": "2026-08-05",
            "by": "test",
            "python_sha": "0" * 40,  # recorded = zeros
            "csharp_sha": "b" * 40,
        },
    }
    import check_twin_parity as ct
    monkeypatch.setattr(ct, "_git_blob_sha", lambda rr, p, git_ref="HEAD": "a" * 40 if p == "X.ipynb" else "b" * 40)
    monkeypatch.setattr(ct, "_content_sha", lambda rr, p, git_ref="HEAD": None)  # not used

    r = verify_recorded_sha(tmp_path, fake_pair)
    assert r["status"] == "MISMATCH"
    assert len(r["mismatches"]) == 1
    assert "python_sha" in r["mismatches"][0]
    assert ("0" * 12) in r["mismatches"][0]
    assert ("a" * 12) in r["mismatches"][0]


def test_verify_recorded_sha_mismatch_on_both_sides(tmp_path, monkeypatch):
    """Recorded python_sha ET csharp_sha divergent -> MISMATCH sur les 2."""
    fake_pair = {
        "name": "Test-Mismatch-Both",
        "family": "Test",
        "python": "X.ipynb",
        "csharp": "Y.ipynb",
        "parity_level": "surface",
        "last_audit": {
            "date": "2026-08-05",
            "by": "test",
            "python_sha": "0" * 40,
            "csharp_sha": "0" * 40,
        },
    }
    import check_twin_parity as ct
    monkeypatch.setattr(ct, "_git_blob_sha", lambda rr, p, git_ref="HEAD": "a" * 40 if p == "X.ipynb" else "b" * 40)
    monkeypatch.setattr(ct, "_content_sha", lambda rr, p, git_ref="HEAD": None)

    r = verify_recorded_sha(tmp_path, fake_pair)
    assert r["status"] == "MISMATCH"
    assert len(r["mismatches"]) == 2
    assert any("python_sha" in m for m in r["mismatches"])
    assert any("csharp_sha" in m for m in r["mismatches"])


def test_verify_recorded_sha_no_audit_record(tmp_path):
    """Pas de last_audit ni audits -> NO_AUDIT, pas de MISMATCH."""
    fake_pair = {
        "name": "Test-NoAudit",
        "family": "Test",
        "python": "X.ipynb",
        "csharp": "Y.ipynb",
        "parity_level": "surface",
        # pas de last_audit, pas de audits
    }
    r = verify_recorded_sha(tmp_path, fake_pair)
    assert r["status"] == "NO_AUDIT"
    assert r["mismatches"] == []


def test_verify_recorded_sha_legacy_vs_append_only_equivalent(tmp_path, monkeypatch):
    """Memes SHA dans `last_audit` (legacy) et `audits[-1]` (append-only) -> OK dans les 2 formes."""
    sha_py = "a" * 40
    sha_cs = "b" * 40
    base = {
        "name": "Test-Equiv",
        "family": "Test",
        "python": "X.ipynb",
        "csharp": "Y.ipynb",
        "parity_level": "surface",
    }
    import check_twin_parity as ct
    monkeypatch.setattr(ct, "_git_blob_sha", lambda rr, p, git_ref="HEAD": sha_py if p == "X.ipynb" else sha_cs)
    monkeypatch.setattr(ct, "_content_sha", lambda rr, p, git_ref="HEAD": None)

    legacy = dict(base, last_audit={"date": "2026-08-05", "by": "test", "python_sha": sha_py, "csharp_sha": sha_cs})
    append_only = dict(base, audits=[{"date": "2026-08-05", "by": "test", "python_sha": sha_py, "csharp_sha": sha_cs}])

    r_legacy = verify_recorded_sha(tmp_path, legacy)
    r_append = verify_recorded_sha(tmp_path, append_only)
    assert r_legacy["status"] == "OK"
    assert r_append["status"] == "OK"


def test_verify_recorded_sha_skips_none_content_sha(tmp_path, monkeypatch):
    """Recorded content_*_sha = None (migration post-volet-(c) pas faite) -> SKIP, pas MISMATCH."""
    fake_pair = {
        "name": "Test-NoContentSha",
        "family": "Test",
        "python": "X.ipynb",
        "csharp": "Y.ipynb",
        "parity_level": "surface",
        "last_audit": {
            "date": "2026-08-05",
            "by": "test",
            "python_sha": "a" * 40,
            "csharp_sha": "b" * 40,
            # content_*_sha absents -> devraient etre ignores (migration progressive)
        },
    }
    import check_twin_parity as ct
    monkeypatch.setattr(ct, "_git_blob_sha", lambda rr, p, git_ref="HEAD": "a" * 40 if p == "X.ipynb" else "b" * 40)
    # _content_sha retourne une valeur meme si recorded=None : c'est OK, on
    # ne signale pas de mismatch tant que recorded est None.
    monkeypatch.setattr(ct, "_content_sha", lambda rr, p, git_ref="HEAD": "c" * 64 if p == "X.ipynb" else "d" * 64)

    r = verify_recorded_sha(tmp_path, fake_pair)
    assert r["status"] == "OK", f"unexpected mismatches: {r['mismatches']}"


# --- tests update_pair no-op detection (#9399 critere 2) ---------------------
#
# Critere 2 du design-gate #9399 : « Le rebaseline manuel --update devient
# facultatif (ou refuse d'ecrire un SHA que la CI recalculera) ». La CI derive
# elle-meme les SHAs depuis le volet b (#9481) ; un rebaseline manuel qui
# n'apporte aucune information nouvelle (SHAs de comparaison identiques au
# `_latest_audit`) est un « faux audit » au sens du design-gate -- dater une
# attestation identique.
#
# On unitarise `update_pair` (retourne (audit, cur_py, is_noop)) et la
# discrimination no-op vs reel, en mockant _git_blob_sha et _content_sha pour
# controler les valeurs calculees sans dependre de l'etat du repo.


def test_update_pair_no_op_when_content_sha_matches(tmp_path, monkeypatch):
    """Recorded content_python_sha == calculated content_python_sha
    (et idem csharp) -> is_noop True, faux audit evite."""
    sha_py = "a" * 40
    sha_cs = "b" * 40
    cpy = "c" * 64
    ccs = "d" * 64
    fake_pair = {
        "name": "Test-NoOp-Content",
        "family": "Test",
        "python": "X.ipynb",
        "csharp": "Y.ipynb",
        "parity_level": "surface",
        "audits": [{
            "date": "2026-08-01",
            "by": "previous-auditor",
            "python_sha": sha_py,
            "csharp_sha": sha_cs,
            "content_python_sha": cpy,
            "content_csharp_sha": ccs,
        }],
    }
    import check_twin_parity as ct
    monkeypatch.setattr(ct, "_git_blob_sha", lambda rr, p, git_ref="HEAD": sha_py if p == "X.ipynb" else sha_cs)
    monkeypatch.setattr(ct, "_content_sha", lambda rr, p, git_ref="HEAD": cpy if p == "X.ipynb" else ccs)

    audit, cur_py, is_noop = update_pair(tmp_path, fake_pair)
    assert cur_py == sha_py, "cur_py should match the recorded git blob SHA"
    assert is_noop is True, "content_sha equality should trigger no-op"
    # L'audit retourne DOIT etre complet (memes SHAs, fresh date/by), c'est
    # le caller qui decide de l'ecrire ou non (refus si is_noop et pas --force).
    assert audit["python_sha"] == sha_py
    assert audit["content_python_sha"] == cpy


def test_update_pair_real_drift_when_content_sha_differs(tmp_path, monkeypatch):
    """Recorded content_python_sha != calculated content_python_sha
    -> is_noop False, vrai rebaseline legitime (pas un faux audit)."""
    fake_pair = {
        "name": "Test-Real-Drift",
        "family": "Test",
        "python": "X.ipynb",
        "csharp": "Y.ipynb",
        "parity_level": "surface",
        "audits": [{
            "date": "2026-08-01",
            "by": "previous-auditor",
            "python_sha": "a" * 40,
            "csharp_sha": "b" * 40,
            "content_python_sha": "c" * 64,  # recorded content_sha stale
            "content_csharp_sha": "d" * 64,
        }],
    }
    import check_twin_parity as ct
    monkeypatch.setattr(ct, "_git_blob_sha", lambda rr, p, git_ref="HEAD": "a" * 40 if p == "X.ipynb" else "b" * 40)
    # Calculated content_sha DIFFERENT du recorded -- vrai drift pedagogique.
    monkeypatch.setattr(ct, "_content_sha", lambda rr, p, git_ref="HEAD": "e" * 64 if p == "X.ipynb" else "f" * 64)

    audit, cur_py, is_noop = update_pair(tmp_path, fake_pair)
    assert cur_py == "a" * 40
    assert is_noop is False, "content_sha drift should NOT trigger no-op"
    assert audit["content_python_sha"] == "e" * 64
    assert audit["content_csharp_sha"] == "f" * 64


def test_update_pair_metadata_only_drift_is_noop(tmp_path, monkeypatch):
    """Le cas designe par ai-01 : un tampon `metadata.cost` seul deplace le
    git blob SHA mais preserve le content_sha (_shas_match utilise content_sha
    d'abord). -> is_noop True, NE PAS ecrire (sinon faux audit). C'est
    precisement la classe de drift Sudoku-8/14 BDD/9 GraphColoring que le
    design-gate a designee comme devant etre ignoree."""
    fake_pair = {
        "name": "Test-Metadata-Only",
        "family": "Sudoku",
        "python": "X.ipynb",
        "csharp": "Y.ipynb",
        "parity_level": "deep",
        "audits": [{
            "date": "2026-08-01",
            "by": "previous-auditor",
            "python_sha": "a" * 40,
            "csharp_sha": "b" * 40,
            "content_python_sha": "c" * 64,  # recorded content_sha preserved
            "content_csharp_sha": "d" * 64,
        }],
    }
    import check_twin_parity as ct
    # Le carnet A BOUGE : git blob SHA different (metadata tampon), MAIS
    # content_sha preserve (la structure pedagogique n'a pas change).
    monkeypatch.setattr(ct, "_git_blob_sha", lambda rr, p, git_ref="HEAD": "1" * 40 if p == "X.ipynb" else "2" * 40)
    monkeypatch.setattr(ct, "_content_sha", lambda rr, p, git_ref="HEAD": "c" * 64 if p == "X.ipynb" else "d" * 64)

    audit, cur_py, is_noop = update_pair(tmp_path, fake_pair)
    assert cur_py == "1" * 40, "git blob SHA moved (metadata-only change)"
    assert audit["python_sha"] == "1" * 40
    assert audit["content_python_sha"] == "c" * 64, "content_sha preserved"
    assert is_noop is True, (
        "metadata-only drift MUST be no-op (content_sha preserved) -- "
        "c'est la classe de faux audit que critere 2 designe."
    )


def test_update_pair_no_audit_record_is_not_noop(tmp_path, monkeypatch):
    """Sans `_latest_audit` (paire non encore auditee), is_noop est False meme
    si les SHAs calcules sont triviaux -- le premier audit doit toujours
    s'ecrire. (Sinon une paire neuve ne pourrait jamais etre auditee.)"""
    fake_pair = {
        "name": "Test-NoAudit",
        "family": "Test",
        "python": "X.ipynb",
        "csharp": "Y.ipynb",
        "parity_level": "surface",
        # pas de last_audit, pas de audits
    }
    import check_twin_parity as ct
    monkeypatch.setattr(ct, "_git_blob_sha", lambda rr, p, git_ref="HEAD": "a" * 40 if p == "X.ipynb" else "b" * 40)
    monkeypatch.setattr(ct, "_content_sha", lambda rr, p, git_ref="HEAD": "c" * 64 if p == "X.ipynb" else "d" * 64)

    audit, cur_py, is_noop = update_pair(tmp_path, fake_pair)
    assert cur_py == "a" * 40
    assert is_noop is False, (
        "First audit of a never-audited pair must NOT be a no-op, sinon le "
        "registre ne peut pas demarrer (cf. migration #9405)."
    )


def test_update_pair_no_op_via_git_blob_sha_fallback(tmp_path, monkeypatch):
    """Fallback legacy : si le `_latest_audit` n'a pas de content_sha (paire
    legacy pre-volet-(c), pas encore re-auditee post-c), ET que le nouveau
    audit non plus (meme forme legacy), alors _shas_match retombe sur les
    git blob SHA. Si git blob SHA egalite, no-op quand meme.

    Note semantique : si l'ancien audit est legacy (no content_sha) et le
    nouveau est content_sha-aware, _shas_match les considere INCOMPATIBLES
    (compare content_sha recorded=None avec content_sha calculated="c"*64 :
    divergent). Ce n'est PAS un cas faux-audit -- c'est une migration de
    forme, et le nouvel audit DOIT s'ecrire (avec une nouvelle entree
    content_sha) pour mettre la paire en conformite avec le schema cible.
    """
    fake_pair = {
        "name": "Test-Legacy-NoOp",
        "family": "Test",
        "python": "X.ipynb",
        "csharp": "Y.ipynb",
        "parity_level": "surface",
        "last_audit": {  # legacy singleton, pas de content_sha
            "date": "2026-08-01",
            "by": "previous-auditor",
            "python_sha": "a" * 40,
            "csharp_sha": "b" * 40,
            # content_python_sha / content_csharp_sha absents
        },
    }
    import check_twin_parity as ct
    monkeypatch.setattr(ct, "_git_blob_sha", lambda rr, p, git_ref="HEAD": "a" * 40 if p == "X.ipynb" else "b" * 40)
    # Calculated content_sha aussi None (legacy total) : _shas_match
    # tombe en fallback git blob SHA, qui sont egaux -> no-op.
    monkeypatch.setattr(ct, "_content_sha", lambda rr, p, git_ref="HEAD": None)

    audit, cur_py, is_noop = update_pair(tmp_path, fake_pair)
    assert cur_py == "a" * 40
    assert is_noop is True, (
        "Legacy form (no content_sha recorded AND no content_sha calculated) "
        "must fall back to git blob SHA equality for no-op detection."
    )


def test_update_pair_partial_drift_is_not_noop(tmp_path, monkeypatch):
    """Une seule cote drift (Python content_sha differe, C# egal) -> is_noop
    False. Une moitie de drift = vrai changement = vrai audit."""
    fake_pair = {
        "name": "Test-Partial-Drift",
        "family": "Test",
        "python": "X.ipynb",
        "csharp": "Y.ipynb",
        "parity_level": "surface",
        "audits": [{
            "date": "2026-08-01",
            "by": "previous-auditor",
            "python_sha": "a" * 40,
            "csharp_sha": "b" * 40,
            "content_python_sha": "c" * 64,  # recorded
            "content_csharp_sha": "d" * 64,  # recorded (same as calculated)
        }],
    }
    import check_twin_parity as ct
    monkeypatch.setattr(ct, "_git_blob_sha", lambda rr, p, git_ref="HEAD": "a" * 40 if p == "X.ipynb" else "b" * 40)
    # Seule la cote Python drift, C# preserved.
    monkeypatch.setattr(ct, "_content_sha", lambda rr, p, git_ref="HEAD": "e" * 64 if p == "X.ipynb" else "d" * 64)

    audit, cur_py, is_noop = update_pair(tmp_path, fake_pair)
    assert audit["content_python_sha"] == "e" * 64
    assert audit["content_csharp_sha"] == "d" * 64
    assert is_noop is False, (
        "Partial drift (one side content_sha differs) is a real change "
        "and must NOT be flagged as no-op."
    )
