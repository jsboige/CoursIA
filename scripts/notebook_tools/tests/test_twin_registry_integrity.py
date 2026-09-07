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
    load_registry, _slug, _latest_audit, _content_sha, verify_recorded_sha,
    update_pair, surgical_rebaseline, migrate_registry_files_per_audit,
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
    # Optionnel (#10439) : verdict de bridge SOTA structure (INTRINSIC/SOTA-OK/
    # RECOVERABLE-*), orthogonal a parity_level. La plupart des paires n'en portent pas.
    "bridge_verdict", "bridge_verdict_reason",
    # Optionnel (#12933) : justification d'une divergence de numerotation python/csharp
    # documentee (lue par check_twin_parity.py au verdict NUMBERING-DRIFT).
    "numbering_exception",
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

    # ``-m`` : montre le diff des merge commits contre chaque parent. Sans cette
    # option, ``git log --raw`` supprime les diffs de merge -> un blob dont la
    # premiere apparition est le RESULTAT d'une resolution de merge (typique des
    # PRs twin ou un merge ``origin/main`` combine un header-hoist + un fix de
    # runtime en un nouveau blob unique) est invisible au walker, et la rebaseline
    # de ce blob echoue sur ``test_audit_shas_exist_in_file_history`` alors que le
    # sha est un vrai blob git (``git cat-file`` / ``git ls-tree`` le confirment).
    # ``-m`` reste dans les ancetres de HEAD (determinisme CI/local preserve, cf
    # note supra sur le rejet de ``--all``) ; le parser deduplique via ``set()``.
    proc = subprocess.run(
        ["git", "log", "HEAD", "-m", "--raw", "--no-renames", "--abbrev=40", "--format="],
        cwd=repo_root, capture_output=True, text=True, encoding="utf-8", errors="replace",
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


def _content_matches_head(repo_root, latest: dict, sha_key: str, rel: str) -> bool:
    """Reconciliation ``orphelin par squash`` (#13100) cote test.

    Vrai si le `content_*_sha` enregistre dans le dernier audit est present ET
    egal au content hash calcule a HEAD par `_content_sha` (qui exclut
    ``nb["metadata"]``, papermill compris -- les normalisations sanctionnees).
    Un sha (git blob) atteste sur une branche puis orpheline par squash-merge
    n'est PAS une fabrication quand le contenu qu'il attestait est porteur de ce
    que main porte aujourd'hui : le hash de contenu le prouve.
    """
    ckey = "content_" + sha_key
    rec = latest.get(ckey)
    if not isinstance(rec, str) or len(rec) != 64:
        return False
    try:
        return _content_sha(repo_root, rel) == rec
    except Exception:
        return False


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
    (Sudoku-08/14-BDD/9, ai-01) reste donc verte ici.
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
    fabricated, crossfile, renamed, orphaned = [], [], [], []
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
                # Reconciliation orphelin par squash (#13100) : un squash-merge
                # re-hashe le blob sans toucher au contenu pedagogique. Le sha
                # atteste etait le vrai blob du carnet sur la branche, mais
                # l'historique de HEAD ne le contient plus -> faux « fabrique ».
                # Un `content_*_sha` enregistre egal au content hash calcule a
                # HEAD prouve que l'attestation correspond a un contenu
                # reellement porte par main (modulo normalisations sanctionnees
                # -- `_content_sha` exclut `nb["metadata"]`, papermill compris).
                # Ce n'est PAS une fabrication : on signale (orpheline), on ne
                # faille pas. Le vrai defaut (fabrication/typo/cross-file) n'a
                # AUCUN content_sha concordant -> rougit toujours.
                if _content_matches_head(repo_root, latest, sha_key, relf):
                    orphaned.append(label)
                else:
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
    # ``orphaned`` est legitime (squash-merge a contenu preserve) -> warning,
    # pas de FAIL : le `--update` de la prochaine PR re-rebaseline le blob. Ne
    # pas le remonter en ''fabricated'' : ce serait rougir `main` pour une
    # attestation veridique.
    if orphaned:
        import warnings
        warnings.warn(
            "blob(s) orphelins par squash mais contenu atteste identique a HEAD "
            "(un --update re-baseline le git blob SHA) : " + "; ".join(orphaned)
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
    # Discrimination reachability (#11919) : recorded == courant (meme SHA),
    # donc trivialement accessible depuis HEAD. Pas un orphelin.
    monkeypatch.setattr(ct, "_blob_ancestor_in", lambda rr, blob_sha, ref="HEAD": True)

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
    precisement la classe de drift Sudoku-08/14 BDD/9 GraphColoring que le
    design-gate a designee comme devant etre ignoree.

    Discrimination reachability (#11919) : le recorded git blob SHA EST
    accessible depuis HEAD (le commit qui le porte est un ancetre, juste pas
    HEAD lui-meme -- le buffer metadata a change entre ce commit et HEAD).
    C'est la difference fondamentale avec un orphelin par squash : dans le
    cas metadata-only, le blob reste reference par un commit ancetre.
    """
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
    # Discrimination reachability : le recorded blob SHA EST accessible (le
    # commit qui le porte est ancetre de HEAD). C'est ce qui distingue
    # metadata-only drift d'un orphelin par squash (#11919) -- les deux cas
    # ont la meme signature `rec_X != cur_X`, differencies par reachability.
    monkeypatch.setattr(ct, "_blob_ancestor_in", lambda rr, blob_sha, ref="HEAD": True)

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
    # Discrimination reachability (#11919) : recorded == courant (meme SHA),
    # donc trivialement accessible depuis HEAD.
    monkeypatch.setattr(ct, "_blob_ancestor_in", lambda rr, blob_sha, ref="HEAD": True)

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


def test_build_blob_history_sees_merge_introduced_blob(tmp_path):
    """Regression #10732 : un blob dont la 1re apparition est le RESULTAT d'un
    merge commit doit etre vu par ``_build_blob_history``.

    Sans ``-m``, ``git log --raw`` supprime les diffs de merge -> le walker ne
    voit jamais le blob merge-resolved, et ``test_audit_shas_exist_in_file_history``
    le classe ``fabricated`` (alors que ``git cat-file`` / ``git ls-tree`` le
    confirment reel). Ce scenario est quotidien sur les PRs twin ou un merge
    ``origin/main`` combine un header-hoist + un fix de runtime en un nouveau
    blob. Constructeur : deux branches divergent editent le meme fichier, le
    merge est resolu en un contenu unique absent des deux parents.
    """
    import subprocess

    def _git(*args):
        return subprocess.run(
            ["git", *args], cwd=tmp_path, capture_output=True, text=True,
            encoding="utf-8", errors="replace", check=True,
        )

    _git("init", "-q")
    _git("config", "user.email", "t@t"); _git("config", "user.name", "t")
    _git("config", "commit.gpgsign", "false")
    (tmp_path / "f.txt").write_text("line1\nline3\n", encoding="utf-8")
    _git("add", "f.txt"); _git("commit", "-qm", "init")
    main_branch = _git("symbolic-ref", "--short", "HEAD").stdout.strip()
    _git("checkout", "-q", "-b", "branch")
    (tmp_path / "f.txt").write_text("line1\nlineB\nline3\n", encoding="utf-8")
    _git("commit", "-qam", "branch edit")
    _git("checkout", "-q", main_branch)
    # divergence cote main pour forcer un vrai merge a 2 parents
    (tmp_path / "f.txt").write_text("lineMAIN1\nline3\n", encoding="utf-8")
    _git("commit", "-qam", "main edit")
    # le merge produit un conflit (sortie non-zero attendue) -> etat de merge
    subprocess.run(
        ["git", "merge", "-q", "--no-ff", "branch"],
        cwd=tmp_path, capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    # resolution manuelle en un CONTENU UNIQUE absent des deux parents
    (tmp_path / "f.txt").write_text("lineMAIN1\nlineB\nline3\nMERGED-UNIQUE\n", encoding="utf-8")
    _git("add", "f.txt"); _git("commit", "-qm", "merge resolved unique")
    merge_blob = _git("rev-parse", "HEAD:f.txt").stdout.strip()
    assert len(merge_blob) == 40, "blob SHA attendu (40 hex)"

    path_blobs, _blob_paths = _build_blob_history(tmp_path)
    assert merge_blob in path_blobs.get("f.txt", set()), (
        f"le blob merge-introduced {merge_blob[:12]} est invisible au walker "
        f"(f.txt a eu les blobs {sorted(s[:12] for s in path_blobs.get('f.txt', set()))}). "
        f"Cause : ``git log --raw`` sans ``-m`` supprime les diffs de merge -> un sha "
        f"atteste dont la 1re apparition est une resolution de merge est classe "
        f"``fabricated`` a tort par ``test_audit_shas_exist_in_file_history``."
    )


# --- #13100 : le rebaseline d'un orphelin par squash ne doit pas etre veto --
#
# Criteres 1+2 de #13100 : un bloc d'audit en indentation CANONIQUE 2/4/6 dont
# le git blob SHA a change (squash-merge) mais dont le content_sha est preserve
# doit se rebaseliner via `surgical_rebaseline`. `update_pair` a deja tranche
# is_noop=False (discrimination reachability #11919 : le recorded blob n'est pas
# ancetre de HEAD) ; la couche d'ecriture ne doit pas RE-veto un _shas_match
# content-only qui produisait le message trompeur « aucun bloc d'audit
# reconnu ». Controle positif : ce test est ROUGE avant le fix (#13100 : la
# cause exacte du refus), VERT apres.


def test_surgical_rebaseline_orphan_blob_content_same_appends():
    """Regression #13100 : entree 2/4/6 canonique, blob deplace (squash),
    contenu preserve -> APPEND d'une nouvelle entree, touches=1.

    Avant le fix, `_transform_audit_block` vetait via `_shas_match` (content
    egal -> « rien ne change ») et `surgical_rebaseline` renvoyait touched=0,
    lis par le caller comme « aucun bloc d'audit reconnu » alors que le header
    2/4/6 est parfaitement reconnu.
    """
    raw = (
        "- name: \"Search-11 Orphan\"\n"
        "  family: Search\n"
        "  python: X.ipynb\n"
        "  csharp: Y.ipynb\n"
        "  parity_level: native-both\n"
        "  audits:\n"
        "    - date: \"2026-08-24\"\n"
        "      by: previous-auditor\n"
        "      python_sha: e032816cc66591c490c447b6bf2bc440e428ce37\n"
        "      csharp_sha: 8a882e759991dc7a0af2c82376334eaeaa884a74\n"
        "      content_python_sha: f3921b23c094a8d16d6f990a4fb6bbae2d0375c5afd774b2626b344cda74acb2\n"
        "      content_csharp_sha: 098a90cd675c7f17f5b3c5debca7305463f1abd7d4788b1ab3a34fa91ad15df4\n"
    )
    # Rebaseline sur la paire : le git blob SHA a bouge (squash) MAIS le
    # content_sha est PRESERVE -- signature exacte de l'orphelin Search-11.
    new_entry = {
        "date": "2026-08-26",
        "by": "myia-po-2026:CoursIA",
        "python_sha": "3e30af4a17a0c88489539174e669b52619139133",
        "csharp_sha": "8a882e759991dc7a0af2c82376334eaeaa884a74",
        "content_python_sha": "f3921b23c094a8d16d6f990a4fb6bbae2d0375c5afd774b2626b344cda74acb2",
        "content_csharp_sha": "098a90cd675c7f17f5b3c5debca7305463f1abd7d4788b1ab3a34fa91ad15df4",
    }
    new_raw, touched = surgical_rebaseline(raw, {"Search-11 Orphan": new_entry})
    assert touched == 1, (
        "le rebaseline d'un orphelin par squash (blob deplace, contenu preserve) "
        "doit APPEND une nouvelle entree -- le bloc d'audit 2/4/6 est reconnu, "
        "mais le veto content-only de la couche d'ecriture le refusait "
        "(« aucun bloc d'audit reconnu » trompeur, #13100)."
    )
    assert "3e30af4a17a0c88489539174e669b52619139133" in new_raw, (
        "le nouveau python_sha (blob HEAD) doit apparaitre dans la nouvelle entree"
    )
    assert raw.count("    - date:") == 1, "fixture : une seule entree au depart"
    assert new_raw.count("    - date:") == 2, (
        "un rebaseline reel APPEND une entree, il ne remplace pas l'historique"
    )


def test_surgical_rebaseline_truly_identical_still_noop():
    """Garde anti-regression : une attestation STRICTEMENT identique (content
    ET git blobs egaux) doit RESTER un no-op byte-identical (#9399 critere 2)."""
    raw = (
        "- name: \"Search-11 Noop\"\n"
        "  family: Search\n"
        "  python: X.ipynb\n"
        "  csharp: Y.ipynb\n"
        "  parity_level: native-both\n"
        "  audits:\n"
        "    - date: \"2026-08-24\"\n"
        "      by: previous-auditor\n"
        "      python_sha: 3e30af4a17a0c88489539174e669b52619139133\n"
        "      csharp_sha: 8a882e759991dc7a0af2c82376334eaeaa884a74\n"
        "      content_python_sha: f3921b23c094a8d16d6f990a4fb6bbae2d0375c5afd774b2626b344cda74acb2\n"
        "      content_csharp_sha: 098a90cd675c7f17f5b3c5debca7305463f1abd7d4788b1ab3a34fa91ad15df4\n"
    )
    same = {
        "date": "2026-08-26",
        "by": "myia-po-2026:CoursIA",
        "python_sha": "3e30af4a17a0c88489539174e669b52619139133",
        "csharp_sha": "8a882e759991dc7a0af2c82376334eaeaa884a74",
        "content_python_sha": "f3921b23c094a8d16d6f990a4fb6bbae2d0375c5afd774b2626b344cda74acb2",
        "content_csharp_sha": "098a90cd675c7f17f5b3c5debca7305463f1abd7d4788b1ab3a34fa91ad15df4",
    }
    out, touched = surgical_rebaseline(raw, {"Search-11 Noop": same})
    assert touched == 0
    assert out == raw, "une attestation identique doit rester byte-identical (faux audit)"


# --- #14911 : file-per-audit (un fichier par audit) --------------------------
#
# #8542 Option C (file-per-pair) supprime la classe de conflit ENTRE paires ;
# mais DANS une paire, la liste append-only `audits:` gardait la classe de
# conflit : deux lanes qui appendent au MOEME bloc `audits:` de la meme paire
# touchent le meme point d'ancrage (la fin de la liste) -> `git` se plaint en
# CONFLIT meme si les dates/lanes different (controle negatif ci-dessous).
#
# #14911 retire cette classe : chaque audit migre vers
# `twin_pairs.d/<slug>/<date>-<lane>.yaml`. Deux lanes ecrivent des fichiers
# differentes -> le merge serveur n'a rien a fusionner (serveur-mergeable, pas
# besoin d'un merge driver). Les tests ci-dessous couvrent :
#   1. le reader (`load_registry`) reconstitue `audits:` depuis les fichiers
#      separes, pour la forme dict ET la forme liste ;
#   2. la migration `migrate_registry_files_per_audit` est sans perte de contenu
#      (comptage + contenu exact, y compris un `reason` qui contient un `"`) ;
#   3. le CONTROLE NEGATIF de conflit (ancienne forme -> CONFLIT) vs le cas
#      positif (nouvelle forme -> merge propre) : c'est la preuve que #14911
#      elimine la classe de conflit dans une paire.


def _write_pair_list_form(yaml_dir: Path, name: str, audits: list[dict]) -> None:
    """Ecrit un fichier de paire au format LISTE d'un dict (forme reelle du
    registre : tranches verbatim de l'ancien mono-fichier)."""
    slug = _slug(name)
    lines = [f'- name: "{name}"', "  family: Test", "  python: X.ipynb",
             "  csharp: Y.ipynb", "  parity_level: surface", "  audits:"]
    for a in audits:
        lines.append("    - date: " + f'"{a["date"]}"')
        lines.append(f"      by: {a['by']}")
        lines.append(f"      python_sha: {a['python_sha']}")
        lines.append(f"      csharp_sha: {a['csharp_sha']}")
    (yaml_dir / f"{slug}.yaml").write_text("\n".join(lines) + "\n", encoding="utf-8")


def _write_audit_file_direct(yaml_dir, name, audit):
    """Ecrit un fichier d'audit separe via _write_audit_file (helper reel)."""
    from check_twin_parity import _write_audit_file
    return _write_audit_file(yaml_dir, name, audit)


def test_load_registry_reconciles_audits_from_files_list_form(tmp_path):
    """Forme liste d'un dict, sans `audits:` inline : le reader reconstitue la
    liste depuis `<slug>/<date>-<lane>.yaml` (nouvelle forme file-per-audit)."""
    reg = tmp_path / "twin_pairs.d"
    reg.mkdir()
    slug = _slug("T-List-L1")
    (reg / f"{slug}.yaml").write_text(
        '- name: "T-List-L1"\n  family: Test\n  python: X.ipynb\n'
        "  csharp: Y.ipynb\n  parity_level: surface\n",
        encoding="utf-8",
    )
    audit = {"date": "2026-08-28", "by": "myia-po-2026:CoursIA",
             "python_sha": "a" * 40, "csharp_sha": "b" * 40}
    _write_audit_file_direct(reg, "T-List-L1", audit)
    pairs = load_registry(reg)
    assert len(pairs) == 1
    assert pairs[0]["audits"] == [audit], (
        "le reader DOIT reconstituer `audits:` depuis `<slug>/` meme pour la "
        "forme liste (sinon un registre migre renvoie des paires SANS audit -> "
        "check_pair/_latest_audit sortiraient NO_AUDIT)."
    )


def test_load_registry_reconciles_audits_from_files_dict_form(tmp_path):
    """Meme garantie pour la forme dict du fichier de paire."""
    reg = tmp_path / "twin_pairs.d"
    reg.mkdir()
    slug = _slug("T-Dict-L1")
    (reg / f"{slug}.yaml").write_text(
        "name: \"T-Dict-L1\"\nfamily: Test\npython: X.ipynb\n"
        "csharp: Y.ipynb\nparity_level: surface\n",
        encoding="utf-8",
    )
    audit = {"date": "2026-08-28", "by": "myia-po-2026:CoursIA",
             "python_sha": "c" * 40, "csharp_sha": "d" * 40}
    _write_audit_file_direct(reg, "T-Dict-L1", audit)
    pairs = load_registry(reg)
    assert len(pairs) == 1
    assert pairs[0]["audits"] == [audit]


def test_migrate_registry_files_per_audit_lossless(tmp_path):
    """Migration sans perte : les audits migrent de la forme `audits:` inline
    vers des fichiers separes, sans perte de contenu (comptage + exactitude).

    Inclut un `reason` contenant un `"` (l'echappement naïf `"..."` casse le
    YAML -> `_dump_audit_yaml` doit utiliser safe_dump)."""
    reg = tmp_path / "twin_pairs.d"
    reg.mkdir()
    _write_pair_list_form(reg, "T-Mig-1", [
        {"date": "2026-08-04", "by": "myia-po-2023:CoursIA",
         "python_sha": "1" * 40, "csharp_sha": "2" * 40,
         "reason": 'f-string avec un levier "prononce" (0.746) et [16] en tete'
                   " de branche"},
        {"date": "2026-08-05", "by": "myia-po-2026:CoursIA",
         "python_sha": "3" * 40, "csharp_sha": "4" * 40},
    ])
    _write_pair_list_form(reg, "T-Mig-2", [
        {"date": "2026-08-06", "by": "myia-po-2024:CoursIA",
         "python_sha": "5" * 40, "csharp_sha": "6" * 40},
    ])

    before = {p["name"]: list(p.get("audits") or []) for p in load_registry(reg)}
    import os
    res = migrate_registry_files_per_audit(reg)
    assert res["migrated"] == 2, f"2 paires traitees attendues, got {res['migrated']}"
    assert res["audits_moved"] == 3, f"3 audits a deplacer, got {res['audits_moved']}"

    # 3 fichiers d'audit au niveau 2, aucun `audits:`/`last_audit:` au niveau 1.
    n_audit = 0
    for root, _, fs in os.walk(str(reg)):
        for f in fs:
            if root != str(reg) and f.endswith(".yaml"):
                n_audit += 1
    assert n_audit == 3, f"3 fichiers d'audit attendus, got {n_audit}"
    for f in reg.glob("*.yaml"):
        if f.name.startswith("_"):
            continue
        txt = f.read_text(encoding="utf-8")
        assert "audits:" not in txt and "last_audit:" not in txt, (
            f"le fichier d'intention {f.name} doit etre STRIP de la liste audits"
        )

    after = {p["name"]: list(p.get("audits") or []) for p in load_registry(reg)}
    assert set(after) == set(before)
    for name in before:
        assert after[name] == before[name], (
            f"perte d'audit pour {name}: {len(before[name])} -> {len(after[name])}"
        )
    # Le reader relit des dicts stables (python_sha/csharp_sha presents).
    for p in load_registry(reg):
        assert p["audits"], f"paire {p['name']} sans audit reconstitue"
        for a in p["audits"]:
            assert a["python_sha"] and a["csharp_sha"]


def test_update_append_on_non_migrated_pair_preserves_history(tmp_path):
    """Anti-regression #14911 : un `--update` sur une paire NON migree doit
    migrer les audits inline existants vers des fichiers AVANT d'appender le
    nouvel audit, sans perdre l'historique (sinon `_strip_audits_from_yaml`
    retirerait la liste entiere et seuls les fichiers restants seraient relus).
    """
    reg = tmp_path / "twin_pairs.d"
    reg.mkdir()
    slug = _slug("T-Append-Inline")
    (reg / f"{slug}.yaml").write_text(
        '- name: "T-Append-Inline"\n  family: T\n  python: X.ipynb\n'
        "  csharp: Y.ipynb\n  parity_level: surface\n"
        "  audits:\n"
        f'    - date: "2026-08-01"\n      by: old1\n      python_sha: {"1" * 40}\n      csharp_sha: {"2" * 40}\n'
        f'    - date: "2026-08-02"\n      by: old2\n      python_sha: {"3" * 40}\n      csharp_sha: {"4" * 40}\n',
        encoding="utf-8",
    )
    raw = (reg / f"{slug}.yaml").read_text(encoding="utf-8")
    import check_twin_parity as ct
    inline = ct._inline_audits_of(raw)
    assert len(inline) == 2, "fixture : 2 audits inline"
    used = set()
    for idx, a in enumerate(inline, start=1):
        ct._write_audit_file(reg, "T-Append-Inline", a, used_names=used, index=idx)
    ct._write_audit_file(reg, "T-Append-Inline",
                         {"date": "2026-08-03", "by": "newlane",
                          "python_sha": "5" * 40, "csharp_sha": "6" * 40},
                         used_names=used, index=len(inline) + 1)
    (reg / f"{slug}.yaml").write_text(ct._strip_audits_from_yaml(raw), encoding="utf-8")

    p = next(x for x in load_registry(reg) if x["name"] == "T-Append-Inline")
    assert len(p["audits"]) == 3, (
        "les 2 audits inline doivent etre preserves + 1 appende = 3 (pas 1, "
        "sinon l'historique est perdu)."
    )
    latest = ct._latest_audit(p)
    assert latest["python_sha"] == "5" * 40, "le nouvel audit doit etre le plus recent"


def test_update_append_on_migrated_pair_goes_last(tmp_path):
    """Sur une paire deja migree (intention sans audits, fichiers 0001..000N),
    `--update` appende au slot suivant (000N+1) qui trie en DERNIER -> le nouvel
    audit devient `_latest_audit`."""
    reg = tmp_path / "twin_pairs.d"
    reg.mkdir()
    slug = _slug("T-Append-Migrated")
    import check_twin_parity as _ct
    d = _ct._audit_dir(reg, slug)
    d.mkdir(parents=True)
    for i in range(1, 4):
        _ct._write_audit_file(reg, "T-Append-Migrated",
                              {"date": f"2026-08-0{i}", "by": f"lane{i}",
                               "python_sha": chr(0x61 + i - 1) * 40,
                               "csharp_sha": "b" * 40}, index=i)
    (reg / f"{slug}.yaml").write_text(
        '- name: "T-Append-Migrated"\n  family: T\n  python: X.ipynb\n'
        "  csharp: Y.ipynb\n  parity_level: surface\n",
        encoding="utf-8",
    )
    # append sans index explicite (comme `--update` sur une paire migree)
    _ct._write_audit_file(reg, "T-Append-Migrated",
                          {"date": "2026-08-04", "by": "newlane",
                           "python_sha": "9" * 40, "csharp_sha": "9" * 40})
    p = next(x for x in load_registry(reg) if x["name"] == "T-Append-Migrated")
    assert len(p["audits"]) == 4
    assert _ct._latest_audit(p)["python_sha"] == "9" * 40, (
        "l'audit appende doit trier en dernier (index 0004 > 0003) et devenir "
        "le _latest_audit."
    )


@pytest.mark.parametrize("old_form", [True, False])
def test_two_lanes_conflict_class(tmp_path, old_form):
    """Controle de la classe de conflit DANS une paire.

    - old_form=True (ancienne forme, liste `audits:` inline) : deux lanes appendent
      chacune un audit a la fin de la MEME liste -> merge git CONFLICT (meme si les
      dates/lanes different : c'est le point d'ancrage, pas la cle, qui conflit).
    - old_form=False (nouvelle forme file-per-audit) : deux lanes ajoutent chacune
      un fichier `<date>-<lane>.yaml` DISTINCT -> merge git propre (serveur-mergeable,
      aucun driver unions requis).
    """
    import subprocess

    def _git(*args):
        return subprocess.run(["git", *args], cwd=tmp_path, capture_output=True,
                              text=True, encoding="utf-8", errors="replace")

    _git("init", "-q")
    _git("config", "user.email", "t@t")
    _git("config", "user.name", "t")
    _git("config", "commit.gpgsign", "false")
    # Portabilite CI : le nom de la branche initiale depend de init.defaultBranch
    # (system config Git-for-Windows = "main", runner ubuntu = compile "master").
    # Jamais coder "main" en dur -- decouvrir le nom (pattern l.1013).
    base_branch = _git("symbolic-ref", "--short", "HEAD").stdout.strip()

    slug = _slug("T-Conflit")
    pair_dir = tmp_path / "registry" / slug
    pair_dir.mkdir(parents=True)

    if old_form:
        # Fichier d'intention avec `audits:` inline (ancienne forme).
        pair_file = tmp_path / "registry" / f"{slug}.yaml"
        pair_file.write_text(
            '- name: "T-Conflit"\n  family: Test\n  python: X.ipynb\n'
            "  csharp: Y.ipynb\n  parity_level: surface\n"
            '  audits:\n    - date: "2026-08-01"\n      by: base\n'
            f"      python_sha: {'a' * 40}\n      csharp_sha: {'b' * 40}\n",
            encoding="utf-8",
        )
    else:
        # Fichier d'intention SANS audits + fichier d'audit de base.
        (tmp_path / "registry" / f"{slug}.yaml").write_text(
            '- name: "T-Conflit"\n  family: Test\n  python: X.ipynb\n'
            "  csharp: Y.ipynb\n  parity_level: surface\n",
            encoding="utf-8",
        )
        _write_audit_file_direct(tmp_path / "registry", "T-Conflit",
                                 {"date": "2026-08-01", "by": "base",
                                  "python_sha": "a" * 40, "csharp_sha": "b" * 40})

    _git("add", "-A")
    _git("commit", "-qm", "base")

    def _lane_append(branch, name, date, sha):
        _git("checkout", "-q", "-b", branch, base_branch)
        if old_form:
            with open(pair_file, "a", encoding="utf-8") as fh:
                fh.write(f'    - date: "{date}"\n      by: lane-{name}\n'
                         f"      python_sha: {sha}\n      csharp_sha: {sha}\n")
            _git("add", pair_file)
        else:
            _write_audit_file_direct(tmp_path / "registry", name,
                                     {"date": date, "by": f"lane-{name}",
                                      "python_sha": sha, "csharp_sha": sha})
            _git("add", "-A")
        _git("commit", "-qm", f"lane {name}")

    # Deux branches divergentes depuis BASE (main), chacune modifiant la MEME
    # paire (dans la meme region de queue pour l'ancienne forme ; deux fichiers
    # DISTINCTS pour la nouvelle).
    _lane_append("lane-A", "T-Conflit", "2026-08-04", "e" * 40)
    _lane_append("lane-B", "T-Conflit", "2026-08-05", "f" * 40)

    # Merge lane-A sur la branche de base : fast-forward (base = ancestor de
    # lane-A) -> pas de conflit. Puis merge lane-B : base = base+auditA,
    # lane-B = base+auditB, merge-base = BASE -> les DEUX branches ont modifie
    # la meme region de queue -> c'est LA la classe de conflit a prouver.
    _git("checkout", "-q", base_branch)
    r1 = _git("merge", "--no-edit", "lane-A")
    assert r1.returncode == 0, "premier merge (fast-forward) doit reussir"
    r2 = _git("merge", "--no-edit", "lane-B")
    if old_form:
        # ancien controle : le merge de deux appends au MEME bord de `audits:`
        # doit CONFLICTER (meme si les dates/lanes different -- c'est le point
        # d'ancrage, pas la cle, qui conflit).
        assert r2.returncode != 0, (
            "ancien controle : deux lanes appendant au meme bloc `audits:` de la "
            "meme paire doivent CONFLICTER (classe de conflit #14911)."
        )
    else:
        # nouvelle forme : deux lanes ecrivent des fichiers d'audit DISTINCTS
        # (<pair>/2026-08-04-lane-a.yaml vs <pair>/2026-08-05-lane-b.yaml) ->
        # le merge serveur n'a rien a fusionner -> pas de conflit.
        assert r2.returncode == 0, (
            "nouvelle forme : deux lanes ajoutant des fichiers d'audit DISTINCTS "
            "doivent se merger proprement (serveur-mergeable, aucun driver union)."
        )
        assert not (tmp_path / ".git" / "MERGE_HEAD").exists()

