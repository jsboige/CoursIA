#!/usr/bin/env python3
"""Acces agent au trousseau partage MyIA-Keys.kdbx.

Le coffre est distribue par le GDrive RooSync (`.shared-state/`), ou toutes les
machines du cluster le voient. Sa passphrase, elle, n'y est JAMAIS : elle vit
dans le gestionnaire d'identifiants Windows (DPAPI, par utilisateur), pose une
fois par machine.

C'est la seule propriete qui fait tenir le dispositif. Le coffre et sa clef
partagent aujourd'hui le meme Google Drive : le PDF de secours
`Emergency MyIA Keys.pdf` est lisible par quiconque lit le Drive qui porte
deja le `.kdbx`. Qui a le Drive a les deux moities. `doctor` le mesure et le
dit ; l'organe, lui, ne recopie jamais la passphrase sur un chemin partage.

REGLE CARDINALE -- aucune sous-commande n'imprime un secret par defaut.
Une valeur est soit *tuyautee* vers son consommateur (`gh-login`,
`--to-env-file`), soit montree *masquee* (`show`, `verify`). Une preuve de
provisionnement est un appel qui passe, jamais une valeur affichee.

Sous-commandes
    doctor      etat du dispositif : coffre, passphrase, outillage, co-localisation
    bootstrap   pose la passphrase dans le gestionnaire d'identifiants (une fois par machine)
    list        noms des entrees (JAMAIS les valeurs)
    show        une entree, masquee
    get         une valeur, vers un fichier .env gitignore
    gh-login    tuyaute un jeton directement dans `gh auth login --with-token`
    verify      les entrees attendues sont-elles la, et le jeton repond-il ?

Codes de sortie -- 0 succes / 1 defaut mesure / 2 impossible a mesurer.
Le 2 n'est PAS un feu vert : il dit que l'organe n'a pas pu conclure.
"""

from __future__ import annotations

import argparse
import json
import os
import platform
import re
import shutil
import subprocess
import sys
from pathlib import Path

EXIT_OK = 0
EXIT_DEFECT = 1
EXIT_UNKNOWN = 2

SERVICE = "MyIA-Keys"
DEFAULT_VAULT = r"G:\Mon Drive\Synchronisation\RooSync\.shared-state\MyIA-Keys.kdbx"
DEFAULT_EMERGENCY_PDF = r"G:\Mon Drive\MyIA\IA\Emergency MyIA Keys.pdf"
DEFAULT_GROUP = "Agents"

# Entrees attendues, par login GitHub. La valeur est le login que le jeton DOIT
# rendre -- c'est ce qui distingue un jeton provisionne d'un jeton qui MARCHE.
#
# `MyIA-Web1` figure ici bien que `docs/reference/cluster-agents.md` ne le liste
# pas : ce document decrit les machines qui portent des grains **CoursIA**, et
# web1 travaille sur `roo-extensions`. Ce n'est pas la bonne population pour ce
# trousseau -- la population pertinente est « les machines qui doivent ouvrir le
# coffre », et web1 en est une (compte GitHub cree le 2026-04-17, entree
# `github web1` dans le coffre, dashboard machine actif).
EXPECTED_GH = {
    "myia-ai-01": "myia-ai-01",
    "myia-po-2023": "myia-po-2023",
    "myia-po-2024": "myia-po-2024",
    "myia-po-2025": "myia-po-2025",
    "myia-po-2026": "myia-po-2026",
    "myia-po-2027": "myia-po-2027",
    "MyIA-Web1": "MyIA-Web1",
}

# Les machines qui doivent BOOTSTRAPPER, c'est-a-dire detenir la passphrase dans
# leur propre gestionnaire d'identifiants. Distinct de EXPECTED_GH : une machine
# doit ouvrir le coffre meme si son compte GitHub n'existe pas encore.
#
# C'est le denominateur du critere de retrait du PDF de secours : tant que les
# N machines n'ont pas bootstrappe, le PDF est leur SEULE source -- le supprimer
# rendrait le coffre inouvrable chez elles (DPAPI n'est ni exportable, ni
# transferable d'une machine a l'autre).
FLEET_MACHINES = (
    "myia-ai-01",
    "myia-po-2023",
    "myia-po-2024",
    "myia-po-2025",
    "myia-po-2026",
    "myia-po-2027",
    "myia-web1",
)


def machine_id() -> str:
    for var in ("ROOSYNC_MACHINE_ID", "MYIA_MACHINE_ID"):
        val = os.environ.get(var)
        if val:
            return val.strip()
    return platform.node().strip().lower()


def vault_path() -> Path:
    return Path(os.environ.get("MYIA_KEYS_VAULT", DEFAULT_VAULT))


# Un coffre de comptes melange DEUX natures de secret, et aucune ne s'annonce :
# le mot de passe de CONNEXION du compte, et le JETON d'API. `gh` n'accepte que
# le second ; lui donner le premier produit un refus d'authentification que rien
# ne relie a sa cause. Mesure du 2026-09-22 sur MyIA-Keys : les 7 entrees
# `github *` portent des mots de passe generes de 20 caracteres, zero jeton.
GH_TOKEN_RE = re.compile(r"^(gh[pousr]_[A-Za-z0-9]{30,}|github_pat_[A-Za-z0-9_]{40,})$")


def secret_kind(value: str | None) -> str:
    """'vide' | 'jeton' | 'mot de passe' -- tranche sur la FORME, jamais sur le
    nom de l'entree : un titre ne prouve pas ce qu'il contient."""
    if not value:
        return "vide"
    if GH_TOKEN_RE.match(value.strip()):
        return "jeton"
    return "mot de passe"


def entry_key(entry) -> tuple[str, str]:
    """Les deux noms sous lesquels une entree peut etre demandee : son titre
    ('github ai-01') et son username ('myia-ai-01'). Chercher par le seul titre
    rendait `verify` faux -- il annoncait 0/6 sur un coffre qui en portait 6."""
    return ((entry.title or "").strip().lower(), (entry.username or "").strip().lower())


# Sel public et fixe : il n'apporte PAS de secret (il est dans le source), il
# separe les domaines. Ce qui protege ici, c'est le cout par essai.
_FP_SALT = b"MyIA-Keys/agent_keyring/fingerprint/v1"
_FP_ROUNDS = 600_000  # recommandation OWASP 2023 pour PBKDF2-HMAC-SHA256


def fingerprint(value: str) -> str:
    """Empreinte NON reversible et COUTEUSE a forcer, pour la passphrase.

    Deux decisions, prises contre deux alertes CodeQL distinctes, et dans les
    deux cas parce que l'outil visait juste sur le fond :

    **1. Pas de queue de valeur.** Une version anterieure publiait les 4
    derniers caracteres -- convention des fournisseurs d'API, ou l'on recoupe
    une queue avec leur interface. Un coffre KeePass n'expose rien de tel : on
    payait une fuite sans rien acheter.

    **2. Pas de sha256 nu.** `py/weak-sensitive-data-hashing` a signale qu'un
    hash rapide est inadapte a un secret -- et cette empreinte est **publiee sur
    un dashboard**, donc elle offre a un attaquant un oracle hors-ligne : il
    devine, il hache, il compare. Sur une passphrase a haute entropie le risque
    est theorique ; sur un secret faible il ne l'est pas, et un outil generique
    ne choisit pas ce qu'on lui donne.

    PBKDF2-HMAC-SHA256, 600 000 tours : deterministe (donc deux machines
    peuvent comparer), mais ~0,3 s par essai -- ce qui rend l'oracle inutile
    sans rien couter a l'usage, puisqu'on l'appelle une fois par `doctor`.

    Le sel est public et fixe : il DOIT l'etre pour que la comparaison
    cross-machine fonctionne. Il ne cache rien, il separe les domaines.
    """
    import hashlib

    if not value:
        return "<vide>"
    digest = hashlib.pbkdf2_hmac("sha256", value.encode("utf-8"), _FP_SALT, _FP_ROUNDS)
    return f"<{len(value)} car.> pbkdf2:{digest.hex()[:12]}"


# --------------------------------------------------------------------------
# passphrase : gestionnaire d'identifiants uniquement
# --------------------------------------------------------------------------

def _keyring():
    try:
        import keyring
    except ImportError:
        print("UNKNOWN: module `keyring` absent -- `python -m pip install keyring`", file=sys.stderr)
        raise SystemExit(EXIT_UNKNOWN)
    return keyring


def read_passphrase() -> str | None:
    kr = _keyring()
    try:
        return kr.get_password(SERVICE, machine_id())
    except Exception as exc:  # backend indisponible
        print(f"UNKNOWN: gestionnaire d'identifiants illisible : {exc}", file=sys.stderr)
        raise SystemExit(EXIT_UNKNOWN)


def write_passphrase(value: str) -> None:
    _keyring().set_password(SERVICE, machine_id(), value)


# --------------------------------------------------------------------------
# coffre
# --------------------------------------------------------------------------

def open_vault(passphrase: str | None = None, quiet: bool = False):
    """Ouvre le coffre. `quiet` sert la boucle d'essai du bootstrap, ou un echec
    est l'issue attendue de presque tous les candidats et n'est pas un defaut."""
    try:
        from pykeepass import PyKeePass
    except ImportError:
        print("UNKNOWN: module `pykeepass` absent -- `python -m pip install pykeepass`", file=sys.stderr)
        raise SystemExit(EXIT_UNKNOWN)

    path = vault_path()
    if not path.is_file():
        print(f"UNKNOWN: coffre introuvable : {path}", file=sys.stderr)
        print("  (GDrive non monte ? synchronisation en cours ?)", file=sys.stderr)
        raise SystemExit(EXIT_UNKNOWN)

    if passphrase is None:
        passphrase = read_passphrase()
    if not passphrase:
        if quiet:
            raise SystemExit(EXIT_DEFECT)
        print(f"DEFECT: aucune passphrase posee pour la machine '{machine_id()}'.", file=sys.stderr)
        print("  Poser une fois :  python scripts/secrets/agent_keyring.py bootstrap", file=sys.stderr)
        raise SystemExit(EXIT_DEFECT)

    try:
        return PyKeePass(str(path), password=passphrase)
    except Exception as exc:
        # Ne jamais renvoyer la passphrase dans le message.
        if not quiet:
            print(f"DEFECT: ouverture du coffre refusee ({type(exc).__name__}).", file=sys.stderr)
        raise SystemExit(EXIT_DEFECT)


def iter_entries(kp, group: str | None):
    entries = kp.entries
    if group:
        entries = [e for e in entries if e.group and e.group.name == group]
    return sorted(entries, key=lambda e: (e.title or "").lower())


def find_entry(kp, title: str, group: str | None):
    wanted = title.strip().lower()
    hits = [e for e in iter_entries(kp, group) if wanted in entry_key(e)]
    if not hits and group:
        hits = [e for e in iter_entries(kp, None) if wanted in entry_key(e)]
    return hits[0] if hits else None


# --------------------------------------------------------------------------
# bootstrap
# --------------------------------------------------------------------------

def pdf_candidates(pdf: Path) -> list[str]:
    """Chaines plausibles extraites du PDF de secours.

    Rien de ce qui sort d'ici n'est imprime : les candidats sont essayes
    contre le coffre et seul le verdict est rendu.
    """
    try:
        from pypdf import PdfReader
    except ImportError:
        print("UNKNOWN: module `pypdf` absent -- `python -m pip install pypdf`", file=sys.stderr)
        raise SystemExit(EXIT_UNKNOWN)

    import html
    import re

    block_re = re.compile(r"</?(p|div|br|li|tr|h[1-6])\b[^>]*>", re.I)

    def strip_markup(text: str) -> list[str]:
        """Le champ /RC d'une annotation est du rich text XHTML. Deux lectures
        sont possibles et on ne peut PAS deviner laquelle est la bonne, donc on
        rend les DEUX :

        A. balises de BLOC -> saut de ligne, balises INLINE -> supprimees.
           PDFgear decoupe une valeur en *runs* de style : remplacer TOUTE
           balise par un saut de ligne coupe la passphrase en morceaux. C'est
           le defaut qui a fait echouer le second essai (74 candidats, aucun
           bon) -- la variante B seule, qui etait le fix du premier.
        B. toute balise -> separateur, pour le cas ou deux champs voisins sont
           colles sans balise de bloc entre eux.
        """
        a = html.unescape(re.sub(r"<[^>]+>", "", block_re.sub("\n", text)))
        b = html.unescape(re.sub(r"<[^>]+>", "\n", text))
        return [a, b]

    chunks: list[str] = []
    reader = PdfReader(str(pdf))
    for page in reader.pages:
        try:
            chunks.append(page.extract_text() or "")
        except Exception:
            pass
        # PDFgear ecrit en annotation, pas dans le flux de page.
        try:
            for annot in (page.get("/Annots") or []):
                obj = annot.get_object()
                for key in ("/Contents", "/RC", "/V"):
                    val = obj.get(key)
                    if isinstance(val, str):
                        chunks.extend(strip_markup(val))
        except Exception:
            pass

    seen: set[str] = set()
    out: list[str] = []

    def push(value: str) -> None:
        value = value.strip().strip('"').strip("'").strip()
        if 6 <= len(value) <= 256 and value not in seen:
            seen.add(value)
            out.append(value)

    # Ordre = probabilite decroissante. Chaque essai coute un KDF Argon2
    # (~1 s) : un ordre au hasard transforme un bootstrap en attente de
    # plusieurs minutes, ce qu'on a mesure au premier passage.
    labelled, lines, tokens = [], [], []
    label_re = re.compile(r"(pass(phrase|word)?|master|mot de passe|clef|cle)\s*[:=]\s*(?P<v>.+)", re.I)

    def variants(value: str):
        """Un PDF porte des espaces insecables et des guillemets typographiques
        que le clavier n'a jamais produits : une comparaison stricte echoue sur
        un caractere invisible. On essaie la forme brute ET la normalisee."""
        yield value
        norm = value.replace("\xa0", " ").replace("\u202f", " ")
        norm = norm.replace("\u2018", "'").replace("\u2019", "'")
        norm = norm.replace("\u201c", '"').replace("\u201d", '"')
        if norm != value:
            yield norm
        collapsed = re.sub(r"\s+", " ", norm).strip()
        if collapsed != norm:
            yield collapsed

    for chunk in chunks:
        for raw in chunk.splitlines():
            m = label_re.search(raw)
            if m:
                labelled.append(m.group("v"))
            lines.append(raw)
        # Le chunk entier : une passphrase a espaces peut n'occuper qu'une
        # annotation, sans aucun saut de ligne autour d'elle.
        lines.append(chunk)
    for chunk in chunks:
        tokens.extend(chunk.split())

    for value in labelled + lines + tokens:
        for form in variants(value):
            push(form)
    return out


def cmd_bootstrap(args) -> int:
    if read_passphrase() and not args.force:
        print(f"OK  passphrase deja posee pour '{machine_id()}'. `--force` pour la remplacer.")
        return EXIT_OK

    candidates: list[str] = []
    source = ""
    if args.from_stdin:
        source = "stdin"
        data = sys.stdin.read().strip()
        if data:
            candidates = [data]
    else:
        pdf = Path(args.from_pdf or DEFAULT_EMERGENCY_PDF)
        source = str(pdf)
        if not pdf.is_file():
            print(f"UNKNOWN: PDF de secours introuvable : {pdf}", file=sys.stderr)
            return EXIT_UNKNOWN
        candidates = pdf_candidates(pdf)

    if not candidates:
        print(f"DEFECT: aucune chaine exploitable dans {source}.", file=sys.stderr)
        return EXIT_DEFECT

    # La validation est l'ouverture reelle du coffre : on ne stocke jamais une
    # passphrase qu'on n'a pas vue fonctionner.
    print(f"{len(candidates)} candidat(s) a essayer (~1 s chacun, KDF Argon2)...", file=sys.stderr)
    for idx, cand in enumerate(candidates, 1):
        if idx % 25 == 0:
            print(f"  ... {idx}/{len(candidates)}", file=sys.stderr)
        try:
            open_vault(cand, quiet=True)
        except SystemExit:
            continue
        write_passphrase(cand)
        print(f"OK  passphrase validee contre le coffre et posee pour '{machine_id()}'.")
        print(f"    source    : {source}")
        print(f"    empreinte : {fingerprint(cand)}")
        print(f"    stockage  : gestionnaire d'identifiants Windows, service '{SERVICE}'")
        print("    la valeur n'a ete ni imprimee, ni ecrite sur disque, ni mise en variable d'environnement.")
        return EXIT_OK

    print(f"DEFECT: aucun des {len(candidates)} candidats de {source} n'ouvre le coffre.", file=sys.stderr)
    print("  Le PDF porte peut-etre la passphrase en image (scan) plutot qu'en texte.", file=sys.stderr)
    print("  Repli :  <commande qui l'emet> | python scripts/secrets/agent_keyring.py bootstrap --from-stdin", file=sys.stderr)
    return EXIT_DEFECT


# --------------------------------------------------------------------------
# lectures
# --------------------------------------------------------------------------

def cmd_list(args) -> int:
    kp = open_vault()
    entries = iter_entries(kp, args.group)
    if args.json:
        print(json.dumps([{"title": e.title, "username": e.username,
                           "group": e.group.name if e.group else None} for e in entries], indent=2))
        return EXIT_OK
    if not entries:
        print(f"DEFECT: aucune entree dans le groupe '{args.group}'.", file=sys.stderr)
        return EXIT_DEFECT
    print(f"{len(entries)} entree(s) -- groupe '{args.group or '*'}' (valeurs NON affichees)")
    for e in entries:
        print(f"  {e.title:<32} user={e.username or '-'}")
    return EXIT_OK


def cmd_show(args) -> int:
    kp = open_vault()
    entry = find_entry(kp, args.entry, args.group)
    if entry is None:
        print(f"DEFECT: entree '{args.entry}' absente.", file=sys.stderr)
        return EXIT_DEFECT
    print(f"titre     : {entry.title}")
    print(f"groupe    : {entry.group.name if entry.group else '-'}")
    print(f"user      : {entry.username or '-'}")
    print(f"url       : {entry.url or '-'}")
    print(f"password  : {secret_kind(entry.password)}")
    if entry.mtime:
        print(f"modifiee  : {entry.mtime.isoformat()}")
    return EXIT_OK


def _git_tracked(path: Path) -> bool:
    try:
        res = subprocess.run(["git", "ls-files", "--error-unmatch", str(path)],
                             capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=15)
        return res.returncode == 0
    except Exception:
        return False


def _git_ignored(path: Path) -> bool | None:
    """True/False si git tranche, None si on n'a pas pu mesurer.

    « Non suivi » ne suffit PAS : un fichier neuf n'est pas suivi et reste
    parfaitement stageable. Ce qui protege, c'est d'etre *ignore*. Et
    l'ignorance peut venir de `.git/info/exclude`, qui est LOCAL au clone et
    non versionne -- donc vraie ici et fausse sur la machine d'a cote.
    """
    try:
        res = subprocess.run(["git", "check-ignore", "-q", str(path)],
                             capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=15)
        if res.returncode in (0, 1):
            return res.returncode == 0
        return None
    except Exception:
        return None


def cmd_get(args) -> int:
    kp = open_vault()
    entry = find_entry(kp, args.entry, args.group)
    if entry is None:
        print(f"DEFECT: entree '{args.entry}' absente.", file=sys.stderr)
        return EXIT_DEFECT
    value = {"password": entry.password, "username": entry.username, "url": entry.url}.get(args.field)
    if not value:
        print(f"DEFECT: champ '{args.field}' vide sur '{entry.title}'.", file=sys.stderr)
        return EXIT_DEFECT

    target = Path(args.to_env_file)
    if _git_tracked(target):
        print(f"DEFECT: {target} est SUIVI PAR GIT -- refus d'y ecrire un secret.", file=sys.stderr)
        return EXIT_DEFECT
    ignored = _git_ignored(target)
    if ignored is None:
        print(f"UNKNOWN: impossible de savoir si {target} est ignore par git -- refus fail-closed.", file=sys.stderr)
        return EXIT_UNKNOWN
    if not ignored and not args.allow_unignored:
        print(f"DEFECT: {target} n'est PAS ignore par git -- refus d'y ecrire un secret.", file=sys.stderr)
        print("  Un fichier neuf n'est pas 'suivi', mais il reste stageable par `git add .`.", file=sys.stderr)
        print("  Ajouter le chemin au .gitignore VERSIONNE (pas .git/info/exclude, qui est local", file=sys.stderr)
        print("  a ce clone et laisse les autres machines sans protection), ou --allow-unignored.", file=sys.stderr)
        return EXIT_DEFECT

    key = args.env_key or f"{entry.title.upper().replace('-', '_')}_TOKEN"
    target.parent.mkdir(parents=True, exist_ok=True)
    lines = []
    if target.exists():
        lines = [l for l in target.read_text(encoding="utf-8").splitlines()
                 if not l.startswith(f"{key}=")]
    lines.append(f"{key}={value}")
    # UTF-8 sans BOM : les parsers .env cassent dessus.
    target.write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
    print(f"OK  '{entry.title}'.{args.field} -> {target} sous la cle {key}")
    print(f"    empreinte : {fingerprint(value)}  (valeur non imprimee)")
    return EXIT_OK


def cmd_gh_login(args) -> int:
    """Tuyaute le jeton dans `gh` sans qu'il touche ni disque ni terminal."""
    if not shutil.which("gh"):
        print("UNKNOWN: `gh` introuvable dans le PATH.", file=sys.stderr)
        return EXIT_UNKNOWN
    kp = open_vault()
    entry = find_entry(kp, args.entry, args.group)
    if entry is None:
        print(f"DEFECT: entree '{args.entry}' absente.", file=sys.stderr)
        return EXIT_DEFECT
    token = entry.password
    if not token:
        print(f"DEFECT: pas de jeton sur '{entry.title}'.", file=sys.stderr)
        return EXIT_DEFECT

    kind = secret_kind(token)
    if kind != "jeton":
        print(f"DEFECT: le secret de '{entry.title}' est un {kind}, pas un jeton d'API.",
              file=sys.stderr)
        print("  `gh auth login --with-token` refuserait, avec un message sans rapport", file=sys.stderr)
        print("  visible avec la cause. Emettre un PAT pour ce compte et le ranger ici.", file=sys.stderr)
        return EXIT_DEFECT


    res = subprocess.run(["gh", "auth", "login", "--hostname", "github.com", "--with-token"],
                         input=token, capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=90)
    if res.returncode != 0:
        print(f"DEFECT: `gh auth login` a refuse le jeton de '{entry.title}'.", file=sys.stderr)
        print(f"  {res.stderr.strip()[:300]}", file=sys.stderr)
        return EXIT_DEFECT

    who = subprocess.run(["gh", "api", "user", "--jq", ".login"],
                         capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=60,
                         env={**os.environ, "GH_TOKEN": token})
    login = who.stdout.strip()
    print(f"OK  jeton de '{entry.title}' accepte -- `gh api user` rend : {login or '?'}")
    # Resolution par titre OU username : le coffre titre 'github ai-01'
    # quand la clef attendue est 'myia-ai-01'. Chercher par le seul titre
    # rendait la verification de login MUETTE (expected=None -> aucun
    # controle), soit le meme defaut que celui corrige dans `verify`.
    expected = args.account
    if not expected:
        for key in entry_key(entry):
            for name, login in EXPECTED_GH.items():
                if key == name.lower():
                    expected = login
                    break
            if expected:
                break
    if expected and login and login.lower() != expected.lower():
        print(f"DEFECT: login attendu '{expected}', obtenu '{login}'.", file=sys.stderr)
        return EXIT_DEFECT
    return EXIT_OK


# --------------------------------------------------------------------------
# doctor / verify
# --------------------------------------------------------------------------

def cmd_doctor(args) -> int:
    defects = 0
    print(f"machine   : {machine_id()}")

    path = vault_path()
    if path.is_file():
        print(f"coffre    : OK  {path}  ({path.stat().st_size} octets)")
    else:
        print(f"coffre    : ABSENT  {path}")
        defects += 1

    for mod in ("pykeepass", "keyring", "pypdf"):
        try:
            __import__(mod)
            print(f"outil     : OK  {mod}")
        except ImportError:
            print(f"outil     : ABSENT  {mod}  -- `python -m pip install {mod}`")
            defects += 1

    try:
        stored = read_passphrase()
    except SystemExit:
        stored = None
    has = bool(stored)
    print(f"passphrase: {'OK  posee dans le gestionnaire d identifiants' if has else 'ABSENTE  -- lancer `bootstrap`'}")
    if has:
        # L'empreinte EST l'organe du critere de retrait du PDF de secours.
        # DPAPI n'etant ni exportable ni interrogeable a distance, aucune
        # machine ne peut verifier qu'une AUTRE a bootstrappe. Ce qui circule,
        # c'est ce sha256 tronque : non reversible, donc publiable sur un
        # dashboard, et suffisant pour repondre a la seule question qui compte
        # -- les N machines portent-elles la MEME passphrase ?
        #
        # Sans cette ligne, le critere « toutes les machines ont bootstrappe »
        # ne serait pas mesurable, et « tout le monde est enregistre » resterait
        # une affirmation invérifiable.
        print(f"empreinte : {fingerprint(stored)}")
        print(f"            a comparer aux {len(FLEET_MACHINES)} machines : "
              + ", ".join(FLEET_MACHINES))
    if not has:
        defects += 1

    # Co-localisation coffre / clef de secours : ce n'est pas un defaut de
    # l'organe, c'est une propriete du rangement -- on la mesure et on la dit.
    pdf = Path(os.environ.get("MYIA_EMERGENCY_PDF", DEFAULT_EMERGENCY_PDF))
    if pdf.is_file() and path.is_file():
        try:
            same = pdf.resolve().drive.lower() == path.resolve().drive.lower()
        except Exception:
            same = False
        if same:
            print()
            print("ATTENTION -- le coffre et sa clef de secours sont sur le MEME volume :")
            print(f"    coffre : {path}")
            print(f"    clef   : {pdf}")
            print("  Qui lit ce volume tient les deux moities. L'organe ne recopie jamais la")
            print("  passphrase sur un chemin partage, mais il ne peut pas deplacer le PDF :")
            print("  c'est un arbitrage de rangement, pas un geste d'agent.")

    if defects:
        print(f"\n{defects} defaut(s).")
        return EXIT_DEFECT
    print("\nDispositif operationnel.")
    return EXIT_OK


def cmd_verify(args) -> int:
    kp = open_vault()
    entries = list(iter_entries(kp, args.group))
    index: dict[str, object] = {}
    for e in entries:
        for key in entry_key(e):
            if key:
                index.setdefault(key, e)

    missing, present, unusable = [], [], []
    for name in EXPECTED_GH:
        entry = index.get(name.lower())
        if entry is None:
            missing.append(name)
            continue
        present.append(name)
        kind = secret_kind(entry.password)
        if kind != "jeton":
            unusable.append((name, kind))
        print(f"  {name:<16} present   entree='{entry.title}'  secret={kind}")
    for name in missing:
        print(f"  {name:<16} ABSENT du coffre")

    print(f"\n{len(present)}/{len(EXPECTED_GH)} entree(s) attendue(s) presente(s).")
    if missing:
        print("Manquantes : " + ", ".join(missing))
    if unusable:
        print("\nPresentes mais INUTILISABLES pour `gh` -- un mot de passe de compte")
        print("n'est pas un jeton d'API, et `gh auth login --with-token` le refuse :")
        for name, kind in unusable:
            print(f"  {name:<16} secret={kind}")
        print("Emettre un PAT par compte (scopes minimaux) et le ranger dans son entree.")
    return EXIT_DEFECT if (missing or unusable) else EXIT_OK


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--group", default=DEFAULT_GROUP, help=f"groupe du coffre (defaut: {DEFAULT_GROUP})")
    sub = ap.add_subparsers(dest="cmd", required=True)

    sub.add_parser("doctor").set_defaults(func=cmd_doctor)

    b = sub.add_parser("bootstrap", help="poser la passphrase (une fois par machine)")
    src = b.add_mutually_exclusive_group()
    src.add_argument("--from-pdf", metavar="PATH", help=f"PDF de secours (defaut: {DEFAULT_EMERGENCY_PDF})")
    src.add_argument("--from-stdin", action="store_true", help="lire la passphrase sur stdin")
    b.add_argument("--force", action="store_true", help="remplacer une passphrase deja posee")
    b.set_defaults(func=cmd_bootstrap)

    l = sub.add_parser("list", help="noms des entrees, jamais les valeurs")
    l.add_argument("--json", action="store_true")
    l.set_defaults(func=cmd_list)

    s = sub.add_parser("show", help="une entree, masquee")
    s.add_argument("entry")
    s.set_defaults(func=cmd_show)

    g = sub.add_parser("get", help="ecrire une valeur dans un .env gitignore")
    g.add_argument("entry")
    g.add_argument("--field", default="password", choices=["password", "username", "url"])
    g.add_argument("--to-env-file", required=True)
    g.add_argument("--env-key")
    g.add_argument("--allow-unignored", action="store_true",
                   help="ecrire meme si la cible n'est pas ignoree par git (a eviter)")
    g.set_defaults(func=cmd_get)

    gh = sub.add_parser("gh-login", help="tuyauter un jeton dans `gh auth login --with-token`")
    gh.add_argument("entry")
    gh.add_argument("--account", help="login GitHub attendu en retour")
    gh.set_defaults(func=cmd_gh_login)

    sub.add_parser("verify", help="les entrees attendues sont-elles la ?").set_defaults(func=cmd_verify)

    args = ap.parse_args()
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
