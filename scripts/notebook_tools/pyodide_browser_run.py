"""Execute des carnets dans un site JupyterLite construit et rendre la preuve.

Ce script sert la mesure du pli 2.1 de l'Epic #27543 : des carnets
selectionnes par le critere d'eligibilite sont reellement executes dans un
navigateur, contre le noyau Pyodide, et le resultat est rendu sous forme de
sorties de cellules, d'etat (succes ou echec) et de capture d'ecran.

Il ne simule rien : la mesure vient du noyau Pyodide qui repond dans la page.
Le site est servi en local par un serveur HTTP trivial ; aucune donnee ne
sort de la machine.

Trois reglages du pilotage, tous appris a l'usage :

- le declenchement passe par le **menu « Run » puis « Run All Cells »** ;
  l'API de commandes (`window.jupyterapp`) n'est pas exposee par JupyterLite ;
- la fin d'execution se lit sur le **compteur d'execution** de chaque cellule
  de code (`[n]:`) et sur la stabilite des sorties, pas sur une horloge ;
- les sorties se lisent par ``textContent`` : ``innerText`` rend vide la
  sortie d'une cellule hors champ, ce qui ferait croire a un carnet muet.

Usage :

    python scripts/notebook_tools/pyodide_browser_run.py \\
        --site .tmp/lite-site/_output \\
        --lot .tmp/lot.json \\
        --out .tmp/executions
"""

from __future__ import annotations

import argparse
import contextlib
import http.server
import json
import re
import socket
import socketserver
import threading
import time
from pathlib import Path
from typing import Any, Dict, Iterator, List, Optional, Sequence

# Un chemin de machine ou un port ephemere dans une preuve publique, c'est
# l'etat de la machine qui a produit la mesure, pas la mesure. Les purges
# ci-dessous sont appliquees au moment de l'ecriture du rapport.
PORT_LOCAL = re.compile(r"(?:127\.0\.0\.1|localhost|\[::1\]):\d+")
NOYAU = re.compile(r"ws://[^\s/]+/api/kernels/[0-9a-fA-F-]+")
UUID = re.compile(
    r"[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}"
)


class QuietHandler(http.server.SimpleHTTPRequestHandler):
    """Serveur HTTP sans journal (le journal polluerait la mesure)."""

    def log_message(self, format: str, *args: Any) -> None:  # noqa: A002
        return


def racine_depot() -> Path:
    """Racine du depot, deduite de l'emplacement du script."""
    return Path(__file__).resolve().parents[2]


def chemin_relatif(chemin: Path, racine: Path) -> str:
    """Chemin exprime depuis la racine du depot, en POSIX.

    Un site construit hors du clone (le cas habituel : le site est un
    artefact de travail, pas une versionnee) est reduit au nom de son
    dossier : la preuve ne doit jamais porter l'arborescence de la machine
    qui l'a produite.
    """
    try:
        return chemin.resolve().relative_to(racine.resolve()).as_posix()
    except ValueError:
        return chemin.resolve().name


def rediger(ligne: str) -> str:
    """Retire les ports locaux et les identifiants de noyau d'une ligne de journal."""
    ligne = NOYAU.sub("ws://<hote>/api/kernels/<id>", ligne)
    ligne = PORT_LOCAL.sub("<hote-local>", ligne)
    ligne = UUID.sub("<uuid>", ligne)
    return ligne


def filtrer_console(journal: Sequence[str]) -> List[str]:
    """Ne garde que les erreurs et les avertissements, expurges.

    Le journal complet du navigateur est un bruit de chantier : il porte
    les ports du serveur local et les identifiants de noyau, qui sont des
    etats de la machine, pas de la preuve d'execution.
    """
    garde: List[str] = []
    for entree in journal:
        typ = entree.split(":", 1)[0].strip().lower()
        if typ not in ("error", "warning", "warn"):
            continue
        garde.append(rediger(entree))
    return garde


def url_de_page(nom: str) -> str:
    """URL de la page servie, sans l'hote ni le port de la machine."""
    return "/lab/index.html?path=%s" % nom


def lire_lot(chemin: Path) -> List[Dict[str, Any]]:
    """Carnets d'un fichier de lot (JSON), dans l'ordre du lot."""
    with open(chemin, encoding="utf-8") as fh:
        lot = json.load(fh)
    return list(lot["carnets"])


def agreger(resultats: Sequence[Dict[str, Any]]) -> List[Dict[str, Any]]:
    """Une ligne de synthese par carnet.

    Le rapport et le JSON portent la meme synthese : elle est calculee une
    seule fois, ici, et les deux la consomment.
    """
    lignes: List[Dict[str, Any]] = []
    for r in resultats:
        lignes.append({
            "carnet": r.get("carnet", ""),
            "cellules_code": r.get("cellules_code", 0),
            "cellules_executees": r.get("cellules_executees", 0),
            "cellules_avec_sortie": r.get("cellules_avec_sortie", 0),
            "erreurs": len(r.get("erreurs", [])),
            "duree_s": r.get("duree_s", 0),
            "temps_premier_resultat_s": r.get("temps_premier_resultat_s"),
            "succes": bool(r.get("succes")),
        })
    return lignes


@contextlib.contextmanager
def serve(directory: Path) -> Iterator[str]:
    """Sert un repertoire en local sur un port libre."""
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
        sock.bind(("127.0.0.1", 0))
        port = int(sock.getsockname()[1])

    class Handler(QuietHandler):
        def __init__(self, *args: Any, **kwargs: Any) -> None:
            super().__init__(*args, directory=str(directory), **kwargs)

    socketserver.TCPServer.allow_reuse_address = True
    with socketserver.TCPServer(("127.0.0.1", port), Handler) as httpd:
        thread = threading.Thread(target=httpd.serve_forever, daemon=True)
        thread.start()
        try:
            yield "http://127.0.0.1:%d" % port
        finally:
            httpd.shutdown()


def trigger_run_all(page: Any) -> str:
    """Declenche « Run All Cells » par le menu de l'interface."""
    try:
        page.locator(".lm-MenuBar-itemLabel:text-is(\"Run\")").first.click(timeout=15000)
    except Exception:
        page.locator("text=Run").first.click(timeout=15000)
    page.wait_for_timeout(1000)
    try:
        page.get_by_text("Run All Cells", exact=True).first.click(timeout=15000)
        return "menu Run > Run All Cells"
    except Exception:
        page.locator("[data-command=\"notebook:run-all-cells\"]").first.click(timeout=15000)
        return "commande notebook:run-all-cells"


def read_cells(page: Any) -> List[Dict[str, Any]]:
    """Etat de chaque cellule : compteur d'execution, sortie, erreur."""
    return page.evaluate(
        """
        () => Array.from(document.querySelectorAll('.jp-Cell')).map((cell, index) => {
          const prompt = cell.querySelector('.jp-InputPrompt');
          const area = cell.querySelector('.jp-OutputArea');
          const text = area ? (area.textContent || '') : '';
          return {
            index: index,
            prompt: prompt ? (prompt.textContent || '').trim() : '',
            sortie: text.trim(),
            erreur: cell.querySelector('.jp-mod-error') !== null
              || /Traceback \\(most recent call last\\)/.test(text),
          };
        })
        """
    )


def run_one(page: Any, base_url: str, name: str, timeout_s: int) -> Dict[str, Any]:
    """Execute un carnet dans la page et rend son etat."""
    started = time.time()
    url = "%s/lab/index.html?path=%s" % (base_url, name)
    result: Dict[str, Any] = {
        "carnet": name,
        # l'URL publique est relative : le port du serveur local est un
        # etat ephemere de la machine, pas une donnee de la mesure
        "url": url_de_page(name),
        "succes": False,
        "cellules": [],
        "erreurs": [],
        "console": [],
        "duree_s": 0.0,
        "temps_premier_resultat_s": None,
        "declenchement": "",
    }
    page.on("console", lambda msg: result["console"].append("%s: %s" % (msg.type, msg.text[:300])))
    page.goto(url, wait_until="domcontentloaded", timeout=timeout_s * 1000)
    page.wait_for_selector(".jp-Cell", timeout=timeout_s * 1000)
    page.wait_for_timeout(2000)

    result["declenchement"] = trigger_run_all(page)

    deadline = time.time() + timeout_s
    last_signature = ""
    stable = 0
    cells: List[Dict[str, Any]] = []
    while time.time() < deadline:
        page.wait_for_timeout(1500)
        cells = read_cells(page)
        code_cells = [c for c in cells if c["prompt"].startswith("[")]
        executed = [c for c in code_cells if c["prompt"] not in ("[ ]:", "[*]:")]
        signature = "|".join("%s#%s" % (c["prompt"], c["sortie"][:120]) for c in cells)
        if signature != last_signature:
            if result["temps_premier_resultat_s"] is None and signature.strip():
                result["temps_premier_resultat_s"] = round(time.time() - started, 1)
            last_signature = signature
            stable = 0
        else:
            stable += 1
        if len(executed) == len(code_cells) and len(code_cells) > 0 and stable >= 3:
            break

    result["cellules"] = cells
    result["cellules_code"] = len([c for c in cells if c["prompt"].startswith("[")])
    result["cellules_rendues"] = len(cells)
    result["cellules_executees"] = len([c for c in cells
                                        if c["prompt"].startswith("[")
                                        and c["prompt"] not in ("[ ]:", "[*]:")])
    result["cellules_avec_sortie"] = len([c for c in cells if c["sortie"]])
    result["erreurs"] = [c["sortie"][:600] for c in cells if c["erreur"]]
    result["succes"] = (
        result["cellules_code"] > 0
        and result["cellules_executees"] == result["cellules_code"]
        and not result["erreurs"]
    )
    result["duree_s"] = round(time.time() - started, 1)
    return result


def render_markdown(results: List[Dict[str, Any]]) -> str:
    """Rend le rapport de mesures en Markdown."""
    lines: List[str] = []
    lines.append("# Executions reelles sous JupyterLite (Pyodide)")
    lines.append("")
    lines.append("<!-- Genere par scripts/notebook_tools/pyodide_browser_run.py -- ne pas editer a la main. -->")
    lines.append("")
    lines.append("Les carnets ci-dessous ont ete **realement executes** dans un navigateur (Chromium headless)")
    lines.append("contre le noyau Pyodide du site JupyterLite construit localement : le menu « Run » puis")
    lines.append("« Run All Cells » a ete declenche dans la page, et les sorties sont lues dans le DOM.")
    lines.append("« Cellules executees » compte les cellules de code dont le compteur d'execution est passe")
    lines.append("de `[ ]:` a `[n]:`.")
    lines.append("")
    lines.append("| Carnet | Cellules code | Cellules executees | Cellules avec sortie | Erreurs | Duree (s) | Premier resultat (s) | Verdict |")
    lines.append("|---|---:|---:|---:|---:|---:|---:|---|")
    for ligne in agreger(results):
        verdict = "succes" if ligne["succes"] else "echec"
        lines.append("| `%s` | %s | %s | %s | %s | %s | %s | **%s** |" % (
            ligne["carnet"], ligne["cellules_code"], ligne["cellules_executees"],
            ligne["cellules_avec_sortie"], ligne["erreurs"],
            ligne["duree_s"], ligne["temps_premier_resultat_s"], verdict))
    lines.append("")
    for r in results:
        lines.append("## `%s`" % r["carnet"])
        lines.append("")
        lines.append("Verdict : **%s** · cellules executees %s/%s · duree %s s · declenchement : `%s`" % (
            "succes" if r.get("succes") else "echec", r.get("cellules_executees", 0),
            r.get("cellules_code", 0), r.get("duree_s"), r.get("declenchement")))
        lines.append("")
        for cell in r.get("cellules", []):
            if not cell.get("sortie"):
                continue
            lines.append("### Cellule %s (`%s`)" % (cell.get("index", "?"), cell.get("prompt", "")))
            lines.append("")
            lines.append("```")
            lines.append(cell["sortie"][:1500])
            lines.append("```")
            lines.append("")
    return "\n".join(lines) + "\n"


def main(argv: Optional[Sequence[str]] = None) -> int:
    """Point d'entree."""
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--site", required=True, help="site JupyterLite construit (dossier _output)")
    parser.add_argument("--lot", required=True, help="JSON du lot selectionne par le critere")
    parser.add_argument("--out", required=True, help="dossier de sortie des mesures")
    parser.add_argument("--timeout", type=int, default=300, help="secondes par carnet")
    parser.add_argument("--screenshots", action="store_true", help="joindre une capture par carnet")
    args = parser.parse_args(argv)

    site = Path(args.site).resolve()
    out_dir = Path(args.out).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)

    names = [Path(c["path"]).name for c in lire_lot(Path(args.lot))]

    from playwright.sync_api import sync_playwright

    results: List[Dict[str, Any]] = []
    with serve(site) as base_url:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True, args=["--no-sandbox"])
            for name in names:
                print("execution : %s" % name, flush=True)
                result = None
                # Une page neuve par carnet : l'application JupyterLite garde
                # l'etat de la page precedente (noyau ouvert, route SPA), et
                # la navigation suivante peut alors etre interrompue. Un
                # contexte neuf supprime cet etat partage.
                for attempt in (1, 2):
                    page = browser.new_page(viewport={"width": 1500, "height": 1000})
                    try:
                        result = run_one(page, base_url, name, args.timeout)
                    except Exception as exc:
                        result = {
                            "carnet": name,
                            "succes": False,
                            "erreurs": ["exception du pilote : %s" % str(exc)[:400]],
                            "cellules": [],
                            "console": [],
                            "duree_s": 0.0,
                            "temps_premier_resultat_s": None,
                            "declenchement": "",
                        }
                    if args.screenshots:
                        shot = out_dir / ("%s.png" % name.replace(".ipynb", ""))
                        try:
                            page.screenshot(path=str(shot), full_page=False)
                            result["capture"] = shot.name
                        except Exception:
                            result["capture"] = ""
                    page.close()
                    if result.get("succes") or attempt == 2:
                        break
                    print("  echec, nouvelle tentative avec une page neuve", flush=True)
                results.append(result)
                print("  -> %s (%s s, %s cellules executees)" % (
                    "succes" if result.get("succes") else "echec",
                    result.get("duree_s"), result.get("cellules_executees", 0)), flush=True)
            browser.close()

    payload = {
        # le site est un artefact de travail : on note son chemin par
        # rapport au depot (ou son seul nom), jamais l'arborescence de la
        # machine qui l'a construit
        "site": chemin_relatif(site, racine_depot()),
        "navigateur": "chromium (playwright, headless)",
        "noyau": "pyodide (jupyterlite)",
        "carnets": [
            {
                **r,
                "url": url_de_page(r.get("carnet", "")),
                "console": filtrer_console(r.get("console", [])),
            }
            for r in results
        ],
        "succes": sum(1 for r in results if r.get("succes")),
        "total": len(results),
    }
    with (out_dir / "executions.json").open("w", encoding="utf-8", newline="\n") as fh:
        json.dump(payload, fh, indent=1, sort_keys=True, ensure_ascii=False)
    with (out_dir / "executions.md").open("w", encoding="utf-8", newline="\n") as fh:
        fh.write(render_markdown(results))
    print("succes : %d / %d" % (payload["succes"], payload["total"]))
    return 0 if payload["succes"] == payload["total"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
