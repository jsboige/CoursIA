"""Tests for check_pcm_single_source.py — garde de source unique du PCM (#20188, critère 2).

La garde doit **discriminer** : verte sur un arbre conforme, rouge dès qu'une
copie dérive, qu'une copie non déclarée apparaît, que la source canonique
bouge ou qu'une déclaration devient orpheline. Le contrôle positif exigé par
#20188 est le cas « une copie volontairement modifiée fait rougir la garde ».
"""

import hashlib
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from check_pcm_single_source import analyse, normalized_sha256  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parents[3]
QC_ROOT = "MyIA.AI.Notebooks/QuantConnect"

CANONICAL_REL = f"{QC_ROOT}/projects/SharedPCM/pouches_pcm.py"
COPY_REL = f"{QC_ROOT}/projects/DemoComposite/portfolio_construction.py"

CANONICAL_SRC = """from AlgorithmImports import *


class MultiStrategyPouchesPCM(PortfolioConstructionModel):
    \"\"\"Canonique de test.\"\"\"

    def __init__(self, additive=False, algorithm=None):
        super().__init__()
        self.additive = additive
        self._algorithm = algorithm
"""

COPY_SRC = """from AlgorithmImports import *


class MultiStrategyPCM(PortfolioConstructionModel):
    \"\"\"Copie declaree de test.\"\"\"

    def __init__(self, additive=False, algorithm=None):
        super().__init__()
        self.additive = additive
        self._algorithm = algorithm
"""

# Un consommateur qui passe `additive` explicitement : il pinne son mode, le
# defaut du canonique ne l'atteint pas.
CONSUMER_EXPLICIT_SRC = """from AlgorithmImports import *
from SharedPCM.pouches_pcm import MultiStrategyPouchesPCM


class DemoComposite(QCAlgorithm):
    \"\"\"Consommateur qui pinne son mode.\"\"\"

    def initialize(self):
        self.set_portfolio_construction(MultiStrategyPouchesPCM(
            alpha_allocations={"Demo": 1.0},
            additive=False,
        ))
"""

# Le meme consommateur, sans `additive` : il herite du defaut du canonique.
CONSUMER_IMPLICIT_SRC = """from AlgorithmImports import *
from SharedPCM.pouches_pcm import MultiStrategyPouchesPCM


class DemoComposite(QCAlgorithm):
    \"\"\"Consommateur qui herite du defaut.\"\"\"

    def initialize(self):
        self.set_portfolio_construction(MultiStrategyPouchesPCM(
            alpha_allocations={"Demo": 1.0},
        ))
"""

# --- Angle mort positionnel (reserve de la revue Hermes sur #25924) ------
#
# Un consommateur qui passe `additive` EN POSITION passe bien le parametre :
# le signaler serait un faux positif sur du code correct. Pour distinguer
# « passe en positionnel » de « omis », il faut la position du parametre
# dans la signature du canonique -- donc une signature qui reproduit celle
# du vrai canonique (`alpha_allocations`, `rebalance`, `additive`), pas la
# signature de test minimale ou `additive` est le premier parametre.

CANONICAL_REAL_SIG_SRC = """from AlgorithmImports import *


class MultiStrategyPouchesPCM(PortfolioConstructionModel):
    \"\"\"Canonique de test, signature reelle.\"\"\"

    def __init__(self, alpha_allocations, rebalance=None, additive=False,
                 algorithm=None):
        super().__init__()
        self.additive = additive
"""

# `additive` passe en positionnel (3e argument positionnel) : il est fourni.
CONSUMER_POSITIONAL_SRC = """from AlgorithmImports import *
from SharedPCM.pouches_pcm import MultiStrategyPouchesPCM


class DemoComposite(QCAlgorithm):
    \"\"\"Consommateur qui passe `additive` en positionnel.\"\"\"

    def initialize(self):
        self.set_portfolio_construction(MultiStrategyPouchesPCM(
            {"Demo": 1.0}, None, False,
        ))
"""

# Seuls `alpha_allocations` et `rebalance` en positionnel : `additive` est
# omis, le consommateur herite du defaut -- il doit etre signale.
CONSUMER_POSITIONAL_WITHOUT_ADDITIVE_SRC = """from AlgorithmImports import *
from SharedPCM.pouches_pcm import MultiStrategyPouchesPCM


class DemoComposite(QCAlgorithm):
    \"\"\"Consommateur positionnel qui n'atteint pas `additive`.\"\"\"

    def initialize(self):
        self.set_portfolio_construction(MultiStrategyPouchesPCM(
            {"Demo": 1.0}, None,
        ))
"""

# Signature ambigue (`*args`) : la position de `additive` n'est pas
# etablie, la garde ne peut pas certifier l'invariant sur les appels
# positionnels -- elle le dit au lieu de passer en silence.
CANONICAL_VARARG_SIG_SRC = """from AlgorithmImports import *


class MultiStrategyPouchesPCM(PortfolioConstructionModel):
    \"\"\"Canonique de test, signature ambigue.\"\"\"

    def __init__(self, alpha_allocations, *args, additive=False, algorithm=None):
        super().__init__()
        self.additive = additive
"""


def _digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _write(root: Path, rel: str, text: str) -> Path:
    path = root / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    return path


def _tree(tmp_path: Path, canonical_src: str = CANONICAL_SRC) -> tuple[Path, Path]:
    """Arbre minimal : canonique + une copie declaree, avec son manifeste."""
    _write(tmp_path, CANONICAL_REL, canonical_src)
    _write(tmp_path, COPY_REL, COPY_SRC)
    manifest = {
        "issue": "#20188",
        "canonical": {
            "path": CANONICAL_REL,
            "classes": ["MultiStrategyPouchesPCM"],
            "sha256": _digest(canonical_src),
        },
        "declared_copies": [
            {
                "path": COPY_REL,
                "classes": ["MultiStrategyPCM"],
                "sha256": _digest(COPY_SRC),
                "reason": "copie declaree de test",
            }
        ],
    }
    manifest_path = tmp_path / "pcm_single_source.json"
    manifest_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    return tmp_path, manifest_path


def _codes(report: dict) -> set:
    return {finding["code"] for finding in report["findings"]}


def test_arbre_conforme_vert(tmp_path):
    """Cas nominal : aucune copie non declaree, aucune declaration perimee."""
    root, manifest = _tree(tmp_path)
    report = analyse(root, manifest)
    assert report["verdict"] == "OK", report
    assert report["findings"] == []


def test_copie_decleree_modifiee_fait_rougir(tmp_path):
    """CONTROLE POSITIF exigé par #20188 : une copie modifiee doit faire rougir."""
    root, manifest = _tree(tmp_path)
    _write(root, COPY_REL, COPY_SRC + "\n# modification volontaire\n")
    report = analyse(root, manifest)
    assert report["verdict"] == "FAIL", report
    assert "DECLARATION_STALE" in _codes(report)


def test_copie_non_decleree_fait_rougir(tmp_path):
    """Une nouvelle copie hors du canonique doit etre signalee."""
    root, manifest = _tree(tmp_path)
    _write(
        root,
        f"{QC_ROOT}/projects/SneakyComposite/portfolio_construction.py",
        COPY_SRC,
    )
    report = analyse(root, manifest)
    assert report["verdict"] == "FAIL", report
    assert "UNDECLARED_COPY" in _codes(report)


# --- Invariant du defaut `additive` (#20188) ----------------------------
#
# Le defaut du canonique doit rester `False` : un consommateur qui omet le
# parametre ne doit pas heriter d'un mode qu'il n'a pas demande. Et aucun
# consommateur ne doit pas instancier le canonique sans ecrire `additive` :
# il heriterait du defaut, et son comportement changerait si le defaut change.


def test_canonique_defaut_additive_non_sur_fait_rougir(tmp_path):
    """CONTROLE POSITIF : un defaut `additive=True` sur le canonique fait rougir."""
    root, manifest = _tree(tmp_path)
    unsafe = CANONICAL_SRC.replace("additive=False", "additive=True")
    _write(root, CANONICAL_REL, unsafe)
    data = json.loads(manifest.read_text(encoding="utf-8"))
    data["canonical"]["sha256"] = _digest(unsafe)
    manifest.write_text(json.dumps(data, indent=2), encoding="utf-8")
    report = analyse(root, manifest)
    assert report["verdict"] == "FAIL", report
    assert "CANONICAL_DEFAULT_UNSAFE" in _codes(report)


def test_consommateur_sans_additive_fait_rougir(tmp_path):
    """CONTROLE POSITIF : un consommateur qui n'ecrit pas `additive` est signale."""
    root, manifest = _tree(tmp_path)
    _write(root, f"{QC_ROOT}/projects/DemoComposite/main.py", CONSUMER_IMPLICIT_SRC)
    report = analyse(root, manifest)
    assert report["verdict"] == "FAIL", report
    assert "CONSUMER_IMPLICIT_DEFAULT" in _codes(report)


def test_consommateur_avec_additive_passe(tmp_path):
    """Un consommateur qui pinne son mode ne fait pas rougir la garde."""
    root, manifest = _tree(tmp_path)
    _write(root, f"{QC_ROOT}/projects/DemoComposite/main.py", CONSUMER_EXPLICIT_SRC)
    report = analyse(root, manifest)
    assert report["verdict"] == "OK", report
    assert "CONSUMER_IMPLICIT_DEFAULT" not in _codes(report)


def test_consommateur_additive_positionnel_passe(tmp_path):
    """`additive` passe en positionnel : il est fourni, la garde reste verte.

    Reserve Hermes (#25924) : avant ce correctif, un appel positionnel
    etait vu comme n'omettant pas `additive`... non : comme l'omettant,
    donc signale a tort.
    """
    root, manifest = _tree(tmp_path, CANONICAL_REAL_SIG_SRC)
    _write(root, f"{QC_ROOT}/projects/DemoComposite/main.py", CONSUMER_POSITIONAL_SRC)
    report = analyse(root, manifest)
    assert report["verdict"] == "OK", report
    assert "CONSUMER_IMPLICIT_DEFAULT" not in _codes(report)


def test_consommateur_positionnel_sans_additive_fait_rougir(tmp_path):
    """CONTROLE POSITIF : un appel positionnel qui n'atteint PAS `additive`
    est bien signale -- le correctif positionnel ne rend pas la garde
    aveugle."""
    root, manifest = _tree(tmp_path, CANONICAL_REAL_SIG_SRC)
    _write(
        root,
        f"{QC_ROOT}/projects/DemoComposite/main.py",
        CONSUMER_POSITIONAL_WITHOUT_ADDITIVE_SRC,
    )
    report = analyse(root, manifest)
    assert report["verdict"] == "FAIL", report
    assert "CONSUMER_IMPLICIT_DEFAULT" in _codes(report)


def test_signature_positionnelle_non_etablie_fait_rougir(tmp_path):
    """Une signature ambigue (`*args`) rend l'invariant non certifiable :
    la garde le dit au lieu de rendre un vert qui ne mesure rien."""
    root, manifest = _tree(tmp_path, CANONICAL_VARARG_SIG_SRC)
    report = analyse(root, manifest)
    assert report["verdict"] == "FAIL", report
    assert "CANONICAL_SIGNATURE_UNREADABLE" in _codes(report)


def test_canonique_modifie_fait_rougir(tmp_path):
    """La source canonique ne bouge pas sans re-declaration."""
    root, manifest = _tree(tmp_path)
    _write(root, CANONICAL_REL, CANONICAL_SRC + "\n# derive du canonique\n")
    report = analyse(root, manifest)
    assert report["verdict"] == "FAIL", report
    assert "CANONICAL_DRIFT" in _codes(report)


def test_declaration_orpheline_fait_rougir(tmp_path):
    """Une copie declaree qui disparait doit etre signalee (declaration a retirer)."""
    root, manifest = _tree(tmp_path)
    (root / COPY_REL).unlink()
    report = analyse(root, manifest)
    assert report["verdict"] == "FAIL", report
    assert "DECLARED_COPY_MISSING" in _codes(report)


def test_manifeste_illisible_ne_passe_pas_au_vert(tmp_path):
    """Un manifeste illisible ne vaut pas un feu vert : la garde sedeclare en erreur."""
    root = tmp_path
    manifest = root / "pcm_single_source.json"
    manifest.write_text("{ pas du json", encoding="utf-8")
    report = analyse(root, manifest)
    assert report["verdict"] == "ERROR", report


def test_empreinte_insensible_aux_fins_de_ligne(tmp_path):
    """L'empreinte est la meme en LF et en CRLF (checkout Windows vs Linux)."""
    path = _write(tmp_path, "a.py", "x = 1\ny = 2\n")
    lf = normalized_sha256(path)
    path.write_bytes(b"x = 1\r\ny = 2\r\n")
    assert normalized_sha256(path) == lf


def test_arbre_du_depot_conforme():
    """Le depot lui-meme est conforme : la garde verte est le cas nominal reel."""
    manifest = REPO_ROOT / "scripts" / "quantconnect" / "pcm_single_source.json"
    report = analyse(REPO_ROOT, manifest)
    assert report["verdict"] == "OK", report["findings"]
    assert report["canonical"] == CANONICAL_REL
    assert len(report["declared_copies"]) == 2


@pytest.mark.parametrize(
    "relative",
    [
        f"{QC_ROOT}/projects/TrendWeatherPointInTime/portfolio_construction.py",
        f"{QC_ROOT}/partner-course-quant-trading/kit-transitoire/03-Framework-Composite/main.py",
    ],
)
def test_copies_decltrees_bien_declarees(relative):
    """Les deux copies qui subsistent sont declarees, avec leur raison."""
    manifest = json.loads(
        (REPO_ROOT / "scripts" / "quantconnect" / "pcm_single_source.json").read_text(
            encoding="utf-8"
        )
    )
    declared = {entry["path"]: entry for entry in manifest["declared_copies"]}
    assert relative in declared
    assert declared[relative]["reason"].strip()
    assert declared[relative]["sha256"] == normalized_sha256(REPO_ROOT / relative)


# --- Contournements mesures par le contre-audit (sondes A / B / C) ---------
#
# La discrimination qui manquait : une sous-classe du canonique n'est une
# specialisation legitime que si elle delegue la reconstruction a super().
# Une sous-classe qui la REDEFINIT sans super() remplace la reconstruction —
# c'est le mode de defaillance #19740 (variante sans le correctif `additive`)
# que la PR pretend fermer.


SPEC_REDEFINE_NO_SUPER = """from AlgorithmImports import *


class MultiStrategyPCM(MultiStrategyPouchesPCM):
    \"\"\"Variante sans delegation : reecrit la reconstruction, ne delegue pas.\"\"\"

    def determine_target_percent(self, active_insights):
        # reconstruction locale, sans super() : c'est une copie.
        return {i: 1.0 for i in active_insights}
"""

SPEC_WITH_SUPER = """from AlgorithmImports import *


class MultiStrategyCappedPCM(MultiStrategyPouchesPCM):
    \"\"\"Specialisation legitime : delegue la reconstruction a super().\"\"\"

    def determine_target_percent(self, active_insights):
        targets = super().determine_target_percent(active_insights)
        return {k: min(v, 0.25) for k, v in targets.items()}
"""

# Contre-exemple de l'ajoint (#24627) : une classe DONT LE NOM SATISFAIT le
# filtre MultiStrategy*PCM qui redefinit la methode canonique en deleguant a
# `other`, pas a super(). Avant le correctif, le simple nom de la methode (sans
# verifier le recepteur) la laissait passer comme specialisation legitime.
SPEC_OTHER_RECEIVER = """from AlgorithmImports import *


class MultiStrategyProbePCM(MultiStrategyPouchesPCM):
    \"\"\"Delegation a `other`, pas a super() : ce n'est PAS le canonique.\"\"\"

    def determine_target_percent(self, active_insights):
        return other.determine_target_percent(active_insights)
"""

# Contre-exemple de l'ajoint (#24627), tête 807606567a4 : la classe delegue
# bien a super(), mais JETTE le resultat (statement nu) puis retourne une
# valeur codée en dur — une copie qui contournait la discrimination
# « redefinit sans super() ». La delegation ne compte que si le resultat de
# super() est CAPTURE ; un resultat jeté ne l'est pas. Limite assumée :
# aucune analyse de flux (une variable affectee puis jamais relue resterait
# exempte).
SPEC_SUPER_RESULT_DISCARDED = """from AlgorithmImports import *


class MultiStrategyProbePCM(MultiStrategyPouchesPCM):
    \"\"\"Delegue a super() mais jette le resultat, puis recalcule en dur.\"\"\"

    def determine_target_percent(self, insights):
        super().determine_target_percent(insights)
        return {"SPY": 1.0}
"""


def test_specialisation_sans_super_est_une_copie(tmp_path):
    """SONDE A : une sous-classe du canonique qui redéfinit la methode
    canonique SANS super() remplace la reconstruction — la garde la signale."""
    root, manifest = _tree(tmp_path)
    _write(
        root,
        f"{QC_ROOT}/projects/SneakySpecial/portfolio_construction.py",
        SPEC_REDEFINE_NO_SUPER,
    )
    report = analyse(root, manifest)
    assert report["verdict"] == "FAIL", report
    assert "UNDECLARED_COPY" in _codes(report)
    # le detail doit nommer la discrimination (redefinition sans super)
    details = [
        f["detail"]
        for f in report["findings"]
        if f["code"] == "UNDECLARED_COPY"
    ]
    assert any("super()" in d for d in details), details


def test_specialisation_avec_super_n_est_pas_une_copie(tmp_path):
    """Discrimination inverse : une sous-classe qui redéfinit la methode MAIS
    delegue a super() est une specialisation legitime — la garde reste verte."""
    root, manifest = _tree(tmp_path)
    _write(
        root,
        f"{QC_ROOT}/projects/LegitSpecial/portfolio_construction.py",
        SPEC_WITH_SUPER,
    )
    report = analyse(root, manifest)
    assert report["verdict"] == "OK", report
    assert report["findings"] == []


def test_other_receiver_n_est_pas_une_delegation_super(tmp_path):
    """Contre-exemple de l'ajoint (#24627) : un appel
    `other.determine_target_percent(...)` ne delegue PAS a super() — le simple
    nom de la methode ne suffit pas a prouver la delegation. La classe porte un
    nom DANS le filtre MultiStrategy*PCM, donc la discrimination est bien
    exercee (l'ancien nom CappedPouchesPCM, hors filtre, ne la demontrait pas).
    La garde la signale comme copie non declaree."""
    root, manifest = _tree(tmp_path)
    _write(
        root,
        f"{QC_ROOT}/projects/OtherReceiver/portfolio_construction.py",
        SPEC_OTHER_RECEIVER,
    )
    report = analyse(root, manifest)
    assert report["verdict"] == "FAIL", report
    assert "UNDECLARED_COPY" in _codes(report)
    details = [
        f["detail"]
        for f in report["findings"]
        if f["code"] == "UNDECLARED_COPY"
    ]
    assert any("sans super()" in d for d in details), details


def test_super_result_discarded_est_une_copie(tmp_path):
    """Contre-exemple de l'ajoint (#24627), tête 807606567a4 : un
    `super().determine_target_percent(...)` posé en statement nu JETTE le
    résultat — la classe recalcule ensuite une valeur codée en dur. La
    délégation ne compte que si le résultat de super() est capturé (affecté,
    retourné, passé en argument) ; un résultat jeté ne l'est pas. La garde
    signale la classe comme copie non déclarée, comme le cas sans super()."""
    root, manifest = _tree(tmp_path)
    _write(
        root,
        f"{QC_ROOT}/projects/DiscardedSuper/portfolio_construction.py",
        SPEC_SUPER_RESULT_DISCARDED,
    )
    report = analyse(root, manifest)
    assert report["verdict"] == "FAIL", report
    assert "UNDECLARED_COPY" in _codes(report)
    details = [
        f["detail"]
        for f in report["findings"]
        if f["code"] == "UNDECLARED_COPY"
    ]
    assert any("sans super()" in d for d in details), details


def test_definition_sans_parentheses_est_signalee(tmp_path):
    """SONDE C : `class MultiStrategyPCM:` (sans parentheses) est bien une
    definition de la famille — l'obligation de `\\s*\\(` la masquait."""
    root, manifest = _tree(tmp_path)
    _write(
        root,
        f"{QC_ROOT}/projects/NoParens/portfolio_construction.py",
        "class MultiStrategyPCM:\n    pass\n",
    )
    report = analyse(root, manifest)
    assert report["verdict"] == "FAIL", report
    assert "UNDECLARED_COPY" in _codes(report)


# --- §2 : les empreintes sont publiées et re-declarables --------------------


def test_json_porte_les_empreintes_pleines(tmp_path):
    """Le rapport JSON porte l'empreinte declaree ET actuelle, en entier (64
    hex) — pas seulement le diff tronque a 12 caracteres du message de finding."""
    root, manifest = _tree(tmp_path)
    report = analyse(root, manifest)
    assert CANONICAL_REL in report["hashes"]
    canon = report["hashes"][CANONICAL_REL]
    assert canon["declared"] == _digest(CANONICAL_SRC)
    assert canon["actual"] == _digest(CANONICAL_SRC)
    assert len(canon["actual"]) == 64
    assert report["hashes"][COPY_REL]["actual"] == _digest(COPY_SRC)


def test_print_hashes_publie_les_empreintes_pleines(tmp_path, capsys):
    """--print-hashes affiche l'empreinte normalisee complete, copiable dans
    le manifeste — la cle qui rend CANONICAL_DRIFT / DECLARATION_STALE
    re-declarables (avant, aucune empreinte n'etait publiee)."""
    root, manifest = _tree(tmp_path)
    from check_pcm_single_source import main

    rc = main(["--root", str(root), "--manifest", str(manifest), "--print-hashes"])
    out = capsys.readouterr().out
    assert rc == 0
    assert _digest(CANONICAL_SRC) in out
    assert _digest(COPY_SRC) in out
