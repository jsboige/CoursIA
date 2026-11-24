#!/usr/bin/env python3
"""Tests du fixer de garde `edited` (#25510, tranche T-C/2).

Ce que ces tests prouvent, dans l'ordre d'importance :

1. **La semantique du garde.** Le garde doit laisser passer un push, un
   `synchronize`, une ouverture, une edition qui change la **base** (retarget)
   et -- pour les workflows dont le verdict depend du body -- une edition de
   body ; il doit **ignorer** une edition de titre seule. La verite est
   evaluee par un **mini-evaluateur** d'expressions GitHub (le sous-ensemble
   utilise par le garde : `||`, `&&`, `==`, `!=`, `null`, parentheses), et non
   par une relecture du texte.
2. **Les parentheses.** Dans les expressions GitHub, `&&` lie plus fort que
   `||` : sans parentheses, `A || B && G` se lit `A || (B && G)` -- le garde
   serait contourne par le premier terme d'une disjonction existante. C'est un
   piege **reel** dans la population (les workflows de garde ont une condition
   en disjonction).
3. **L'idempotence** : repasser le fixer ne doit rien changer.
4. **La population reelle** : chaque workflow du census porte le garde sur
   tous ses jobs, et le mode `--check` passe sur le depot.
5. **Le declencheur n'est pas touche** : `edited` reste dans les types -- c'est
   la forme retenue ; le fixer ne doit pas modifier le bloc `on:`.
6. **Le check requis n'est pas touche** : `pr-gate.yml` produit le seul check
   exige sur `main` (`PR gate`) ; il n'ecoute pas `edited` et ce fixer ne le
   touche donc pas.

Run: python -m pytest scripts/tests/test_apply_edited_trigger_guard.py
"""
from __future__ import annotations

import math
import sys
from pathlib import Path

import pytest
import yaml

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "ci"))

import apply_edited_trigger_guard as fixer  # noqa: E402
import list_edited_trigger_workflows as census  # noqa: E402


# --- mini-evaluateur d'expressions GitHub ------------------------------------
#
# Sous-ensemble couvert : `||`, `&&`, `==`, `!=`, `null`, `true`, `false`,
# chaines en apostrophes, identifiants pointues et parentheses. C'est
# exactement ce dont le garde a besoin -- ni plus, ni moins.

NAN = math.nan


class _Env:
    """Un environnement `github.event...` minimal."""

    def __init__(self, action, changes=None):
        self.values = {
            "github": {
                "event": {
                    "action": action,
                    "changes": changes,
                },
            },
        }

    def get(self, path: str):
        node = self.values
        for part in path.split("."):
            if not isinstance(node, dict):
                return None
            node = node.get(part)
        return node


def _to_number(value) -> float:
    """Le cast numerique de GitHub (null -> 0, booleen -> 0/1, chaine -> NaN)."""
    if value is None:
        return 0.0
    if isinstance(value, bool):
        return 1.0 if value else 0.0
    if isinstance(value, (int, float)):
        return float(value)
    if isinstance(value, str):
        try:
            return float(value)
        except ValueError:
            return NAN
    return NAN


def _truthy(value) -> bool:
    if value is None or value is False:
        return False
    if value is True:
        return True
    if isinstance(value, str):
        return value != ""
    if isinstance(value, (int, float)):
        return value != 0
    return True


def _equal(left, right) -> bool:
    if isinstance(left, str) and isinstance(right, str):
        return left == right
    if isinstance(left, str) or isinstance(right, str):
        return _to_number(left) == _to_number(right)
    return left == right


def _tokenize(text: str) -> list[str]:
    tokens: list[str] = []
    index = 0
    while index < len(text):
        char = text[index]
        if char.isspace():
            index += 1
            continue
        if char in "()":
            tokens.append(char)
            index += 1
            continue
        if text.startswith("||", index) or text.startswith("&&", index):
            tokens.append(text[index:index + 2])
            index += 2
            continue
        if text.startswith("==", index) or text.startswith("!=", index):
            tokens.append(text[index:index + 2])
            index += 2
            continue
        if char == "'":
            end = text.index("'", index + 1)
            tokens.append(text[index:end + 1])
            index = end + 1
            continue
        if char.isalnum() or char in "._":
            end = index
            while end < len(text) and (text[end].isalnum() or text[end] in "._"):
                end += 1
            tokens.append(text[index:end])
            index = end
            continue
        raise AssertionError(f"jeton non reconnu dans {text!r} a {index}")
    return tokens


class _Parser:
    """Parseur recursif descendant du sous-ensemble ci-dessus."""

    def __init__(self, tokens: list[str], env: _Env):
        self.tokens = tokens
        self.pos = 0
        self.env = env

    def peek(self):
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def take(self):
        token = self.tokens[self.pos]
        self.pos += 1
        return token

    def parse(self):
        value = self.parse_or()
        assert self.peek() is None, f"jetons restants : {self.tokens[self.pos:]}"
        return value

    def parse_or(self):
        value = self.parse_and()
        while self.peek() == "||":
            self.take()
            right = self.parse_and()
            value = value if _truthy(value) else right
        return value

    def parse_and(self):
        value = self.parse_cmp()
        while self.peek() == "&&":
            self.take()
            right = self.parse_cmp()
            value = right if _truthy(value) else value
        return value

    def parse_cmp(self):
        left = self.parse_unary()
        if self.peek() in ("==", "!="):
            operator = self.take()
            right = self.parse_unary()
            equal = _equal(left, right)
            return equal if operator == "==" else not equal
        return left

    def parse_unary(self):
        token = self.peek()
        if token == "(":
            self.take()
            value = self.parse_or()
            assert self.take() == ")"
            return value
        token = self.take()
        if token == "null":
            return None
        if token == "true":
            return True
        if token == "false":
            return False
        if token.startswith("'"):
            return token[1:-1]
        return self.env.get(token)


def evaluate(expression: str, action, changes=None):
    """Evalue une expression du sous-ensemble, dans un evenement donne."""
    return _Parser(_tokenize(expression), _Env(action, changes)).parse()


# --- 1. semantique du garde ----------------------------------------------------


BASE_CASES = [
    ("opened", None, True, "une ouverture n'est pas une edition"),
    ("synchronize", None, True, "un push n'est pas une edition"),
    ("reopened", None, True, "une reouverture n'est pas une edition"),
    ("edited", {"base": None, "body": None}, False,
     "edition de titre seule : le verdict ne bouge pas"),
    ("edited", {"base": {"ref": "main"}, "body": None}, True,
     "retarget : le diff base-relative change, le verdict doit rejouer"),
]


@pytest.mark.parametrize("action,changes,expected,why", BASE_CASES)
def test_le_garde_de_base(action, changes, expected, why):
    assert evaluate(fixer.GUARD_BASE, action, changes) is expected, why


def test_le_garde_de_body_laisse_passer_une_edition_de_body():
    """Un workflow dont le verdict depend du body doit rejouer quand le body
    change -- le census donne l'axe, il ne le devine pas."""
    assert evaluate(fixer.GUARD_BODY, "edited",
                    {"base": None, "body": {"body": "texte"}}) is True
    assert evaluate(fixer.GUARD_BODY, "edited",
                    {"base": None, "body": None}) is False
    assert evaluate(fixer.GUARD_BODY, "synchronize", None) is True


def test_le_garde_ignore_une_edition_de_titre_meme_avec_un_preexistant():
    """Le garde compose avec une condition existante : une disjonction
    preexistante ne doit pas pouvoir contourner le garde (c'est le piege de
    precedence : `A || B && G` se lit `A || (B && G)`)."""
    existing = ("github.event.pull_request.head.repo.full_name == null "
                "|| github.event.pull_request.head.repo.full_name == 'repo'")
    composed = f"({existing}) && ({fixer.GUARD_BASE})"
    # La condition preexistante est vraie (fork), mais le garde l'annule.
    assert evaluate(f"({existing})", "edited", {"base": None}) is True
    assert evaluate(composed, "edited", {"base": None, "body": None}) is False
    assert evaluate(composed, "edited", {"base": {"ref": "x"}}) is True


# --- 2. le fixer --------------------------------------------------------------


WORKFLOW_SAMPLE = """\
name: Echantillon
on:
  pull_request:
    types: [opened, synchronize, edited, reopened]
    paths:
      - '**.py'
concurrency:
  group: echantillon-${{ github.ref }}
  cancel-in-progress: true
jobs:
  un:
    name: Un
    runs-on: ubuntu-latest
    steps:
      - run: echo un
"""


def test_le_fixer_ajoute_le_garde_a_un_job_sans_if():
    text, changed = fixer.apply_guard(WORKFLOW_SAMPLE, fixer.GUARD_BASE)
    assert changed == 1
    assert f"if: ({fixer.GUARD_BASE})" in text


def test_le_fixer_parenthese_la_condition_existante():
    """La condition existante est groupee : sans les parentheses, `&&` lie
    plus fort que `||` et le garde serait contourne."""
    sample = WORKFLOW_SAMPLE.replace(
        "    name: Un\n",
        "    name: Un\n    if: a == null || b == 'x'\n",
    )
    text, changed = fixer.apply_guard(sample, fixer.GUARD_BASE)
    assert changed == 1
    assert f"if: (a == null || b == 'x') && ({fixer.GUARD_BASE})" in text


def test_le_fixer_preserve_le_commentaire_de_fin_de_ligne():
    """Le commentaire de fin de ligne n'est pas mange : il porte souvent la
    raison d'une condition."""
    sample = WORKFLOW_SAMPLE.replace(
        "    name: Un\n",
        "    name: Un\n    if: a == null # raison\n",
    )
    text, _ = fixer.apply_guard(sample, fixer.GUARD_BASE)
    assert "# raison" in text


def test_le_fixer_est_idempotent():
    once, first = fixer.apply_guard(WORKFLOW_SAMPLE, fixer.GUARD_BASE)
    twice, second = fixer.apply_guard(once, fixer.GUARD_BASE)
    assert first == 1
    assert second == 0
    assert once == twice


def test_le_fixer_ne_touche_pas_le_declencheur():
    """`edited` reste dans les types : c'est la forme retenue. Le bloc `on:`
    doit etre byte-identique avant et apres."""
    texte, _ = fixer.apply_guard(WORKFLOW_SAMPLE, fixer.GUARD_BASE)
    assert texte.split("jobs:")[0] == WORKFLOW_SAMPLE.split("jobs:")[0]


def test_le_fixer_separe_la_concurrence():
    text, changed = fixer.apply_group(WORKFLOW_SAMPLE, fixer.separator_for([]))
    assert changed == 1
    assert "meta-edit" in text
    assert text.count("meta-edit") == 1
    again, changed_again = fixer.apply_group(text, fixer.separator_for([]))
    assert changed_again == 0
    assert again == text


def test_la_separation_de_concurrence_depende_de_l_axe():
    """Une edition de body partage le groupe du run reel (le verdict bouge),
    une edition de titre non."""
    base = fixer.separator_for(["paths"])
    body = fixer.separator_for(["body"])
    assert "changes.body == null" not in base
    assert "changes.body == null" in body
    assert "changes.base == null" in base
    assert "changes.base == null" in body


# --- 3. la population reelle --------------------------------------------------


def test_le_mode_check_passe_sur_le_depot():
    """Tous les workflows du census portent le garde et la cle de groupe
    separee."""
    assert fixer.main(["--root", str(ROOT), "--check"]) == 0


def test_chaque_workflow_de_la_population_ecoute_encore_edited():
    """La forme retenue garde `edited` dans les types : le census doit
    retrouver, pour chaque workflow de la population, un declencheur qui
    l'ecoute toujours."""
    rows = fixer.population(ROOT)
    assert rows, "le census ne trouve personne : le test ne prouve rien"
    for row in rows:
        data = yaml.safe_load(
            (ROOT / row["workflow"]).read_text(encoding="utf-8")
        )
        on = data.get(True) if isinstance(data.get(True), dict) else data["on"]
        types = on["pull_request"]["types"]
        assert "edited" in types, row["workflow"]


def test_le_producteur_du_check_requis_n_est_pas_touche():
    """`pr-gate.yml` produit le seul check exige sur `main` (`PR gate`). Il
    n'ecoute pas `edited` (rev. #16624) et n'est donc pas dans la population
    du fixer : le verifier, c'est qu'il n'y est pas."""
    rel = ".github/workflows/pr-gate.yml"
    assert rel not in {row["workflow"] for row in fixer.population(ROOT)}
    text = (ROOT / rel).read_text(encoding="utf-8")
    assert fixer.GUARD_BASE not in text


def test_une_exclusion_nominative_vise_un_workflow_qui_ecoute_encore_edited():
    """Une exclusion n'a de sens que pour un workflow du census : une entree
    qui nomme un workflow sorti du census est du code mort, et ce test la
    refuse. C'est ce qui est arrive a `notebook-latex-control-chars.yml` :
    exclu tant que la tranche T-A/2 etait ouverte, il a perdu son declencheur
    `pull_request` a son merge et n'ecoute plus `edited` du tout."""
    listening = {row["workflow"] for row in census.survey(ROOT)}
    assert fixer.EXCLUDED <= listening, sorted(fixer.EXCLUDED - listening)
    population = {row["workflow"] for row in fixer.population(ROOT)}
    assert not (fixer.EXCLUDED & population)


def test_le_garde_latex_absorbe_par_la_voie_rapide_est_hors_population():
    """Temoin du cas ci-dessus : le workflow n'est plus dans le census, donc
    plus dans la population, sans exclusion nominative."""
    rel = ".github/workflows/notebook-latex-control-chars.yml"
    assert rel not in {row["workflow"] for row in census.survey(ROOT)}
    assert rel not in {row["workflow"] for row in fixer.population(ROOT)}
    assert rel not in fixer.EXCLUDED


def test_le_workflow_a_dependance_titre_est_hors_population():
    """Un verdict titre-dépendant doit toujours rejouer : GitHub n'expose pas
    `changes.title`, donc une edition de titre ne se distingue pas d'une
    edition de body."""
    population = {row["workflow"] for row in fixer.population(ROOT)}
    for row in census.survey(ROOT):
        if "title" in row["depends_on"]:
            assert row["workflow"] not in population
