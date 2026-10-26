"""Tests de check_obsolete_chat_model.py -- regle #22783.

Pins le contrat : un appel chat dont l'argument ``model`` resout (analyse
AST bornee inter-cellules) vers un identifiant de la liste obsolete chat
ROUGIT ; tout le reste reste silencieux -- modeles TTS/transcribe (famille
SPECIFIQUE), commentaires et markdown (invisibles a l'AST), configuration
seulement imprimee ou sondee (``test_model`` du 00-3, temoin negatif
calibre sur le triage c.6428439365), modeles courants. Le cas fondateur
LiveCoding (config cell 1 -> ``model=llm_model`` / ``self.llm_model``) est
prouve sur le carnet reel. Aucun reseau, aucun kernel.
"""
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from check_obsolete_chat_model import (OBSOLETE_CHAT_MODELS,
                                       analyze_notebook, cell_kind,
                                       is_obsolete_chat_model, main)


def nb(*cells):
    return {"cells": list(cells), "metadata": {}, "nbformat": 4,
            "nbformat_minor": 5}


def code(source, cid=""):
    return {"cell_type": "code", "id": cid, "source": source,
            "outputs": [], "execution_count": 1}


def md(source):
    return {"cell_type": "markdown", "id": "m", "source": source}


REPO = Path(__file__).resolve().parents[3]
LIVECODING = (REPO / "MyIA.AI.Notebooks" / "GenAI" / "Audio" /
              "04-Applications" / "04-5-LiveCoding-LLM-Music.ipynb")
CONFIG_00_3 = (REPO / "MyIA.AI.Notebooks" / "GenAI" / "00-GenAI-Environment" /
               "00-3-API-Endpoints-Configuration.ipynb")


def _analyze(notebook):
    import check_obsolete_chat_model as mod
    scanner = mod.NotebookScanner("mem")
    scanner.scan(notebook["cells"])
    return {"findings": scanner.findings,
            "doc_mentions": scanner.doc_mentions,
            "doc_marked_cells": scanner.doc_marked_cells,
            "unresolved": scanner.unresolved,
            "stats": scanner.stats}


# ---------------------------------------------------------------------------
# POSITIFS : la garde rougit
# ---------------------------------------------------------------------------

def test_literal_flagged():
    report = _analyze(nb(code(
        'from openai import OpenAI\n'
        'client.chat.completions.create(model="gpt-4o-mini", messages=[])')))
    assert len(report["findings"]) == 1
    f = report["findings"][0]
    assert f["site"] == "chat.completions.create"
    assert f["model"] == "gpt-4o-mini"


def test_intercell_variable_flagged():
    """Cas fondateur LiveCoding : config cell 1, appel dans une cellule
    ulterieure."""
    report = _analyze(nb(
        code('llm_model = "gpt-4o-mini"   # Parametres Papermill', "c1"),
        code('response = client.chat.completions.create(\n'
             '    model=llm_model,\n'
             '    messages=[{"role": "user", "content": "hi"}])', "c20")))
    assert len(report["findings"]) == 1
    f = report["findings"][0]
    assert f["cell"] == 1
    assert f["cell_id"] == "c20"
    assert f["model"] == "gpt-4o-mini"
    assert "cell 0" in f["via"]  # la chaine cite la cellule de config


def test_self_attr_via_instantiation_flagged():
    """MusicSession (LiveCoding cell 36) : __init__ sans defaut, la valeur
    vient de l'instantiation."""
    report = _analyze(nb(
        code('llm_model = "gpt-4o-mini"'),
        code('class MusicSession:\n'
             '    def __init__(self, llm_model, system_prompt):\n'
             '        self.llm_model = llm_model\n'
             '    def compose(self, instruction):\n'
             '        response = client.chat.completions.create(\n'
             '            model=self.llm_model, messages=[])\n'
             '        return response\n'
             'session = MusicSession(llm_model, "prompt")')))
    assert len(report["findings"]) == 1
    f = report["findings"][0]
    assert f["model"] == "gpt-4o-mini"
    assert "MusicSession" in f["via"]


def test_env_default_flagged():
    """Le defaut d'environnement declare dans la source est un chemin de
    cible statiquement visible."""
    report = _analyze(nb(code(
        'import os\n'
        'm = os.getenv("OPENAI_MODEL", "gpt-4o-mini")\n'
        'client.chat.completions.create(model=m, messages=[])')))
    assert len(report["findings"]) == 1
    assert report["findings"][0]["model"] == "gpt-4o-mini"
    assert "getenv" in report["findings"][0]["via"]


def test_function_default_param_flagged():
    """04-1 : defaut de parametre consomme par l'appel chat."""
    report = _analyze(nb(code(
        'def generate(text, llm_client=None, model: str = "gpt-4o-mini"):\n'
        '    return client.chat.completions.create(model=model,\n'
        '                                           messages=[])')))
    assert len(report["findings"]) == 1
    assert report["findings"][0]["model"] == "gpt-4o-mini"


def test_dict_subscript_consumed_flagged():
    """Config intercellules consommee : la cle directe d'un dictionnaire
    litteral plat atteint un appel chat."""
    report = _analyze(nb(
        code('cfg = {"test_model": "gpt-4o-mini"}'),
        code('client.chat.completions.create(model=cfg["test_model"],\n'
             '                               messages=[])')))
    assert len(report["findings"]) == 1
    assert report["findings"][0]["model"] == "gpt-4o-mini"


def test_nested_dict_subscript_bounded_unresolved():
    """Limite declaree : les dictionnaires imbriques ne sont pas suivis --
    rapporte unresolved, jamais accuse."""
    report = _analyze(nb(
        code('api_config = {"openai": {"test_model": "gpt-4o-mini"}}'),
        code('cfg = api_config["openai"]\n'
             'client.chat.completions.create(model=cfg["test_model"],\n'
             '                               messages=[])')))
    assert report["findings"] == []
    assert len(report["unresolved"]) >= 1


def test_provider_prefix_flagged():
    report = _analyze(nb(code(
        'lm = dspy.LM("openai/gpt-4o-mini")')))
    assert len(report["findings"]) == 1
    assert report["findings"][0]["site"] == "dspy.LM"
    assert report["findings"][0]["model"] == "gpt-4o-mini"


def test_dspy_lm_in_code_cell_flagged():
    report = _analyze(nb(code(
        'import dspy\nlm = dspy.LM("openai/gpt-4o-mini")')))
    assert len(report["findings"]) == 1
    assert report["findings"][0]["model"] == "gpt-4o-mini"


def test_dated_snapshot_chat_flagged():
    report = _analyze(nb(code(
        'client.chat.completions.create(model="gpt-4o-mini-2024-07-18",\n'
        '                             messages=[])')))
    assert len(report["findings"]) == 1


def test_marker_never_exempts_real_call():
    """HARD (coordinateur) : un marqueur documentaire n'exonere JAMAIS un
    appel chat reel."""
    report = _analyze(nb(code(
        '# obsolescence: DOC\n'
        'client.chat.completions.create(model="gpt-4o-mini", messages=[])')))
    assert len(report["findings"]) == 1


def test_retry_final_state_flagged():
    """Appel defini avant la liaison, nom lie plus tard : reprise sur l'etat
    final du carnet."""
    report = _analyze(nb(
        code('def ask():\n'
             '    return client.chat.completions.create(model=m,\n'
             '                                          messages=[])'),
        code('m = "gpt-4o-mini"'),
        code('ask()')))
    assert len(report["findings"]) == 1
    assert "etat final" in report["findings"][0]["via"]


def test_chat_openai_constructor_flagged():
    report = _analyze(nb(code(
        'llm = ChatOpenAI(model="gpt-4")')))
    assert len(report["findings"]) == 1
    assert report["findings"][0]["site"] == "ChatOpenAI"


def test_alias_chain_flagged():
    report = _analyze(nb(
        code('llm_model = "gpt-4o-mini"'),
        code('m2 = llm_model'),
        code('client.chat.completions.create(model=m2, messages=[])')))
    assert len(report["findings"]) == 1


def test_reassignment_to_current_silent():
    """Flux : la reaffectation courante AVANT l'appel l'emporte."""
    report = _analyze(nb(
        code('m = "gpt-4o-mini"'),
        code('m = "gpt-5.6-luna"'),
        code('client.chat.completions.create(model=m, messages=[])')))
    assert report["findings"] == []


# ---------------------------------------------------------------------------
# NEGATIFS : temoins calibres sur le triage, la garde reste verte
# ---------------------------------------------------------------------------

def test_tts_and_specific_families_not_flagged():
    """SPECIFIQUE : un prefixe gpt-4o n'accuse jamais gpt-4o-mini-tts ;
    les endpoints non-chat ne sont pas des sites chat."""
    report = _analyze(nb(code(
        'audio = client.audio.speech.create(model="gpt-4o-mini-tts",\n'
        '                                   voice="alloy", input="bonjour")\n'
        'tr = client.audio.transcriptions.create(model="whisper-1",\n'
        '                                        file=None)\n'
        'txt = client.chat.completions.create(model="gpt-4o-mini-tts",\n'
        '                                     messages=[])')))
    assert report["findings"] == []


def test_chat_call_with_tts_name_not_flagged():
    """Meme dans un appel chat, un identifiant TTS courant n'est pas
    obsolete chat (appariement exact)."""
    report = _analyze(nb(code(
        'client.chat.completions.create(model="gpt-4o-mini-tts-2025-03-20",\n'
        '                             messages=[])')))
    assert report["findings"] == []


def test_models_probe_not_flagged():
    report = _analyze(nb(code(
        'models = client.models.list()\n'
        'import requests\n'
        'r = requests.get("https://api.openai.com/v1/models")')))
    assert report["findings"] == []
    assert report["unresolved"] == []


def test_markdown_and_comments_silent():
    """22c : le dspy.LM propose en MARKDOWN n'est pas du code execute ; les
    commentaires sont invisibles a l'AST."""
    report = _analyze(nb(
        md('Recommandation initiale : `dspy.LM("openai/gpt-4o-mini")`'),
        code('# Indice : llm_light = ChatOpenAI(model="gpt-4o", temperature=0)\n'
             'x = 1')))
    assert report["findings"] == []
    assert report["doc_mentions"] == []  # aucun litteral de code concerne


def test_printed_config_not_flagged():
    """00-3 : test_model configure/imprime/sonde, jamais consomme par un
    appel chat -> vert, mention doc advisory sans effet sur l'exit."""
    report = _analyze(nb(code(
        'api_config = {"openai": {"test_model": "openai/gpt-4o-mini"}}\n'
        'print(api_config["openai"]["test_model"])\n'
        'models = client.models.list()')))
    assert report["findings"] == []
    assert len(report["doc_mentions"]) == 1
    assert report["doc_mentions"][0]["models"] == ["gpt-4o-mini"]


def test_doc_marker_silences_advisory():
    src = ('api_config = {"openai": {"test_model": "openai/gpt-4o-mini"}}'
       '  # obsolescence: DOC\nprint(api_config)')
    report = _analyze(nb(code(src)))
    assert report["findings"] == []
    assert report["doc_mentions"] == []
    assert report["doc_marked_cells"] == 1


def test_current_models_clean():
    src = ('client.chat.completions.create(model="gpt-5.6-luna", messages=[])\n'
           'client.chat.completions.create(model="gpt-5.6-sol", messages=[])\n'
           'client.chat.completions.create(model="qwen3.6-35b-a3b", messages=[])')
    report = _analyze(nb(code(src)))
    assert report["findings"] == []


def test_ollama_colon_model_clean():
    report = _analyze(nb(code(
        'lm = dspy.LM("ollama_chat/qwen2.5:7b-instruct-q4_K_M")')))
    assert report["findings"] == []


def test_non_python_cell_skipped():
    report = _analyze(nb(code(
        '#!csharp\nvar x = client.chat.completions.create("gpt-4o-mini");')))
    assert report["findings"] == []
    assert report["stats"]["non_python_cells"] == 1
    assert report["stats"]["python_cells"] == 0


def test_ipython_cell_magic_still_scanned():
    report = _analyze(nb(code(
        '%%capture\n'
        'client.chat.completions.create(model="gpt-4o-mini", messages=[])')))
    assert len(report["findings"]) == 1


def test_dynamic_model_unresolved_not_flagged():
    report = _analyze(nb(code(
        'm = f"openai/{os.environ[\'MODEL\']}"\n'
        'client.chat.completions.create(model=m, messages=[])')))
    assert report["findings"] == []
    assert len(report["unresolved"]) >= 1


def test_env_without_default_not_flagged():
    report = _analyze(nb(code(
        'import os\n'
        'm = os.getenv("OPENAI_MODEL")\n'
        'client.chat.completions.create(model=m, messages=[])')))
    assert report["findings"] == []


# ---------------------------------------------------------------------------
# Unites isolees
# ---------------------------------------------------------------------------

def test_is_obsolete_exact_not_prefix():
    assert is_obsolete_chat_model("gpt-4o-mini")
    assert is_obsolete_chat_model("openai/gpt-4o-mini")
    assert is_obsolete_chat_model("gpt-4o-mini-2024-07-18")
    assert is_obsolete_chat_model("gpt-4")
    assert not is_obsolete_chat_model("gpt-4o-mini-tts")
    assert not is_obsolete_chat_model("gpt-4o-mini-transcribe")
    assert not is_obsolete_chat_model("gpt-4o-realtime-preview")
    assert not is_obsolete_chat_model("gpt-5.6-luna")
    assert not is_obsolete_chat_model("whisper-1")


def test_cell_kind():
    assert cell_kind("#!csharp\nvar x;")[0].startswith("non_python")
    assert cell_kind("x = 1")[0] == "python"
    assert cell_kind("%matplotlib inline\nx = 1")[0] == "python"
    assert cell_kind("def f(:")[0] == "unparsed"


# ---------------------------------------------------------------------------
# CLI : exit codes
# ---------------------------------------------------------------------------

def _run_main(tmp_path, sources, extra=None):
    """Un carnet par appel : toutes les cellules dans le MEME fichier
    (l'analyse inter-cellules est intra-carnet)."""
    p = tmp_path / "n.ipynb"
    p.write_text(json.dumps(nb(*[code(s) for s in sources])), encoding="utf-8")
    return main([str(p), *(extra or [])])


def test_main_exit_1_on_finding(tmp_path, capsys):
    assert _run_main(tmp_path, [
        'llm_model = "gpt-4o-mini"',
        'client.chat.completions.create(model=llm_model, messages=[])',
    ]) == 1
    out = capsys.readouterr().out
    assert "FINDING" in out and "gpt-4o-mini" in out


def test_main_exit_0_clean(tmp_path):
    assert _run_main(tmp_path, [
        'client.chat.completions.create(model="gpt-5.6-luna", messages=[])',
    ]) == 0


def test_main_exit_2_missing_file(tmp_path, capsys):
    assert main([str(tmp_path / "absent.ipynb")]) == 2
    assert "ERREUR" in capsys.readouterr().err


def test_main_json_shape(tmp_path, capsys):
    assert _run_main(tmp_path, [
        'client.chat.completions.create(model="gpt-4o-mini", messages=[])',
    ], ["--json"]) == 1
    payload = json.loads(capsys.readouterr().out)
    assert payload["findings"][0]["model"] == "gpt-4o-mini"
    assert payload["stats"]["chat_sites"] == 1


def test_main_obsolete_extension(tmp_path):
    assert _run_main(tmp_path, [
        'client.chat.completions.create(model="my-private-legacy", messages=[])',
    ], ["--obsolete", "my-private-legacy"]) == 1


# ---------------------------------------------------------------------------
# Corpus reel : le test qui prouve qu'elle ROUGIT
# ---------------------------------------------------------------------------

@pytest.mark.skipif(not LIVECODING.exists(), reason="carnet reel absent")
def test_corpus_livecoding_red():
    """Cas fondateur #22783 : 3 sites (cellules 20/33/36), exit 1."""
    report = analyze_notebook(str(LIVECODING))
    cells = sorted(f["cell"] for f in report["findings"])
    assert cells == [20, 33, 36], report["findings"]
    assert all(f["model"] == "gpt-4o-mini" for f in report["findings"])
    assert main([str(LIVECODING)]) == 1


@pytest.mark.skipif(not CONFIG_00_3.exists(), reason="carnet reel absent")
def test_corpus_00_3_green_but_advisory():
    """Temoin negatif calibre : configuration documentaire -> vert, advisory
    sans marqueur, exit 0."""
    report = analyze_notebook(str(CONFIG_00_3))
    assert report["findings"] == []
    assert len(report["doc_mentions"]) >= 1
    assert main([str(CONFIG_00_3)]) == 0
