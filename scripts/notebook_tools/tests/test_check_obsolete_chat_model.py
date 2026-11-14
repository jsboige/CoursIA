"""Tests de check_obsolete_chat_model.py -- regle #22783.

Pins le contrat : un appel chat dont l'argument ``model`` resout (analyse
AST bornee inter-cellules) vers un identifiant de la liste obsolete chat
ROUGIT ; tout le reste reste silencieux -- modeles TTS/transcribe (famille
SPECIFIQUE), commentaires et markdown (invisibles a l'AST), configuration
seulement imprimee ou sondee (forme ``test_model`` du 00-3, temoin negatif
calibre sur le triage c.6428439365), modeles courants. Le cas fondateur
LiveCoding (config -> ``model=llm_model`` / ``self.llm_model``) est prouve
sur une fixture FIGEE de sa forme -- jamais sur le carnet vivant, dont la
migration #22783 doit faire disparaitre la dette sans faire echouer cette
suite (review PR #22800) ; les carnets reels ne servent que d'observation
en invariant compatible migration. Aucun reseau, aucun kernel.
"""
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from check_obsolete_chat_model import (OBSOLETE_CHAT_MODELS,
                                       analyze_notebook,
                                       analyze_python_module, cell_kind,
                                       collect_sources,
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


@pytest.mark.parametrize("client_call", [
    'requests.post(f"{base}/chat/completions", json=payload)',
    'httpx.post("https://example.test/v1/chat/completions", json=payload)',
    ('urllib.request.urlopen(urllib.request.Request('
     'f"{base}/chat/completions", '
     'data=json.dumps(payload)))'),
    ('urllib.request.urlopen(urllib.request.Request('
     'url=f"{base}/chat/completions", '
     'data=json.dumps(payload).encode("utf-8")))'),
    ('urllib.request.urlopen(url=f"{base}/chat/completions", '
     'data=json.dumps(payload).encode("utf-8"))'),
    ('urllib.request.urlopen(url=urllib.request.Request('
     'url=f"{base}/chat/completions", '
     'data=json.dumps(payload).encode("utf-8")))'),
    ('urllib.request.urlopen("https://example.test/v1/chat/completions", '
     'payload)'),
    ('requests.post(url=f"{base}/chat/completions", json=payload)'),
    ('httpx.post(url="https://example.test/v1/chat/completions", '
     'json=payload)'),
])
def test_raw_http_chat_payload_alias_and_env_default_flagged(client_call):
    """Les clients HTTP bruts consomment le champ model du payload JSON."""
    report = _analyze(nb(code(
        'import json\n'
        'm = os.getenv("OPENAI_CHAT_MODEL_ID", "gpt-4o-mini")\n'
        'payload = {"model": m, "messages": []}\n'
        f'{client_call}')))
    assert len(report["findings"]) == 1
    finding = report["findings"][0]
    assert finding["model"] == "gpt-4o-mini"
    assert finding["site"] == "http.chat.completions"
    assert "OPENAI_CHAT_MODEL_ID" in finding["via"]


def test_raw_http_inline_payload_and_literal_model_flagged():
    report = _analyze(nb(code(
        'requests.post("https://example.test/v1/chat/completions", '
        'json={"model": "gpt-4o-mini", "messages": []})')))
    assert len(report["findings"]) == 1
    assert report["findings"][0]["model"] == "gpt-4o-mini"


@pytest.mark.parametrize("source", [
    'requests.post("https://example.test/v1/models", '
    'json={"model": "gpt-4o-mini"})',
    'httpx.post("https://example.test/v1/chat/completions", '
    'json={"model": "gpt-5.6-luna"})',
    'urllib.request.urlopen("https://example.test/v1/models")',
    'requests.get("https://example.test/v1/chat/completions", '
    'json={"model": "gpt-4o-mini"})',
    'requests.post("https://[invalid/chat/completions", '
    'json={"model": "gpt-4o-mini"})',
])
def test_raw_http_nonchat_or_current_calls_are_silent(source):
    report = _analyze(nb(code(source)))
    assert report["findings"] == []
    assert report["unresolved"] == []


def test_raw_http_query_and_unrelated_payload_do_not_create_chat_finding():
    report = _analyze(nb(code(
        'unused = {"model": "gpt-4o-mini"}\n'
        'requests.post("https://example.test/v1/models?next="'
        '"/chat/completions", json={"model": "gpt-4o-mini"})')))
    assert report["findings"] == []
    assert report["unresolved"] == []
    assert report["stats"]["chat_sites"] == 0


def test_raw_http_query_fstring_nest_pas_un_chemin_chat():
    report = _analyze(nb(code(
        'requests.post(f"https://example.test/v1/models?next={base}'
        '/chat/completions", json={"model": "gpt-4o-mini"})')))
    assert report["findings"] == []
    assert report["stats"]["chat_sites"] == 0


def test_urllib_payload_encode_modele_courant():
    report = _analyze(nb(code(
        'payload = {"model": "gpt-5.6-luna"}\n'
        'urllib.request.urlopen(url=urllib.request.Request('
        'url="https://example.test/v1/chat/completions", '
        'data=json.dumps(payload).encode("utf-8")))')))
    assert report["findings"] == []
    assert report["unresolved"] == []
    assert report["stats"]["chat_sites"] == 1


def test_urllib_non_string_encode_argument_stays_unresolved():
    report = _analyze(nb(code(
        'payload = {"model": "gpt-4o-mini"}\n'
        'urllib.request.urlopen(urllib.request.Request('
        '"https://example.test/v1/chat/completions", '
        'data=json.dumps(payload).encode(123)))')))
    assert report["findings"] == []
    assert len(report["unresolved"]) == 1


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


def test_battery_for_loop_obsolete_entry_flagged():
    """Liste de dictionnaires (batterie de modeles) : la boucle execute
    chaque entree, donc une entree obsolete est un site atteignable."""
    report = _analyze(nb(
        code('BATTERY = [\n'
             '    {"model": "gpt-5.6-luna", "label": "mini"},\n'
             '    {"model": "gpt-4o-mini", "label": "ancien"},\n'
             ']'),
        code('for cfg in BATTERY:\n'
             '    client.chat.completions.create(model=cfg["model"],\n'
             '                                   messages=[])')))
    assert len(report["findings"]) == 1
    f = report["findings"][0]
    assert f["model"] == "gpt-4o-mini"
    assert "entree 1" in f["via"]  # localise l'entree fautive


def test_battery_all_current_silent():
    report = _analyze(nb(
        code('BATTERY = [{"model": "gpt-5.6-luna"}, {"model": "gpt-5.6-sol"}]'),
        code('for cfg in BATTERY:\n'
             '    client.chat.completions.create(model=cfg["model"],\n'
             '                                   messages=[])')))
    assert report["findings"] == []


def test_battery_indexed_entry_flagged():
    """``BATTERY[0]["cle"]`` : entree designee par un index litteral."""
    report = _analyze(nb(
        code('BATTERY = [{"model": "gpt-4o-mini"}, {"model": "gpt-5.6-sol"}]'),
        code('client.chat.completions.create(model=BATTERY[0]["model"],\n'
             '                               messages=[])')))
    assert len(report["findings"]) == 1
    assert report["findings"][0]["model"] == "gpt-4o-mini"


def test_battery_displayed_not_flagged():
    """Temoin negatif : une batterie seulement AFFICHEE (aucun appel chat)
    reste silencieuse -- c'est la forme des configurations du 00-3."""
    report = _analyze(nb(
        code('TEST_MODELS = [{"model": "gpt-4o-mini", "api": "openai"}]\n'
             'for cfg in TEST_MODELS:\n'
             '    print(cfg["model"])')))
    assert report["findings"] == []


def test_battery_dynamic_index_unresolved():
    """Index dynamique : non resolu, jamais accuse."""
    report = _analyze(nb(
        code('BATTERY = [{"model": "gpt-4o-mini"}]'),
        code('for i in range(1):\n'
             '    client.chat.completions.create(model=BATTERY[i]["model"],\n'
             '                                   messages=[])')))
    assert report["findings"] == []
    assert len(report["unresolved"]) >= 1


def test_battery_with_dynamic_entry_not_followed():
    """Une entree non resoluble fait retomber la batterie entiere en non
    suivie : aucune resolution partielle devinee."""
    report = _analyze(nb(
        code('import os\n'
             'BATTERY = [{"model": "gpt-4o-mini"},\n'
             '           {"model": os.environ["OTHER_MODEL"]}]'),
        code('for cfg in BATTERY:\n'
             '    client.chat.completions.create(model=cfg["model"],\n'
             '                                   messages=[])')))
    assert report["findings"] == []
    assert len(report["unresolved"]) >= 1


def test_local_battery_does_not_pollute_module():
    """Une batterie locale (corps de fonction) ne sort pas de son scope."""
    report = _analyze(nb(
        code('def build():\n'
             '    BATTERY = [{"model": "gpt-4o-mini"}]\n'
             '    return BATTERY'),
        code('for cfg in BATTERY:\n'
             '    client.chat.completions.create(model=cfg["model"],\n'
             '                                   messages=[])')))
    assert report["findings"] == []


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
# HTTP brut (forme non-SDK, #25072) : le "model" vit dans le corps json=/data=
# ---------------------------------------------------------------------------

def test_http_raw_inline_dict_flagged():
    """HTTP brut : json={"model": ...} inline, URL cible /chat/completions."""
    report = _analyze(nb(code(
        'import requests\n'
        'resp = requests.post("https://api.openai.com/v1/chat/completions",\n'
        '                    json={"model": "gpt-4o-mini", "messages": []})')))
    assert len(report["findings"]) == 1
    f = report["findings"][0]
    assert f["site"] == "http.chat.completions"
    assert f["model"] == "gpt-4o-mini"


def test_http_raw_named_dict_flagged():
    """HTTP brut : le "model" est dans un dict lié à un nom (json=payload),
    dont la valeur est un défaut d'env — la forme du client v4 mesuré."""
    report = _analyze(nb(
        code('import os\n'
             'import requests\n'
             '_MODEL = os.getenv("OPENAI_CHAT_MODEL_ID", "gpt-4o-mini")'),
        code('payload = {"model": _MODEL, "messages": []}\n'
             'resp = requests.post(f"{base}/chat/completions", json=payload)')))
    assert len(report["findings"]) == 1
    f = report["findings"][0]
    assert f["site"] == "http.chat.completions"
    assert f["model"] == "gpt-4o-mini"
    assert "getenv" in f["via"]


def test_http_raw_current_model_silent():
    """HTTP brut : un modèle courant dans le corps ne rougit pas."""
    report = _analyze(nb(code(
        'import requests\n'
        'resp = requests.post("https://api.openai.com/v1/chat/completions",\n'
        '                    json={"model": "gpt-5.6-luna", "messages": []})')))
    assert report["findings"] == []


def test_http_raw_non_chat_url_silent():
    """HTTP brut : une URL non-chat (/models) n'est pas un site chat."""
    report = _analyze(nb(code(
        'import requests\n'
        'r = requests.get("https://api.openai.com/v1/models")')))
    assert report["findings"] == []
    assert report["stats"]["chat_sites"] == 0


# ---------------------------------------------------------------------------
# Isolation des scopes locaux (defaut 2, review PR #22800) : une locale ne
# sort JAMAIS de sa fonction -- ni dans un sens (FP) ni dans l'autre
# (blanchiment), ni entre fonctions, ni pour les dictionnaires.
# ---------------------------------------------------------------------------

def test_local_obsolete_in_unused_function_no_fp():
    """Temoin execute par le parent : la locale obsolete d'une fonction
    JAMAIS APPELEE ne doit pas polluer la resolution globale."""
    report = _analyze(nb(code(
        'model = "qwen3.6-35b-a3b"\n'
        'def unused():\n'
        '    model = "gpt-4o-mini"\n'
        'client.chat.completions.create(model=model, messages=[])')))
    assert report["findings"] == []


def test_local_current_does_not_bleach_global_obsolete():
    """Symetrique : la locale courante d'une fonction ne blanchit pas le
    global obsolete consomme au niveau module ; l'appel propre a la
    fonction voit SA locale (pas de finding) et l'appel module ROUGIT."""
    report = _analyze(nb(code(
        'model = "gpt-4o-mini"\n'
        'def helper():\n'
        '    model = "gpt-5.6-luna"\n'
        '    return client.chat.completions.create(model=model,\n'
        '                                          messages=[])\n'
        'r = client.chat.completions.create(model=model, messages=[])')))
    assert len(report["findings"]) == 1
    assert report["findings"][0]["line"] == 6


def test_cross_function_locals_isolated():
    """La locale de f() est invisible pour g() : l'appel de g() reste
    non resolu, jamais accuse."""
    report = _analyze(nb(code(
        'def a():\n'
        '    model = "gpt-4o-mini"\n'
        '    return model\n'
        'def b():\n'
        '    return client.chat.completions.create(model=model,\n'
        '                                          messages=[])')))
    assert report["findings"] == []


def test_local_dict_does_not_pollute_global_dict():
    """dict_values aussi : le dict local d'une fonction ne masque ni ne
    remplace le dict global consomme ailleurs."""
    report = _analyze(nb(code(
        'cfg = {"m": "gpt-5.6-luna"}\n'
        'def unused():\n'
        '    cfg = {"m": "gpt-4o-mini"}\n'
        '    return cfg\n'
        'client.chat.completions.create(model=cfg["m"], messages=[])')))
    assert report["findings"] == []


def test_local_dict_consumed_in_own_function_flagged():
    """Symetrique positif : un dict LOCAL consomme DANS sa fonction rougit
    (le cloisonnement ne cree pas d'angle mort)."""
    report = _analyze(nb(code(
        'def run():\n'
        '    cfg = {"m": "gpt-4o-mini"}\n'
        '    return client.chat.completions.create(model=cfg["m"],\n'
        '                                          messages=[])')))
    assert len(report["findings"]) == 1


def test_local_binding_consumed_in_own_function_flagged():
    """Une locale obsolete consomme dans SA fonction rougit."""
    report = _analyze(nb(code(
        'def run():\n'
        '    model = "gpt-4o-mini"\n'
        '    return client.chat.completions.create(model=model,\n'
        '                                          messages=[])')))
    assert len(report["findings"]) == 1


def test_class_body_binding_invisible_to_methods():
    """Semantique Python : le scope de classe n'est pas visible dans les
    methodes -- l'affectation de corps de classe ne pollue pas la
    resolution module."""
    report = _analyze(nb(code(
        'class Conf:\n'
        '    model = "gpt-4o-mini"\n'
        'def ask():\n'
        '    return client.chat.completions.create(model=model,\n'
        '                                          messages=[])')))
    assert report["findings"] == []


# ---------------------------------------------------------------------------
# Isolation lexicale, Defaut 3 (review PR #22800, sonde parent) : une locale
# DYNAMIQUE ne retombe JAMAIS sur la globale homonyme, et un nom local ou
# parametre homonyme MASQUE le dictionnaire global.
# ---------------------------------------------------------------------------

def test_local_dynamic_never_retries_module():
    """Sonde parent exacte : globale obsolete + locale dynamique homonyme
    consommee dans la fonction -> JAMAIS de finding via 'etat final'."""
    report = _analyze(nb(code(
        'model = "gpt-4o-mini"\n'
        'def compose():\n'
        '    model = get_current_model()\n'
        '    client.chat.completions.create(model=model, messages=[])')))
    assert report["findings"] == []
    reasons = " ".join(u["reason"] for u in report["unresolved"])
    assert "sans repli module" in reasons


def test_local_scalar_shadows_global_dict():
    """Un scalaire local homonyme MASQUE le dict global : la souscription ne
    consulte jamais la table module."""
    report = _analyze(nb(code(
        'cfg = {"m": "gpt-4o-mini"}\n'
        'def run():\n'
        '    cfg = get_cfg()\n'
        '    client.chat.completions.create(model=cfg["m"], messages=[])')))
    assert report["findings"] == []


def test_param_shadows_global_dict():
    """Un parametre homonyme masque le dict global : non resolu, jamais
    accuse."""
    report = _analyze(nb(code(
        'cfg = {"m": "gpt-4o-mini"}\n'
        'def run(cfg):\n'
        '    client.chat.completions.create(model=cfg["m"], messages=[])')))
    assert report["findings"] == []


def test_module_dynamic_name_retry_still_works():
    """Le repli 'etat final' reste legitime pour un nom de SCOPE MODULE
    dynamique au point d'appel puis fixe obsolete plus tot (defaut 1)."""
    report = _analyze(nb(code(
        'def ask():\n'
        '    return client.chat.completions.create(model=m,\n'
        '                                          messages=[])\n'
        'm = "gpt-4o-mini"\n'
        'ask()')))
    assert len(report["findings"]) == 1
    assert "etat final" in report["findings"][0]["via"]


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
# Temoin rouge hermetique : la forme fondatrice LiveCoding, FIGEE
# ---------------------------------------------------------------------------

LIVECODING_SHAPE_CELLS = [
    # cell 0 -- cellule de parametres (forme Papermill du carnet reel) :
    'llm_model = "gpt-4o-mini"          # Modele pour la generation de code\n'
    'use_llm = True',
    # cell 1 -- site chat direct via la variable :
    'response = client.chat.completions.create(\n'
    '    model=llm_model,\n'
    '    messages=[{"role": "user", "content": "beat"}])',
    # cell 2 -- second site direct :
    'response = client.chat.completions.create(\n'
    '    model=llm_model,\n'
    '    messages=[{"role": "user", "content": "pattern"}])',
    # cell 3 -- classe + self.llm_model + instanciation (cellule 36 reelle) :
    'class MusicSession:\n'
    '    def __init__(self, llm_model, system_prompt):\n'
    '        self.llm_model = llm_model\n'
    '    def compose(self, instruction):\n'
    '        response = client.chat.completions.create(\n'
    '            model=self.llm_model, messages=[])\n'
    '        return response\n'
    'session = MusicSession(llm_model, "prompt")',
]


def test_livecoding_shape_red_hermetic(tmp_path):
    """Le test qui prouve qu'elle ROUGIT -- sur une fixture FIGEE de la
    forme fondatrice (config cell 1 -> model=llm_model cellules 20/33,
    self.llm_model cellule 36), PAS sur le carnet vivant : la suite ne doit
    pas echouer au moment precis ou la migration #22783 corrige la dette."""
    p = tmp_path / "livecoding_shape.ipynb"
    p.write_text(json.dumps(
        nb(*[code(src, cid=f"c{i}") for i, src in
             enumerate(LIVECODING_SHAPE_CELLS)])), encoding="utf-8")
    report = analyze_notebook(str(p))
    cells = sorted(f["cell"] for f in report["findings"])
    assert cells == [1, 2, 3], report["findings"]
    assert all(f["model"] == "gpt-4o-mini" for f in report["findings"])
    assert "MusicSession" in report["findings"][2]["via"]
    assert main([str(p)]) == 1


# ---------------------------------------------------------------------------
# Corpus reel : observation en INVARIANT compatible migration
# ---------------------------------------------------------------------------

@pytest.mark.skipif(not (LIVECODING.exists() and CONFIG_00_3.exists()),
                    reason="carnets reels absents")
@pytest.mark.parametrize("path", [LIVECODING, CONFIG_00_3],
                         ids=["livecoding", "config-00-3"])
def test_corpus_scan_migration_compatible(path):
    """Observation bornee sur les carnets reels : le scan ne crashe pas,
    n'accuse que des identifiants de la liste obsolete chat, et l'exit
    reflute exactement les findings -- rouge tant que la dette vive existe,
    vert apres migration. AUCUNE assertion sur le nombre de findings ni sur
    la presence d'un modele obsolète (etats mutables par les grains de
    migration #22783)."""
    report = analyze_notebook(str(path))
    for f in report["findings"]:
        assert f["model"] in OBSOLETE_CHAT_MODELS, f
    assert main([str(path)]) == (1 if report["findings"] else 0)


# ---------------------------------------------------------------------------
# Modules .py hors carnet
#
# Un appel chat ne vit pas seulement dans un carnet : des modules consommes
# par les carnets portent des replis litteraux. Mesure firsthand (31/10) :
# ``scripts/slides/livecoding_video_pipeline.py`` repliait sur ``gpt-4o-mini`` via
# ``os.environ.get("OPENAI_MODEL", ...)`` -- invisible d'un scan borne aux
# carnets, et invisible aussi d'un scan .py avant le cas ``or`` ci-dessous.
# ---------------------------------------------------------------------------

MODULE_CHAT = (
    "from openai import OpenAI\n"
    "client = OpenAI()\n"
    "\n"
    "\n"
    "def narrate(prompt):\n"
    "    return client.chat.completions.create(\n"
    "        model='gpt-4o-mini', messages=[{'role': 'user', 'content': prompt}])\n"
)


def test_python_module_accepte_par_la_cli(tmp_path):
    """Un module .py est une unite scannable : le scan le voit et ROUGIT."""
    p = tmp_path / "pipeline.py"
    p.write_text(MODULE_CHAT, encoding="utf-8")
    assert collect_sources([str(p)]) == [(p, "python")]
    report = analyze_python_module(str(p))
    assert report["kind"] == "python"
    assert report["stats"]["python_modules"] == 1
    assert [f["model"] for f in report["findings"]] == ["gpt-4o-mini"]
    assert main([str(p)]) == 1


def test_python_module_repli_or_resolu(tmp_path):
    """``variable or os.environ.get("M", "<modele>")`` : le repli litteral est
    la valeur statiquement visible, donc un FINDING -- c'est la forme qui
    etait un FAUX NEGATIF (site dit ``unresolved``, litteral classe mention
    doc)."""
    p = tmp_path / "repli.py"
    p.write_text(
        "import os\n"
        "from openai import OpenAI\n"
        "client = OpenAI()\n"
        "\n"
        "\n"
        "def narrate(prompt, llm_model=None):\n"
        "    model = llm_model or os.environ.get('OPENAI_MODEL', 'gpt-4o-mini')\n"
        "    return client.chat.completions.create(\n"
        "        model=model, messages=[{'role': 'user', 'content': prompt}])\n",
        encoding="utf-8")
    report = analyze_python_module(str(p))
    assert [f["model"] for f in report["findings"]] == ["gpt-4o-mini"], \
        report
    assert report["unresolved"] == []
    assert "repli 'or'" in report["findings"][0]["via"]
    assert main([str(p)]) == 1


def test_python_module_repli_or_sans_litteral_reste_unresolved(tmp_path):
    """Temoin negatif du cas ``or`` : sans litteral, rien n'est accuse."""
    p = tmp_path / "sans_repli.py"
    p.write_text(
        "import os\n"
        "from openai import OpenAI\n"
        "client = OpenAI()\n"
        "\n"
        "\n"
        "def narrate(prompt, llm_model=None):\n"
        "    model = llm_model or os.environ.get('OPENAI_MODEL')\n"
        "    return client.chat.completions.create(\n"
        "        model=model, messages=[{'role': 'user', 'content': prompt}])\n",
        encoding="utf-8")
    report = analyze_python_module(str(p))
    assert report["findings"] == []
    assert len(report["unresolved"]) == 1
    assert main([str(p)]) == 0


LLM_CLIENT_SHAPE = (
    "import os\n"
    "import requests\n"
    "\n"
    "_API_BASE: str = os.getenv('OPENAI_API_BASE', 'https://api.openai.com/v1')\n"
    "_MODEL: str = os.getenv('OPENAI_CHAT_MODEL_ID', 'gpt-4o-mini')\n"
    "\n"
    "\n"
    "def complete(messages, timeout=30):\n"
    "    payload: dict = {'model': _MODEL, 'messages': messages}\n"
    "    resp = requests.post(f'{_API_BASE}/chat/completions',\n"
    "                         json=payload, timeout=timeout)\n"
    "    return resp\n"
)


def test_python_module_http_raw_named_dict_flagged(tmp_path):
    """Forme du client v4 mesurée (AnnAssign + dict nommé + f-string URL, le
    tout dans une fonction) : le scan .py la ROUGIT (#25072)."""
    p = tmp_path / "llm_client.py"
    p.write_text(LLM_CLIENT_SHAPE, encoding="utf-8")
    report = analyze_python_module(str(p))
    assert [f["model"] for f in report["findings"]] == ["gpt-4o-mini"], report
    assert report["findings"][0]["site"] == "http.chat.completions"
    assert main([str(p)]) == 1


def test_python_module_http_raw_current_silent(tmp_path):
    """Témoin négatif : le même client avec un modèle courant reste vert."""
    p = tmp_path / "llm_client_ok.py"
    p.write_text(
        LLM_CLIENT_SHAPE.replace("gpt-4o-mini", "gpt-5.6-luna"),
        encoding="utf-8")
    report = analyze_python_module(str(p))
    assert report["findings"] == []
    assert main([str(p)]) == 0


def test_python_module_sain_reste_silencieux(tmp_path):
    """Temoin negatif : un module sans appel chat ne produit rien, et une
    mention en chaine non consommee reste advisory."""
    p = tmp_path / "sain.py"
    p.write_text(
        "'Ancienne cible historique : gpt-4o-mini.'\n"
        "# un commentaire citant gpt-4o-mini est ignore par l'AST\n"
        "def f():\n"
        "    return 1\n",
        encoding="utf-8")
    report = analyze_python_module(str(p))
    assert report["findings"] == []
    assert report["stats"]["python_modules"] == 1
    assert main([str(p)]) == 0


def test_suffixe_inconnu_refuse(tmp_path):
    """La CLI refuse un fichier qui n'est ni carnet ni module, plutot que de
    le sauter en silence."""
    p = tmp_path / "notes.txt"
    p.write_text("gpt-4o-mini", encoding="utf-8")
    with pytest.raises(FileNotFoundError):
        collect_sources([str(p)])


def test_collect_sources_skips_build_and_dep_dirs(tmp_path):
    """La descente d'un dossier ecart les dossiers de build/dependance
    (``.lake``, ``__pycache__``, ...) : de la sortie de build, pas une source a
    scanner. Regression #14755 : .lake/packages/mathlib crashait la passe."""
    (tmp_path / "top.py").write_text("x = 1\n", encoding="utf-8")
    lake = tmp_path / ".lake" / "packages" / "mathlib"
    lake.mkdir(parents=True)
    (lake / "deep.py").write_text("y = 2\n", encoding="utf-8")
    cache = tmp_path / "__pycache__"
    cache.mkdir()
    (cache / "cached.py").write_text("z = 3\n", encoding="utf-8")

    collected = collect_sources([str(tmp_path)])
    names = {q.name for q, _kind in collected}
    assert names == {"top.py"}


def test_analyze_python_module_unstatable_degrades_to_skip(
        tmp_path, monkeypatch, capsys):
    """Un fichier dont ``exists()`` leve (chemin long / verrou, WinError 1920)
    degrade en skip rapporte, jamais en crash de la passe entiere.
    Regression #14755 : le .lake de SymbolicAI tuait le scan."""
    p = tmp_path / "module.py"
    p.write_text("x = 1\n", encoding="utf-8")

    def boom(self):
        raise OSError(1920, "chemin injoignable")

    monkeypatch.setattr(Path, "exists", boom)
    report = analyze_python_module(str(p))
    assert report["kind"] == "python"
    assert report["findings"] == []
    assert report["stats"]["skipped"] == 1
    assert "injoignable" in capsys.readouterr().err
