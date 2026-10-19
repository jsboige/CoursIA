"""Tests de `check_env_example_secrets`.

Issue de reference : #20919. Contrat de l'organe (3 controles) :

  1. controle positif : une phrase secrete d'un mot ordinaire ajoutee en valeur
     doit rougir. (le test attrape la regression du cas fondateur `Propaganda`).
  2. controle negatif : les 32 fichiers actuels, avec leurs marqueurs, doivent
     passer -- l'instrument n'accuse pas les patterns didactiques ni les placeholders.
  3. exemption inline : une ligne ``KEY=  # OK: <raison>`` est acceptee
     (commentaire inline, pas une valeur).
"""
import importlib.util
import json
import sys
import subprocess
from pathlib import Path

_SPEC = importlib.util.spec_from_file_location(
    "check_env_example_secrets",
    Path(__file__).resolve().parents[1] / "check_env_example_secrets.py",
)
mod = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(mod)


# ---------- 1. controles positifs (defauts) ----------

def test_mot_ordinaire_rougit():
    """Cas fondateur 'Propaganda' (TEXT_CONFIG_PASSPHRASE) : un mot lisible."""
    assert mod.is_marker("Propaganda") is False
    assert mod.is_marker("changeme") is False
    assert mod.is_marker("hello") is False


def test_url_nest_pas_un_secret():
    """Les URLs ne sont JAMAIS des secrets, meme si la cle contient TOKEN/KEY."""
    assert mod.is_marker("https://api.openai.com/v1") is True
    assert mod.is_marker("https://whisper-api.myia.io") is True


def test_chemin_windows_pas_secret():
    """Chemin WSL/Windows n'est pas un secret."""
    assert mod.is_marker("\\\\wsl.localhost\\Ubuntu\\home\\jesse\\workspace") is True
    assert mod.is_marker("/path/to/lean") is True


def test_chiffre_et_bool_pas_secret():
    """Numerique et boolean ne sont pas des secrets."""
    assert mod.is_marker("300") is True
    assert mod.is_marker("0.05") is True
    assert mod.is_marker("-1") is True
    assert mod.is_marker("true") is True
    assert mod.is_marker("FALSE") is True
    assert mod.is_marker("0") is True
    assert mod.is_marker("1") is True


def test_placeholder_chevrons():
    """Chevrons / crochets = placeholders explicites."""
    assert mod.is_marker("<your_api_key>") is True
    assert mod.is_marker("[FILL_ME]") is True
    assert mod.is_marker("<your_text_config_passphrase>") is True


def test_your_xxx_here_normalisations():
    """Separateurs variables, suffixe variable."""
    assert mod.is_marker("your_api_key_here") is True
    assert mod.is_marker("your-gemini-api-key") is True
    assert mod.is_marker("your.openai.key.here") is True
    assert mod.is_marker("your_qdrant_api_key") is True
    assert mod.is_marker("YOUR_BEARER_TOKEN_HERE") is True


def test_change_me_xxx():
    """change-me / xxx sont des marqueurs evidents."""
    assert mod.is_marker("change-me-strong-password") is True
    assert mod.is_marker("change_me") is True
    assert mod.is_marker("xxx") is False   # 3 x ne suffit pas, on exige 4+
    assert mod.is_marker("xxxx") is True
    assert mod.is_marker("xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx") is True


def test_prefixes_didactiques_openai_hf():
    """Prefixes sk-/sk-or-/sk-proj-/ghp/hf avec placeholder ne rougissent pas."""
    assert mod.is_marker("sk-...") is True
    assert mod.is_marker("sk-proj-1234567890") is True
    assert mod.is_marker("sk-or-v1-...") is True
    assert mod.is_marker("sk-ant-...") is True
    assert mod.is_marker("hf_...") is True
    assert mod.is_marker("hf_xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx") is True
    assert mod.is_marker("ghp_...") is True


def test_auto_generated_placeholder():
    """Mots-cles placeholder/example/dummy/sample/fake/fill/replace_with."""
    assert mod.is_marker("auto_generated_secret_key") is True
    assert mod.is_marker("replace_with_your_openai_api_key") is True


def test_modeles_ne_sont_pas_secrets():
    """Les noms de modeles ne sont pas des secrets."""
    assert mod.is_marker("gpt-5-mini") is True
    assert mod.is_marker("claude-sonnet-4-6") is True
    assert mod.is_marker("qwen3.6-35b-a3b") is True
    assert mod.is_marker("meta-llama/llama-3.2-3b-instruct:free") is True
    assert mod.is_marker("Qwen/Qwen2.5-72B-Instruct") is True


def test_utilisateur_par_defaut():
    """admin / root / user / default ne sont pas des secrets."""
    assert mod.is_marker("admin") is True
    assert mod.is_marker("root") is True
    assert mod.is_marker("default") is True
    assert mod.is_marker("etudiant") is True


def test_valeur_vide():
    assert mod.is_marker("") is True
    assert mod.is_marker("   ") is True


# ---------- 2. strip value ----------

def test_strip_value_enleve_commentaire_inline():
    assert mod._strip_value("  # commentaire") == ""
    assert mod._strip_value("'valmont_db_pass' # defaut compose") == "valmont_db_pass"
    assert mod._strip_value('"Propaganda"') == "Propaganda"
    assert mod._strip_value("your_key_here  # defaut") == "your_key_here"


def test_strip_value_handle_guillemets_et_quotes_simples():
    assert mod._strip_value("'valmont_db_pass'") == "valmont_db_pass"
    assert mod._strip_value('"Propaganda"') == "Propaganda"
    assert mod._strip_value("plain") == "plain"


# ---------- 3. controle negatif sur le repo (32 fichiers) ----------

def test_scan_32_fichiers_principal_pas_de_defaut():
    """Le scan des fichiers traces git doit rendre 0 defaut.

    C'est le controle negatif exige par l'issue #20919. On court en sous-processus
    pour eviter que pytest ne pollue la sortie.
    """
    repo = Path(__file__).resolve().parents[3]   # scripts/ci/tests/ -> racine
    out = subprocess.run(
        [sys.executable, str(repo / "scripts" / "ci" / "check_env_example_secrets.py"),
         "--root", str(repo), "--json"],
        cwd=repo, capture_output=True, text=True,
        encoding="utf-8", errors="replace", check=False,
    )
    if out.returncode not in (0, 1):
        raise AssertionError(f"unexpected exit {out.returncode}: {out.stderr}")
    payload = json.loads(out.stdout)
    assert payload["status"] in ("OK", "DEFECT"), payload
    assert payload["files_scanned"] >= 30, payload   # 32 attendus, 30 = garde
    if payload["status"] != "OK":
        raise AssertionError(
            f"32 env examples should pass after the c.1683 cleanup, "
            f"got {len(payload['defects'])} defect(s):\n"
            + "\n".join(f"  {d['file']}:{d['line']}  {d['name']}={d['raw']!r}"
                        for d in payload["defects"])
        )


# ---------- 4. controle positif : check_file attrape les violations ----------

def test_check_file_attrape_mot_ordinaire(tmp_path):
    f = tmp_path / "sub.env.example"
    f.write_text(
        "API_KEY=Propaganda\n"
        "DB_PASSWORD=my_real_password\n"
        "URL=https://api.openai.com\n"
        "GOOD_KEY=your_key_here\n",
        encoding="utf-8",
    )
    defects = mod.check_file(f)
    assert len(defects) == 2
    names = {d[1] for d in defects}
    assert names == {"API_KEY", "DB_PASSWORD"}


def test_check_file_ignore_commentaires(tmp_path):
    f = tmp_path / "sub.env.example"
    f.write_text(
        "# OPENAI_API_KEY=sk-realkey-abc\n"
        "  # API_PASSWORD=PlainPassword\n"
        "GOOD_KEY=your_key_here\n",
        encoding="utf-8",
    )
    defects = mod.check_file(f)
    assert defects == []


def test_check_file_ignore_si_cle_pas_de_type_secret(tmp_path):
    f = tmp_path / "sub.env.example"
    f.write_text(
        "BATCH_MODE=Propaganda\n"           # PAS un nom de type secret
        "DB_HOST=localhost\n"
        "GOOD_KEY=your_key_here\n",
        encoding="utf-8",
    )
    defects = mod.check_file(f)
    assert defects == []


def test_check_file_exemption_commentaire_inline(tmp_path):
    f = tmp_path / "sub.env.example"
    f.write_text(
        "API_KEY=  # OK: optionnel, laissez vide\n"
        "GOOD_KEY=your_key_here\n",
        encoding="utf-8",
    )
    defects = mod.check_file(f)
    assert defects == []


# ---------- 5. exemption inline : une valeur REELLE peut etre publiee ----------

def test_check_file_exemption_en_fin_de_ligne_valeur_reelle(tmp_path):
    """`KEY=vraie_valeur  # OK: <raison>` est acceptee (forme en fin de ligne)."""
    f = tmp_path / "sub.env.example"
    f.write_text(
        "API_KEY=myrealpassword  # OK: valeur legitime\n"
        "GOOD_KEY=your_key_here\n",
        encoding="utf-8",
    )
    exemptions: list = []
    defects = mod.check_file(f, exemptions=exemptions)
    assert defects == []
    assert len(exemptions) == 1
    assert exemptions[0]["name"] == "API_KEY"
    assert "valeur legitime" in exemptions[0]["reason"]


def test_check_file_exemption_marqueur_ligne_precedente(tmp_path):
    """Un marqueur `# OK: <raison>` sur la ligne du dessus couvre la valeur.

    Cette forme laisse la valeur byte-identique -- indispensable quand la
    valeur est relue par du code (le corpus chiffre ICT la relit depuis ce
    fichier) : un commentaire en fin de ligne la casserait.
    """
    f = tmp_path / "sub.env.example"
    f.write_text(
        "# Corpus chiffre, passphrase publiee par design (decision user #7742).\n"
        "# OK: passphrase publiee par design\n"
        "ICT_S6B_PASSPHRASE=\"Rhetorique\"\n",
        encoding="utf-8",
    )
    exemptions: list = []
    defects = mod.check_file(f, exemptions=exemptions)
    assert defects == []
    assert len(exemptions) == 1
    assert exemptions[0]["name"] == "ICT_S6B_PASSPHRASE"
    assert exemptions[0]["line"] == 3


def test_check_file_exemption_sans_raison_ne_exempte_pas(tmp_path):
    """`# OK:` sans raison n'est pas une exemption : la valeur rouge toujours."""
    f = tmp_path / "sub.env.example"
    f.write_text(
        "# OK:\n"
        "API_KEY=myrealpassword\n",
        encoding="utf-8",
    )
    defects = mod.check_file(f)
    assert len(defects) == 1
    assert defects[0][1] == "API_KEY"


def test_check_file_exemption_sans_raison_en_fin_de_ligne(tmp_path):
    """`KEY=vraie_valeur  # OK:` (raison vide) rouge aussi."""
    f = tmp_path / "sub.env.example"
    f.write_text(
        "API_KEY=myrealpassword  # OK:\n",
        encoding="utf-8",
    )
    defects = mod.check_file(f)
    assert len(defects) == 1
    assert defects[0][1] == "API_KEY"


def test_check_file_exemption_non_adjacente_ne_couvre_pas(tmp_path):
    """Le marqueur ne couvre que la valeur qu'il precede immediatement."""
    f = tmp_path / "sub.env.example"
    f.write_text(
        "# OK: raison pour la valeur ci-dessous\n"
        "BATCH_MODE=1\n"
        "API_KEY=myrealpassword\n",
        encoding="utf-8",
    )
    defects = mod.check_file(f)
    assert len(defects) == 1
    assert defects[0][1] == "API_KEY"


def test_check_file_marqueur_avant_commentaire_intermediaire(tmp_path):
    """Un commentaire ordinaire entre le marqueur et la valeur n'annule pas."""
    f = tmp_path / "sub.env.example"
    f.write_text(
        "# OK: raison\n"
        "# un commentaire ordinaire\n"
        "API_KEY=myrealpassword\n",
        encoding="utf-8",
    )
    defects = mod.check_file(f)
    assert defects == []


def test_exemptions_listees_dans_la_sortie_json(tmp_path, capsys):
    """Les exemptions restent visibles : elles sont listees dans la sortie JSON."""
    f = tmp_path / "sub.env.example"
    f.write_text(
        "# OK: passphrase publiee par design\n"
        "API_KEY=myrealpassword\n",
        encoding="utf-8",
    )
    rc = mod.main(["--files", str(f), "--json"])
    out = capsys.readouterr().out
    payload = json.loads(out)
    assert rc == mod.EXIT_OK, payload
    assert payload["status"] == "OK", payload
    assert len(payload["exemptions"]) == 1, payload
    assert payload["exemptions"][0]["name"] == "API_KEY"
    assert payload["exemptions"][0]["reason"], payload
