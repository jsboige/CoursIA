#!/usr/bin/env python3
"""Tests unitaires pour comfyui_client.py — client ComfyUI REST API.

CI-runnables SANS serveur ComfyUI : urllib.request.urlopen est mocke via
`mock.patch.object` (les imports sont top-level dans comfyui_client.py,
donc on patche l'attribut du module importe plutot que sys.modules['']).
Valide le contrat :
- Configuration ComfyUI (defaults + custom).
- Construction du client (server_url strip slash + client_id random).
- _make_request : GET/POST + headers + Bearer + urlopen errors (HTTPError/URLError).
- queue_prompt : propagation + erreur si prompt_id absent.
- get_system_stats / get_history : delegation _make_request.
- wait_for_completion : polling + TimeoutError + errors workflow.
- Workflow builders : structure (class_type, inputs, edges references)
  pour generate_text2image / generate_text2image_lightning /
  generate_text2video_wan / generate_text2video_hunyuan / generate_bonsai.

Quirks pinnes AS-OBSERVED (PAS fixes -- one-subject-per-PR) :
- _make_request construit une Request differente pour GET (sans data kwarg)
  alors qu'autrement le data=None est envoye (urllib leve TypeError si
  data=None pour POST, mais OK pour GET).
- queue_prompt leve Exception generique (pas HTTPError) si prompt_id absent.
- wait_for_completion poll en boucle infinie, sortie uniquement sur outputs
  ou errors ou TimeoutError.
"""

import json
import sys
from pathlib import Path
from unittest import mock

import pytest

# Rendre le package `helpers` importable depuis ce fichier de test.
SHARED = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(SHARED))
sys.path.insert(0, str(SHARED.parent))

from helpers import comfyui_client  # noqa: E402


# ============================================================================
# ComfyUIConfig
# ============================================================================

class TestComfyUIConfig:
    """Configuration du client ComfyUI."""

    def test_default_values(self):
        """Defaults : localhost:8188, timeout 120s, poll 2s, pas de token."""
        config = comfyui_client.ComfyUIConfig()
        assert config.base_url == "http://localhost:8188"
        assert config.timeout == 120
        assert config.poll_interval == 2
        assert config.api_token is None

    def test_custom_values(self):
        """Tous les args sont customisables."""
        config = comfyui_client.ComfyUIConfig(
            base_url="https://comfy.example.com",
            timeout=300,
            poll_interval=5,
            api_token="secret-token-xyz",
        )
        assert config.base_url == "https://comfy.example.com"
        assert config.timeout == 300
        assert config.poll_interval == 5
        assert config.api_token == "secret-token-xyz"

    def test_base_url_preserved_verbatim(self):
        """L'URL n'est PAS strippee ici (le strip se fait dans ComfyUIClient)."""
        config = comfyui_client.ComfyUIConfig(base_url="http://example.com/")
        assert config.base_url == "http://example.com/"


# ============================================================================
# ComfyUIClient.__init__
# ============================================================================

class TestComfyUIClientInit:
    """Initialisation du client."""

    def test_strips_trailing_slash_from_base_url(self):
        """server_url normalise : pas de slash final, meme si passe avec."""
        client = comfyui_client.ComfyUIClient("http://localhost:8188/")
        assert client.server_url == "http://localhost:8188"

    def test_strips_multiple_trailing_slashes(self):
        """Plusieurs trailing slashes sont tous retires."""
        client = comfyui_client.ComfyUIClient("http://localhost:8188///")
        assert client.server_url == "http://localhost:8188"

    def test_client_id_is_random_int_string(self):
        """client_id est un string d'un int random entre 1 et 1_000_000."""
        client = comfyui_client.ComfyUIClient("http://localhost:8188")
        # Le code utilise `str(random.randint(1, 1000000))`.
        assert isinstance(client.client_id, str)
        assert client.client_id.isdigit()
        assert 1 <= int(client.client_id) <= 1_000_000

    def test_api_token_stored_verbatim(self):
        """api_token (ou None) est preserve tel quel."""
        client = comfyui_client.ComfyUIClient("http://x", api_token="tok")
        assert client.api_token == "tok"
        client_none = comfyui_client.ComfyUIClient("http://x")
        assert client_none.api_token is None


# ============================================================================
# _make_request — HTTP layer
# ============================================================================

def _fake_response(body_dict):
    """Construit un mock de la response urllib (context manager)."""
    body_bytes = json.dumps(body_dict).encode()
    fake_resp = mock.MagicMock()
    fake_resp.read.return_value = body_bytes
    fake_resp.__enter__.return_value = fake_resp
    fake_resp.__exit__.return_value = False
    return fake_resp


class TestMakeRequest:
    """Couche HTTP via urllib.request.urlopen."""

    def test_get_request_no_body(self):
        """GET sans data : urlopen appele avec Request GET."""
        with mock.patch.object(comfyui_client.request, "urlopen") as mock_urlopen:
            mock_urlopen.return_value = _fake_response({"ok": True})
            client = comfyui_client.ComfyUIClient("http://x")
            result = client._make_request("/system_stats")
        assert result == {"ok": True}
        # Verifier la Request passee a urlopen
        req = mock_urlopen.call_args.args[0]
        assert req.method == "GET"
        assert req.full_url == "http://x/system_stats"

    def test_post_request_json_body(self):
        """POST avec data dict : body serialise en JSON, Content-Type pose."""
        with mock.patch.object(comfyui_client.request, "urlopen") as mock_urlopen:
            mock_urlopen.return_value = _fake_response({"prompt_id": "abc"})
            client = comfyui_client.ComfyUIClient("http://x")
            result = client._make_request("/prompt", method="POST", data={"x": 1})
        assert result == {"prompt_id": "abc"}
        req = mock_urlopen.call_args.args[0]
        assert req.method == "POST"
        assert req.data == json.dumps({"x": 1}).encode()

    def test_bearer_header_added_when_token(self):
        """Si api_token fourni : header Authorization: Bearer <token>."""
        with mock.patch.object(comfyui_client.request, "urlopen") as mock_urlopen:
            mock_urlopen.return_value = _fake_response({})
            client = comfyui_client.ComfyUIClient("http://x", api_token="secret")
            client._make_request("/foo")
        req = mock_urlopen.call_args.args[0]
        assert req.get_header("Authorization") == "Bearer secret"

    def test_no_bearer_header_without_token(self):
        """Sans api_token : pas de header Authorization."""
        with mock.patch.object(comfyui_client.request, "urlopen") as mock_urlopen:
            mock_urlopen.return_value = _fake_response({})
            client = comfyui_client.ComfyUIClient("http://x")
            client._make_request("/foo")
        req = mock_urlopen.call_args.args[0]
        assert req.get_header("Authorization") is None

    def test_content_type_json_header(self):
        """Content-Type: application/json toujours present."""
        with mock.patch.object(comfyui_client.request, "urlopen") as mock_urlopen:
            mock_urlopen.return_value = _fake_response({})
            client = comfyui_client.ComfyUIClient("http://x")
            client._make_request("/foo")
        req = mock_urlopen.call_args.args[0]
        assert req.get_header("Content-type") == "application/json"

    def test_url_normalization(self):
        """endpoint avec ou sans leading slash, server_url avec trailing slash : tout OK."""
        with mock.patch.object(comfyui_client.request, "urlopen") as mock_urlopen:
            mock_urlopen.return_value = _fake_response({})
            client = comfyui_client.ComfyUIClient("http://x/")
            client._make_request("/foo")
        req = mock_urlopen.call_args.args[0]
        # Pas de double slash.
        assert req.full_url == "http://x/foo"

    def test_method_uppercase(self):
        """method est uppercase avant d'etre passee a urllib."""
        with mock.patch.object(comfyui_client.request, "urlopen") as mock_urlopen:
            mock_urlopen.return_value = _fake_response({})
            client = comfyui_client.ComfyUIClient("http://x")
            client._make_request("/foo", method="post", data={"y": 2})
        req = mock_urlopen.call_args.args[0]
        assert req.method == "POST"

    def test_post_without_data_kwarg_skips_data(self):
        """POST sans data kwarg : pas de body (req.data est None)."""
        with mock.patch.object(comfyui_client.request, "urlopen") as mock_urlopen:
            mock_urlopen.return_value = _fake_response({})
            client = comfyui_client.ComfyUIClient("http://x")
            client._make_request("/foo", method="POST")
        req = mock_urlopen.call_args.args[0]
        # urllib gere data=None comme pas de body.
        assert req.data is None

    def test_http_error_raises_exception_with_body(self):
        """HTTPError leve une Exception avec code + body dans le message."""
        # HTTPError en Python 3.13 a la signature (url, code, msg, hdrs, fp).
        from urllib.error import HTTPError
        fake_http_err = HTTPError(
            url="http://x/foo",
            code=500,
            msg="Internal Server Error",
            hdrs={},
            fp=mock.MagicMock(read=mock.Mock(return_value=b"comfyui crashed")),
        )
        with mock.patch.object(comfyui_client.request, "urlopen") as mock_urlopen:
            mock_urlopen.side_effect = fake_http_err
            client = comfyui_client.ComfyUIClient("http://x")
            with pytest.raises(Exception, match="HTTP 500"):
                client._make_request("/foo")

    def test_url_error_raises_exception(self):
        """URLError leve une Exception avec reason dans le message."""
        from urllib.error import URLError
        fake_url_err = URLError("Connection refused")
        with mock.patch.object(comfyui_client.request, "urlopen") as mock_urlopen:
            mock_urlopen.side_effect = fake_url_err
            client = comfyui_client.ComfyUIClient("http://x")
            with pytest.raises(Exception, match="URL Error"):
                client._make_request("/foo")


# ============================================================================
# queue_prompt
# ============================================================================

class TestQueuePrompt:
    """Enqueue d'un workflow dans ComfyUI."""

    def test_returns_prompt_id_from_response(self):
        """queue_prompt retourne response['prompt_id']."""
        with mock.patch.object(comfyui_client.request, "urlopen") as mock_urlopen:
            mock_urlopen.return_value = _fake_response({"prompt_id": "xyz-789"})
            client = comfyui_client.ComfyUIClient("http://x")
            result = client.queue_prompt({"1": {"class_type": "LoadImage"}})
        assert result == "xyz-789"

    def test_payload_includes_workflow_and_client_id(self):
        """Le payload contient le workflow + le client_id du client."""
        with mock.patch.object(comfyui_client.request, "urlopen") as mock_urlopen:
            mock_urlopen.return_value = _fake_response({"prompt_id": "x"})
            client = comfyui_client.ComfyUIClient("http://x")
            client.client_id = "test-cid-123"
            client.queue_prompt({"1": {"class_type": "Foo"}})
        req = mock_urlopen.call_args.args[0]
        body = json.loads(req.data.decode())
        assert body["prompt"] == {"1": {"class_type": "Foo"}}
        assert body["client_id"] == "test-cid-123"

    def test_missing_prompt_id_raises_exception(self):
        """Si response n'a pas 'prompt_id', leve Exception (pas silencieux)."""
        with mock.patch.object(comfyui_client.request, "urlopen") as mock_urlopen:
            mock_urlopen.return_value = _fake_response({"error": "bad workflow"})
            client = comfyui_client.ComfyUIClient("http://x")
            with pytest.raises(Exception, match="Prompt queue failed"):
                client.queue_prompt({"1": {}})

    def test_uses_post_method(self):
        """queue_prompt utilise POST (pas GET)."""
        with mock.patch.object(comfyui_client.request, "urlopen") as mock_urlopen:
            mock_urlopen.return_value = _fake_response({"prompt_id": "x"})
            client = comfyui_client.ComfyUIClient("http://x")
            client.queue_prompt({})
        req = mock_urlopen.call_args.args[0]
        assert req.method == "POST"
        # Endpoint /prompt (le code l'utilise directement).
        assert req.full_url == "http://x/prompt"


# ============================================================================
# get_system_stats / get_history
# ============================================================================

class TestSystemAndHistory:
    """Delegations simples a _make_request."""

    def test_get_system_stats_calls_system_stats_endpoint(self):
        """get_system_stats delegue a _make_request('/system_stats')."""
        with mock.patch.object(comfyui_client.ComfyUIClient, "_make_request") as mock_make:
            mock_make.return_value = {"system": {"ram_free": 1234}}
            client = comfyui_client.ComfyUIClient("http://x")
            result = client.get_system_stats()
        assert result == {"system": {"ram_free": 1234}}
        mock_make.assert_called_once_with("/system_stats")

    def test_get_history_uses_prompt_id_in_url(self):
        """get_history(prompt_id) delegue a _make_request('/history/<id>')."""
        with mock.patch.object(comfyui_client.ComfyUIClient, "_make_request") as mock_make:
            mock_make.return_value = {"abc-123": {"outputs": {}}}
            client = comfyui_client.ComfyUIClient("http://x")
            result = client.get_history("abc-123")
        assert result == {"abc-123": {"outputs": {}}}
        mock_make.assert_called_once_with("/history/abc-123")


# ============================================================================
# wait_for_completion
# ============================================================================

class TestWaitForCompletion:
    """Polling sur /history/<prompt_id> jusqu'a outputs/errors/timeout."""

    def test_returns_outputs_when_present(self):
        """Si history[prompt_id]['outputs'] existe, retourne le result immediatement."""
        with mock.patch.object(comfyui_client.ComfyUIClient, "get_history") as mock_get:
            mock_get.return_value = {
                "abc": {"outputs": {"images": ["img1.png", "img2.png"]}}
            }
            client = comfyui_client.ComfyUIClient("http://x")
            result = client.wait_for_completion("abc", timeout=10)
        assert result["outputs"]["images"] == ["img1.png", "img2.png"]

    def test_raises_on_workflow_errors(self):
        """Si history[prompt_id]['errors'] est non-vide, leve Exception."""
        with mock.patch.object(comfyui_client.ComfyUIClient, "get_history") as mock_get:
            mock_get.return_value = {
                "abc": {"errors": [{"type": "node_failure", "message": "boom"}]}
            }
            client = comfyui_client.ComfyUIClient("http://x")
            with pytest.raises(Exception, match="Workflow execution failed"):
                client.wait_for_completion("abc", timeout=10)

    def test_polls_until_outputs_ready(self):
        """Poll jusqu'a ce que 'outputs' apparaisse."""
        with mock.patch.object(comfyui_client.ComfyUIClient, "get_history") as mock_get, \
             mock.patch.object(comfyui_client.time, "sleep") as mock_sleep:
            # 3 polls: 2 sans outputs, 1 avec outputs
            mock_get.side_effect = [
                {"abc": {"status": "running"}},
                {"abc": {"status": "queued"}},
                {"abc": {"outputs": {"images": ["done.png"]}}},
            ]
            client = comfyui_client.ComfyUIClient("http://x")
            result = client.wait_for_completion("abc", timeout=10, poll_interval=1)
        assert result["outputs"]["images"] == ["done.png"]
        assert mock_sleep.call_count == 2  # sleep entre les polls (pas apres le dernier)
        assert mock_get.call_count == 3

    def test_timeout_raises_after_deadline(self):
        """Si timeout depasse sans outputs ni errors, leve TimeoutError."""
        with mock.patch.object(comfyui_client.ComfyUIClient, "get_history") as mock_get, \
             mock.patch.object(comfyui_client.time, "sleep") as mock_sleep, \
             mock.patch.object(comfyui_client.time, "time") as mock_time:
            # Simuler un timeout : start_time=100, time=100, 101, 102, 103...
            mock_time.side_effect = [100, 100, 200]  # Premier check: ok, 2e: timeout
            mock_get.return_value = {"abc": {"status": "still running"}}
            client = comfyui_client.ComfyUIClient("http://x")
            with pytest.raises(TimeoutError, match="timed out"):
                client.wait_for_completion("abc", timeout=10)
        # Verifier que le TimeoutError cite bien le prompt_id
        mock_sleep.assert_called_once()  # Sleep 1 fois avant le timeout

    def test_no_outputs_no_errors_keeps_polling(self):
        """Si history[prompt_id] existe mais sans outputs ni errors, continue polling."""
        with mock.patch.object(comfyui_client.ComfyUIClient, "get_history") as mock_get, \
             mock.patch.object(comfyui_client.time, "sleep") as mock_sleep:
            # 2 polls sans outputs, puis un avec outputs
            mock_get.side_effect = [
                {"abc": {"status": "in_progress"}},
                {"abc": {"status": "in_progress"}},
                {"abc": {"outputs": {"done": True}}},
            ]
            client = comfyui_client.ComfyUIClient("http://x")
            result = client.wait_for_completion("abc", timeout=10)
        assert result["outputs"] == {"done": True}

    def test_empty_history_dict_keeps_polling(self):
        """Si history ne contient pas prompt_id (workflow pas demarre), continue polling."""
        with mock.patch.object(comfyui_client.ComfyUIClient, "get_history") as mock_get, \
             mock.patch.object(comfyui_client.time, "sleep") as mock_sleep:
            mock_get.side_effect = [
                {},  # Pas encore dans l'history
                {"abc": {"outputs": {"img": "ok"}}},
            ]
            client = comfyui_client.ComfyUIClient("http://x")
            result = client.wait_for_completion("abc", timeout=10)
        assert result["outputs"]["img"] == "ok"


# ============================================================================
# Workflow builders — structural validation
# ============================================================================
#
# Les generate_* methods construisent un workflow dict et deleguent a
# queue_prompt + wait_for_completion. On teste ici la STRUCTURE du workflow
# (nodes, edges, class_type, inputs) sans appeler le serveur reel.
#


def _stub_queue_and_wait(workflow_captured):
    """Stub queue_prompt + wait_for_completion : capture le workflow, retourne result vide."""

    def _fake_queue(self, workflow):
        workflow_captured.append(workflow)
        return "fake-prompt-id"

    def _fake_wait(self, prompt_id, timeout=None):
        return {"outputs": {}}

    return _patch_queue(_fake_queue), _patch_wait(_fake_wait)


def _patch_queue(func):
    return mock.patch.object(comfyui_client.ComfyUIClient, "queue_prompt", func)


def _patch_wait(func):
    return mock.patch.object(comfyui_client.ComfyUIClient, "wait_for_completion", func)


class TestGenerateText2Image:
    """Workflow Qwen natif Phase 29 (FP8 Comfy-Org)."""

    def test_workflow_uses_native_qwen_nodes(self):
        """Architecture Phase 29 : VAELoader + CLIPLoader + UNETLoader."""
        captured = []
        with _patch_queue(lambda self, wf: (captured.append(wf) or "id")), \
             _patch_wait(lambda self, pid, timeout=None: {"outputs": {}}):
            client = comfyui_client.ComfyUIClient("http://x")
            client.generate_text2image("a cat")
        wf = captured[0]
        # 11 nodes pour le workflow Qwen natif complet.
        assert len(wf) == 11
        # Nodes critiques Phase 29.
        assert wf["1"]["class_type"] == "VAELoader"
        assert wf["2"]["class_type"] == "CLIPLoader"
        assert wf["2"]["inputs"]["type"] == "sd3"
        assert wf["3"]["class_type"] == "UNETLoader"
        assert wf["3"]["inputs"]["weight_dtype"] == "fp8_e4m3fn"
        assert wf["4"]["class_type"] == "ModelSamplingAuraFlow"
        assert wf["4"]["inputs"]["shift"] == 3.0
        assert wf["5"]["class_type"] == "CFGNorm"
        assert wf["6"]["class_type"] == "TextEncodeQwenImageEdit"
        assert wf["7"]["class_type"] == "ConditioningZeroOut"
        assert wf["8"]["class_type"] == "EmptySD3LatentImage"
        assert wf["9"]["class_type"] == "KSampler"
        assert wf["9"]["inputs"]["scheduler"] == "beta"
        assert wf["9"]["inputs"]["cfg"] == 1.0
        assert wf["10"]["class_type"] == "VAEDecode"
        assert wf["11"]["class_type"] == "SaveImage"

    def test_prompt_propagated_to_text_encode_node(self):
        """Le prompt est injecte dans node 6 (TextEncodeQwenImageEdit)."""
        captured = []
        with _patch_queue(lambda self, wf: (captured.append(wf) or "id")), \
             _patch_wait(lambda self, pid, timeout=None: {"outputs": {}}):
            client = comfyui_client.ComfyUIClient("http://x")
            client.generate_text2image("a fluffy cat sitting on a red cushion")
        wf = captured[0]
        assert wf["6"]["inputs"]["prompt"] == "a fluffy cat sitting on a red cushion"

    def test_steps_kwarg_overrides_num_inference_steps(self):
        """L'alias 'steps' prend precedence sur 'num_inference_steps'."""
        captured = []
        with _patch_queue(lambda self, wf: (captured.append(wf) or "id")), \
             _patch_wait(lambda self, pid, timeout=None: {"outputs": {}}):
            client = comfyui_client.ComfyUIClient("http://x")
            client.generate_text2image("x", steps=10, num_inference_steps=99)
        wf = captured[0]
        # KSampler (node 9) doit avoir steps=10 (PAS 99).
        assert wf["9"]["inputs"]["steps"] == 10

    def test_default_inference_steps_is_20(self):
        """Sans steps/num_inference_steps : default 20 (optimal Qwen)."""
        captured = []
        with _patch_queue(lambda self, wf: (captured.append(wf) or "id")), \
             _patch_wait(lambda self, pid, timeout=None: {"outputs": {}}):
            client = comfyui_client.ComfyUIClient("http://x")
            client.generate_text2image("x")
        wf = captured[0]
        assert wf["9"]["inputs"]["steps"] == 20


class TestGenerateText2ImageLightning:
    """Workflow Nunchaku Lightning V2.0 INT4 (4 steps)."""

    def test_uses_nunchaku_loader_not_unet_loader(self):
        """Lightning utilise NunchakuQwenImageDiTLoader (PAS UNETLoader)."""
        captured = []
        with _patch_queue(lambda self, wf: (captured.append(wf) or "id")), \
             _patch_wait(lambda self, pid, timeout=None: {"outputs": {}}):
            client = comfyui_client.ComfyUIClient("http://x")
            client.generate_text2image_lightning("a cat")
        wf = captured[0]
        # Node 3 = NunchakuQwenImageDiTLoader (PAS UNETLoader).
        assert wf["3"]["class_type"] == "NunchakuQwenImageDiTLoader"
        # Pas de UNETLoader dans le workflow.
        for node_id, node in wf.items():
            assert node["class_type"] != "UNETLoader", f"Node {node_id} unexpectedly uses UNETLoader"

    def test_lightning_uses_simple_scheduler_not_beta(self):
        """Lightning utilise scheduler='simple' (PAS 'beta' comme Qwen natif)."""
        captured = []
        with _patch_queue(lambda self, wf: (captured.append(wf) or "id")), \
             _patch_wait(lambda self, pid, timeout=None: {"outputs": {}}):
            client = comfyui_client.ComfyUIClient("http://x")
            client.generate_text2image_lightning("a cat")
        wf = captured[0]
        assert wf["9"]["inputs"]["scheduler"] == "simple"

    def test_lightning_default_steps_is_4(self):
        """Lightning a steps=4 par defaut (vs 20 pour Qwen natif)."""
        captured = []
        with _patch_queue(lambda self, wf: (captured.append(wf) or "id")), \
             _patch_wait(lambda self, pid, timeout=None: {"outputs": {}}):
            client = comfyui_client.ComfyUIClient("http://x")
            client.generate_text2image_lightning("a cat")
        wf = captured[0]
        assert wf["9"]["inputs"]["steps"] == 4

    def test_lightning_clip_type_is_qwen_image(self):
        """CLIPLoader (node 2) utilise type='qwen_image' (PAS 'sd3')."""
        captured = []
        with _patch_queue(lambda self, wf: (captured.append(wf) or "id")), \
             _patch_wait(lambda self, pid, timeout=None: {"outputs": {}}):
            client = comfyui_client.ComfyUIClient("http://x")
            client.generate_text2image_lightning("a cat")
        wf = captured[0]
        assert wf["2"]["inputs"]["type"] == "qwen_image"


class TestGenerateText2VideoWan:
    """Workflow Wan 2.1 1.3B (EmptyHunyuanLatentVideo + Wan CLIP)."""

    def test_workflow_uses_wan_clip_loader(self):
        """Wan utilise CLIPLoader avec type='wan' (PAS 'sd3' ni 'qwen_image')."""
        captured = []
        with _patch_queue(lambda self, wf: (captured.append(wf) or "id")), \
             _patch_wait(lambda self, pid, timeout=None: {"outputs": {}}):
            client = comfyui_client.ComfyUIClient("http://x")
            client.generate_text2video_wan("a cat walking")
        wf = captured[0]
        # CLIPLoader (node 38) avec type='wan'.
        clip_nodes = [n for n in wf.values() if n["class_type"] == "CLIPLoader"]
        assert len(clip_nodes) >= 1
        assert any(n["inputs"].get("type") == "wan" for n in clip_nodes)

    def test_workflow_uses_empty_hunyuan_latent_video(self):
        """Wan utilise EmptyHunyuanLatentVideo (PAS EmptySD3LatentImage)."""
        captured = []
        with _patch_queue(lambda self, wf: (captured.append(wf) or "id")), \
             _patch_wait(lambda self, pid, timeout=None: {"outputs": {}}):
            client = comfyui_client.ComfyUIClient("http://x")
            client.generate_text2video_wan("a cat walking")
        wf = captured[0]
        # EmptyHunyuanLatentVideo PAS EmptySD3LatentImage (Qwen image).
        assert any(n["class_type"] == "EmptyHunyuanLatentVideo" for n in wf.values())
        assert not any(n["class_type"] == "EmptySD3LatentImage" for n in wf.values())

    def test_wan_default_frames_is_16(self):
        """Wan : num_frames=16 par defaut."""
        captured = []
        with _patch_queue(lambda self, wf: (captured.append(wf) or "id")), \
             _patch_wait(lambda self, pid, timeout=None: {"outputs": {}}):
            client = comfyui_client.ComfyUIClient("http://x")
            client.generate_text2video_wan("a cat walking")
        wf = captured[0]
        latent_node = next(n for n in wf.values() if n["class_type"] == "EmptyHunyuanLatentVideo")
        assert latent_node["inputs"]["frame_limit"] == 16


class TestGenerateBonsai:
    """Workflow BonsaiTernaryNode (Bonsai-Image 4B 2-bit ternary)."""

    def test_workflow_uses_bonsai_ternary_node(self):
        """Bonsai utilise BonsaiTernaryNode (custom node ComfyUI-Bonsai)."""
        captured = []
        with _patch_queue(lambda self, wf: (captured.append(wf) or "id")), \
             _patch_wait(lambda self, pid, timeout=None: {"outputs": {}}):
            client = comfyui_client.ComfyUIClient("http://x")
            client.generate_bonsai("a bonsai tree")
        wf = captured[0]
        assert wf["1"]["class_type"] == "BonsaiTernaryNode"

    def test_bonsai_default_model_type(self):
        """Bonsai : model_type='Bonsai-4B (2-Bit Ternary)' par defaut."""
        captured = []
        with _patch_queue(lambda self, wf: (captured.append(wf) or "id")), \
             _patch_wait(lambda self, pid, timeout=None: {"outputs": {}}):
            client = comfyui_client.ComfyUIClient("http://x")
            client.generate_bonsai("a bonsai tree")
        wf = captured[0]
        assert wf["1"]["inputs"]["model_type"] == "Bonsai-4B (2-Bit Ternary)"

    def test_bonsai_includes_save_image_node(self):
        """Bonsai inclut un node SaveImage (node 2)."""
        captured = []
        with _patch_queue(lambda self, wf: (captured.append(wf) or "id")), \
             _patch_wait(lambda self, pid, timeout=None: {"outputs": {}}):
            client = comfyui_client.ComfyUIClient("http://x")
            client.generate_bonsai("a bonsai tree")
        wf = captured[0]
        assert wf["2"]["class_type"] == "SaveImage"


class TestSeedHandling:
    """Generation de seed aleatoire si None."""

    def test_seed_default_is_random_in_range(self):
        """Si seed=None, un random 0..2^32-1 est utilise."""
        captured = []
        with _patch_queue(lambda self, wf: (captured.append(wf) or "id")), \
             _patch_wait(lambda self, pid, timeout=None: {"outputs": {}}):
            client = comfyui_client.ComfyUIClient("http://x")
            # Mock random.randint pour controler le seed.
            with mock.patch.object(comfyui_client.random, "randint") as mock_rand:
                mock_rand.return_value = 12345
                client.generate_text2image("a cat")
        wf = captured[0]
        # KSampler (node 9) utilise le seed mocke.
        assert wf["9"]["inputs"]["seed"] == 12345
        mock_rand.assert_called_once_with(0, 2**32 - 1)

    def test_explicit_seed_used_verbatim(self):
        """Si seed est explicite, il est utilise tel quel (random NON appele)."""
        captured = []
        with _patch_queue(lambda self, wf: (captured.append(wf) or "id")), \
             _patch_wait(lambda self, pid, timeout=None: {"outputs": {}}):
            client = comfyui_client.ComfyUIClient("http://x")
            with mock.patch.object(comfyui_client.random, "randint") as mock_rand:
                client.generate_text2image("a cat", seed=42)
                mock_rand.assert_not_called()
        wf = captured[0]
        assert wf["9"]["inputs"]["seed"] == 42


# ============================================================================
# load_from_env
# ============================================================================

class TestLoadFromEnv:
    """Charge un client ComfyUI depuis .env."""

    def test_creates_client_from_env_url(self, tmp_path):
        """Lit COMFYUI_API_URL et cree un client avec server_url."""
        env_file = tmp_path / ".env"
        env_file.write_text(
            "COMFYUI_API_URL=http://comfy:8188\n"
            "COMFYUI_API_TOKEN=secret-abc\n"
        )
        client = comfyui_client.load_from_env(env_file)
        assert client.server_url == "http://comfy:8188"
        assert client.api_token == "secret-abc"

    def test_raises_if_no_env_file_found(self, tmp_path):
        """Si aucun .env trouve dans cwd/parents, leve ValueError."""
        # tmp_path isole, pas de .env dedans.
        with mock.patch.object(comfyui_client.Path, "cwd", return_value=tmp_path):
            with pytest.raises(ValueError, match="non trouv"):
                comfyui_client.load_from_env()

    def test_raises_if_no_url_in_env(self, tmp_path):
        """Si .env existe mais sans COMFYUI_API_URL, leve ValueError."""
        env_file = tmp_path / ".env"
        env_file.write_text("OTHER_VAR=foo\n")
        with pytest.raises(ValueError, match="COMFYUI_API_URL manquant"):
            comfyui_client.load_from_env(env_file)

    def test_quotes_stripped_from_env_values(self, tmp_path):
        """Les valeurs .env ont leurs quotes simples/doubles strippees."""
        env_file = tmp_path / ".env"
        env_file.write_text(
            'COMFYUI_API_URL="http://comfy:8188"\n'
            "COMFYUI_API_TOKEN='secret-abc'\n"
        )
        client = comfyui_client.load_from_env(env_file)
        assert client.server_url == "http://comfy:8188"
        assert client.api_token == "secret-abc"

    def test_comments_ignored(self, tmp_path):
        """Les lignes commencant par # sont ignorees."""
        env_file = tmp_path / ".env"
        env_file.write_text(
            "# This is a comment\n"
            "COMFYUI_API_URL=http://comfy:8188\n"
            "# Another comment\n"
            "COMFYUI_API_TOKEN=secret\n"
        )
        client = comfyui_client.load_from_env(env_file)
        assert client.server_url == "http://comfy:8188"
        assert client.api_token == "secret"


# ============================================================================
# create_client
# ============================================================================

class TestCreateClient:
    """Factory create_client."""

    def test_create_client_with_config(self):
        """create_client(config) utilise la config explicite."""
        config = comfyui_client.ComfyUIConfig(
            base_url="http://custom:9000",
            api_token="tok",
        )
        client = comfyui_client.create_client(config)
        assert client.server_url == "http://custom:9000"
        assert client.api_token == "tok"

    def test_create_client_without_config_falls_back_to_env(self, tmp_path):
        """create_client() sans config charge depuis .env."""
        env_file = tmp_path / ".env"
        env_file.write_text("COMFYUI_API_URL=http://env:8188\n")
        with mock.patch.object(comfyui_client.Path, "cwd", return_value=tmp_path):
            client = comfyui_client.create_client()
        assert client.server_url == "http://env:8188"