"""Tests des operations FICHIERS et BIBLIOTHEQUE de qc-mcp-lite.

Ces tests vivaient dans `test_server.py`, qui a franchi le plafond des 800
lignes impose aux scripts neufs par le cliquet de taille
(`scripts/tests/test_script_size_ratchet.py`). Le scindage est mecanique : le
corps des tests est repris verbatim, seul le module qui les porte change.
"""
import sys
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).parent.parent))
from server import (
    attach_library,
    create_file,
    delete_file,
    read_file,
    read_project,
    update_file_contents,
)

from ._qc_helpers import _DUMMY_ENV, _mock_api_response


@patch.dict("os.environ", _DUMMY_ENV)
class TestReadProjectLibraries:
    def test_surfaces_the_attached_libraries_and_their_flag(self):
        """The attached libraries are listed, and their files carry
        `isLibrary: true` — a green compile proves nothing, the listing does."""
        project = _mock_api_response({
            "projects": [{
                "projectId": 42,
                "name": "Consumer",
                "organizationId": "org-consumer",
                "libraries": [
                    {"projectId": 37966475, "libraryName": "SharedPCM", "access": True},
                ],
            }]
        })
        files = _mock_api_response({
            "files": [
                {"name": "main.py", "content": "x" * 10},
                {"name": "pouches_pcm.py", "content": "y" * 20, "isLibrary": True},
            ]
        })
        with patch("requests.post", side_effect=[project, files]):
            result = read_project(42)
        assert result["libraries"] == [
            {"projectId": 37966475, "libraryName": "SharedPCM", "access": True}
        ]
        library_files = [f for f in result["files"] if f["isLibrary"]]
        assert library_files == [{"name": "pouches_pcm.py", "size": 20, "isLibrary": True}]


@patch.dict("os.environ", _DUMMY_ENV)
class TestAttachLibrary:
    def test_attaches_by_numeric_id_and_returns_the_proof(self):
        """The library is designated by its NUMERIC id — QC rejects the name
        ("Given library ID is not valid")."""
        update = _mock_api_response({"success": True})
        project = _mock_api_response({
            "projects": [{
                "projectId": 42,
                "libraries": [
                    {"projectId": 37966475, "libraryName": "SharedPCM", "access": True},
                ],
            }]
        })
        files = _mock_api_response({
            "files": [
                {"name": "main.py", "content": "x" * 10},
                {"name": "pouches_pcm.py", "content": "y" * 20, "isLibrary": True},
            ]
        })
        with patch("requests.post", side_effect=[update, project, files]) as mock_post:
            result = attach_library(42, 37966475)

        assert mock_post.call_args_list[0].args[0].endswith("/projects/update")
        assert mock_post.call_args_list[0].kwargs["json"] == {
            "projectId": 42,
            "libraries": [37966475],
        }
        assert result["libraries"] == [
            {"projectId": 37966475, "libraryName": "SharedPCM", "access": True}
        ]
        assert result["libraryFiles"] == ["pouches_pcm.py"]

    def test_cross_organization_attachment_is_accepted(self):
        """The library may live in another organization than the consumer."""
        update = _mock_api_response({"success": True})
        project = _mock_api_response({
            "projects": [{
                "projectId": 42,
                "libraries": [
                    {"projectId": 37966475, "libraryName": "SharedPCM", "access": True},
                ],
            }]
        })
        files = _mock_api_response({"files": []})
        with patch("requests.post", side_effect=[update, project, files]):
            result = attach_library(42, 37966475)
        assert result["libraries"][0]["access"] is True


@patch.dict("os.environ", _DUMMY_ENV)
class TestDeleteFile:
    def test_deletes_the_named_file(self):
        """The old local copy of a shared module is dropped once the library
        is attached — the consumer then reads the single source."""
        mock_resp = _mock_api_response({"success": True})
        with patch("requests.post", return_value=mock_resp) as mock_post:
            result = delete_file(42, "pouches_pcm.py")
        assert mock_post.call_args.kwargs["json"] == {
            "projectId": 42,
            "name": "pouches_pcm.py",
        }
        assert mock_post.call_args.args[0].endswith("/files/delete")
        assert result == {"success": True, "name": "pouches_pcm.py"}


@patch.dict("os.environ", _DUMMY_ENV)
class TestReadFile:
    def test_reads_specific_file(self):
        mock_resp = _mock_api_response({
            "files": [{"name": "main.py", "content": "print('hello')"}]
        })
        with patch("requests.post", return_value=mock_resp):
            result = read_file(1, "main.py")
            assert result["name"] == "main.py"
            assert result["content"] == "print('hello')"

    def test_reads_all_files(self):
        mock_resp = _mock_api_response({
            "files": [
                {"name": "main.py", "content": "code1"},
                {"name": "alpha.py", "content": "code2" * 100},
            ]
        })
        with patch("requests.post", return_value=mock_resp):
            result = read_file(1)
            assert result["count"] == 2
            assert result["files"][1]["size"] > 0


@patch.dict("os.environ", _DUMMY_ENV)
class TestUpdateFile:
    def test_update_file_contents(self):
        mock_resp = _mock_api_response({"success": True})
        with patch("requests.post", return_value=mock_resp) as mock_post:
            result = update_file_contents(1, "main.py", "new content")
            assert result["success"] is True
            assert result["name"] == "main.py"
            body = mock_post.call_args.kwargs["json"]
            assert body["content"] == "new content"


@patch.dict("os.environ", _DUMMY_ENV)
class TestCreateFile:
    def test_create_file(self):
        mock_resp = _mock_api_response({"success": True})
        with patch("requests.post", return_value=mock_resp) as mock_post:
            result = create_file(1, "new_file.py", "# new file")
            assert result["success"] is True
            body = mock_post.call_args.kwargs["json"]
            assert body["name"] == "new_file.py"
            assert body["content"] == "# new file"

    def test_create_file_empty_content(self):
        mock_resp = _mock_api_response({"success": True})
        with patch("requests.post", return_value=mock_resp) as mock_post:
            result = create_file(1, "empty.py")
            assert result["success"] is True
            body = mock_post.call_args.kwargs["json"]
            assert body["content"] == ""
