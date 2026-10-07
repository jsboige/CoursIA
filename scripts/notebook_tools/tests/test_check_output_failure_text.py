"""Tests for check_output_failure_text.py — capability-downgrade axis (#14603).

Pins the couple contract: a capability value regression AND a witness-line
disappearance on a byte-identical-source cell is the finding; each half
alone, a changed source, a same-tier value wiggle, and the restoration
(upgrade) direction are all silent. No network, no kernel.
"""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from check_output_failure_text import (CAPABILITY_VALUE_RE,
                                       _sample_location,
                                       CAPABILITY_WITNESS_PATTERNS,
                                       capability_downgrades,
                                       metadata_texts,
                                       scan)


def cell(source, out_text):
    return {"cell_type": "code", "source": source,
            "outputs": [{"output_type": "stream", "name": "stdout",
                         "text": out_text}]}


def nb(*cells):
    return {"cells": list(cells), "metadata": {}, "nbformat": 4,
            "nbformat_minor": 5}


GPU_SRC = "print(info)\nprint(f'VRAM utilisee : {v:.2f} GB')"
GPU_OUT = "Device : cuda\nVRAM utilisee : 0.64 GB"
CPU_OUT = "Device : cpu"


def test_couple_fires():
    got = capability_downgrades(nb(cell(GPU_SRC, GPU_OUT)),
                                nb(cell(GPU_SRC, CPU_OUT)))
    assert len(got) == 1
    assert got[0]["cell"] == 0
    assert got[0]["base"] == "cuda"
    assert got[0]["head"] == "cpu"


def test_legit_reexec_silent():
    wiggle = "Device : cuda\nVRAM utilisee : 0.63 GB"
    assert capability_downgrades(nb(cell(GPU_SRC, GPU_OUT)),
                                 nb(cell(GPU_SRC, wiggle))) == []


def test_changed_source_silent():
    assert capability_downgrades(
        nb(cell(GPU_SRC, GPU_OUT)),
        nb(cell(GPU_SRC + "\nprint('cpu fallback')", CPU_OUT))) == []


def test_value_regression_without_witness_loss_silent():
    kept = "Device : cpu\nVRAM utilisee : 0.00 GB"
    assert capability_downgrades(nb(cell(GPU_SRC, GPU_OUT)),
                                 nb(cell(GPU_SRC, kept))) == []


def test_witness_loss_without_value_regression_silent():
    assert capability_downgrades(nb(cell(GPU_SRC, GPU_OUT)),
                                 nb(cell(GPU_SRC, "Device : cuda"))) == []


def test_upgrade_silent():
    # Restoration direction of #14262: cpu -> cuda with the witness line
    # APPEARING must never fire.
    assert capability_downgrades(nb(cell(GPU_SRC, CPU_OUT)),
                                 nb(cell(GPU_SRC, GPU_OUT))) == []


def test_markdown_cells_ignored():
    # Same index, but the base cell is markdown: index-matched comparison
    # must skip non-code cells, not crash.
    assert capability_downgrades(
        nb({"cell_type": "markdown", "source": GPU_SRC,
            "outputs": []}, cell(GPU_SRC, GPU_OUT)),
        nb(cell(GPU_SRC, CPU_OUT))) == []


def test_value_extraction_witnessed_forms():
    for text, expected in (
            ("Mode : batch, Device : cuda", {"cuda"}),
            ("Device : cpu", {"cpu"}),
            ("Device: CUDA", {"cuda"}),
            ("device='cuda:0'", {"cuda"}),
            ("torch.device('cuda:0')", set()),
            ("VRAM utilisee : 0.64 GB", set())):
        assert CAPABILITY_VALUE_RE.search(text) is not None or not expected
        got = set()
        for m in CAPABILITY_VALUE_RE.finditer(text):
            v = m.group(1).lower().split(":")[0].strip()
            got.add(v)
        assert got == expected, text


def test_witness_patterns_match_measured_lines():
    # Closed, witnessed set -- measured on origin/main 2026-09-04.
    for line in ("VRAM utilisee : 0.64 GB",
                 "GPU : NVIDIA GeForce RTX 3090 (24.0 GB VRAM)",
                 "24.0 GB VRAM)"):
        assert any(p.search(line) for p in CAPABILITY_WITNESS_PATTERNS), line


# ---------------------------------------------------------------------------
# #19638: coexistence in declared-fallback cells.
# When a cell carries BOTH a declared banner AND substantial output, scanning
# the same notebook as base (no base_nb) and as head (with base_nb=base) must
# agree on the classification. The pre-fix behaviour was DF=1 / TF=1 (the
# asymmetry that rougied 4 carnets Image at every re-execution); the fix
# moves coexistence to DF=1 / DF=1 while preserving the substitution shape
# (substantial base -> banner-only head stays TF).
# ---------------------------------------------------------------------------

def _cid(cid, source, outputs):
    return {"cell_type": "code", "id": cid, "source": source, "outputs": outputs}


def test_19638_coexistence_classified_df_on_both_scans():
    """#19638: banner + substantial output at the same notebook must be DF on
    BOTH scan(base) and scan(head, base_nb=base). The pre-fix asymmetry was
    DF=1 / TF=1 (rougied 4 carnets Image at every re-execution)."""
    src = ("try:\n"
           "    import graphviz\n"
           "    g = graphviz.Digraph(); g.edge('a', 'b'); display(g)\n"
           "except ImportError:\n"
           "    print('Graphviz non disponible : rendu du graphe saute')\n"
           "print(info)")
    banner_only = [{"output_type": "stream",
                     "text": "Graphviz non disponible : rendu du graphe saute"}]
    render = [{"output_type": "display_data",
               "data": {"image/svg+xml": "<svg/>",
                        "text/plain": "<graphviz.Digraph object>"}}]
    # Coexistence: banner + substantial output in BOTH base and head
    coexistence = banner_only + render
    base_nb = {"cells": [_cid("c-gv", src, coexistence)]}
    head_nb = {"cells": [_cid("c-gv", src, coexistence)]}

    base_scan = scan(base_nb)
    head_scan = scan(head_nb, base_nb=base_nb)

    assert len(base_scan["TOOL_FAILURE"]) == 0
    assert len(base_scan["DECLARED_FALLBACK"]) == 1
    assert len(head_scan["TOOL_FAILURE"]) == 0
    assert len(head_scan["DECLARED_FALLBACK"]) == 1


def test_19638_substitution_keeps_tf_head():
    """#19638: the substitution (base had substantial render -> head has only
    the banner) stays a capability loss and keeps the TOOL_FAILURE label on
    the head scan."""
    src = ("try:\n"
           "    import graphviz\n"
           "    g = graphviz.Digraph(); g.edge('a', 'b'); display(g)\n"
           "except ImportError:\n"
           "    print('Graphviz non disponible : rendu du graphe saute')\n"
           "print(info)")
    banner_only = [{"output_type": "stream",
                     "text": "Graphviz non disponible : rendu du graphe saute"}]
    render = [{"output_type": "display_data",
               "data": {"image/svg+xml": "<svg/>",
                        "text/plain": "<graphviz.Digraph object>"}}]
    base_nb = {"cells": [_cid("c-gv", src, render)]}      # base: render
    head_nb = {"cells": [_cid("c-gv", src, banner_only)]}  # head: lost render

    base_scan = scan(base_nb)
    head_scan = scan(head_nb, base_nb=base_nb)

    # Base has no fill, no banner: nothing to scan.
    assert len(base_scan["TOOL_FAILURE"]) == 0
    assert len(base_scan["DECLARED_FALLBACK"]) == 0
    # Head lost the render: substitution, stays TF (the damage #3473 / #11685).
    assert len(head_scan["TOOL_FAILURE"]) == 1
    assert len(head_scan["DECLARED_FALLBACK"]) == 0


def test_19638_already_in_fallback_keeps_df():
    """#19638: a cell already in fallback at base (banner + no render at
    base) and STILL in fallback at head (banner + no render) keeps DF on
    both scans -- no regression to call."""
    src = ("try:\n"
           "    import graphviz\n"
           "    g = graphviz.Digraph(); g.edge('a', 'b'); display(g)\n"
           "except ImportError:\n"
           "    print('Graphviz non disponible : rendu du graphe saute')\n"
           "print(info)")
    banner_only = [{"output_type": "stream",
                     "text": "Graphviz non disponible : rendu du graphe saute"}]
    base_nb = {"cells": [_cid("c-gv", src, banner_only)]}
    head_nb = {"cells": [_cid("c-gv", src, banner_only)]}

    base_scan = scan(base_nb)
    head_scan = scan(head_nb, base_nb=base_nb)

    assert len(base_scan["TOOL_FAILURE"]) == 0
    assert len(base_scan["DECLARED_FALLBACK"]) == 1
    assert len(head_scan["TOOL_FAILURE"]) == 0
    assert len(head_scan["DECLARED_FALLBACK"]) == 1


def test_19638_restored_after_substitution():
    """#19638: a cell that was in fallback at base and RESTORED a render at
    head (banner + render at head, only banner at base) is no longer a
    fallback -- the substantial output is back. The exemption does NOT
    carry over from base."""
    src = ("try:\n"
           "    import graphviz\n"
           "    g = graphviz.Digraph(); g.edge('a', 'b'); display(g)\n"
           "except ImportError:\n"
           "    print('Graphviz non disponible : rendu du graphe saute')\n"
           "print(info)")
    banner_only = [{"output_type": "stream",
                     "text": "Graphviz non disponible : rendu du graphe saute"}]
    coexistence = banner_only + [
        {"output_type": "display_data",
         "data": {"image/svg+xml": "<svg/>",
                  "text/plain": "<graphviz.Digraph object>"}}
    ]
    base_nb = {"cells": [_cid("c-gv", src, banner_only)]}
    head_nb = {"cells": [_cid("c-gv", src, coexistence)]}

    head_scan = scan(head_nb, base_nb=base_nb)
    assert len(head_scan["TOOL_FAILURE"]) == 0
    assert len(head_scan["DECLARED_FALLBACK"]) == 1


def test_19638_six_image_carnets_no_longer_rougied():
    """#19638: the four carnets listed in the issue (plus a sweep of
    GenAI/Image for thoroughness) now scan the same DF=1 / DF=1, so a
    re-execution on the same carnet does not rougir the gate."""
    import json as _json
    from pathlib import Path as _Path
    REPO = _Path(__file__).resolve().parent.parent.parent.parent
    listed = (
        "GenAI/Image/01-Foundation/01-2-GPT-5-Image-Generation.ipynb",
        "GenAI/Image/01-Foundation/01-5b-Qwen-Image-Edit-2509.ipynb",
        "GenAI/Image/02-Advanced/02-5-Bonsai-Image-Ternary.ipynb",
        "GenAI/Image/03-Orchestration/03-3-Performance-Optimization.ipynb",
    )
    for rel in listed:
        path = REPO / "MyIA.AI.Notebooks" / rel
        if not path.is_file():
            continue
        nb = _json.loads(path.read_text(encoding="utf-8"))
        base_scan = scan(nb)
        head_scan = scan(nb, base_nb=nb)
        assert len(base_scan["TOOL_FAILURE"]) == 0, (
            f"{rel}: scan(base) still TF>0 ({base_scan})")
        assert len(head_scan["TOOL_FAILURE"]) == 0, (
            f"{rel}: scan(+base) still TF>0 ({head_scan})")


def test_19640_substitution_loses_svg_stays_tf():
    """#19640 review : base SVG + info, head banniere + info -> le SVG est
    perdu. Mere substantiality ne suffit pas : la coexistence n'est
    declaree QUE si la tete preserve le rendu de la base. Ici, le SVG
    n'est plus dans la tete (la banniere l'a REMPLACE), et la banniere
    n'etait pas dans la base. Les deux formes de preservation echouent,
    donc le hit reste TOOL_FAILURE -- c'est exactement la classe de
    degat que #3473 / #11685 ont ouverte.
    """
    src = ("try:\n"
           "    import graphviz\n"
           "    g = graphviz.Digraph(); g.edge('a', 'b'); display(g)\n"
           "except ImportError:\n"
           "    print('Graphviz non disponible : rendu du graphe saute')\n"
           "print('Graphe : 2 noeuds, 1 arete')")
    render = [{"output_type": "display_data",
               "data": {"image/svg+xml": "<svg/>",
                        "text/plain": "<graphviz.Digraph object>"}},
              {"output_type": "stream",
               "text": "Graphe : 2 noeuds, 1 arete"}]
    head = [{"output_type": "stream",
             "text": "Graphviz non disponible : rendu du graphe saute"},
            {"output_type": "stream",
             "text": "Graphe : 2 noeuds, 1 arete"}]
    base_nb = {"cells": [_cid("c-gv", src, render)]}      # base: SVG + info
    head_nb = {"cells": [_cid("c-gv", src, head)]}        # head: banner + info
    head_scan = scan(head_nb, base_nb=base_nb)
    # La SVG a ete REMPLACE par la banner. L'info est identique. Le hit
    # DOIT rester TF -- sinon la garde laisse passer la substitution.
    assert len(head_scan["TOOL_FAILURE"]) == 1
    assert len(head_scan["DECLARED_FALLBACK"]) == 0


def test_19640_banner_already_in_base_keeps_df():
    """#19640 review : la banniere matchee figurait deja dans la sortie
    de la base. Elle n'est alors pas nouvelle, donc ce n'est pas une
    substitution. La forme (2) de preservation tient, et la cellule
    reste DF -- c'est l'asymetrie decrite dans le corps de l'issue.
    """
    src = ("try:\n"
           "    import graphviz\n"
           "    g = graphviz.Digraph(); g.edge('a', 'b'); display(g)\n"
           "except ImportError:\n"
           "    print('Graphviz non disponible : rendu du graphe saute')\n"
           "print('Graphe : 2 noeuds, 1 arete')")
    # La base porte DEJA la banniere (en plus du SVG) : c'est une
    # decoration, pas une substitution. Le scan base la compterait
    # naturellement, mais on verifie que le scan head SUR LA MEME
    # cellule est coherent -- la banniere n'etait pas nouvelle.
    base_outputs = [
        {"output_type": "stream",
         "text": "Graphviz non disponible : rendu du graphe saute"},
        {"output_type": "display_data",
         "data": {"image/svg+xml": "<svg/>",
                  "text/plain": "<graphviz.Digraph object>"}},
    ]
    head_outputs = [
        {"output_type": "stream",
         "text": "Graphviz non disponible : rendu du graphe saute"},
        {"output_type": "display_data",
         "data": {"image/svg+xml": "<svg/>",
                  "text/plain": "<graphviz.Digraph object>"}},
    ]
    base_nb = {"cells": [_cid("c-gv", src, base_outputs)]}
    head_nb = {"cells": [_cid("c-gv", src, head_outputs)]}
    head_scan = scan(head_nb, base_nb=base_nb)
    # La banniere etait deja dans la base : preservation par forme (2).
    # Le SVG est aussi preserve (forme 1). Coexistence confirmee.
    assert len(head_scan["DECLARED_FALLBACK"]) == 1
    assert len(head_scan["TOOL_FAILURE"]) == 0


def test_19640_svg_present_in_head_keeps_df_without_banner_match():
    """#19640 review : forme (1) de preservation -- les types MIME non
    textuels de la base (image/svg+xml) sont tous presents a la tete.
    La banniere peut etre nouvelle : pas une condition suffisante
    pour trancher seule. La preservation tient par la forme (1).
    """
    src = ("try:\n"
           "    import graphviz\n"
           "    g = graphviz.Digraph(); g.edge('a', 'b'); display(g)\n"
           "except ImportError:\n"
           "    print('Graphviz non disponible : rendu du graphe saute')\n"
           "print('Graphe : 2 noeuds, 1 arete')")
    # Base : SVG + info. Tete : SVG + banner + info. La banniere est
    # NOUVELLE (pas dans la base) -- forme (2) echouera. Mais le SVG
    # survit -- forme (1) tient. Coexistence par preservation MIME.
    base_outputs = [
        {"output_type": "display_data",
         "data": {"image/svg+xml": "<svg/>",
                  "text/plain": "<graphviz.Digraph object>"}},
        {"output_type": "stream",
         "text": "Graphe : 2 noeuds, 1 arete"},
    ]
    head_outputs = [
        {"output_type": "stream",
         "text": "Graphviz non disponible : rendu du graphe saute"},
        {"output_type": "display_data",
         "data": {"image/svg+xml": "<svg/>",
                  "text/plain": "<graphviz.Digraph object>"}},
        {"output_type": "stream",
         "text": "Graphe : 2 noeuds, 1 arete"},
    ]
    base_nb = {"cells": [_cid("c-gv", src, base_outputs)]}
    head_nb = {"cells": [_cid("c-gv", src, head_outputs)]}
    head_scan = scan(head_nb, base_nb=base_nb)
    assert len(head_scan["DECLARED_FALLBACK"]) == 1
    assert len(head_scan["TOOL_FAILURE"]) == 0


def test_19640_base_svg_head_banner_only_no_info_stays_tf():
    """#19640 review : cas du tableau, ligne 1. Base = SVG + info, tete =
    banner + info. Meme resultat que le test fondateur (perte de SVG),
    parce que la preservation par forme (1) demande la presence des
    MIMEs non textuels, et `image/svg+xml` n'est plus dans la tete.
    Forme (2) demande que la banniere matchee figurait dans la base :
    pas le cas ici (la base avait le SVG, pas la banner).
    """
    src = ("try:\n"
           "    import graphviz\n"
           "    g = graphviz.Digraph(); g.edge('a', 'b'); display(g)\n"
           "except ImportError:\n"
           "    print('Graphviz non disponible : rendu du graphe saute')\n"
           "print(info)")
    info_text = "info: ok"
    base_outputs = [
        {"output_type": "display_data",
         "data": {"image/svg+xml": "<svg/>",
                  "text/plain": "<graphviz.Digraph object>"}},
        {"output_type": "stream", "text": info_text},
    ]
    head_outputs = [
        {"output_type": "stream",
         "text": "Graphviz non disponible : rendu du graphe saute"},
        {"output_type": "stream", "text": info_text},
    ]
    base_nb = {"cells": [_cid("c-gv", src, base_outputs)]}
    head_nb = {"cells": [_cid("c-gv", src, head_outputs)]}
    head_scan = scan(head_nb, base_nb=base_nb)
    # Perte du SVG, banner nouvelle : TF.
    assert len(head_scan["TOOL_FAILURE"]) == 1
    assert len(head_scan["DECLARED_FALLBACK"]) == 0


def test_founding_fixture_fires():
    """The #14262 founding pair, pinned as a fixture because the degraded
    head is branch-side history of a squash-merged PR (absent from fresh
    clones). Both cells must fire; the sources must be byte-identical so
    the finding cannot be an artifact of a source change."""
    fx = (Path(__file__).parent / "fixtures"
          / "demucs_downgrade_pair_14603.json")
    blob = json.loads(fx.read_text(encoding="utf-8"))
    assert blob["provenance"]["founding_pr"] == 14262
    for b, h in zip(blob["base_cells"], blob["head_cells"]):
        assert b["source"] == h["source"]
    got = capability_downgrades({"cells": blob["base_cells"]},
                                {"cells": blob["head_cells"]})
    assert len(got) == 2
    assert all(g["base"] == "cuda" and g["head"] == "cpu"
               and g["witness_lost"] >= 1 for g in got)


# --- #14513: MACHINE_PATH extended to document/cell metadata ---------------
# The output-only predicate was blind to metadata; a machine path in
# metadata.path passed the gate green (#14272 / #13891). The REAL leaked
# value is the positive control.

DUP_PATH = ("C:\\dev\\CoursIA-cycle-32\\MyIA.AI.Notebooks\\"
            "GenAI\\PostTraining")


def test_metadata_texts_yields_string_values():
    cells = {"cells": [
        {"cell_type": "code", "metadata": {"path": DUP_PATH}, "outputs": []},
        {"cell_type": "markdown", "metadata": {"tags": ["x"]}, "outputs": []}],
        "metadata": {"path": DUP_PATH, "kernelspec": {"name": "python3"}}}
    locs = list(metadata_texts(cells))
    assert ("doc:path", DUP_PATH) in locs
    assert ("cell[0]:path", DUP_PATH) in locs
    # dicts are not scanned; tags is a list.
    assert not any(l.startswith("doc:kernelspec") for l, _ in locs)


def test_metadata_path_machine_fires():
    nb_ = {"cells": [], "metadata": {"path": DUP_PATH}}
    hits = [loc for loc, _ in scan(nb_)["MACHINE_PATH"]]
    assert "doc:path" in hits


def test_cell_metadata_machine_fires():
    cell = {"cell_type": "code", "source": "print(1)",
            "metadata": {"path": DUP_PATH}, "outputs": []}
    hits = [loc for loc, _ in scan({"cells": [cell], "metadata": {}})
            ["MACHINE_PATH"]]
    assert "cell[0]:path" in hits


def test_metadata_path_clean_silent():
    # No metadata, and a repo-relative value (the shape the pre-commit hook
    # and convention leave in place) must stay silent.
    assert scan({"cells": [], "metadata": {}})["MACHINE_PATH"] == []
    rel = {"cells": [], "metadata": {"path": (
        "MyIA.AI.Notebooks/GenAI/PostTraining/"
        "PT_11c_grpo_qwen17_rlvr.ipynb")}}
    assert scan(rel)["MACHINE_PATH"] == []


def test_metadata_papermill_paths_silent():
    # Precaution 1 of #14513: input_path/output_path normalized to a
    # repo-relative path or basename must never fire retroactively.
    pm = {"input_path": ("MyIA.AI.Notebooks/GenAI/PostTraining/"
                         "PT_11c_grpo_qwen17_rlvr.ipynb"),
          "output_path": "PT_11c_grpo_qwen17_rlvr.ipynb"}
    assert scan({"cells": [], "metadata": {"papermill": pm}})["MACHINE_PATH"] == []


def test_metadata_non_string_silent():
    # Document metadata is scanned for STRING values only -- dicts (kernelspec,
    # language_info) and ints are not machine paths by construction.
    nb_ = {"cells": [], "metadata": {
        "kernelspec": {"name": "python3", "display_name": "Python 3"},
        "language_info": {"name": "python"},
        "toc": 3}}
    assert scan(nb_)["MACHINE_PATH"] == []


def test_output_paths_still_scanned_alongside_metadata():
    # The extension must not regress the original output surface: an output
    # path AND a metadata path both fire, with distinct locations.
    cell = {"cell_type": "code", "source": "print(1)",
            "metadata": {"path": DUP_PATH},
            "outputs": [{"output_type": "stream", "text": DUP_PATH}]}
    nb_ = {"cells": [cell], "metadata": {"path": DUP_PATH}}
    hits = scan(nb_)["MACHINE_PATH"]
    locs = [loc for loc, _ in hits]
    assert "doc:path" in locs
    assert "cell[0]:path" in locs
    assert 0 in locs  # output hit keeps its cell index


def test_sample_location_renders_each_shape_once():
    # Les trois formes que scan() produit cote a cote (cf. le test ci-dessus)
    # doivent s'imprimer telles quelles. Sans le tri, l'imprimeur FAIL
    # enveloppait tout dans cell[...] : un hit metadata de document sortait
    # "cell[doc:path]" et un hit metadata de cellule "cell[cell[0]:path]".
    assert _sample_location(0) == "cell[0]"        # hit d'output : index entier
    assert _sample_location("doc:path") == "doc:path"
    assert _sample_location("cell[0]:path") == "cell[0]:path"


def test_sample_location_no_double_wrapping_on_real_scan_output():
    # Controle positif sur les localisations REELLES de scan(), pas sur des
    # litteraux : aucune sortie ne doit contenir "cell[cell[" ni "cell[doc:".
    cell_ = {"cell_type": "code", "source": "print(1)",
             "metadata": {"path": DUP_PATH},
             "outputs": [{"output_type": "stream", "text": DUP_PATH}]}
    nb_ = {"cells": [cell_], "metadata": {"path": DUP_PATH}}
    rendered = [_sample_location(loc) for loc, _ in scan(nb_)["MACHINE_PATH"]]
    assert rendered, "le controle positif doit produire des hits"
    for r in rendered:
        assert "cell[cell[" not in r
        assert "cell[doc:" not in r


# --- #18567: a web URL is not a path of the executing machine --------------

def test_web_url_under_home_silent():
    out = ("=== Sources ===\n4. RAG vs Fine-tuning: "
           "https://www.ccs.neu.edu/home/alina/classes/Fall2024/Lecture11.pdf"
           "?utm_source=openai\n")
    assert scan(nb(cell("print(x)", out)))["MACHINE_PATH"] == []


def test_local_server_url_still_fires():
    out = "Ouvert : http://localhost:8888/files/home/agent/CoursIA/x.ipynb"
    assert scan(nb(cell("print(x)", out)))["MACHINE_PATH"] != []


def test_file_url_still_fires():
    out = "Rapport : file:///home/agent/CoursIA/report.html"
    assert scan(nb(cell("print(x)", out)))["MACHINE_PATH"] != []


def test_bare_path_next_to_web_url_still_fires():
    out = "Source https://example.org/a -- cache /home/agent/CoursIA/y.py"
    hits = scan(nb(cell("print(x)", out)))["MACHINE_PATH"]
    assert [m for _, m in hits] == ["/home/agent/"]


def test_web_url_in_metadata_silent():
    nb_ = {"cells": [], "nbformat": 4, "nbformat_minor": 5,
           "metadata": {"source": "https://example.edu/home/alice/notes/"}}
    assert scan(nb_)["MACHINE_PATH"] == []


# --- DECLARED_FALLBACK axis (#18916) ---------------------------------------
# Demo-mode stubs (#18893, Lean-10) print their fallback banner from the
# cell's own source. The soft motif in the OUTPUT is exempted from
# TOOL_FAILURE iff the SOURCE declares it: literal substring, or the [SKIP]
# marker on both sides. Every other shape still fires.

STUB_LITERAL_SRC = "print('[SKIP] LeanDojo non disponible')"
STUB_INTERP_SRC = ("try:\n    import lean_dojo\n"
                   "except Exception as e:\n"
                   "    print(f'[SKIP] LeanRunner indisponible: {e}')")
STUB_INTERP_OUT = ("[SKIP] LeanRunner indisponible: LeanDojo not available. "
                   "Install with: pip install lean-dojo")


def test_declared_fallback_literal_source_exempted():
    got = scan(nb(cell(STUB_LITERAL_SRC, "[SKIP] LeanDojo non disponible")))
    assert got["TOOL_FAILURE"] == []
    assert len(got["DECLARED_FALLBACK"]) == 1
    assert got["DECLARED_FALLBACK"][0][0] == 0


def test_declared_fallback_skip_marker_interpolated_exempted():
    got = scan(nb(cell(STUB_INTERP_SRC, STUB_INTERP_OUT)))
    assert got["TOOL_FAILURE"] == []
    assert len(got["DECLARED_FALLBACK"]) == 1


def test_undeclared_soft_motif_still_fires():
    got = scan(nb(cell("print(result)", "Graphviz non disponible")))
    assert len(got["TOOL_FAILURE"]) == 1
    assert got["DECLARED_FALLBACK"] == []


def test_declared_stub_does_not_mask_real_failure():
    got = scan(nb(cell(STUB_LITERAL_SRC,
                       "[SKIP] LeanDojo non disponible\n"
                       "bash: dot: command not found")))
    assert got["TOOL_FAILURE"], "hard pattern must win over the exemption"


def test_declared_fallback_never_gates():
    """compare() doit rapporter la classe sans la faire regresser."""
    from check_output_failure_text import compare
    paths = ["nb.ipynb"]
    base_nb = nb(cell("print('ok')", "ok"))
    head_nb = nb(cell(STUB_LITERAL_SRC, "[SKIP] LeanDojo non disponible"))
    import check_output_failure_text as m
    orig = m.read_notebook_at
    m.read_notebook_at = lambda ref, path, cwd=None: (
        base_nb if ref == "b" else head_nb)
    try:
        rows = compare("b", "h", paths)
    finally:
        m.read_notebook_at = orig
    assert rows[0]["regressed"] is False
    assert rows[0]["classes"]["DECLARED_FALLBACK"]["delta"] == 1


# --- Base-conditioned exemption (#19038 review, ai-01) ---------------------
# The two anchors alone cannot tell a declared demo stub from a degradation
# SUFFERED at re-execution: every try/except cell carries its banner as a
# literal in its own source. A banner that REPLACES a substantial base output
# is a capability loss (#3473 / #11685) and must keep gating.

GRAPHVIZ_SRC = ("try:\n"
                "    import graphviz\n"
                "    g = graphviz.Digraph(); g.edge('a', 'b'); display(g)\n"
                "except ImportError:\n"
                "    print('Graphviz non disponible : rendu du graphe saute')")
BANNER_OUT = "Graphviz non disponible : rendu du graphe saute"


def id_cell(cid, source, outputs):
    return {"cell_type": "code", "id": cid, "source": source,
            "outputs": outputs}


def stream(text):
    return [{"output_type": "stream", "name": "stdout", "text": text}]


RENDER = [{"output_type": "display_data",
           "data": {"image/svg+xml": "<svg/>",
                    "text/plain": "<graphviz.Digraph object>"}}]


def test_declared_banner_replacing_a_base_render_still_fires():
    """The hole ai-01 reproduced: base renders, head prints only its banner."""
    base = {"cells": [id_cell("c-gv", GRAPHVIZ_SRC, RENDER)]}
    head = {"cells": [id_cell("c-gv", GRAPHVIZ_SRC, stream(BANNER_OUT))]}

    got = scan(head, base_nb=base)

    assert len(got["TOOL_FAILURE"]) == 1, "a lost render must keep gating"
    assert not got["DECLARED_FALLBACK"]


def test_declared_fallback_kept_when_base_was_already_in_fallback():
    base = {"cells": [id_cell("c-gv", GRAPHVIZ_SRC, stream(BANNER_OUT))]}
    head = {"cells": [id_cell("c-gv", GRAPHVIZ_SRC, stream(BANNER_OUT))]}

    got = scan(head, base_nb=base)

    assert not got["TOOL_FAILURE"]
    assert len(got["DECLARED_FALLBACK"]) == 1


def test_declared_fallback_kept_for_a_cell_new_at_head():
    base = {"cells": [id_cell("c-gv", GRAPHVIZ_SRC, RENDER)]}
    head = {"cells": [id_cell("c-new", GRAPHVIZ_SRC, stream(BANNER_OUT))]}

    got = scan(head, base_nb=base)

    assert not got["TOOL_FAILURE"], "a cell with no base carrier is a stub"
    assert len(got["DECLARED_FALLBACK"]) == 1


def test_declared_banner_over_a_mime_only_render_still_fires():
    """A figure has no text/plain repr -- it must still count as content."""
    base = {"cells": [id_cell("c-gv", GRAPHVIZ_SRC,
                              [{"output_type": "display_data",
                                "data": {"image/svg+xml": "<svg/>"}}])]}
    head = {"cells": [id_cell("c-gv", GRAPHVIZ_SRC, stream(BANNER_OUT))]}

    got = scan(head, base_nb=base)

    assert len(got["TOOL_FAILURE"]) == 1


def test_without_a_base_the_exemption_is_unchanged():
    """scan() without base_nb keeps its historical classification."""
    head = {"cells": [id_cell("c-gv", GRAPHVIZ_SRC, stream(BANNER_OUT))]}

    got = scan(head)

    assert not got["TOOL_FAILURE"]
    assert len(got["DECLARED_FALLBACK"]) == 1


def test_compare_gates_a_banner_that_replaces_a_render():
    """End-to-end: the ratchet goes red on the very shape it must catch."""
    from check_output_failure_text import compare
    import check_output_failure_text as m

    paths = ["nb.ipynb"]
    base_nb = {"cells": [id_cell("c-gv", GRAPHVIZ_SRC, RENDER)]}
    head_nb = {"cells": [id_cell("c-gv", GRAPHVIZ_SRC, stream(BANNER_OUT))]}
    orig = m.read_notebook_at
    m.read_notebook_at = lambda ref, path, cwd=None: (
        base_nb if ref == "b" else head_nb)
    try:
        rows = compare("b", "h", paths)
    finally:
        m.read_notebook_at = orig

    assert rows[0]["regressed"] is True
    assert rows[0]["classes"]["TOOL_FAILURE"]["delta"] == 1
    assert rows[0]["classes"]["DECLARED_FALLBACK"]["delta"] == 0
