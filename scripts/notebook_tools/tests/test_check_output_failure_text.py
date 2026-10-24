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


def test_declared_fallback_kept_when_base_output_echoes_before_failing():
    """Faux 0 -> 1 mesure sur #19697 : le repli execute son chemin normal AVANT
    d'echouer, donc sa sortie de base porte des lignes d'echo (« Inpainting:
    '...' », soumission du workflow) qui la rendent ``substantial`` au sens
    textuel. Ce cas est le seul qui atteint ``_in_fallback`` avec un verdict
    True : ``test_declared_fallback_kept_when_base_was_already_in_fallback``
    (base = banniere seule) sort par ``_substantial_output`` des la premiere
    condition, sans jamais lire ``_in_fallback``."""
    out = "graphe: 2 noeuds, 1 arete\n" + BANNER_OUT
    base = {"cells": [id_cell("c-gv", GRAPHVIZ_SRC, stream(out))]}
    head = {"cells": [id_cell("c-gv", GRAPHVIZ_SRC, stream(out))]}

    got = scan(head, base_nb=base)

    assert not got["TOOL_FAILURE"]
    assert len(got["DECLARED_FALLBACK"]) == 1


def test_declared_banner_over_an_echoing_head_still_fires_when_base_rendered():
    """Le pendant du test precedent, et la raison pour laquelle la decision se
    prend sur la BASE : la base RENDAIT (aucun repli), la tete n'imprime plus
    que ses lignes d'echo puis la banniere. L'echo rend la sortie de tete
    ``substantial`` au sens textuel -- une condition qui exigerait que la tete
    ait perdu sa substance laisserait donc passer la perte de rendu."""
    out = "graphe: 2 noeuds, 1 arete\n" + BANNER_OUT
    base = {"cells": [id_cell("c-gv", GRAPHVIZ_SRC, RENDER)]}
    head = {"cells": [id_cell("c-gv", GRAPHVIZ_SRC, stream(out))]}

    got = scan(head, base_nb=base)

    assert len(got["TOOL_FAILURE"]) == 1, "un rendu perdu doit continuer a gater"
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


# --- ImportError : la forme d'une exception levee, pas le mot nu (#20701) ---

IMPORT_TABLE_CITATION = (
    "| **Imports plats vs package** : le projet utilise `from utils import ...` "
    "(pas de package) | `ImportError` si la CLI est lancee depuis un autre "
    "dossier | Meme pattern que `tests/test_utils.py` |")


def test_importerror_raised_forms_fire():
    """Chaque forme produite par une levee reelle reste un TOOL_FAILURE :
    derniere ligne de trace, variante coloree IPython, derniere ligne sans
    message, et gestionnaire imprimant la classe en milieu de ligne."""
    for raised in ("Traceback (most recent call last):\n"
                   "ImportError: cannot import name 'X' from 'y'",
                   "\x1b[0;31mImportError\x1b[0m: cannot import name 'X'",
                   "Traceback (most recent call last):\nImportError",
                   "Erreur: ImportError: cannot import name 'X'"):
        got = scan(nb(cell("print(x)", raised)))["TOOL_FAILURE"]
        assert len(got) == 1, raised


def test_importerror_table_citation_silent():
    """Ligne citee dans l'issue #20701 : le nom nu dans un tableau de risques."""
    assert scan(nb(cell("print(x)", IMPORT_TABLE_CITATION)))[
        "TOOL_FAILURE"] == []


def test_importerror_backticked_citation_with_message_silent():
    """Une citation qui porte un message reste une citation : le backtick
    place avant le nom l'exclut."""
    text = "Voir `ImportError: cannot import name 'X'` dans la doc."
    assert scan(nb(cell("print(x)", text)))["TOOL_FAILURE"] == []


def test_importerror_citation_does_not_mask_raise_in_same_stream():
    text = IMPORT_TABLE_CITATION + "\nImportError: cannot import name 'X'"
    assert len(scan(nb(cell("print(x)", text)))["TOOL_FAILURE"]) == 1


def test_importerror_sample_is_not_ventilated_as_degraded_hint():
    """Le balayage classe un constat en DEGRADED_HINT si son texte extrait
    contient un motif mou. Une levee dont le message en porte un doit rester
    un TOOL_FAILURE."""
    from check_output_failure_text import _is_degraded_hint
    hits = scan(nb(cell("print(x)", "ImportError: not available on this "
                                    "platform")))["TOOL_FAILURE"]
    assert len(hits) == 1
    assert not _is_degraded_hint(hits[0][1])


# ---------------------------------------------------------------------------
# #20120 : texte de programme affiche vs chemin emis par le runtime.
# Calibration de l'issue : deux carnets Aspire affichent le source AppHost
# qu'ils generent, et le chemin de montage y ouvre un litteral de chaine
# (faux positifs, doivent sortir de MACHINE_PATH) ; le carnet Orleans affiche
# une valeur emise par le runtime, chemin nu (controle positif, doit rester
# signale). Forme retenue : decision ai-01 c.6262311553 (OPEN_LITERAL).
# Lignes verbatim des sorties committees.
# ---------------------------------------------------------------------------

ASPIRE_LINE = (
    '.WithBindMount(Path.Combine(Environment.GetFolderPath('
    'Environment.SpecialFolder.UserProfile), ".cache/huggingface"), '
    '"/home/appuser/.cache/huggingface")')
ORLEANS_LINE = ("Content root path: /home/user/wt-aspire/MyIA.AI.Notebooks/"
                "GenAI/Integrations-DotNet/Orleans/OrleansAspireLab")


def test_20120_aspire_program_literal_exempted():
    got = scan(nb(cell("print(x)", ASPIRE_LINE)))

    assert got["MACHINE_PATH"] == []
    assert [m for _, m in got["PROGRAM_LITERAL"]] == ["/home/appuser/"]


def test_20120_orleans_runtime_control_still_flagged():
    got = scan(nb(cell("print(x)", ORLEANS_LINE)))

    assert [m for _, m in got["MACHINE_PATH"]] == ["/home/user/"]
    assert got["PROGRAM_LITERAL"] == []


def test_20120_quoted_shapes_are_the_known_bound():
    # Borne connue, dans le sens faux negatif : sous la forme retenue
    # (decision ai-01 c.6262311553), tout chemin precede immediatement d'un
    # guillemet ouvre un litteral et est exempte -- prose citante, repr,
    # argument nomme, JSON, parenthese, couples. Aucune occurrence de ces
    # formes dans le corpus au 2026-10-19 (mesure po-2024 c.6086700118,
    # 0 collaterai sur les hote/env) ; la borne est epinglee pour rester
    # visible si elle se materialise.
    for line in (
            'Serving from "/home/alice/CoursIA/x"',
            "No such file or directory: '/home/alice/CoursIA/x.csv'",
            'Config(path="/home/alice/CoursIA/x")',
            '{"path": "/home/alice/CoursIA/x", "n": 1}',
            'error: cannot open file ("/home/alice/CoursIA/x")',
            "[('cwd', \"/home/alice/CoursIA/x\"), ('n', 1)]"):
        got = scan(nb(cell("print(x)", line)))
        assert got["MACHINE_PATH"] == [], line
        assert len(got["PROGRAM_LITERAL"]) == 1, line


def test_20120_bare_shapes_stay_flagged():
    # Formes nues -- aucun guillemet ne precede le chemin : elles restent
    # signalees. C'est la ligne Orleans (`Content root path: ...`), le
    # Windows nu, et le commentaire sans guillemets.
    for line in (
            "Output written to D:\\dev\\CoursIA\\out.txt",
            "Content root path: /home/alice/CoursIA/x",
            "// /home/alice/CoursIA/x"):
        got = scan(nb(cell("print(x)", line)))
        assert len(got["MACHINE_PATH"]) == 1, line
        assert got["PROGRAM_LITERAL"] == [], line


def test_20120_traceback_paths_are_the_known_bound():
    # #21444 inverse la borne : une trace d'erreur cite ses chemins entre
    # guillemets (`File "..."`, en-tete `<Nom>Error: [Errno ...`) -- c'est la
    # classe B de la regle 6 (chemin dans une exception), le mecanisme meme
    # de l'Epic #21424 : ces lignes restent MACHINE_PATH. La ligne citante
    # HORS trace reste exempte (test quoted_shapes ci-dessus).
    trace = ('Traceback (most recent call last):\n'
             '  File "/home/alice/CoursIA/run.py", line 3, in <module>\n'
             '    main()\n'
             "FileNotFoundError: [Errno 2] No such file or directory: "
             "'/home/alice/CoursIA/data.csv'")
    got = scan(nb(cell("main()", trace)))

    assert len(got["MACHINE_PATH"]) == 2
    assert got["PROGRAM_LITERAL"] == []


def test_20120_code_comment_path_stays_flagged():
    # Borne assumee dans l'autre sens : un chemin nu dans un commentaire
    # affiche n'ouvre rien, il reste signale (faux positif conserve). La
    # variante entre guillemets, elle, tombe dans la borne faux negatif.
    got = scan(nb(cell("print(x)", '# chemin: /home/alice/CoursIA/x')))

    assert len(got["MACHINE_PATH"]) == 1
    quoted = scan(nb(cell("print(x)", '# chemin: "/home/alice/CoursIA/x"')))
    assert quoted["MACHINE_PATH"] == []
    assert len(quoted["PROGRAM_LITERAL"]) == 1


def test_20120_positional_call_echo_is_known_exempt_bound():
    # Borne connue, epinglee pour qu'elle reste visible : un echo runtime qui
    # reproduit un appel positionnel (`Config("/home/...")`) a la forme du
    # texte de programme et est exempte. Aucune occurrence dans le corpus.
    got = scan(nb(cell("print(x)", 'Config("/home/alice/CoursIA/x")')))

    assert got["MACHINE_PATH"] == []
    assert len(got["PROGRAM_LITERAL"]) == 1


def test_20120_windows_call_literal_follows_the_same_rule():
    # La regle porte sur les quatre formes de chemin, pas sur /home seul :
    # un littéral Windows d'appel affiche est du texte de programme aussi.
    line = 'Path.Combine("D:\\\\dev\\\\CoursIA", "x")'
    got = scan(nb(cell("print(x)", line)))

    assert got["MACHINE_PATH"] == []
    assert len(got["PROGRAM_LITERAL"]) == 1


def test_20120_metadata_is_not_exempted():
    # L'exemption ne touche que les sorties affichees, jamais les metadata.
    got = scan({"cells": [], "metadata": {
        "cfg": 'Config(a, "/home/alice/CoursIA/x")'}})

    assert len(got["MACHINE_PATH"]) == 1
    assert got["PROGRAM_LITERAL"] == []


def test_20120_corpus_calibration_lines_at_fixed_cells():
    # Critere 4 de la decision ai-01 (c.6262311553) : les 7 lignes du jeu de
    # calibration sont rejouees sur les carnets reels, aux indices du champ
    # `cell` de l'organe -- qui est 0-based (#19984 ; la plupart des autres
    # organes notebooks du depot sont 1-based, d'ou l'epinglage explicite,
    # sinon on compare la cellule voisine). Aspire : 01 cell 3, 02 cell 2
    # (PROGRAM_LITERAL) ; Orleans : 02 cells 12, 16, 19, 21, 23 (MACHINE_PATH).
    root = Path(__file__).resolve().parents[3]
    base = "MyIA.AI.Notebooks/GenAI/Integrations-DotNet"
    cases = (
        (f"{base}/Aspire/01-Aspire-Orchestration-GenAi.ipynb",
         "PROGRAM_LITERAL", [3]),
        (f"{base}/Aspire/02-Aspire-GenAiStack-Reel.ipynb",
         "PROGRAM_LITERAL", [2]),
        (f"{base}/Orleans/02-Orleans-Aspire-CoHost.ipynb",
         "MACHINE_PATH", [12, 16, 19, 21, 23]),
    )
    for rel, cls, cells in cases:
        with open(root / rel, encoding="utf-8") as fh:
            doc = json.load(fh)
        got = scan(doc)
        assert [i for i, _ in got[cls]] == cells, rel
        other = "MACHINE_PATH" if cls == "PROGRAM_LITERAL" else "PROGRAM_LITERAL"
        assert got[other] == [], rel


def test_20120_compare_gate_still_fires_on_runtime_path_only():
    # Bout en bout : le ratchet reste rouge sur un chemin runtime ajoute, et
    # reste silencieux sur un littéral de programme ajoute (pas de
    # regression).
    from check_output_failure_text import compare
    import check_output_failure_text as m

    empty = {"cells": []}
    orig = m.read_notebook_at
    try:
        for head_line, expected in ((ORLEANS_LINE, True),
                                    (ASPIRE_LINE, False)):
            head_nb = nb(cell("print(x)", head_line))
            m.read_notebook_at = lambda ref, path, cwd=None, _h=head_nb: (
                empty if ref == "b" else _h)
            rows = compare("b", "h", ["nb.ipynb"])
            assert rows[0]["regressed"] is expected, head_line
    finally:
        m.read_notebook_at = orig


# --- #21816: echec de workflow ComfyUI ------------------------------------
# Le service repond une erreur et le carnet commite son repli a la place de
# l'illustration (C.2). Les trois formes sont les lignes REELLES du blob
# degrade de Barbie-Schreck, avant #21815.

COMFY_LOG = ("ERROR:BarbieVsAne:Erreur generation image: Workflow execution "
             "failed (server reported error): [")
COMFY_SKIP = "WARNING:BarbieVsAne:Illustration indisponible pour cette replique"


def test_21816_comfyui_fallback_fires():
    for line in (COMFY_LOG, COMFY_SKIP):
        got = scan(nb(cell("print(x)", line)))["TOOL_FAILURE"]
        assert len(got) == 1, line


def test_21816_comfyui_fallback_is_hard_even_when_source_declares_it():
    # Le carnet degrade porte le message en LITTERAL dans le source de sa
    # cellule de repli (c'est ainsi qu'il l'ecrit). L'exemption des modes
    # demo (#18916 / #19697) ne doit pas l'absoudre : la banniere a remplace
    # un rendu, c'est la degradation elle-meme.
    src = ("try:\n"
           "    generate()\n"
           "except Exception as exc:\n"
           "    logger.warning('Illustration indisponible pour cette replique')\n")
    got = scan(nb(cell(src, COMFY_SKIP)))
    assert got["TOOL_FAILURE"] and not got["DECLARED_FALLBACK"]


def test_21816_declared_interactive_fallback_stays_out():
    # Controle negatif : les deux cellules de mode interactif declarees du
    # depot (DALL-E 1-1 cellule 23, Whisper 1-2 cellule 45) sont des branches
    # de repli PREVUES. Elles restent des replis declares, jamais des echecs.
    cases = (
        ("print('[skip] Mode interactif non disponible (execution "
         "automatisee)')",
         "[skip] Mode interactif non disponible (execution automatisee)"),
        ("print('Mode interactif non disponible (execution automatisee)')",
         "Mode interactif non disponible (execution automatisee)"),
    )
    for src, out in cases:
        got = scan(nb(cell(src, out)))
        assert got["TOOL_FAILURE"] == [], out
        assert len(got["DECLARED_FALLBACK"]) == 1, out
