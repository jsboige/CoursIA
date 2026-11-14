"""Tests de scripts/ci/check_cancelled_only_commits.py (#22088).

Chaque verdict est verifie par un CONTROLE POSITIF (la forme mesuree est
reconnue) ET par son CONTROLE NEGATIF. Le controle negatif qui compte le plus
est celui du rouge MERITE : un commit porteur d'une vraie jambe en echec ne
doit jamais etre classe « annulation seule », sinon l'organe blanchirait une
regression -- exactement l'inverse du service rendu.
"""

import pathlib
import sys
from datetime import datetime, timedelta

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from check_cancelled_only_commits import (  # noqa: E402
    ADVISORY_ONLY,
    KILLED,
    STARTED_GRACE_SECONDS,
    SUPERSEDED,
    analyse,
    cancelled_kind,
    classify,
    is_advisory_leg,
    leg_conclusion,
    leg_fields,
    leg_name,
)

#: Debut arbitraire, construit une fois : toute duree de test se derive d'ici
#: par arithmetique (`timedelta`). Interpoler les chiffres du seuil dans une
#: chaine ISO -- l'ancien ``f"04:00:0{G // 60}Z"`` -- ne marchait que pour un
#: seuil dont les minutes tiennent sur un chiffre : 600 s y devenait
#: ``04:00:010Z``, que ``fromisoformat`` lit comme 1 seconde de vie.
_STARTED = datetime.fromisoformat("2026-11-13T04:00:00+00:00")
_STARTED_Z = "2026-11-13T04:00:00Z"


def _ended_after(seconds):
    """Horodatage de fin ISO (suffixe Z) a ``seconds`` du debut de reference."""
    return (_STARTED + timedelta(seconds=seconds)).isoformat().replace("+00:00", "Z")


def test_succes_ordinaire():
    assert classify("SUCCESS", [("Build", "SUCCESS")]) == "OK"


def test_commit_sans_aucune_jambe():
    # Un commit dont les workflows ne se declenchent pas n'est pas rouge.
    assert classify(None, []) == "OK"


def test_rouge_merite_par_une_vraie_jambe():
    assert classify("FAILURE", [("Tests", "FAILURE")]) == "OK"


def test_rouge_emprunte_par_une_annulation_seule():
    # Le defaut #22088 : aucune jambe n'a echoue, pourtant le commit est rouge.
    assert classify("FAILURE", [("Scripts Tests (CPU)", "CANCELLED")]) == "CANCELLED_ONLY"


def test_annulation_plus_jambes_vertes_reste_empruntee():
    legs = [("A", "CANCELLED"), ("B", "SUCCESS"), ("C", "SKIPPED"), ("D", "NEUTRAL")]
    assert classify("FAILURE", legs) == "CANCELLED_ONLY"


def test_annulation_plus_vraie_panne_n_est_pas_empruntee():
    # Controle negatif central : la presence d'une annulation n'excuse rien.
    legs = [("A", "CANCELLED"), ("B", "FAILURE")]
    assert classify("FAILURE", legs) == "OK"


def test_rouge_sans_jambe_lisible_n_est_pas_accuse():
    # FAILURE avec uniquement du vert : conclusion non modelisee, pas un blanc-seing.
    assert classify("FAILURE", [("A", "NEUTRAL")]) == "UNKNOWN"


def test_troncature_interdit_l_accusation():
    # Une vraie panne peut se trouver au-dela de la page de 100 contextes.
    assert classify("FAILURE", [("A", "CANCELLED")], truncated=True) == "UNKNOWN"


def test_troncature_ne_blanchit_pas_une_panne_visible():
    # Une panne deja visible reste meritee, troncature ou pas.
    assert classify("FAILURE", [("A", "FAILURE"), ("B", "CANCELLED")], truncated=True) == "OK"


def test_en_cours_n_est_pas_un_verdict():
    assert classify("PENDING", [("A", "CANCELLED")]) == "PENDING"


def test_lecture_des_deux_typologies_de_jambes():
    # Un CheckRun porte `name`+`conclusion`, un StatusContext `context`+`state`.
    check_run = {"name": "Build Quarto site", "conclusion": "CANCELLED"}
    status_ctx = {"context": "ci/legacy", "state": "FAILURE"}
    assert leg_name(check_run) == "Build Quarto site"
    assert leg_conclusion(check_run) == "CANCELLED"
    assert leg_name(status_ctx) == "ci/legacy"
    assert leg_conclusion(status_ctx) == "FAILURE"


def test_analyse_extrait_la_fenetre_et_le_verdict():
    node = {
        "oid": "a" * 40,
        "committedDate": "2026-10-23T21:48:04Z",
        "messageHeadline": "Fix(ci): exemple",
        "statusCheckRollup": {
            "state": "FAILURE",
            "contexts": {
                "pageInfo": {"hasNextPage": False},
                "nodes": [
                    {"__typename": "CheckRun", "name": "validate", "conclusion": "SUCCESS"},
                    {"__typename": "CheckRun", "name": "Scripts Tests (CPU)", "conclusion": "CANCELLED"},
                ],
            },
        },
    }
    row = analyse(node)
    assert row["verdict"] == "CANCELLED_ONLY"
    assert row["non_green"] == ["Scripts Tests (CPU)=CANCELLED"]
    assert row["truncated"] is False


def test_analyse_signale_la_troncature():
    node = {
        "oid": "b" * 40,
        "committedDate": "2026-10-23T21:48:04Z",
        "messageHeadline": "Fix(ci): exemple tronque",
        "statusCheckRollup": {
            "state": "FAILURE",
            "contexts": {
                "pageInfo": {"hasNextPage": True},
                "nodes": [
                    {"__typename": "CheckRun", "name": "A", "conclusion": "CANCELLED"},
                ],
            },
        },
    }
    row = analyse(node)
    assert row["truncated"] is True
    assert row["verdict"] == "UNKNOWN"


# --- #25181 : deux annulations, un seul rendu ---------------------------------
#
# `cancelled` couvre deux evenements que l'UI peint a l'identique. Les tests
# ci-dessous separent la supersession de file (empruntee) de la mort d'infra
# (meritee), et verifient que le doute ne blanchit jamais le second.


def test_deux_uplets_restent_acceptes():
    # La forme historique (name, conclusion) reste lisible : un StatusContext
    # ne porte aucune mesure de duree, et un appelant doit pouvoir classer.
    assert leg_fields(("A", "CANCELLED")) == ("A", "CANCELLED", None, None)


def test_annulation_sans_demarrage_est_empruntee():
    # Aucun startedAt : le job n'a jamais eu de runner. Rien de mesure.
    assert cancelled_kind(None, None) == SUPERSEDED
    legs = [("Scripts Tests (CPU)", "CANCELLED", None, None)]
    assert classify("FAILURE", legs) == "CANCELLED_ONLY"


def test_job_tue_a_son_timeout_est_une_mort_d_infra():
    # Controle positif du defaut #25181 : 60 min de runner, puis `cancelled`.
    legs = [("Build Quarto site", "CANCELLED",
             "2026-11-13T04:00:00Z", "2026-11-13T05:00:17Z")]
    assert cancelled_kind(*legs[0][2:]) == KILLED
    assert classify("FAILURE", legs) == "INFRA_ONLY"


def test_demarrage_sans_fin_lisible_reste_une_mort_d_infra():
    # Le doute ne doit jamais disculper un job qui a tenu un runner.
    legs = [("Build Quarto site", "CANCELLED", "2026-11-13T04:00:00Z", None)]
    assert cancelled_kind("2026-11-13T04:00:00Z", None) == KILLED
    assert classify("FAILURE", legs) == "INFRA_ONLY"


def test_supersession_mixee_a_une_mort_d_infra_reste_infra():
    legs = [
        ("Another build", "CANCELLED", None, None),
        ("Build Quarto site", "CANCELLED", "2026-11-13T04:00:00Z",
         "2026-11-13T05:00:15Z"),
    ]
    assert classify("FAILURE", legs) == "INFRA_ONLY"


def test_annulation_sous_le_seuil_reste_empruntee():
    # Un job qui n'a vecu que quelques secondes n'a pas ete tue : il a perdu
    # sa place. Le seuil separe la file du travail.
    legs = [("Build", "CANCELLED", _STARTED_Z,
             _ended_after(STARTED_GRACE_SECONDS - 1))]
    assert classify("FAILURE", legs) == "CANCELLED_ONLY"


def test_la_frontiere_du_seuil_est_mesuree_a_la_seconde_pres():
    # Controle de bornes G-1 / G / G+1 : la frontiere est inclusive (``>=``),
    # et sa preuve ne depend pas du nombre de chiffres du seuil -- un seuil a
    # trois chiffres ne doit rien changer au verdict des bornes.
    g = STARTED_GRACE_SECONDS
    assert cancelled_kind(_STARTED_Z, _ended_after(g - 1)) == SUPERSEDED
    assert cancelled_kind(_STARTED_Z, _ended_after(g)) == KILLED
    assert cancelled_kind(_STARTED_Z, _ended_after(g + 1)) == KILLED


def test_une_vraie_panne_reste_meritee_meme_avec_une_mort_d_infra():
    # Controle negatif : le nouveau verdict n'absorbe pas le rouge merite.
    legs = [
        ("Build Quarto site", "CANCELLED", "2026-11-13T04:00:00Z",
         "2026-11-13T05:00:15Z"),
        ("Tests", "FAILURE"),
    ]
    assert classify("FAILURE", legs) == "OK"


def test_analyse_expose_la_preuve_de_chaque_annulation():
    # Le rapport doit dire POURQUOI la jambe est INFRA, sinon le lecteur voit
    # le meme mot `CANCELLED` que pour une supersession.
    node = {
        "oid": "c" * 40,
        "committedDate": "2026-11-13T05:01:00Z",
        "messageHeadline": "Feat(x): exemple",
        "statusCheckRollup": {
            "state": "FAILURE",
            "contexts": {
                "pageInfo": {"hasNextPage": False},
                "nodes": [
                    {"__typename": "CheckRun", "name": "Build Quarto site",
                     "conclusion": "CANCELLED",
                     "startedAt": "2026-11-13T04:00:00Z",
                     "completedAt": "2026-11-13T05:00:15Z"},
                ],
            },
        },
    }
    row = analyse(node)
    assert row["verdict"] == "INFRA_ONLY"
    assert row["cancelled_evidence"] == ["Build Quarto site=KILLED(60 min)"]


# --- #26355 : les jambes consultatives ne sont pas des rouges merites ---------
#
# `scripts/pr_gate.py` ne bloque pas sur une jambe dont le nom porte le marqueur
# `advisory`. Cet organe-la comptait pourtant comme un rouge merite : mesuree
# sur #26336, la contradiction etait une lecture du rapport, pas du depot. Les
# tests ci-dessous tiennent les deux bouts : la jambe consultative change de
# categorie (controle positif), et une jambe requise rouge le reste (controle
# negatif) -- un organe qui blanchirait une vraie panne serait pire que muet.


def test_le_predicat_consultatif_vient_du_pr_gate():
    # Controle positif a la source : le predicat EST celui du gate (importe),
    # pas une copie du sous-chaine qui deriverait au premier changement de
    # regle. Une jambe marquee est consultative, le check requis ne l'est pas.
    assert is_advisory_leg("CJK residue advisory (label, non-blocking)") is True
    assert is_advisory_leg("PR gate") is False
    assert is_advisory_leg("") is False


def test_le_predicat_couvre_le_nom_de_workflow_sans_marqueur_de_job():
    # Trois workflows portent le marqueur sur leur NOM DE WORKFLOW seulement :
    # leur job doit rester consultatif, sinon le rapport contredit le gate sur
    # ces trois-la (PRs #12524 / #12783 bloquees 44h/9h).
    from check_cancelled_only_commits import advisory_job_names

    sans_marqueur = [n for n in advisory_job_names() if "advisory" not in n.lower()]
    if not sans_marqueur:
        return  # aucun .github/workflows lisible : rien a demontrer ici
    assert is_advisory_leg(sans_marqueur[0]) is True


def test_une_jambe_consultative_rouge_n_est_pas_un_rouge_merite():
    # Controle positif du defaut #26336 : la jambe est rouge, le gate ne bloque
    # pas dessus. Quatrieme categorie, distincte des merites.
    legs = [("CJK residue advisory (label, non-blocking)", "FAILURE")]
    assert classify("FAILURE", legs) == ADVISORY_ONLY


def test_une_jambe_requise_rouge_reste_un_rouge_merite():
    # Controle negatif central : la presence d'une jambe consultative n'excuse
    # jamais une jambe requise en echec.
    legs = [("Tests", "FAILURE"),
            ("CJK residue advisory (label, non-blocking)", "FAILURE")]
    assert classify("FAILURE", legs) == "OK"


def test_une_annulation_consultative_ne_fabrique_pas_un_rouge_emprunte():
    # Une jambe consultative annulee ne doit pas faire accuser le commit : ce
    # sont les jambes requises qui portent le verdict.
    legs = [("Scripts Tests (CPU)", "CANCELLED"),
            ("Grain tag advisory (labels, non bloquant)", "FAILURE")]
    assert classify("FAILURE", legs) == "CANCELLED_ONLY"


def test_une_annulation_consultative_ne_cree_pas_une_mort_d_infra():
    # Le KILLED se lit sur les seules jambes requises ; une consultative tuee
    # ne fabrique pas une mort d'infra, et n'en efface pas une non plus.
    legs = [
        ("Build Quarto site", "CANCELLED", _STARTED_Z, _ended_after(3600)),
        ("Trivial-diff advisory (warning sur la trivialite, #15740)", "CANCELLED"),
    ]
    assert classify("FAILURE", legs) == "INFRA_ONLY"


def test_troncature_ne_blanchit_pas_un_rouge_consultatif_seul():
    # Truncation fail-closed dans les deux sens : une panne requise peut se
    # trouver au-dela de la page, donc « seul du consultatif » ne se conclut pas.
    legs = [("CJK residue advisory (label, non-blocking)", "FAILURE")]
    assert classify("FAILURE", legs, truncated=True) == "UNKNOWN"


def test_le_predicat_est_injectable():
    # Le defaut est la regle du gate ; un appelant qui sait mieux peut la
    # remplacer -- c'est ce qui rend la classification testable sans disque.
    assert classify("FAILURE", [("X", "FAILURE")],
                    advisory=lambda _n: True) == ADVISORY_ONLY
    assert classify("FAILURE", [("X", "FAILURE")],
                    advisory=lambda _n: False) == "OK"


def test_analyse_isole_la_jambe_consultative_d_un_rouge_requis():
    # Commit mixte : le verdict reste merite, mais la colonne de preuve doit
    # nommer la jambe que le gate ignore -- sinon le meme nom se lit comme un
    # rouge merite et la contradiction revient par le rendu.
    node = {
        "oid": "d" * 40,
        "committedDate": "2026-11-14T01:00:00Z",
        "messageHeadline": "Fix(ci): exemple mixte",
        "statusCheckRollup": {
            "state": "FAILURE",
            "contexts": {
                "pageInfo": {"hasNextPage": False},
                "nodes": [
                    {"__typename": "CheckRun", "name": "Tests", "conclusion": "FAILURE"},
                    {"__typename": "CheckRun",
                     "name": "CJK residue advisory (label, non-blocking)",
                     "conclusion": "FAILURE"},
                ],
            },
        },
    }
    row = analyse(node)
    assert row["verdict"] == "OK"
    assert row["non_green"] == [
        "Tests=FAILURE",
        "CJK residue advisory (label, non-blocking)=FAILURE",
    ]
    assert row["advisory_legs"] == [
        "CJK residue advisory (label, non-blocking)=FAILURE",
    ]


def test_analyse_ne_compte_que_du_consultatif_comme_une_quatrieme_categorie():
    node = {
        "oid": "e" * 40,
        "committedDate": "2026-11-14T01:05:00Z",
        "messageHeadline": "Fix(ci): exemple consultatif seul",
        "statusCheckRollup": {
            "state": "FAILURE",
            "contexts": {
                "pageInfo": {"hasNextPage": False},
                "nodes": [
                    {"__typename": "CheckRun",
                     "name": "CJK residue advisory (label, non-blocking)",
                     "conclusion": "FAILURE"},
                    {"__typename": "CheckRun", "name": "PR gate", "conclusion": "SUCCESS"},
                ],
            },
        },
    }
    row = analyse(node)
    assert row["verdict"] == ADVISORY_ONLY
    assert row["advisory_legs"] == [
        "CJK residue advisory (label, non-blocking)=FAILURE",
    ]


#: Le workflow `main-red-legibility.yml` fait tourner l'organe sur un sparse
#: checkout : si la liste oublie une depense locale d'import (le garde-fou
#: #26458 : `pr_gate.py` importe `gh_identity.py` au module), le job de main
#: sort « instrument incomplet » a chaque passe alors que les tests, eux,
#: tournent sur un checkout complet et restent verts. Ce test rejoue la liste
#: telle quelle : il copie EXACTEMENT les fichiers du bloc `sparse-checkout:`
#: dans un dossier vide et exige que l'organe y reponde `--help` (rc=0).
_WF_NAME = "main-red-legibility.yml"


def _sparse_checkout_list(workflow_text):
    """Extrait la liste du bloc `sparse-checkout: |` du workflow."""
    import re

    m = re.search(
        r"sparse-checkout:\s*\|\s*\n((?:[ \t]+\S[^\n]*\n)+)",
        workflow_text,
    )
    assert m, f"bloc sparse-checkout introuvable dans {_WF_NAME}"
    lignes = [l.strip() for l in m.group(1).splitlines()]
    return [l for l in lignes if l and not l.startswith("#")]


def test_sparse_checkout_ferme_les_imports_de_l_organe(tmp_path):
    """L'organe doit vivre avec la SEULE liste sparse-checkout du workflow."""
    import shutil
    import subprocess

    racine = pathlib.Path(__file__).resolve().parents[2]
    workflow = racine / ".github" / "workflows" / _WF_NAME
    assert workflow.is_file(), f"workflow absent : {workflow}"
    fichiers = _sparse_checkout_list(workflow.read_text(encoding="utf-8"))
    assert fichiers, "liste sparse-checkout vide"

    for rel in fichiers:
        source = racine / rel
        assert source.is_file(), (
            f"la liste sparse-checkout cite un fichier absent du depot : {rel}"
        )
        cible = tmp_path / rel
        cible.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, cible)

    organe = tmp_path / "scripts" / "ci" / "check_cancelled_only_commits.py"
    resultat = subprocess.run(
        [sys.executable, "-I", str(organe), "--help"],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        cwd=str(tmp_path),
    )
    assert resultat.returncode == 0, (
        "l'organe sort en rc="
        f"{resultat.returncode} sur la seule liste sparse-checkout "
        "(depense locale d'import manquante ?)\n"
        f"stdout: {resultat.stdout[-400:]}\nstderr: {resultat.stderr[-400:]}"
    )
