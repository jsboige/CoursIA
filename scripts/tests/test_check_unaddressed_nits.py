"""Tests for scripts/check_unaddressed_nits.py (#11044, gate B.0).

L'organe encode une seule question : « cette remarque de review a-t-elle ete
LEVEE avant le merge ? ». Toute sa correction tient dans ce qui compte comme
levee — et c'est precisement la que les deux defauts trouves en review sont nes.
Les deux sont couverts ici :

  - **Le bruit ne leve pas** (defaut signale par Hermes sur #11045) : un
    commentaire de bot CI ou un tag de protocole nu, poste entre le nit et le
    merge, ne repond a rien. Sans ce filtre l'organe reproduisait exactement le
    defaut qu'il traque, et sur ce depot ou les bots commentent a chaque push le
    failure mode etait la regle, pas l'exception.
  - **Un commit ne leve pas** : un push muet est indiscernable d'un push qui
    repond. Sur l'incident fondateur #10761, le « traitement » etait un rebase
    qui n'adressait aucun des deux nits. Ce qui leve une remarque est une phrase,
    pas un SHA.

S'y ajoutent la borne anti-retroactivite (un commentaire poste APRES le merge
est une annonce de merge, pas une reponse) et la normalisation des accents (les
agents ecrivent « sont adresses », les marqueurs disent « sont adresses »).

Aucun appel reseau : `analyse()` est pur, on lui passe des payloads construits.
"""
import importlib.util
import sys
from datetime import datetime, timezone
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
CHECK_PATH = HERE.parent / "check_unaddressed_nits.py"

spec = importlib.util.spec_from_file_location("check_unaddressed_nits", CHECK_PATH)
mod = importlib.util.module_from_spec(spec)
sys.modules["check_unaddressed_nits"] = mod
spec.loader.exec_module(mod)


def at(hour: int) -> str:
    return f"2026-08-14T{hour:02d}:00:00Z"


MERGED = datetime(2026, 8, 14, 20, 0, tzinfo=timezone.utc)

# Un nit user : CRLF (redige dans l'UI web), poste 11 h avant le merge.
USER_NIT = {
    "author": {"login": "jsboige"},
    "createdAt": at(9),
    "body": "Attention 2 nits:\r\n- il va falloir splitter\r\n- l'attribution est fausse",
}


def run(comments, commits=None, threads=None):
    data = {
        "number": 0,
        "title": "t",
        "comments": comments,
        "reviews": [],
        "commits": commits if commits is not None else [{"committedDate": at(19)}],
    }
    return mod.analyse(data, threads or [], MERGED)


def test_nit_seul_bloque():
    assert run([USER_NIT])["blocked"] is True


def test_commit_posterieur_ne_leve_pas():
    """#10761 : le rebase de 19:41 n'adressait aucun des nits de 11:07."""
    res = run([USER_NIT], commits=[{"committedDate": at(19)}])
    assert res["blocked"] is True
    assert res["blocking"][0]["code_pushed_after"] is True  # rapporte, pas decisif


@pytest.mark.parametrize(
    "noise",
    [
        pytest.param({"author": {"login": "github-actions"}, "createdAt": at(12),
                      "body": "Golden set: 0 diff. Variation cap: OK."},
                     id="bot-ci"),
        pytest.param({"author": {"login": "codecov"}, "createdAt": at(12),
                      "body": "Coverage: 91.2% (+0.1%)"},
                     id="bot-codecov"),
        pytest.param({"author": {"login": "jsboige"}, "createdAt": at(12),
                      "body": "[CLAIMED] lane myia-po-2023:CoursIA -- paths: a/b"},
                     id="tag-protocole-nu"),
        pytest.param({"author": {"login": "jsboige"}, "createdAt": at(12),
                      "body": "[DISPATCH->inbox] grain suivant poste en DM"},
                     id="tag-dispatch"),
    ],
)
def test_le_bruit_ne_leve_pas_un_nit(noise):
    """Defaut Hermes sur #11045 : n'importe quel bruit eteignait le nit."""
    assert run([USER_NIT, noise])["blocked"] is True


def test_vraie_reponse_humaine_leve():
    reply = {"author": {"login": "jsboige"}, "createdAt": at(12),
             "body": "Bien vu, l'attribution est corrigee en cellule 0 et 2."}
    assert run([USER_NIT, reply])["blocked"] is False


def test_tag_de_protocole_portant_une_levee_leve():
    """Un tag n'est disqualifie que s'il est NU : `[DONE] ... sont adresses` repond."""
    done = {"author": {"login": "jsboige"}, "createdAt": at(12),
            "body": "[DONE] les 2 nits sont adresses, commit abc123."}
    assert run([USER_NIT, done])["blocked"] is False


def test_accents_absents_matchent_quand_meme():
    """Les agents ecrivent sans accents ; les marqueurs sont accentues."""
    assert mod.has_marker("les 2 points sont adresses", mod.LIFT_MARKERS)
    assert mod.has_marker("les 2 points sont adressés", mod.LIFT_MARKERS)
    assert not mod.has_marker("rien a voir", mod.LIFT_MARKERS)


def test_commentaire_post_merge_ne_leve_pas():
    """La borne anti-retroactivite : l'annonce de merge n'est pas une reponse.

    Sans elle, le gate ratait son propre incident fondateur — mon commentaire de
    merge « eteignait » un nit vieux de 17 h.
    """
    after = {"author": {"login": "jsboige"}, "createdAt": at(21),  # apres MERGED
             "body": "Merge apres verification des checks."}
    assert run([USER_NIT, after])["blocked"] is True


def test_thread_inline_non_resolu_bloque():
    thread = {"resolved": False, "outdated": False, "path": "a.py", "line": 12,
              "author": "jsboige", "body": "ce nom est trompeur", "createdAt": at(10)}
    res = run([], threads=[thread])
    assert res["blocked"] is True
    assert res["blocking"][0]["kind"] == "INLINE-UNRESOLVED"


def test_thread_inline_resolu_ne_bloque_pas():
    thread = {"resolved": True, "outdated": False, "path": "a.py", "line": 12,
              "author": "jsboige", "body": "ce nom est trompeur", "createdAt": at(10)}
    assert run([], threads=[thread])["blocked"] is False


def test_pr_propre_ne_bloque_pas():
    assert run([])["blocked"] is False


# --- Recalibrage FP (triage po-2024:CoursIA-2, fenetre 07-14..07-20 : 11/64) ---
#
# Le defaut mesure : une review POSITIVE contenant le mot « CONCERN » (ou
# « CHANGES_REQUESTED ») etait classee BOT-CONCERN. Les cas ci-dessous sont les
# classes reels des 11 FP nommes, plus les garde-fous : la review mixte Hermes
# (reserve vivante + « Safe to merge » de conclusion) et le SCOPE FLAG doivent
# TOUJOURS flagger. Acceptation falsifiable : voir `classify`, chaque corpus
# provient d'une PR citee du triage.


def test_review_positive_neguee_ne_flagge_pas():
    """FP #6986/#7233/#7252/#7284/#7286 : « No/Pas de CHANGES_REQUESTED » cite
    le verdict sans l'emettre — y compris avec une frontiere newline."""
    assert mod.classify(
        "jsboige", "Pas de CHANGES_REQUESTED de ma part, verify EXEC_PROVED.") is None
    assert mod.classify(
        "jsboige", "No CHANGES_REQUESTED from this review.") is None
    assert mod.classify(
        "jsboige", "10/10 EXACT MATCH, unchallenged by me.\n\nNo CHANGES_REQUESTED") is None


def test_verdict_structurel_positif_balaie_le_decompte():
    """FP #7583/#7593 : le commentaire RELEVE puis RESOUT (« 2 CONCERNS...
    addressed les deux... Verdict : COMMENT_WITHOUT_CONCERNS »). Le verdict
    formel positif decide, la prose ne compte plus."""
    body = ("NanoClaw a reviewe avec 2 CONCERNS (path leak + notebook non execute). "
            "Les 3 commits suivants addressed les deux. CONCERN 1 RESOLVED. "
            "Verdict : COMMENT_WITHOUT_CONCERNS")
    assert mod.classify("jsboige", body) is None


def test_narration_prefix_plus_soft_positive_ne_flagge_pas():
    """FP #6699 : narration d'une review pre-fix (« the CHANGES_REQUESTED
    reflects a pre-fix state ») + « Safe to merge »."""
    body = ("## Status update — now CLEAN\n**Conclusion for merge-gate**: "
            "the CHANGES_REQUESTED reflects a **pre-fix state** and is now stale. "
            "Safe to merge.")
    assert mod.classify("jsboige", body) is None


def test_hypothetique_plus_safe_ne_flagge_pas():
    """FP #7248 : modal hypothesique (« would `CHANGES_REQUESTED` a probeAddresses
    strip ») dans une peer-review SAFE for merge."""
    body = ("**Peer-review — SAFE for merge, SUPPORT.** A reviewer following the rule "
            "literally would `CHANGES_REQUESTED` a probeAddresses strip; "
            "No CHANGES_REQUESTED.")
    assert mod.classify("jsboige", body) is None


def test_rapport_verdict_ok_ne_flagge_pas():
    """FP #6291 : rapport de verification positif redige dans l'UI web (CRLF),
    « **Verdict** : OK » — l'approbation souple devance la branche HUMAN."""
    body = "**Verdict** : OK (post-rebase, 11/11 CI).\r\nDecision ai-01 REQUISE : merge."
    assert mod.classify("jsboige", body) is None


def test_hermes_mixte_conserve_ses_reserves():
    """NON-LEVE #6849/#6852/#7704 : verdict [COMMENT_WITH_CONCERNS] EMIS + « Safe
    to merge » de conclusion. La reserve vivante l'emporte sur l'approbation
    souple — sinon on transformerait 4 vrais positifs en FP."""
    body = ("[Hermes] **[COMMENT_WITH_CONCERNS]** — notebook solide, 2 concerns FYI "
            "(seed, convergence).\nContenu verifie firsthand, code correct. "
            "**[Safe to merge]**")
    assert mod.classify("jsboige", body) == "BOT-CONCERN"


def test_gate_avant_merge_conserve():
    """NON-LEVE #6698 : gate conditionnel (« [avant merge] ») + « Safe to merge »."""
    body = ("QA vision a confirmer par une lane vision (MiniMax M3 / ai-01) "
            "[avant merge]. **[Safe to merge]**")
    assert mod.classify("jsboige", body) == "BOT-CONCERN"


def test_scope_flag_flagge():
    """NON-LEVE #7298 (+ 7 PRs du 07-18 recuperees par le marqueur) : « SCOPE FLAG,
    do NOT batch-merge » est un concern reel que l'ancien organe ne voyait pas —
    il attrapait #7298 par accident via un marqueur nie."""
    body = ("**Forensic cross-verify (po-2023) — SCOPE FLAG, do NOT batch-merge "
            "(identifier rename).** 1 identifier regression detectee.")
    assert mod.classify("jsboige", body) == "BOT-CONCERN"
    assert mod.classify(
        "jsboige", "This is a scope mismatch per one-subject-per-PR.") == "BOT-CONCERN"
    assert mod.classify(
        "jsboige", "No scope mismatch: le diff suit le body declare.") is None


def test_changes_requested_emis_flagge_toujours():
    """Garde-fou anti-surcorrection : un CHANGES_REQUESTED reellement emis reste
    une reserve."""
    assert mod.classify(
        "jsboige", "CHANGES_REQUESTED: la cellule 12 casse le kernel.") == "BOT-CONCERN"
    assert mod.classify(
        "jsboige", "2 CONCERNS ouverts, non adressés avant merge.") == "BOT-CONCERN"


# --- FN window 04-23..04-30 (triage po-2023 sur #11044) : la classe critique
# echappait a l'organe. Les 2 PRs ci-dessous ont ete mergees sans AUCUNE levee
# (0 commentaire, 0 commit post-review) avec des demandes CRITIQUES dans la
# review — et l'organe renvoyait 0 flag : « before merge » anglais n'etait pas
# un marqueur alors que « avant merge » francais l'etait. Corpus minimal : 2
# PRs, une seule formulation a couvrir.


def test_demande_anglaise_before_merge_flagge():
    """FN #594 : « several correctness issues that should be addressed before
    merge » + sections ### Critical — merge 2h apres, zero levee."""
    assert mod.classify(
        "jsboige", "Overall: solid structure. However, there are several "
        "correctness issues that should be addressed before merge.") == "BOT-CONCERN"


def test_must_fix_before_merge_flagge():
    """FN #590 : « CRITICAL — Must fix before merge » (liens morts nb01) —
    merge 4h apres, zero levee. Meme occurrence « before merge »."""
    assert mod.classify(
        "jsboige", "### CRITICAL — Must fix before merge\n"
        "1. Broken cross-references in nb01 conclusion table.") == "BOT-CONCERN"


def test_retraction_narree_ne_flagge_pas():
    """FP #748 (fenetre 05-01..05-07, triage po-2023) : le commentaire est la
    RETRACTION elle-meme — « CORRECTION — Previous CHANGES_REQUESTED was
    incorrect... Revised verdict: APPROVE » — suivi du bot « APPROVE —
    previous CHANGES_REQUESTED retracted ». « previous » ne peut que narrer
    une reserve passee, jamais en emettre une."""
    assert mod.classify(
        "jsboige", "## CORRECTION — Previous CHANGES_REQUESTED was incorrect\n"
        "Verified on all 4 scripts on main. Revised verdict: APPROVE.") is None
    assert mod.classify(
        "clusterManager-Myia",
        "APPROVE — previous CHANGES_REQUESTED retracted (see correction "
        "comment).") is None


# --- Fenetre 05-08..05-14 (triage po-2023, 18 flags / 249 PRs) : trois
# narrations mesurees, une par citer ajoute. Le reste de la fenetre (11
# FLAG-OK, 0 DEFECT-ALIVE sur main) confirme le regime de reviews : les
# reserves reelles y sont levees, les flags restants sont des narrations.


def test_negation_pas_nu_ne_flagge_pas():
    """FP #860 : « **COMMENTED** (pas CHANGES_REQUESTED) » — negation
    francaise SANS « de ». La review scoping elle-meme ses 3 points comme
    anomalies de checkpoint non bloquantes."""
    body = ("### Verdict\n**COMMENTED** (pas CHANGES_REQUESTED) — les 3 points "
            "ci-dessus sont des anomalies dans les checkpoint JSON, pas dans "
            "le code source.")
    assert mod.classify("jsboige", body) is None


def test_stale_narree_ne_flagge_pas():
    """FP #977 : « pending dismissal of stale CHANGES_REQUESTED » — le nit
    est une demande de RE-REVIEW apres fixes documentes, pas une reserve
    emise contre le merge."""
    body = ("@clusterManager-Myia please re-review: po-2026 has pushed 8 commits "
            "with documented fixes addressing all 4 flagged notebooks. Branch is "
            "now mergeable pending dismissal of stale CHANGES_REQUESTED.")
    assert mod.classify("jsboige", body) is None


def test_needs_rebase_ne_flagge_pas():
    """FP #887 (recidive de #729, fenetre 05-01..05-07) : « CONFLICTING —
    needs rebase before merge » — demande procedurelle satisfaite par le
    merge lui-meme."""
    body = ("### Notes\n- **CONFLICTING** — needs rebase before merge (same as "
            "#882)\n- No CI checks triggered (CoursIA notebooks repo)")
    assert mod.classify("jsboige", body) is None


def test_verdict_conditionnel_fleche_ne_flagge_pas():
    """FP #1247 (fenetre 05-15..05-21) : « Si Static validation rouge →
    CHANGES_REQUESTED + diagnostic » — verdict CONDITIONNEL futur. La fleche
    devant le marqueur est une derivation, jamais une emission."""
    body = ("### Verdict pré-merge\nAPPROVED conditionnel : merge dès que catalog "
            "drift fixé ET Static validation H.1/H.3 GREEN. Si Static validation "
            "rouge → CHANGES_REQUESTED + diagnostic.")
    assert mod.classify("myia-ai-01", body) is None


def test_verdict_emis_sans_fleche_flagge():
    """Garde-fou : l'arrow-citer ne desactive que la forme conditionnelle —
    un verdict reellement emis reste une reserve."""
    assert mod.classify(
        "jsboige", "Verdict : CHANGES_REQUESTED — la cellule 12 casse le kernel."
    ) == "BOT-CONCERN"


# --- Fenetre 05-22..05-28 (triage po-2023) : la RETRACTION narree. Le
# coordinateur retire SA PROPRE reserve anterieure — le commentaire qui
# retracte ne peut pas etre une nouvelle emission.


def test_retraction_earlier_ne_flagge_pas():
    """FP #1458 : « my earlier CHANGES_REQUESTED was a FALSE POSITIVE
    (retracted) » + APPROVED « Supersedes my earlier false-positive
    CHANGES_REQUESTED » + « **Retracting CHANGES_REQUESTED → approving.** ».
    « earlier »/« false-positive »/« retracting » ne peuvent que narrer un
    verdict passe."""
    assert mod.classify(
        "myia-ai-01", "## Correction — my earlier CHANGES_REQUESTED was a "
        "FALSE POSITIVE (retracted). That claim was wrong.") is None
    assert mod.classify(
        "myia-ai-01", "Approved after merge-tree verification. Supersedes my "
        "earlier false-positive CHANGES_REQUESTED.") is None
    assert mod.classify(
        "myia-ai-01", "True post-merge delta verified. **Retracting "
        "CHANGES_REQUESTED → approving.** Mea culpa.") is None


def test_supersede_possessif_ne_flagge_pas():
    """FP #1442 : « APPROVE (supersedes my CHANGES_REQUESTED of 03:21) » —
    la nouvelle review REMPLACE l'ancienne reserve, elle n'en emet pas."""
    assert mod.classify(
        "myia-ai-01", "**ai-01 — APPROVE (supersedes my CHANGES_REQUESTED "
        "of 03:21).** All three blockers are resolved.") is None


def test_my_concern_emis_flagge_malgre_citer():
    """Garde-fou anti-surcorrection : « my » nu n'est PAS un citer (forme
    bi-mot « supersedes my » uniquement) — « my CONCERNS: » est une emission."""
    assert mod.classify(
        "jsboige", "my CONCERNS: the attribution in cell 0 is still wrong."
    ) == "BOT-CONCERN"
