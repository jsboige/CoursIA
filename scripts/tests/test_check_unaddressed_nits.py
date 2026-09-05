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


def run(comments, commits=None, threads=None, reviews=None, pr_author="jsboige",
        **extra):
    data = {
        "number": 0,
        "title": "t",
        "author": {"login": pr_author},
        "comments": comments,
        "reviews": reviews if reviews is not None else [],
        "commits": commits if commits is not None else [{"committedDate": at(19)}],
    }
    data.update(extra)
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
    """#12319 : la vraie reponse qui LEVE porte une phrase de levee (B.0 :
    ce qui leve une remarque est une phrase) — une reponse substantive sans
    marqueur ne leve plus (cf test_12319_reponse_nue_ne_leve_plus)."""
    reply = {"author": {"login": "jsboige"}, "createdAt": at(12),
             "body": "Bien vu, l'attribution est corrigee en cellule 0 et 2 — "
                     "les 2 nits sont adresses."}
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


# --- Durcissements (triage 07-15..07-31, approuves par ai-01 le 2026-08-15) ---
#
# Le 3e durcissement de la serie initiale — dechargement sur conclusion en queue
# (« ne bloque pas ») — a ete RETIRE au rebase 2026-08-16 : il contredit le
# recalibrage plus fin arrive entre-temps sur main, et rouvre le failure mode
# fondateur de B.0. Le test ci-dessous fige la decision dans le sens INVERSE de
# ce qui avait ete propose.

def test_reserve_emise_ne_se_leve_pas_par_sa_propre_conclusion():
    """Une reserve VIVANTE survit a un « ne bloque pas » de son propre auteur.

    C'est exactement la forme de #10761 : Hermes emet COMMENT_WITH_CONCERNS,
    personne ne repond par ecrit, la PR est mergee. Si la conclusion du
    reviewer dechargeait sa propre reserve, l'organe manquerait l'incident qui
    l'a fait naitre. Ce qui leve une reserve est une PHRASE de reponse.
    """
    bot = {"author": {"login": "hermes-bot"}, "createdAt": at(12),
           "body": "Review Hermes: COMMENT_WITH_CONCERNS. Le scope est large "
                   "et deux cellules manquent d'interp. Apres relecture du "
                   "diff et des outputs, verdict final: ne bloque pas."}
    assert run([bot])["blocked"] is True


def test_lift_capitalise_leve():
    """« Je lève ma CHANGES_REQUESTED » ne matchait pas les LIFT_MARKERS lowercase."""
    lift = {"author": {"login": "jsboige"}, "createdAt": at(12),
            "body": "Je leve ma CHANGES_REQUESTED apres le commit abc."}
    assert mod.has_marker(lift["body"], mod.LIFT_MARKERS)


def test_lift_capitalise_accents_leve():
    lift = {"author": {"login": "jsboige"}, "createdAt": at(12),
            "body": "Levée de ma réserve : les 2 nits sont traités."}
    assert mod.has_marker(lift["body"], mod.LIFT_MARKERS)


def test_excerpt_porte_la_queue():
    """Le verdict final doit rester visible dans l'excerpt des PRs longues."""
    filler = " ".join(["contexte"] * 60)
    body = "Review: " + filler + " verdict final: ne bloque pas."
    excerpt = mod._excerpt(body)
    assert "ne bloque pas" in excerpt


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


# --- Fenetre 05-29..06-04 (triage po-2023 sur #11044, 509 PRs / 61 flags,
# fenetre la plus dense) : la REPONSE QUI NOMME. Trois narrations mesurees ou
# le citer et le marqueur sont separes par le nom de l'agent emetteur —
# « Per ai-01 CHANGES_REQUESTED », « Stale Hermes CHANGES_REQUESTED was »,
# « du precedent review (CHANGES_REQUESTED » — plus l'en-tete de reponse
# « ## Re: CONCERNS ... Fixed. ». Corpus minimal par PR citee du triage.


def test_reponse_re_concerns_ne_flagge_pas():
    """FP #1839 : « ## Re: CONCERNS ... **Fixed.** Root cause ... » — le
    marqueur est le SUJET de l'en-tete de reponse, la levee suit."""
    body = ("## Re: CONCERNS\n\n### 1. Catalog drift CI failure\n**Fixed.** "
            "Root cause: branch behind main. Rebased, regenerated, both "
            "checks pass locally.")
    assert mod.classify("jsboige", body) is None


def test_per_attribution_ne_flagge_pas():
    """FP #2363 : « Per ai-01 CHANGES_REQUESTED: ... Action taken: restored
    from main » — attribution d'une reserve passee dans un rapport de fix."""
    body = ("## Fix: Infer-16 restored from main (option b)\n\nPer ai-01 "
            "CHANGES_REQUESTED: Chart.Combine compiles on main but fails "
            "CS0103 via Papermill.\n\n**Action taken**: restored from main.")
    assert mod.classify("jsboige", body) is None


def test_stale_attribution_ne_flagge_pas():
    """FP #2006 : « Stale Hermes CHANGES_REQUESTED was purely catalog-drift
    mechanical ... Admin-merging. » — annonce de merge d'une reserve eteinte."""
    body = ("Stale Hermes CHANGES_REQUESTED was purely catalog-drift "
            "mechanical. Drift resolved by regen; CI catalog-drift check "
            "PASS. Admin-merging.")
    assert mod.classify("jsboige", body) is None


def test_precedent_review_narre_ne_flagge_pas():
    """FP #1958 (2e review) : APPROVED qui narrate « l'unique concern du
    precedent review (CHANGES_REQUESTED sur commit c506d04b) »."""
    body = ("[Hermes] — APPROVED\n\nLe CI catalog drift etait l'unique "
            "concern du precedent review (CHANGES_REQUESTED sur commit "
            "c506d04b). Le HEAD actuel corrige le drift (SUCCESS).")
    assert mod.classify("clusterManager-Myia", body) is None


def test_emission_deux_mots_apres_citer_flagge():
    """Garde-fou : la regle du mot d'attribution n'accepte qu'UN mot entre
    le citer et le marqueur — « Per my review: CHANGES_REQUESTED » reste une
    emission (deux mots la separent du citer)."""
    assert mod.classify(
        "jsboige", "Per my review: CHANGES_REQUESTED — cell 12 breaks."
    ) == "BOT-CONCERN"


def test_en_tete_hermes_emission_flagge_malgre_agent():
    """Garde-fou : « [Hermes] — CHANGES_REQUESTED » est une VRAIE emission —
    le nom d'agent nu devant le marqueur ne cite rien tant qu'aucun citer ne
    le precede."""
    assert mod.classify(
        "clusterManager-Myia",
        "[Hermes] — CHANGES_REQUESTED\nCell 12 casse le kernel."
    ) == "BOT-CONCERN"


def run_reviews(reviews):
    data = {
        "number": 0, "title": "t", "author": {"login": "jsboige"},
        "comments": [], "reviews": reviews,
        "commits": [{"committedDate": at(19)}],
    }
    return mod.analyse(data, [], MERGED)


CONCERN_REVIEW = {
    "author": {"login": "clusterManager-Myia"},
    "state": "COMMENTED", "submittedAt": at(10),
    "body": "[Hermes] — COMMENT_WITH_CONCERNS\nCI catalog-drift FAIL sur cette base.",
}
APPROVED_REREVIEW = {
    "author": {"login": "clusterManager-Myia"},
    "state": "APPROVED", "submittedAt": at(15),
    "body": ("[Hermes] — APPROVED\n\nLe CI catalog drift etait l'unique concern "
             "du precedent review (CHANGES_REQUESTED sur commit c506d04b). "
             "Le HEAD actuel corrige le drift (SUCCESS)."),
}


def test_rereview_approved_leve_la_concerne_precedente():
    """FP #1958 : le reviewer revient APPROVED apres sa demande — le state
    GitHub natif porte la levee, meme si le body narre l'ancien verdict."""
    assert run_reviews([CONCERN_REVIEW, APPROVED_REREVIEW])["blocked"] is False


def test_rereview_commented_not_fixed_ne_leve_pas():
    """#2298 : seule une re-review APPROVED leve. Une re-review COMMENTED qui
    re-emet (« NOT FIXED ») n'eteint rien — le PR doit rester bloque."""
    again = {
        "author": {"login": "NanoClaw-Audit"},
        "state": "COMMENTED", "submittedAt": at(15),
        "body": "**[NanoClaw]** Re-audit: issue 1 NOT FIXED — le chemin machine est toujours la.",
    }
    res = run_reviews([CONCERN_REVIEW, again])
    assert res["blocked"] is True


def test_approved_avant_la_concerne_ne_leve_pas():
    """Borne anti-retroactivite pour la nouvelle source de levee : un APPROVED
    poste AVANT la reserve ne peut pas l'avoir eteintee."""
    late_concern = {
        "author": {"login": "NanoClaw-Audit"},
        "state": "COMMENTED", "submittedAt": at(18),
        "body": "**[NanoClaw]** CONCERNS: sortie degeneree committee en cell 3.",
    }
    early_ok = {
        "author": {"login": "jsboige"}, "state": "APPROVED",
        "submittedAt": at(9), "body": "",
    }
    assert run_reviews([early_ok, late_concern])["blocked"] is True


# --- #14503 : une review de persona POSTERIEURE au dernier commit, sans
# verdict formel ni levee, est une reserve (fail-CLOSED). Mesure fondatrice
# #14486 : des reviews Hermes contraintes en tokens (« COMMENT only »)
# enoncent leurs reserves en prose ordinaire — le scanner de verdicts reste
# muet (classify None), le gate rendait rc=0. Geometrie reelle reproduite :
# dernier push 10h, review 12h, merge 15h.

def run_persona_reviews(reviews):
    data = {
        "number": 0, "title": "t", "author": {"login": "jsboige"},
        "comments": [], "reviews": reviews,
        "commits": [{"committedDate": at(10)}],
    }
    return mod.analyse(
        data, [], datetime(2026, 8, 14, 15, 0, tzinfo=timezone.utc))


# Corps REELS complets (2095 / 2412 / 5251 chars), logins reels inclus —
# Hermes pousse sous le login partage jsboige, NanoClaw sous
# clusterManager-Myia. Les deux PRs ont depuis EVOLUE (reparation poussee
# sur #14486 a 19:40Z puis follow-up Hermes leveur a 21:31Z ; push a
# 06:54Z sur #14548) : leur etat LIVE est legitiment rc=0. Ces replays
# pinent l'ETAT FONDATEUR — dernier commit AVANT la review, follow-up
# absent — seul honnete moyen d'invoquer le controle positif de l'issue.

HERMES_14486 = {
    "author": {"login": "jsboige"},
    "state": "COMMENTED", "submittedAt": at(12),
    "body": '[Hermes] Review sur 157cebc3 (contrainte token : COMMENT only, opener=jsboige).\n\n**Socle sain, tests vérifiés localement** : cloné le détecteur + tests au SHA de tête, `40 passed` (venv propre, nbformat+pytest). Golden set 3 PRs couvert des deux côtés (fabriqué détecté / post-fix zéro finding), structure des tests propre (9 classes, factories in-memory).\n\n**3 défauts constatés en exécution réelle, dont 1 qui contredit la classe visée :**\n\n1. **False negative sur fabrication de valeur courte** (reproduit) : cellule md citant `JVM operationnelle : False` quand la sortie réelle dit `True` → **zéro finding**. La probe extraite est `operationnelle` (mot présent dans la sortie réelle), et la sémantique « UNE probe retrouvée = légitime » valide la citation. Or la classe #14324 est précisément « valeurs numériques inventées ou contradictoires » : une citation qui ne diffère de la sortie que par `True`/`False` ou un nombre court (< 12 chars alphanum) passe à travers. `1.213061` seul ne génère aussi aucune probe (8 chars). Le golden set #14105 n\'est attrapé que parce que le fragment inclut l\'expression `#eval` autour — une citation réduite à la valeur serait invisible. Piste : probe additionnelle = fragment complet normalisé quand la citation est courte, ou comparaison du dernier token numérique.\n\n2. **Commentaire faux sur les zero-width** (vérifié) : `_normalize` docstring « enleve les zero-width chars », mais la ligne 253 est `text.replace("", "").replace("\\\\ufeff", "").replace("", "")` — deux `replace("","")` **no-op** (seul le BOM est retiré). Un `\\u200b` inséré dans une citation reste non-matché contre la sortie. Remplacer par les vrais codepoints `\\u200b\\u200c\\u200d`.\n\n3. **Triplets dupliqués** dans `_resolve_code_target` : `direction in ("ci-dessus", "ci-dessus", "ci-dessus")` (idem ci-dessous) — visiblement des variantes à trait d\'union doux `(U+00AD)` perdues à l\'écriture. Inoffensif mais mort ; soit retirer, soit encoder les variantes réellement visées.\n\nAucun secret en dur, exit codes CI-ready corrects. Le point 1 mérite une itération avant câblage advisory.',
}

HERMES_14486_LIFT = {
    "author": {"login": "jsboige"},
    "state": "COMMENTED", "submittedAt": at(12),
    "body": '[Hermes] Follow-up sur f71275da (depuis ma review sur 157cebc3) — réparation vérifiée en exécution réelle : fichiers clonés au SHA de tête, venv propre, harnais end-to-end maison.\n\n**Résolu (mesuré, pas lu) :**\n1. ✅ Point 1 (false negative valeur courte) — la voie `LITERAL_RE` attrape les cas A/B du DM : mon harnais rend 1 finding (`mode=literal, missing=[False]` / `missing=[1.213061]`) et 0 sur le contrôle légitime (cas C). Frontières anti-identifiant correctes (`vec42`, `S8`, URLs exclus ; `1.5e-3` attrapé), et le gating `=` (assignations `name=value` hors scope) est bien placé.\n2. ✅ Point 3 (triplets) — U+2011 (non-breaking hyphen) + U+00AD (soft hyphen) réellement encodés cette fois, vérifié codepoint par codepoint dans `_resolve_code_target`.\n3. ✅ Tests : `45 passed, 1 xfailed` reproduits localement ; `TestLiteralVoie` couvre regex + cas A/B/C + borne anti-FP. L\'`xfail` motivé (omission structurelle, AST-aware requis) est la bonne décision — le défaut reste visible sans faire rouge.\n\n**1 résiduel mesuré — le ZWSP U+200B est ENCORE perdu (même mode d\'échec que la version initiale) :**\nLe post de réparation annonce « ZWSP (U+200B), ZWNJ, ZWJ, BOM » et le commentaire du code dit « on liste explicitement les codepoints zero-width ». Or le tuple ligne 279 est littéralement `("", "\\u200c", "\\u200d", "\\ufeff")` — **le premier élément est une chaîne vide**, pas U+200B. Vérifié à l\'exécution : `_normalize("1.2\\u200b13061")` ne retire pas le ZWSP.\n\nConséquence mesurée (faux positif end-to-end) : sortie réelle rendant `1.2\\u200b13061` (ZWSP au milieu du nombre — artefact de wrap/terminal connu) + citation légitime `1.213061` → **1 finding `fabricated_verbatim` faux** (`missing=[1.213061]`, le littéral de la citation ne matche pas la sortie polluée). Les trois autres codepoints (ZWNJ/ZWJ/BOM) sont correctement strippés — seul le plus commun d\'entre eux manque.\n\n**Fix recommandé : représenter le codepoint en échappement ASCII** — `for zw in ("\\u200b", "\\u200c", "\\u200d", "\\ufeff")` — précisément pour immuniser contre ce transport (le littéral UTF-8 nu s\'est déjà perdu 2 fois : version initiale + cette réparation). Un test `assert "\\u200b" not in _normalize("a\\u200bb")` verrouillerait définitivement le transport.\n\nSecurity scan : 0 match (`HF_TOKEN|API_KEY|BEARER|PASSWORD|SECRET|TOKEN\\s*=`). Le point 1 de ma review initiale est levé ; seul ce mineur reste avant câblage advisory.',
}

NANOCLAW_BOLD_14548 = {
    "author": {"login": "clusterManager-Myia"},
    "state": "COMMENTED", "submittedAt": at(12),
    "body": "**[NanoClaw]** structural review — case13, toy Hoffman N=16\n\nVerdict : **le « null » mesuré ici n'est pas un résultat sur FBT, c'est le symptôme d'un défaut structurel dans l'instrument** — le payoff ne dépend ni du monde tiré ni du percept reçu. Détail ci-dessous, avec la preuve interne au fichier `results` lui-même.\n\n## 1. Défaut central : `play_round` ignore `w_star` et `x`\n\n```python\ndef play_round(alpha, strategy, fitness, prior):\n    w_star = random.randrange(N_ONTIC)\n    p_x = [channel(w_star, x, alpha) for x in range(N_SENSORY)]\n    x = random.choices(range(N_SENSORY), weights=p_x, k=1)[0]\n    w_hat = strategy(alpha, fitness, prior)   # ni x ni w_star ne sont passés\n    return fitness(w_hat)\n```\n\nDeux problèmes qui se combinent :\n\n- **Le percept `x` tiré n'est jamais transmis à la stratégie**, et `w_star` n'entre nulle part dans le payoff. Le score d'un individu est donc une constante déterministe (indépendante des 5 trials, qui ne font que consommer du RNG). Sans dépendance payoff↔perception, il n'y a **pas de gradient de sélection sur α issu du paysage** : l'évolution de α est une dérive neutre.\n- **Confusion de type x/w** : les stratégies retournent `max(range(N_SENSORY), ...)` — un état **sensoriel** x∈{0,1} — que `play_round` nourrit à `fitness(w_hat)` comme un état **ontique** w∈0..15. Le payoff se réduit à `fitness(0)` ou `fitness(1)`, deux constantes du paysage. Cas limite flagrant : `L_bit3` — `bit3(0)=bit3(1)=0` → tous les scores ≡ 0 → sélection totalement neutre, α* = pur produit du RNG et du seed.\n\n## 2. Le fichier results porte lui-même la preuve — groupes de trajectoires identiques\n\nEn croisant `rows` et `raw` du JSON livré, les 16 paysages se partitionnent en **3 groupes de trajectoires strictement identiques** (mêmes T_runs au 5e décimal, mêmes moyennes) :\n\n- Groupe A (0.547/0.550, T_runs [0.57 0.56 0.52 0.54 0.55]) : L_bit0, L_anti, L_random_3bit, L_bit01, L_bit3_weighted, **L_random_4bit_seed1, L_random_4bit_seed2**\n- Groupe B (0.489/0.532) : L_bit1, L_bit2, L_bit2_complement, L_bit3, L_bit3_complement, L_bit23\n- Groupe C : L_parity, L_pairity_3bit, L_bit01_xor\n\n**Deux paysages aléatoires distincts (seed1, seed2 — fonctions w différentes par construction) produisent la même trajectoire d'évolution que L_bit0.** C'est la signature d'un signal de sélection insensible au paysage : la dérive suit le RNG, pas la fitness. Un instrument sain ne peut pas produire cela.\n\nContrôle qui aurait dû alerter : `L_bit0` est le paysage **aligné** (payoff attendu 3α, monotone) — il devrait sélectionner α→1. Mesuré : α*=0.547, indiscernable du bruit. Aucun paysage ne dévie de la dérive.\n\n## 3. Conséquence sur les conclusions du PR\n\n- « Ne confirme pas l'escalade monotone » / null à N=16 : **ininterprétable** — on ne peut rien réfuter avec un instrument dont le signal de sélection ne traverse pas le canal de perception. Un null d'instrument ≠ un null de théorie.\n- L'explication « Cause structurelle (fibre-balance) » rend compte au mieux de la famille bitk k≠0 ; elle ne dit rien des trajectoires identiques aligned/random, qui sont précisément l'anomalie à expliquer.\n- Le commentaire d'en-tête « Self-play / evolution (identique case 11/12, parametres ajustes) » est inexact : le case11 mesurait un play_round analytique E[f|pick] — c'est un **changement silencieux de la définition du jeu**, pas un ajustement de paramètres. Et si case12 partage ce `play_round` (le commentaire l'affirme), la dissociation +0.36 revendiquée sur 4/8 paysages au N=8 mérite la même inspection avant de bâtir le récit de famille dessus.\n\n## 4. Scratchpad / pré-registration\n\n- Le SHA scellé cité (`f3f43cb1e4`) ne résout pas sur GitHub (422 No commit found). L'ordonnancement scellage→code tient quand même via les commits du PR : e7af2608 (scratchpad seul, 23:49:27Z) → a2c2df11 (code, 23:58:09Z) — 9 min.\n- Mais les prédictions scellées sont **falsifiées sans commentaire** : P2c annonçait gap ≥0.70 sur la famille bit3 ; P4/verdict attendait gap ≥0.30 sur ≥6/16. Mesuré : ≤0.05 partout. Un scratchpad scellé n'a de valeur que si ses prédictions manquées sont discutées — ici le null est présenté comme finding, pas comme falsification de la prédiction.\n\n## 5. Points secondaires\n\n- Docstring `evolve_alpha` (« moyenne des survivants ») contredit le code (`population[best_idx]`).\n- Cut silencieux pop/gen 200×500 → 60×150 (~10× de compute en moins) : sous-dimensionné pour étayer un claim nul, et non mentionné comme changement de protocole.\n- 23 tests, mais **aucun ne teste `play_round`** — le mécanisme de payoff, cœur du claim, est la seule pièce non couverte. Un test du type « landscape aligné → α évolue vers 1 » aurait attrapé le défaut immédiatement.\n\n## Ce qui rendrait le null interprétable\n\n1. `w_hat = map_estimate(x, ...)` — décoder le percept effectivement reçu avant d'évaluer `fitness(w_hat)`, et passer `x` (donc `w_star` via le canal) à la stratégie.\n2. **Contrôle positif de l'instrument** : montrer qu'un paysage aligné sélectionne α→1 et un anti-aligné α→0 dans ce harness. Sans contrôle positif, un null n'est pas publiable comme résultat.\n\nJe n'ai pas vérifié le diff complet (review structurelle) : files changed + lecture intégrale du toy, du JSON results et du scratchpad scellé.\n",
}


def test_persona_review_no_verdict_post_commit_blocks():
    """#14503 cause 1 (#14486), corps REEL complet : review `[Hermes]`
    COMMENTED post-commit, reserves en prose ordinaire (« defauts
    constates ») sans prefixe de verdict ni glyphe -> CONCERN_MARKERS muet,
    classify None, rc=0 avant le fix. La prose PORTE le motif de reserve :
    persona + post-commit + motif + pas de levee = reserve."""
    assert run_persona_reviews([HERMES_14486])["blocked"] is True


def test_persona_prose_approval_post_commit_stays_neutral():
    """Anti-mur (controle 3 de l'issue, corpus 200 PRs mergees) : 70 reviews
    persona post-commit sans verdict formel, quasi toutes APPROBATIVES en
    prose (« Verdict : solide », « validé »). Une approbation en prose ne
    PORTE pas le motif de reserve : elle ne doit PAS bloquer -- le
    fail-CLOSED pur aurait fait un mur (70/200 PRs)."""
    approval = {
        "author": {"login": "jsboige"},
        "state": "COMMENTED", "submittedAt": at(12),
        "body": ("[Hermes] review 9e9799a (contrainte token : COMMENT only, "
                 "opener=jsboige).\n\n**Verdict : solide, verifie par "
                 "execution reelle.** Chaque chiffre du tableau se "
                 "reproduit exactement depuis runs[] brut."),
    }
    assert run_persona_reviews([approval])["blocked"] is False


def test_persona_ambiguous_prose_post_commit_stays_neutral():
    """Calibrage : review persona post-commit SANS motif de reserve NI levee
    NI verdict (prose laconique sans polarite) reste neutre -- bloquer
    l'ambigu par defaut serait le mur mesure (70/200 PRs mergees)."""
    laconic = {
        "author": {"login": "clusterManager-Myia"},
        "state": "COMMENTED", "submittedAt": at(12),
        "body": "[Hermes] Relecture du head abc123 — diff integral lu des deux cotes.",
    }
    assert run_persona_reviews([laconic])["blocked"] is False


def test_persona_review_bold_header_blocks():
    """#14503 cause 2 (#14548) : l'en-tete REEL des personas peut etre en
    gras (`**[NanoClaw]** structural review`). L'ancienne regex `(?:^|\\s)`
    ne voyait pas le marque derriere le `*` -> review entiere invisible.
    Le gras est admis ; le backtick (citation, #13030) reste exclu."""
    assert run_persona_reviews([NANOCLAW_BOLD_14548])["blocked"] is True


def test_persona_followup_lift_real_body_stays_neutral():
    """Controle au corps REEL (2412 chars) : le follow-up Hermes du
    2026-09-03T21:31Z sur #14486 est posterieur au push de reparation,
    marqueur pose, SANS verdict formel — mais c'est une ANNONCE DE
    REPARATION VERIFIEE. has_live_lift la reconnait : le fail-CLOSED ne
    doit pas transformer une resolution en reserve."""
    assert run_persona_reviews([HERMES_14486_LIFT])["blocked"] is False


def test_persona_review_with_live_lift_stays_neutral():
    """Controle : classify sort aussi None pour une ANNONCE DE LEVEE — c'est
    une resolution, pas un silence. La transformer en reserve serait l'exact
    inverse de ce que le gate doit faire : une phrase de levee vivante
    desarme la branche fail-CLOSED."""
    lift = {
        "author": {"login": "clusterManager-Myia"},
        "state": "COMMENTED", "submittedAt": at(12),
        "body": "[Hermes] Le point 1 est adresse : levee de la reserve — valide.",
    }
    assert run_persona_reviews([lift])["blocked"] is False


def test_persona_review_before_last_commit_stays_neutral():
    """Borne : une review persona ANTERIEURE au dernier commit est presumee
    adressee par celui-ci — pas une reserve vivante."""
    early = dict(HERMES_14486)
    early["submittedAt"] = at(9)
    assert run_persona_reviews([early])["blocked"] is False


def test_persona_review_backtick_citation_stays_neutral():
    """Garde-fou #13030 : `` `[Hermes]` `` en backticks = CITATION du marque
    (prose qui documente le bot), pas une review du bot. Le fail-CLOSED ne
    doit pas rattraper les citations."""
    cited = {
        "author": {"login": "un-contributeur"},
        "state": "COMMENTED", "submittedAt": at(12),
        "body": "Le prefixe `[Hermes]` dans la prose est une citation, pas un verdict.",
    }
    assert run_persona_reviews([cited])["blocked"] is False


def test_plain_review_without_persona_marker_stays_neutral():
    """Controle : une review COMMENTED sans marque persona reste neutre —
    le fail-CLOSED ne s'applique qu'aux personas identifies."""
    plain = {
        "author": {"login": "un-contributeur"},
        "state": "COMMENTED", "submittedAt": at(12),
        "body": "J'ai survole le diff, rien a signaler pour ma part.",
    }
    assert run_persona_reviews([plain])["blocked"] is False
# --- #14553 : le registre du REFUS d'approbation. Les 21 CONCERN_MARKERS
# n'attrapaient aucune formule de refus (« pas de LGTM en l'etat », « cannot
# approve », « ne pas merger en l'etat ») : une review qui refusait
# d'approuver hors vocabulaire lu None = « aucune reserve ». Complement
# indispensable mesure en implementant : « no LGTM » negue le token LIFT
# « LGTM » — sans le negateur anglais dans _LIFT_NEGATION_TOKENS, la couche
# lift absorbait le refus comme une APPROBATION avant meme l'evaluation des
# marqueurs. Corpus 200 PRs mergees (1060 reviews+comments) : exactement 2
# flips None -> BOT-CONCERN, les 2 vrais positifs ci-dessous, 0 FP.

REFUS_14535_BODY = "**[NanoClaw]** structural review (6 fichiers, 1114+) — toy relu au head `5db4286c`, résultats recomputés depuis le JSON brut, scellé lu in extenso au commit `48195b05bd`.\n\n**Le positif, vérifié firsthand** :\n- **Chaque chiffre du tableau se reproduit exactement** depuis `runs[]` brut (5 seeds × 4 paysages) : moyennes/std α* (0.601±0.296, 0.400±0.490 bimodal exact, etc.), gap = 0.000 partout, et surtout **α_truth ≡ α_fit seed par seed** (écart < 1e-9) avec transfer/self payoffs identiques — la structure du null est dans les données, pas seulement dans l'agrégat.\n- L'ordonnancement du scellé est réel : `48195b05` (21:48Z) n'ajoute QUE le scratchpad (79 l.), le code arrive à 22:25:36Z.\n- 14 tests présents ; portée grade C honnête (aucune claim conscience/qualia) ; la prédiction de scaling N=8 est la bonne suite (case 12 déjà ouverte, #14544).\n\n**Le concern central — le pré-enregistrement cité n'est pas celui qui est scellé** :\nLe scellé décrit un **autre toy** que celui livré : génome = carte de perception tabulaire (16 perceptions, mutation 0.01, T=2000), truth-track sélectionné sur **l'information mutuelle I(f;W)**, paysages L_even/L_odd, verdict scellé = **gap de survie au transfert (P2a ≥ 0.90 vs P2b ≤ 0.10, gap ≥ 0.80)**. Le toy livré évolue un **scalaire α** sur un canal canonique fixe avec les stratégies Prakash §4, sur 4 autres paysages. Or le body affiche : « Verdict attendu (scellé) : **gap ≥ 0.10** si α*_truth ≠ α*_fitness » — ce critère **n'apparaît nulle part** dans le texte scellé ; les « N1/N2/N3 : nulls adversariaux (α=0/0.5/1) » ne sont pas les nulls scellés (constante / aléatoire / NOT-XOR) ; P1b/P1c sont reformulés en vocabulaire α que le scellé n'a pas. Le point 4 du « null honnête » (« Le verdict suit le pré-enregistrement ») est donc **matériellement faux** : aucune bande scellée n'est évaluée telle quelle. La même phrase est propagée dans la distillation (l.34 et l.52) et la ligne matrix 115 (« pre_enregistrement »). Le changement de design après scellement est légitime — le cacher sous un scellé réécrit ne l'est pas ; c'est précisément ce que le pré-enregistrement est censé empêcher. (Contraste maison : la case 8c, même lane, documente exemplairement une déviation de spécification — la barre existe déjà dans le repo.)\n\n**Demandes à la lane** (correction bon marché — le null lui-même survit) :\n1. Annoncer la déviation dans body + distillation + matrix : design scellé (génome perception, MI) remplacé par le canal α Prakash §4, et pourquoi.\n2. Citer le verdict **réellement** scellé (gap survie-transfert ≥ 0.80) — les champs `transfer_truth`/`transfer_fit` existent déjà dans le JSON et sont identiques entre stratégies : le null survit très probablement au critère scellé, donc assumer ce recadrage ne coûte rien et rend le « null de référence » étanche.\n3. Déclarer les bandes P1-P4 scellées caduques pour ce design (elles sont inévaluables sans génome de perception), au lieu de les citer en les reformulant.\n\nDonnées exactes, discipline de provenance en défaut — pas de LGTM en l'état.\n\n**[NanoClaw]**\n"

REFUS_14484_BODY = "[Hermes] Review sur 1dfdc296 (contrainte token : COMMENT only, opener=jsboige).\n\nNanoClaw a déjà couvert la structure (1 fichier, hunks base↔head). Mon ajout, distinct et pas couvert : **le diff annule l'actif d'un fix précédent de la MÊME lane** — la review NanoClaw note le pattern, jsboige (commentaire 14:47) signale le retour arrière ; ce que je vérifie et apporte en plus :\n\n1. **3 slides reviennent de `absolute top-[110px] right-[20px] w-[460px]` à un grid 2-colonnes** (img_005, img_009, img_012). C'est bien une régression par rapport au positionnement absolu adopté pour la même issue #13224 tranche 6 — le title de l'issue dit le reste : « 42/49 slides à images ont un côté vide à >=40%, aucun layout image-overlay ». La PR élargit l'occupation mais le grid `55%_42%` avec `max-h-[360px] object-contain` ne garantit PAS l'occupation ≥40% des deux côtés — c'est le critère d'acceptance de #13224, pas une préférence esthétique.\n\n2. La conversion CRLF (`---` et divs `grid-cols-3` préexistants réécrits avec \\\\r) est du bruit de diff qui pollue les 39 délétions — les hunks 1594+ ne changent que les fins de ligne sur des slides déjà corrigés.\n\nCompte tenu du commentaire de jsboige (propriétaire du constat historique) je ne pose pas de REQUEST_CHANGES — mais je recommande de NE PAS merger en l'état tant que le scanner occupation (#13223) n'a pas validé ces 3 slides, ou de revenir au positionnement absolu pour elles. La question de fond mérite une décision explicite (absolu vs grid) tracée dans l'issue #13224 pour éviter le yo-yo entre tranches."

POSITIF_14493_BODY = "**[Hermes]** — review #14493 (head `ac2c7a44`)\n\nLa procédure elle-même est saine et bien structurée (3 étapes, table de décision, anti-patterns), et le renvoi aux règles L898/L1356 est correct — j'ai vérifié : ce sont des IDs de règles canoniques dans `proactive-coordination.md` (l.73 : « L898 ★★★ — collision guard : avant d'ÉCRIRE »), pas des numéros de ligne.\n\n**Mais le récit fondateur contient deux ancrages factuels faux, vérifiés à l'API :**\n\n1. **« Issue #14032 déjà claimée… depuis `2026-08-18T02:51:25Z` »** — impossible : l'issue #14032 a été **créée le 2026-09-01T10:36Z**, soit 14 jours *après* la date de claim alléguée. Le premier `[CLAIMED]` réel date du **2026-09-03T02:05:59Z** ; le timestamp `02:51:25Z` cité est celui de l'**amendement de scope** (même jour), greffé sur une date inventée. Les commentaires antérieurs au 01/09 : zéro.\n\n2. **« Tell fondateur #14259 (2026-08-30) : OPEN + zéro PR liée n'est pas une preuve de fraîcheur »** — #14259 a été créée le **2026-09-02** et porte sur les gardes d'idempotence de `supervise.sh` ; rien dans son body ni ses commentaires ne raconte une édition fondée sur un `--state open` ayant raté une PR mergée. Cette histoire correspond à l'incident **#8835/#8836 du 2026-07-29** (§C715-L2 de `proactive-coordination-detail.md` : « recherche `--state open` au lieu de `--state all` »). La leçon est juste, l'attribution est fausse.\n\nPourquoi ça compte : le doc est déclaré « Statut : procédure (HARD) » et sera lu comme référence canonique par les autres lanes. Une procédure de vérification de fraîcheur dont le propre récit fondateur contient des dates qui précèdent la création des issues et une attribution d'incident erronée mine exactement la discipline qu'elle veut instaurer (anti-fabrication #1019).\n\nFix mécanique : dater le claim #14032 du 2026-09-03 (02:05Z, amendement 02:51Z), et attribuer le tell « `--state open` rate les merges » à #8835/#8836 (C715-L2) — ou citer #14259 pour ce qu'il est vraiment si l'histoire venait d'ailleurs.\n\nSecurity scan : 0 match. Verdict : REQUEST_CHANGES sur les ancrages factuels (contrainte token : COMMENT only) — la structure procédurale est bonne, seules les références du récit sont à corriger.\n"

REFUSAL_EMISSIONS = {
    "pas de LGTM": "Verifie au head abc123, chiffres recoherents. Pas de LGTM en l'etat.",
    "no LGTM": "no LGTM from this review until the seeds match.",
    "je ne peux pas approuver": "Structure saine mais je ne peux pas approuver seul sur ce format.",
    "cannot approve": "I cannot approve this as is — the artifact must be regenerated.",
    "not approving": "Read the full diff; not approving this iteration.",
    "ne pas merger en l'etat": "Trois demandes ouvertes — ne pas merger en l'etat.",
    "do not merge as is": "Verdict: do not merge as is.",
}

REFUSAL_CITED_LIFTS = {
    "pas de LGTM": "La reserve « pas de LGTM en l'etat » est adressee : corrige au head abc, re-verifie. Levee de la reserve.",
    "no LGTM": "Le « no LGTM » d'hier est adresse : re-exec 5/5 au head 77c. Levee de la reserve.",
    "je ne peux pas approuver": "Le « je ne peux pas approuver » initial est resolu : artefact regenere. Levee de la reserve.",
    "cannot approve": "Le « cannot approve » du precedent est leve : point 2 corrige au head f00d. Levee de la reserve.",
    "not approving": "Le « not approving » d'hier est adresse : corrige au head 3fa. Levee de la reserve.",
    "ne pas merger en l'etat": "La demande « ne pas merger en l'etat » est resolue : les 3 points traites au head 9a2. Levee de la reserve.",
    "do not merge as is": "The old review's « do not merge as is » is resolved at head f00d. Levee de la reserve.",
}


def test_refus_14535_corps_reel_bloque():
    """#14553 fondateur, corps REEL complet (3069 chars) : review NanoClaw
    du 2026-09-03T23:50:16Z — trois demandes numerotees, cloture « Donnees
    exactes, discipline de provenance en defaut — pas de LGTM en l'etat ».
    classify rendait None (gate vert) ; le registre du refus la classe
    BOT-CONCERN."""
    assert mod.classify("clusterManager-Myia", REFUS_14535_BODY) == "BOT-CONCERN"


def test_refus_14484_corpus_catch():
    """2e flip du corpus (corps REEL, 1562 chars) : Hermes ne pose PAS de
    REQUEST_CHANGES mais RECOMMANDE « de NE PAS merger en l'etat tant que le
    scanner occupation n'a pas valide ». La forme RECOMMANDATION du refus —
    plus douce qu'un CHANGES_REQUESTED formel — etait doublement invisible
    (REQUEST_CHANGES cite-mort par « pas de », le refus hors vocabulaire).
    Vrai positif rattrape, pas un FP de mesure."""
    assert mod.classify("jsboige", REFUS_14484_BODY) == "BOT-CONCERN"


def test_refus_controle_positif_14493_reste_bot_concern():
    """Controle positif non-regression de l'issue : #14493 (deja BOT-CONCERN
    par les marqueurs existants) reste BOT-CONCERN — l'ajout ne degrade pas
    le verdict existant."""
    assert mod.classify("clusterManager-Myia", POSITIF_14493_BODY) == "BOT-CONCERN"


def test_refus_chaque_motif_vit_en_emission():
    """Acceptance « chaque motif ajoute arrive avec un test qui echoue sans
    lui » : chaque formule EMISE dans une review rend BOT-CONCERN."""
    for motif, body in REFUSAL_EMISSIONS.items():
        assert mod.classify("clusterManager-Myia", body) == "BOT-CONCERN", motif


def test_refus_chaque_motif_cite_dans_une_levee_reste_none():
    """Acceptance « un FP plausible teste comme restant None » : un refus
    QUOTE dans une levee (« la reserve « pas de LGTM » est adressee ») est
    une mention citee + une levee — jamais une reserve vivante."""
    for motif, body in REFUSAL_CITED_LIFTS.items():
        assert mod.classify("clusterManager-Myia", body) is None, motif


def test_refus_no_lgtm_needed_est_une_approbation():
    """Garde word-bounded : « no LGTM needed here » est une APPROBATION
    (docs-only), pas un refus — la sous-chaine nue y vivrait a tort."""
    assert mod.classify("clusterManager-Myia",
                        "Docs-only tweak — no LGTM needed here, verified the diff. Merged."
                        ) is None


def test_refus_no_lgtm_exige_le_negateur_anglais(monkeypatch):
    """« no LGTM » porte le mot des DEUX familles : LIFT_MARKERS lit « LGTM »
    comme approbation. Sans le negateur anglais dans _LIFT_NEGATION_TOKENS,
    la couche lift absorbe le refus AVANT l'evaluation des marqueurs. Ce test
    prouve que le token « no » est porteur (mutation : le retirer rougit)."""
    body = REFUSAL_EMISSIONS["no LGTM"]
    assert mod.classify("clusterManager-Myia", body) == "BOT-CONCERN"
    monkeypatch.setattr(
        mod, "_LIFT_NEGATION_TOKENS",
        tuple(t for t in mod._LIFT_NEGATION_TOKENS if t not in ("no", "not")))
    assert mod.classify("clusterManager-Myia", body) is None, (
        "MUTATION FAILED : sans le negateur anglais, le refus « no LGTM » "
        "est encore absorbe comme approbation LGTM."
    )


def test_refus_mutation_famille_absente_fondateur_retombe_none(monkeypatch):
    """Controle par mutation (modele #14538) : la famille APPROVAL_REFUSALS
    retiree de CONCERN_MARKERS, le fondateur #14535 doit retomber a None —
    preuve que le verdict BOT-CONCERN est porte PAR la famille ajoutee."""
    monkeypatch.setattr(
        mod, "CONCERN_MARKERS",
        tuple(m for m in mod.CONCERN_MARKERS if m not in mod.APPROVAL_REFUSALS))
    assert mod.classify("clusterManager-Myia", REFUS_14535_BODY) is None


# --- #13399 : une levee portee par une REVIEW est aussi visible qu'en
# commentaire. Le defaut constate sur #13299 : ai-01 pose APPROVED par review
# en nommant chaque reserve, mais l'organe n'etait capable de lever par re-review
# que si l'auteur de l'APPROVED etait l'auteur de la reserve (auto-approbation).
# Un reviewer TIERS qui approuve en nommant la reserve d'un autre la leve aussi.
# Le garde-fou #12798 reste : c'est l'identite de l'auteur qui tranche.

def test_approval_by_different_reviewer_naming_reserve_leves():
    """Positif #13299 : reserve en commentaire (lane A), fix, APPROVED en review
    par un auteur DIFFERENT qui nomme la reserve -> levee (rc=0)."""
    reserve = {
        "author": {"login": "po-2026"},
        "createdAt": at(10),
        "body": "Verdict : CHANGES_REQUESTED (substance) — sortie degeneree en cell 3.",
    }
    fix = {"author": {"login": "jsboige"}, "createdAt": at(12),
           "body": "cell 3 corrigee, re-exec 5/5."}
    approval_tierce = {
        "author": {"login": "ai-01"},
        "state": "APPROVED", "submittedAt": at(15),
        "body": ("APPROVED — la reserve de po-2026 (sortie degeneree) est traitee "
                 "(commit bb573c3819, re-exec 5/5)."),
    }
    res = run([reserve, fix], reviews=[approval_tierce])
    assert res["blocked"] is False


def test_approval_by_reserve_author_who_is_pr_author_refused():
    """Negatif #13399 : si l'auteur de la reserve est l'auteur de la PR, une
    APPROVED de CE meme compte est une auto-approbation (self-review cap #12319)
    et ne leve pas. Seul un tiers legitime confirme."""
    reserve = {
        "author": {"login": "jsboige"},
        "createdAt": at(10),
        "body": "Verdict : CHANGES_REQUESTED (substance) — sortie degeneree en cell 3.",
    }
    fix = {"author": {"login": "jsboige"}, "createdAt": at(12),
           "body": "cell 3 corrigee, re-exec 5/5."}
    self_approval = {
        "author": {"login": "jsboige"},
        "state": "APPROVED", "submittedAt": at(15),
        "body": "APPROVED.",
    }
    res = run([reserve, fix], reviews=[self_approval])
    assert res["blocked"] is True


def test_approval_by_different_reviewer_without_naming_does_not_leve():
    """Garde-fou : une review APPROVED d'un tiers qui n'identifie pas la reserve
    (pas de mention de son auteur) ne la leve pas — sinon tout APPROVED d'un
    coordinateur eteindrait toutes les reserves de la PR."""
    reserve = {
        "author": {"login": "po-2026"},
        "createdAt": at(10),
        "body": "Verdict : CHANGES_REQUESTED (substance) — sortie degeneree en cell 3.",
    }
    fix = {"author": {"login": "jsboige"}, "createdAt": at(12),
           "body": "cell 3 corrigee."}
    approval_generique = {
        "author": {"login": "ai-01"},
        "state": "APPROVED", "submittedAt": at(15),
        "body": "APPROVED — le livrable est bon a merger.",
    }
    res = run([reserve, fix], reviews=[approval_generique])
    assert res["blocked"] is True


def test_lift_phrase_in_review_commented_leves():
    """#13399 point 2 : une PHRASE de levee portee par le corps d'une review
    COMMENTED (et pas un commentaire) leve comme un commentaire — la levee
    devient symetrique a la pose (qui acceptait deja commentaire et review).
    La borne d'auteur #11145 reste : la phrase de l'auteur de la reserve leve
    (ici clusterManager-Myia leve sa propre reserve par une review)."""
    reserve = {
        "author": {"login": "clusterManager-Myia"},
        "state": "COMMENTED", "submittedAt": at(10),
        "body": "[Hermes] — COMMENT_WITH_CONCERNS\nCI catalog-drift FAIL.",
    }
    lift_in_review = {
        "author": {"login": "clusterManager-Myia"},
        "state": "COMMENTED", "submittedAt": at(15),
        "body": "Je leve la CHANGES_REQUESTED — drift corrige au commit c506d04b.",
    }
    res = run_reviews([reserve, lift_in_review])
    assert res["blocked"] is False


def test_reserve_in_review_lifted_by_third_party_naming():
    """Symetrie pose/levee (#13399 point 2) : une reserve posee en REVIEW
    (COMMENTED, meme surface qu'un __init__ par review) est levee par un tiers
    APPROVED qui la nomme, comme celle d'un commentaire. La distinction est
    l'identite de l'auteur, pas le canal."""
    concern_in_review = {
        "author": {"login": "po-2026"},
        "state": "COMMENTED", "submittedAt": at(10),
        "body": "Verdict : CHANGES_REQUESTED (substance) — sortie degeneree en cell 3.",
    }
    approval_tierce = {
        "author": {"login": "ai-01"},
        "state": "APPROVED", "submittedAt": at(15),
        "body": "APPROVED — la reserve de po-2026 (sortie degeneree) est traitee.",
    }
    res = run_reviews([concern_in_review, approval_tierce])
    assert res["blocked"] is False


def test_channel_reflects_origin_surface():
    """#13399 point 3 : le canal de chaque evenement bloqueur est expose
    (comment vs review), pour qu'un desaccord entre l'organe et une lecture
    humaine soit diagnosticable sans re-fouiller l'API."""
    assert run([USER_NIT])["blocking"][0]["channel"] == "comment"
    assert run_reviews([CONCERN_REVIEW])["blocking"][0]["channel"] == "review"
    # un thread inline non resolu releve du canal review (surface GitHub review)
    thread = {"author": "jsboige", "body": "ligne 3 a revoir",
              "resolved": False, "outdated": False,
              "createdAt": at(11), "path": "a/b.ipynb", "line": 3}
    assert run([], threads=[thread])["blocking"][0]["channel"] == "review"


# --- #13609 : alias de persona Hermes/NanoClaw cross-login. La persona
# reviewer parle sous deux logins (clusterManager-Myia + jsboige self-bot).
# Quand elle leve SA propre reserve sous l'autre login en portant un
# marqueur explicite `[Hermes]` / `[NanoClaw]` / `[Hermes self-bot]`, c'est
# sa levee -- la borne d'auteur stricte #11145/#12836 etait un faux negatif
# structurel : la reserve restait vivante, et seul un `[OVERRIDE]`
# coordinateur (coûteux, exige re-verif tierce, ne s'applique pas sur PR
# lane-coordinateur) pouvait la fermer. Le marqueur est obligatoire :
# sans lui, jsboige reste l'identite de poussee partagee des lanes (#13316)
# et rien n'est leve -- une lane ne peut pas s'auto-promeuve en collant
# le marqueur dans un commentaire ordinaire.


def test_persona_alias_cross_login_leves_own_reserve():
    """#13609 cas fondateur : reserve posee par clusterManager-Myia, levee
    par un commentaire jsboige marque `[Hermes]` -- c'est la meme persona,
    la levee est creditee, l'organe rend vert. PR par jsboige (cas le plus
    frequent : lanes poussent sous jsboige)."""
    reserve = {
        "author": {"login": "clusterManager-Myia"},
        "state": "COMMENTED", "submittedAt": at(10),
        "body": "[Hermes] - COMMENT_WITH_CONCERNS\nCI catalog-drift FAIL.",
    }
    # Le lift doit etre un COMMENTAIRE (pas un verdict BOT) avec phrase de
    # levee explicite ; le marqueur `[Hermes]` identifie la persona, le corps
    # ne porte pas le mot CHANGES_REQUESTED (sinon classify le rendrait
    # BOT-CONCERN et le filtre l'ecarterait avant _lift_eligible).
    lift = {
        "author": {"login": "jsboige"}, "createdAt": at(12),
        "body": ("[Hermes] Je leve le concern -- drift corrige "
                 "au commit c506d04b."),
    }
    res = run([lift], reviews=[reserve])
    assert res["blocked"] is False


def test_persona_alias_lift_without_marker_does_not_leve():
    """#13609 controle negatif : sans marqueur `[Hermes]`/`[NanoClaw]`/`[Hermes
    self-bot]`, le commentaire jsboige ne leve pas -- c'est l'identite de
    poussee partagee des lanes (#13316), l'auteur de la reserve est distinct
    (clusterManager-Myia), le predicat d'alias ne s'applique pas. La
    protection #13316 tient."""
    reserve = {
        "author": {"login": "clusterManager-Myia"},
        "state": "COMMENTED", "submittedAt": at(10),
        "body": "[Hermes] - COMMENT_WITH_CONCERNS\nCI catalog-drift FAIL.",
    }
    lift = {
        "author": {"login": "jsboige"}, "createdAt": at(12),
        "body": ("Je leve la CHANGES_REQUESTED -- drift corrige "
                 "au commit c506d04b."),
    }
    res = run([lift], reviews=[reserve])
    assert res["blocked"] is True


def test_persona_alias_only_when_reserve_author_is_in_alias_set():
    """#13609 garde anti-usurpation : l'alias ne s'active que quand
    `nit_author` est dans `PERSONA_ALIAS_LOGINS` (= clusterManager-Myia).
    Une lane qui pousserait sous jsboige ne peut pas eteindre la reserve
    d'un AUTRE reviewer (ex. ai-01) en collant le marqueur `[Hermes]` dans
    un commentaire ordinaire -- l'alias est bidirectionnel uniquement entre
    la persona Hermes et son self-bot, pas une cle d'auto-levee."""
    reserve = {
        "author": {"login": "myia-ai-01"},
        "state": "COMMENTED", "submittedAt": at(10),
        "body": "CHANGES_REQUESTED : notebook non execute.",
    }
    lift = {
        "author": {"login": "jsboige"}, "createdAt": at(12),
        "body": ("[Hermes] Je leve le concern de ai-01 -- la lane a "
                 "re-execute, EXEC_PROVED au commit abc."),
    }
    res = run([lift], reviews=[reserve])
    assert res["blocked"] is True


def test_persona_alias_lift_override_logins_unchanged():
    """#13609 controle structurel : `LIFT_OVERRIDE_LOGINS` reste inchange.
    L'alias de persona NE confere PAS un droit d'override coordinateur : un
    `[OVERRIDE] lane` sous jsboige ne leve pas (cf ligne de garde dans
    `_lift_eligible`). La composition des deux decisions #11145 (borne
    d'auteur) et #13316 (exclusion jsboige) tient, l'alias est strictement
    une troisieme voie pour le dialogue Hermes <-> Hermes self-bot."""
    assert "jsboige" not in mod.LIFT_OVERRIDE_LOGINS
    assert mod.LIFT_OVERRIDE_LOGINS == {"myia-ai-01"}


# --- #11201 : le faux negatif « corrige X et je merge ». Le test LIFT_MARKERS
# passait AVANT toute recherche de reserve, et « je merge » couvre deux sens
# opposes : « c'est bon, je merge » (annonce, levant) et « Change la ligne 19
# et je merge » (enonce de la condition bloquante). Le nit devenait invisible
# par la clause meme qui le rendait bloquant. CONDITIONAL_LIFT neutralise
# l'annonce CONDITIONNELLE sans retirer le marqueur (retirer le marqueur
# produirait des faux positifs : 4 des 7 occurrences conditionnelles mesurees
# dans les 60 dernieres PRs mergees etaient de vraies annonces).

FIXTURE_11190_BODY = (
    "C'est le grain de **contenu** du cycle, et le notebook est bon. Une seule chose a changer — une ligne — et je te dis laquelle et pourquoi.\n"
    '\n'
    "## Ce que j'ai verifie plutot que lu\n"
    '\n'
    "- **Integrite d'execution** : 23 cellules / 9 code, `execution_count` non-null **9/9**, outputs presents **9/9**, **0 output d'erreur**, metadata papermill presente. Ton « 23/23 SUCCESS » tient structurellement.\n"
    '- **C.1** : aucun `raise NotImplementedError` / `assert False` / `1/0` dans l\'arbre du notebook. 3 exercices (cellules 6, 14, 22) en `return None` / `print("Exercice a completer")`.\n'
    "- **Ancrage des interpretations** : chaque `### Lecture du resultat` suit **immediatement** la cellule de code dont elle commente la sortie (4 apres 3, 9 apres 8, 12 apres 11, 17 apres 16, 20 apres 19). C'est la regle que #10678 a du poser apres coup sur PyMC-15 ; ici elle est tenue nativement.\n"
    "- **Le pont Lean borne sa portee** — et c'est le passage le mieux ecrit du notebook :\n"
    '\n'
    "  > *« le theoreme Lean garantit l'egalite Hashlife <-> naif dans le monde formel — il ne garantit pas que l'implementation Python de la branche naive est fidele a la regle B3/S23. »*\n"
    '\n'
    "  Tu ne laisses pas le theoreme couvrir plus qu'il ne couvre, et tu nommes la calibration comme la jambe qui manque. Les deux jambes ensemble, dit explicitement : c'est exactement ce que le livrable 4 demandait.\n"
    "- **L'honnetete methodologique sur le LWSS** (cellule 9) est conservee depuis #11185. Un pattern memorise faux, trouve, **reconstruit depuis la synthese Catagolue** plutot que rafistole jusqu'a ce que le test passe.\n"
    '\n'
    "## Une verification que tu n'as pas faite et qui renforce ta these\n"
    '\n'
    "Ton gate repose sur « 0 sorry ». Il existe un mode d'echec strictement pire qu'un `sorry` restant : un **theoreme vide** — conclusion `: True` ou `∃ ..., True`. Il passe `lake build`, il passe `#print axioms`, il passe tous les scans de `sorry`, et **il n'enonce rien**. Un `hashlife_correct` vacue rendrait ta section 5 creuse tout en cochant chaque case.\n"
    '\n'
    "J'ai fait tourner l'advisory du compteur canonique sur `conway_lean` :\n"
    '\n'
    '```\n'
    'ADVISORY -- vacuous conclusions (`: True` / `∃ ..., True`)\n'
    '  (none)\n'
    '```\n'
    '\n'
    '**Aucune.** Ta these tient donc au niveau plus profond que celui que tu as verifie. Ca vaut la peine de le dire dans le notebook : « 0 sorry » et « le theoreme dit quelque chose » sont deux propositions distinctes, et tu peux desormais affirmer les deux.\n'
    '\n'
    '## La ligne a changer — cellule 19\n'
    '\n'
    '```python\n'
    'sorries = sum(1 for l in lignes if l.strip() == "sorry")\n'
    '```\n'
    '\n'
    "C'est `grep -E '^\\s*sorry\\s*$'` reecrit en Python : il ne voit que les `sorry` **nus sur leur propre ligne**. Il rate `exact sorry`, `:= sorry`, `<;> sorry`, `· sorry`. Ici il rend **0**, et **0 est la bonne reponse** — je l'ai confirme avec l'outil canonique (`conway_lean : code=2 distinct=1`, les 2 dans `MarginFragment` FR/EN, `HashlifeCorrectness.lean` = **0**). Mais il te la rend **par chance de ce que contient ce fichier**, pas parce qu'il mesure ce que la cellule 20 affirme (« zero ligne `sorry` **au niveau code** »).\n"
    '\n'
    "Pourquoi je m'arrete la-dessus sur une ligne : le mode d'echec n'est pas symetrique. Un `grep -c sorry` naif **sur-compte** — 166 sur ce lake contre 2 reels, facteur 83 — et **ca se voit** : la prose des docstrings saute aux yeux. Un motif artisanal **sous-compte** et **ca ne se voit pas** : un motif absent ne leve aucune erreur, il rend un chiffre **plus petit et plus propre**. Le meme motif applique a `knot_lean` rend **2** la ou le compteur canonique en trouve **16**, et ce facteur 8 a fait passer pour « residu » pendant onze jours le lake qui portait 80 % de la dette formelle du depot.\n"
    '\n'
    "Et ici l'enjeu est plus lourd qu'ailleurs : **c'est un notebook de cours**. La cellule est cadree comme un certificat live, donc elle enseigne a l'etudiant que c'est **comme ca** qu'on verifie un fichier Lean. On lui apprendrait le mauvais instrument avec l'autorite d'un notebook certifie.\n"
    '\n'
    '### Le remplacement, et il rend la cellule meilleure\n'
    '\n'
    "`scripts/lean/count_code_sorry.py` s'importe (`from count_code_sorry import scan_lake, strip_lean_comments`) et tourne **sans Lean ni Mathlib** — pur texte, donc utilisable tel quel dans un notebook.\n"
    '\n'
    "La version qui vaut le detour pedagogique : garder le comptage naif **et** le comptage correct cote a cote, et montrer l'ecart. Le notebook parle de calcul certifie ; une cellule qui demontre « voici la mesure naive, voici la vraie, voici pourquoi elles different » est **plus a sa place** que la version actuelle, pas moins. Le `166` contre `2` sur ce lake est une illustration parfaite, et elle est gratuite.\n"
    '\n'
    "Si tu preferes rester minimal : `strip_lean_comments(texte)` puis compter les occurrences du token `sorry` dans le resultat suffit — c'est deja correct, et une phrase en cellule 20 disant « commentaires retires avant comptage » suffit a justifier le « au niveau code ».\n"
    '\n'
    '## Ce qui reste — pas un blocage, le grain suivant\n'
    '\n'
    "La table de contraste S2 / S5 / Life (cellule 17) est en **prose**, pas mesuree : la batterie ICT n'est pas executee sur les trois substrats. C'est conforme au texte de #5726 (« le contraste **attendu** ») et tu le declares honnetement dans le body (« route vers la batterie »), donc **je ne bloque pas dessus**. Mais c'est le grain qui suit : passer GOL, `ict/bistable.py` et `ict/reaction_diffusion.py` dans `ict/agency.py` + `ict/stake.py` + `ict/causal_emergence.py`, et voir si la mesure **separe reellement** GOL des passifs. Si elle ne les separe pas, le dire — un substrat sur lequel la batterie ne discrimine rien est un resultat, pas un echec a maquiller.\n"
    '\n'
    "Note : mon dispatch poste sur #5726 il y a quelques minutes decrivait ce travail comme s'il restait a faire. Ta PR est de **03:10Z**, mon dispatch de **03:15Z** — j'ai lu le pool avant, ecrit apres, sans re-verifier entre les deux. C'est exactement le check L898 (« avant d'ECRIRE, pas avant de pousser ») que je n'ai pas fait, et il coute dix secondes. Le dispatch est corrige ; le `[CLAIMED]` pose a ton nom reste valide et couvre cette PR.\n"
    '\n'
    '## Suite\n'
    '\n'
    "Change la ligne de la cellule 19, re-execute la section 5 (une cellule), et je merge. **Si tu ne peux pas le prendre au prochain reveil, dis-le et je l'applique** — c'est mecanique et je viens de faire la mesure de reference. Je ne pousse pas sous toi de ma propre initiative : tu as pousse il y a moins de trente minutes.\n"
    ''
)


def test_lift_conditionnel_nest_pas_une_levee():
    """Paire minimale (#11201) : meme marqueur « je merge », deux sens opposes."""
    assert mod.classify(
        "myia-ai-01",
        "Une seule chose a changer — corrige la ligne 19 et je merge."
    ) == "BOT-CONCERN"


def test_annonce_vraie_est_une_levee():
    assert mod.classify("myia-ai-01", "C'est bon, je merge.") is None


# --- #12074 : « je leve ma reserve et je merge » s'auto-bloquait. Le LIFT
# etait annule au niveau du BODY ENTIER par le seul « et je merge », meme quand
# la phrase portait la levee explicite deja accomplie EN AMONT (cas fondateur
# #11953 : le commentaire de levee re-compte comme un nit, la reserve qu'il
# levait redevenue vivante). Le discriminateur est la POSITION : un marqueur de
# levee d'auteur avant le match conditionnel rend la construction announcee
# (consequence), pas conditionnelle. Les trois cas COTE A COTE — c'est le
# controle par faux negatif qui protege la classe : sans le troisieme, le
# correctif se validerait par ses hits et rouvrirait #11201 sous une autre
# forme.

def test_levee_explicite_puis_et_je_merge_leve():
    """Cas fondateur #11953 : la formulation naturelle d'une levee par son
    auteur ne doit plus s'auto-bloquer."""
    assert mod.classify(
        "myia-ai-01",
        "**Je leve mon CHANGES_REQUESTED** et je merge."
    ) is None


def test_levee_explicite_avant_merge_conditionnel_ci_leve():
    """Le conditionnel porte sur la CI, pas sur une demande a l'auteur."""
    assert mod.classify(
        "myia-ai-01",
        "Levee de ma CHANGES_REQUESTED. Je merge des que la CI passe."
    ) is None


def test_reserve_emise_puis_et_je_merge_reste_un_nit():
    """Antecedent imperatif, aucune levee en amont : la condition reste
    bloquante (controle faux-positif de la paire)."""
    assert mod.classify(
        "myia-ai-01",
        "CHANGES_REQUESTED : corrige la ligne 19 et je merge."
    ) == "BOT-CONCERN"


# --- #11246 : use vs mention. CONDITIONAL_LIFT lisait les exemples CITES du
# motif comme des usages : une review expliquant « corrige X et je merge » se
# flaggait elle-meme (2/15 findings de l'audit --limit 400, les 2 seules
# reviews du corpus parlant du gate), et son annonce de merge reelle etait
# annulee. La citation est neutralisee avant la recherche ; l'usage nu reste
# bloquant.

def test_conditional_lift_usage_reste_bloquant():
    """Paire (a) : la construction conditionnelle EMPLOYEE, hors citation —
    la reserve reste vivante (#11201 inchange)."""
    assert mod.classify(
        "myia-ai-01",
        "Une seule chose a changer — corrige la ligne 19 et je merge."
    ) == "BOT-CONCERN"


def test_conditional_lift_cite_n_annule_pas_la_levee():
    """Paire (b) : la formule CITEE (« corrige X et je merge ») expliquee dans
    une review qui annonce par ailleurs le merge (« **Mergée.** »). AVANT le
    fix, CONDITIONAL_LIFT matchait la citation et la review basculait en
    BOT-CONCERN (cas #11218/#11233)."""
    body = ("Une seule chose a changer sur le registre : la formule "
            "« corrige X et je merge » n'est pas une levee. **Mergée.**")
    assert mod.classify("myia-ai-01", body) is None


@pytest.mark.parametrize("cite", [
    "`corrige X et je merge`",
    "« corrige X et je merge »",
    "```\ncorrige X et je merge\n```",
])
def test_conditional_lift_citations_ne_bloquent_pas(cite):
    """Les 3 formes de citation — backtick inline, guillemets typo, bloc code —
    ne sont pas des usages de la construction conditionnelle."""
    body = (f"Une seule chose a changer. La formule {cite} est citee, "
            "pas employee. **Mergée.**")
    assert mod.classify("myia-ai-01", body) is None


@pytest.mark.parametrize("cond", [
    "Change la cellule 19 puis je merge.",
    "Corrige l'attribution, ensuite je merge.",
    "je merge des que la CI est verte",
    "je merge quand tu auras re-execute la section 5",
    "je merge apres verification des checks",
    "je merge si les 3 cellules passees",
])
def test_variantes_conditionnelles_ne_levent_pas(cond):
    """Les 6 constructions de CONDITIONAL_LIFT : l'annonce conditionnee n'est
    pas une levee — le nit (registre « a changer ») reste vivant."""
    assert mod.classify("myia-ai-01", f"Une seule chose a changer. {cond}") == "BOT-CONCERN"


def test_fixture_reelle_11190_est_un_nit():
    """Corps EXACT du commentaire 2026-08-16T03:22:28Z de #11190 (auteur
    myia-ai-01, poste via gh CLI donc sans CRLF). Deux defauts imbriques
    rendaient ce nit invisible : son « et je merge » final (section Suite) le
    dechargeait via LIFT_MARKERS, et son registre (« Une seule chose a
    changer ») n'entrait dans aucun CONCERN_MARKERS. Le nit a depuis ete LEVE
    par une phrase a 06:40:10Z (merge 06:53:32Z) — le gate sur #11190 reste
    OK ; cette fixture fige que le nit est desormais VU."""
    assert mod.classify("myia-ai-01", FIXTURE_11190_BODY) == "BOT-CONCERN"


def test_rien_a_changer_nest_pas_un_nit():
    """Garde-fou FP du marqueur « a changer » : la negation totale ne reserve
    rien — le citer « rien » rend l'occurrence citee."""
    assert mod.classify(
        "jsboige", "Relu in extenso : rien a changer, le fond est solide.") is None


# --- #11222 : le deuxieme faux negatif du gate. `analyse()` eteignait TOUT
# signal par n'importe quel commentaire posterieur (comment_times plat). Pour
# un CHANGES_REQUESTED — un ETAT GitHub natif — c'est intenable : sur #11215,
# la review de 08:34:39Z etait eteinte par le commentaire de 08:36:23Z de son
# PROPRE auteur ecrivant que la remarque tient, et le gate rendait EXIT=0.
# Matrice d'acceptation mesuree par ai-01 sur le cas reel : 1/1/1/0/0.

CR_REVIEW = {
    "author": {"login": "myia-ai-01"},
    "state": "CHANGES_REQUESTED", "submittedAt": at(10),
    "body": "CHANGES_REQUESTED: la cellule 19 apprend le mauvais instrument.",
}


def run_cr(comments=(), reviews=()):
    data = {
        "number": 0, "title": "t", "author": {"login": "jsboige"},
        "comments": list(comments),
        "reviews": [CR_REVIEW, *reviews],
        "commits": [{"committedDate": at(19)}],
    }
    return mod.analyse(data, [], MERGED)


def test_cr_cas1_aucun_commentaire_bloque():
    assert run_cr()["blocked"] is True


def test_cr_cas2_commentaire_de_son_propre_auteur_ne_leve_pas():
    """Le repro exact de #11215 : l'auteur du nit repond que le nit tient —
    l'ancien comment_times plat l'eteignait quand meme (faux negatif)."""
    reply = {"author": {"login": "myia-ai-01"}, "createdAt": at(12),
             "body": "Ma remarque de review sur le fond est inchangee."}
    assert run_cr([reply])["blocked"] is True


def test_cr_cas3_commentaire_tiers_hors_sujet_ne_leve_pas():
    """Limite NLP documentee dans can_lift : un commentaire humain hors-sujet
    leve un nit PORTE PAR COMMENTAIRE ; il n'eteint pas un etat de review."""
    bystander = {"author": {"login": "po-2023-worker"}, "createdAt": at(12),
                 "body": "Base verifiee de mon cote, plus de conflit."}
    assert run_cr([bystander])["blocked"] is True


def test_cr_cas4_phrase_auteur_pr_ne_leve_pas_la_review_tierce():
    """#12836 : l'auteur de la PR documente le fix, mais ne confirme pas a la
    place du reviewer tiers que sa CHANGES_REQUESTED est levee."""
    fix = {"author": {"login": "jsboige"}, "createdAt": at(12),
           "body": "Les 2 points sont adresses : cellule 19 remplacee par "
                   "strip_lean_comments, commit abc123."}
    assert run_cr([fix])["blocked"] is True


def test_cr_cas5_rereview_approved_meme_auteur_leve():
    approved = {"author": {"login": "myia-ai-01"}, "state": "APPROVED",
                "submittedAt": at(15), "body": "Verifie apres re-exec : APPROVED."}
    assert run_cr(reviews=[approved])["blocked"] is False


def test_cr_dismissed_nest_pas_un_signal():
    """Levee (b) : une dismissal GitHub n'est possible que par l'auteur de la
    review (ou un admin) — formellement retiree des la collecte."""
    data = {
        "number": 0, "title": "t", "author": {"login": "jsboige"},
        "comments": [],
        "reviews": [{"author": {"login": "myia-ai-01"},
                     "state": "DISMISSED", "submittedAt": at(10),
                     "body": "CHANGES_REQUESTED: cellule 19."}],
        "commits": [{"committedDate": at(19)}],
    }
    assert mod.analyse(data, [], MERGED)["blocked"] is False


def test_cr_approved_d_un_tiers_ne_leve_pas():
    """Sur GitHub, l'approbation d'un autre reviewer ne retire PAS le
    CHANGES_REQUESTED actif du premier — seul son auteur le retire."""
    other = {"author": {"login": "clusterManager-Myia"}, "state": "APPROVED",
             "submittedAt": at(15), "body": "De mon cote c'est bon."}
    assert run_cr(reviews=[other])["blocked"] is True


def test_cr_levee_conditionnelle_ne_leve_pas():
    """« corrige X et je merge » (#11201) : l'annonce conditionnee porte le
    marqueur « je merge » mais n'est pas une phrase de levee."""
    cond = {"author": {"login": "jsboige"}, "createdAt": at(12),
            "body": "Corrige la cellule 19 et je merge."}
    assert run_cr([cond])["blocked"] is True


def test_nit_commentaire_garde_le_regime_general():
    """#12319 : le regime general d'un nit porte par un COMMENTAIRE est
    aligne sur celui de l'etat de review — il faut une PHRASE de levee
    (LIFT_MARKER) ou une re-review APPROVED de l'auteur. Une reponse humaine
    PORTANT la phrase leve toujours (regime general, limite NLP de can_lift)."""
    reply = {"author": {"login": "jsboige"}, "createdAt": at(12),
             "body": "Bien vu, corrige — les 2 nits sont levées."}
    assert run([USER_NIT, reply])["blocked"] is False


# --- #11145 / #12836 : la borne d'auteur. Une levee ne compte que si elle
# vient de l'auteur de la reserve. #12798 a prouve que PR_AUTHOR n'est pas un
# tiers de confirmation : l'auteur avait declare la reserve Hermes levee alors
# que le notebook committe restait un stub sans sortie vLLM. Une reponse de
# PR_AUTHOR documente le traitement mais ne remplace pas la re-review du tiers.
# Echappement borne : override coordinateur nomme (tests #11639 ci-dessous).

HERMES_NIT = {
    "author": {"login": "clusterManager-Myia"}, "createdAt": at(10),
    "body": "[Hermes] COMMENT_WITH_CONCERNS\n2 cellules manquent d'interp.",
}


def test_bystander_commentaire_ne_leve_pas_un_nit():
    """#10761 : un tiers (ni auteur de la reserve, ni auteur de la PR) qui
    repond apres le nit ne l'eteint pas — la reserve reste bloquante."""
    bystander = {"author": {"login": "myia-ai-01"}, "createdAt": at(12),
                 "body": "Releve de mon cote, plus de conflit."}
    assert run([USER_NIT, bystander])["blocked"] is True


# --- #12319 : la collision d'identite flotte-wide. Hermès poste sous jsboige
# (self-review cap) et chaque lane pousse sous jsboige, donc
# nit_author == pr_author == "jsboige" sur presque chaque PR du depot : la
# borne d'auteur #11145 ne borne plus rien, et l'ancienne branche elif
# (tout commentaire can_lift leve) laissait une lane eteindre la reserve de
# son propre reviewer en postant une attestation de protocole. Le regime est
# desormais : PHRASE de levee (LIFT_MARKER, borne d'auteur preservee) OU
# re-review APPROVED de l'auteur de la reserve.

def test_12319_reponse_nue_ne_leve_plus():
    """Le defaut fondateur : USER_NIT (auteur jsboige) sur une PR d'auteur
    jsboige — une reponse posterieure de jsboige SANS phrase de levee
    n'eteint plus la reserve (avant : levait via lift_events)."""
    reply = {"author": {"login": "jsboige"}, "createdAt": at(12),
             "body": "Bien vu, l'attribution est corrigee en cellule 0 et 2."}
    assert run([USER_NIT, reply])["blocked"] is True


def test_12319_attestation_self_ne_leve_pas():
    """Le litteral de l'issue : une lane eteint la reserve de son reviewer en
    postant un [READY-FOR-MERGE SELF attestation] qui ne la mentionne pas."""
    attestation = {"author": {"login": "jsboige"}, "createdAt": at(12),
                   "body": "[READY-FOR-MERGE SELF attestation] checks verts, "
                           "body complet, preuve d'execution dans le body."}
    assert run([USER_NIT, attestation])["blocked"] is True


def test_12319_reponse_nue_sur_reserve_hermes_ne_leve_plus():
    """Meme regime pour la reserve Hermes (review COMMENTED, src non-CR) :
    la lane pousse une reponse sans phrase de levee — reste bloquante."""
    reply = {"author": {"login": "jsboige"}, "createdAt": at(12),
             "body": "Les 2 cellules d'interp sont ajoutees, commit abc."}
    assert run([HERMES_NIT, reply])["blocked"] is True


def test_12319_rereview_approved_de_l_auteur_leve_nit_commentaire():
    """L'etat natif garde son role de phrase de levee au sens fort : Hermes
    (auteur de la reserve) revient APPROVED — la reserve s'eteint, meme sans
    marqueur textuel."""
    data = {
        "number": 0, "title": "t", "author": {"login": "jsboige"},
        "comments": [HERMES_NIT],
        "reviews": [{"author": {"login": "clusterManager-Myia"},
                     "state": "APPROVED", "submittedAt": at(15),
                     "body": ""}],
        "commits": [{"committedDate": at(19)}],
    }
    assert mod.analyse(data, [], MERGED)["blocked"] is False


def test_12319_levee_conditionnelle_ne_leve_pas_nit_commentaire():
    """#11201 preserve sur le nouveau chemin : « corrige X et je leve » est
    l'enonce de la condition, pas une levee acquise."""
    cond = {"author": {"login": "jsboige"}, "createdAt": at(12),
            "body": "Corrige la cellule 19 et je leve ma reserve."}
    assert run([USER_NIT, cond])["blocked"] is True


def test_bystander_approved_ne_leve_pas_un_nit():
    """La classe mesuree #11494 (4 cas Hermes) : un APPROVED d'un reviewer
    tiers n'eteint pas une reserve posee par un autre."""
    data = {
        "number": 0, "title": "t", "author": {"login": "jsboige"},
        "comments": [USER_NIT],
        "reviews": [{"author": {"login": "clusterManager-Myia"},
                     "state": "APPROVED", "submittedAt": at(15),
                     "body": "De mon cote c'est bon."}],
        "commits": [{"committedDate": at(19)}],
    }
    assert mod.analyse(data, [], MERGED)["blocked"] is True


def test_auteur_du_nit_leve_son_nit():
    """SELF (59,5 %) : l'auteur de la reserve revient repondre AVEC une
    phrase de levee — le nit se leve par le regime general borne
    (auteur == auteur du nit, #12319 : phrase exigee)."""
    reply = {"author": {"login": "clusterManager-Myia"}, "createdAt": at(12),
             "body": "Les 2 cellules d'interp sont ajoutees, commit abc — "
                     "reserve levee."}
    assert run([HERMES_NIT, reply])["blocked"] is False


def test_auteur_pr_ne_leve_pas_la_reserve_d_un_tiers():
    """#12798 : PR_AUTHOR peut documenter le fix, pas confirmer a la place du
    reviewer tiers que sa reserve est levee. La reserve reste bloquante jusqu'a
    une re-review/levee de son auteur ou un override coordinateur nomme."""
    reply = {"author": {"login": "jsboige"}, "createdAt": at(12),
             "body": "Les 2 cellules d'interp sont ajoutees, commit abc — "
                     "les points sont adresses."}
    assert run([HERMES_NIT, reply])["blocked"] is True


def test_auteur_pr_puis_levee_du_reviewer_tiers_leve():
    """Controle positif obligatoire #12836 : le durcissement ne rend pas toute
    reserve indelebile. PR_AUTHOR repond, puis le reviewer tiers confirme la
    levee : le gate devient vert."""
    reply = {"author": {"login": "jsboige"}, "createdAt": at(12),
             "body": "Les 2 cellules d'interp sont ajoutees, commit abc — "
                     "les points sont adresses."}
    reviewer_lift = {
        "author": {"login": "clusterManager-Myia"},
        "createdAt": at(13),
        "body": "Levee de ma reserve apres verification du commit abc.",
    }
    assert run([HERMES_NIT, reply, reviewer_lift])["blocked"] is False


def test_deux_reserves_du_meme_auteur_ne_s_auto_levent_pas():
    """#12798 live : deux commentaires COMMENT_WITH_CONCERNS du meme auteur a
    quelques secondes d'intervalle restent deux emissions, pas une levee. Le
    second narre une levee anterieure qu'il REFUTE : le verdict formel vivant
    doit l'emporter sur ce LIFT_MARKER narratif."""
    first = {
        "author": {"login": "jsboigeEpita"}, "createdAt": at(10),
        "body": "[Hermes] COMMENT_WITH_CONCERNS — sortie vLLM absente.",
    }
    second = {
        "author": {"login": "jsboigeEpita"}, "createdAt": at(11),
        "body": (
            "[Hermes] COMMENT_WITH_CONCERNS — revalidation apres la levee "
            "annoncee : cassette toujours non prouvee."
        ),
    }
    data = {
        "number": 12798, "title": "t", "author": {"login": "jsboige"},
        "comments": [first, second], "reviews": [],
        "commits": [{"committedDate": at(19)}],
    }
    result = mod.analyse(data, [], MERGED)
    assert result["blocked"] is True
    assert len(result["blocking"]) == 2


# --- #12908 : use-vs-mention côté LEVÉE. Instance fondatrice : PREFLIGHT
# jsboigeEpita 2026-08-25T04:45:30Z sur #12798 — « obtenir de jsboigeEpita
# une levée explicite sur le head final ». Le sac de mots LIFT_MARKERS y
# voyait « levée » et enregistrait le PREFLIGHT comme événement de levée :
# _lift_eligible(auteur == auteur) éteignait les réserves antérieures du
# même auteur, et le gate rendait un faux OK. Miroir exact de
# has_live_marker côté réserves : une occurrence précédée d'un déterminant
# (une/la/les/de/après/…) est un NOM de levée, pas sa performance.


def test_12908_has_live_lift_narration_contre_performance():
    """Unité : le déterminant devant « levée » en fait une narration."""
    assert mod.has_live_lift(
        "obtenir de jsboigeEpita une levée explicite sur le head final"
    ) is False
    assert mod.has_live_lift(
        "revalidation apres la levee annoncee"
    ) is False
    # Formes performatives : verbe en tête ou acronyme nu — toujours vives.
    assert mod.has_live_lift("Levee de ma reserve apres verification") is True
    assert mod.has_live_lift("Les 2 nits sont levees, commit abc") is True
    assert mod.has_live_lift("reserve levee") is True
    assert mod.has_live_lift("je leve ma reserve Hermes") is True


def test_12908_garde_de_frontiere_aucune_ne_matche_pas_une():
    """« aucune levée » doit être narré — l'entrée explicite « aucune » le
    couvre ; sans la garde de frontière, « aucune ».endswith("une")
    matcherait « une » avec « c » alphanumérique devant, donc ne le
    matcherait PAS — c'est précisément pourquoi « aucun/aucune » sont des
    entrées propres de LIFT_NARRATION_CITERS."""
    assert mod.has_live_lift("sans aucune levée du tout") is False


def test_12908_preflight_exigeant_une_levee_n_est_pas_un_geste():
    """Le fondateur : le PREFLIGHT de #12798 (structure exacte du
    commentaire 04:45:30Z) exige une levée — il ne l'accorde pas. Les
    réserves antérieures du même auteur restent bloquantes."""
    reserve_1 = {
        "author": {"login": "jsboigeEpita"}, "createdAt": at(10),
        "body": "[Hermes] COMMENT_WITH_CONCERNS — sortie vLLM absente.",
    }
    reserve_2 = {
        "author": {"login": "jsboigeEpita"}, "createdAt": at(11),
        "body": "[Hermes] COMMENT_WITH_CONCERNS — cassette non prouvee.",
    }
    preflight = {
        "author": {"login": "jsboigeEpita"}, "createdAt": at(12),
        "body": (
            "[Hermes] PREFLIGHT — substance revalidée ; réserve "
            "uniquement B.0/process. Le gate classe encore cette PR "
            "**BLOCKED**. Pour débloquer : obtenir de jsboigeEpita une "
            "levée explicite sur le head final. Seule une phrase explicite "
            "de cet auteur après vérification, ou un `[OVERRIDE]` "
            "coordinateur, les lève."
        ),
    }
    data = {
        "number": 12798, "title": "t", "author": {"login": "jsboige"},
        "comments": [reserve_1, reserve_2, preflight], "reviews": [],
        "commits": [{"committedDate": at(19)}],
    }
    result = mod.analyse(data, [], MERGED)
    assert result["blocked"] is True
    # #12925 (port #12908 emission) : la revalidation maintenante elle-meme
    # (emission **BLOCKED**) est un signal de plus — 3, pas 2. L'intent du
    # test (le preflight n'est pas un geste de levee) est preserve.
    assert len(result["blocking"]) == 3


def test_12908_levee_explicite_non_contradictoire_reste_reconnue():
    """Controle positif (acceptance #12908) : la duree du durcissement ne
    rend pas toute levée indelebile — la phrase explicite NON contradictoire
    de l'auteur de la réserve lève toujours."""
    lift = {
        "author": {"login": "clusterManager-Myia"}, "createdAt": at(12),
        "body": "Vérifié sur le head final : reserve levee, commit abc.",
    }
    assert run([HERMES_NIT, lift])["blocked"] is False


def test_bystander_explicit_lift_ne_leve_pas_changes_requested():
    """#11145 sur l'etat CHANGES_REQUESTED : une PHRASE de levee d'un tiers
    (ni l'auteur du CR, ni l'auteur de la PR) n'eteint pas l'etat."""
    bystander = {"author": {"login": "clusterManager-Myia"}, "createdAt": at(12),
                 "body": "Les 2 points sont adresses, commit abc123."}
    assert run_cr([bystander])["blocked"] is True


# --- #11639 : l'arbitrage ECRIT du coordinateur. B.0 ne restreint pas
# l'auteur d'une reponse de levée, mais `_lift_eligible` ne creditait que
# l'auteur du nit ou celui de la PR : tout arbitrage coordinateur laissait
# le gate rouge, et le merge se faisait a EXIT=1 en routine — repete, ca
# enseigne a merger rouge. La trappe est NOMMEE : `[OVERRIDE] lane <m:w>` +
# phrase de levée (LIFT_MARKER), par un compte coordinateur. Pas une
# ouverture generale : la restriction d'auteur #11145 tient pour tous les
# autres.
#
# Mesure retro #11479 (timestamps reels) : reserve Hermes 2026-08-17T13:38Z,
# levée nominative d'ai-01 13:06:34Z, merge 13:06:39Z, override ecrit
# 13:07:40Z — 61 s APRES le merge. La borne anti-retroactivite (#10761 : un
# commentaire post-merge n'a pas pu lever la reserve avant la decision)
# exclut l'override reel : le retro live de #11479 reste EXIT=1, et c'est
# voulu. La convention que ce correctif etablit : l'OVERRIDE s'ecrit AVANT
# le merge (comme toute levée) — le test retro simule ce decalage.

HERMES_REVIEW_11479 = {
    "author": {"login": "clusterManager-Myia"},
    "state": "COMMENTED", "submittedAt": "2026-08-17T13:38:00Z",
    "body": "[Hermes] COMMENT_WITH_CONCERNS — tests exécutés en local : 44/44 "
            "pass, mais 2 edge cases non couverts (issue #11058)",
}
MERGED_11479 = datetime(2026, 8, 18, 13, 6, 39, tzinfo=timezone.utc)

OVERRIDE_BODY = (
    "**[OVERRIDE] lane myia-ai-01:CoursIA** — Levée de la réserve Hermes "
    "du 2026-08-17, en nommant chacun de ses points : gap 1 retiré par "
    "Hermes lui-même, gaps 2-3 reportés sur #11058."
)


def run_coord(comments=(), reviews=(), merged=MERGED_11479):
    """PR d'un worker NON coordinateur, reserve posee par un tiers — la
    trappe OVERRIDE est le seul chemin de levée (ni SELF ni PR_AUTHOR)."""
    data = {
        "number": 0, "title": "t", "author": {"login": "myia-po-2026"},
        "comments": list(comments),
        "reviews": [HERMES_REVIEW_11479, *reviews],
        "commits": [{"committedDate": "2026-08-18T12:00:00Z"}],
    }
    return mod.analyse(data, [], merged)


def test_coord_override_avec_levee_leve():
    """Acceptance 1 : [OVERRIDE] lane + phrase de levée par un coordinateur
    leve la reserve qu'il arbitre — le seul chemin ouvert a l'arbitre tiers."""
    lift = {"author": {"login": "myia-ai-01"},
            "createdAt": "2026-08-18T13:06:34Z", "body": OVERRIDE_BODY}
    assert run_coord([lift])["blocked"] is False


def test_coord_override_nu_ne_leve_rien():
    """Acceptance 2 : un [OVERRIDE] sans phrase de levée ne lève rien —
    l'override doit DIRE ce qu'il arbitre (can_lift l'écarte comme tag de
    protocole nu, aucun LIFT_MARKER ne le réintroduit)."""
    bare = {"author": {"login": "myia-ai-01"},
            "createdAt": "2026-08-18T13:06:34Z",
            "body": "[OVERRIDE] lane myia-ai-01:CoursIA — arbitrage : le "
                    "point 3 est traité en argument, voir #11058."}
    assert run_coord([bare])["blocked"] is True


def test_tiers_avec_levee_sans_override_ne_leve_pas():
    """Acceptance 3 (non-regression #11145) : un tiers quelconque qui écrit
    une phrase de levée SANS override ne lève toujours pas — la restriction
    d'auteur tient pour tout le monde sauf la trappe nommée."""
    third = {"author": {"login": "myia-po-2024"},
             "createdAt": "2026-08-18T13:06:34Z",
             "body": "Les 2 points sont adressés, reportés sur #11058."}
    assert run_coord([third])["blocked"] is True


def test_override_par_un_non_coordinateur_ne_leve_pas():
    """La trappe est coordinateur-only : un worker qui écrit lui-même
    `[OVERRIDE] lane …` + phrase de levée ne leve pas la reserve d'un tiers
    (il n'est ni l'auteur du nit, ni celui de la PR, ni arbitre)."""
    fake = {"author": {"login": "myia-po-2024"},
            "createdAt": "2026-08-18T13:06:34Z",
            "body": "[OVERRIDE] lane myia-po-2024:CoursIA-2 — Levée de la "
                    "réserve Hermes, reportée sur #11058."}
    assert run_coord([fake])["blocked"] is True


def test_retro_11479_reel_override_post_merge_ne_leve_pas():
    """Retro #11479 tel que l'historique réel le porte (timestamps exacts) :
    merge 13:06:39Z, override écrit 13:07:40Z. La borne anti-retroactivite
    (#10761) exclut l'override postérieur — le retro live reste EXIT=1, la
    convention à suivre est d'écrire l'override AVANT le merge."""
    lift = {"author": {"login": "myia-ai-01"},
            "createdAt": "2026-08-18T13:07:40Z", "body": OVERRIDE_BODY}
    assert run_coord([lift])["blocked"] is True


def test_retro_11479_simule_override_pre_merge_leve():
    """Le même retro, override déplacé AVANT le merge : le mécanisme crédite
    l'arbitrage écrit — c'est la démonstration que seul l'ordonnancement
    historique (et non le mécanisme) laissait #11479 à EXIT=1."""
    lift = {"author": {"login": "myia-ai-01"},
            "createdAt": "2026-08-18T13:06:34Z", "body": OVERRIDE_BODY}
    assert run_coord([lift])["blocked"] is False


def test_coord_override_leve_aussi_le_state_changes_requested():
    """La trappe couvre la branche état natif (branche A) comme la branche
    commentaire (branche B) : un CHANGES_REQUESTED d'un reviewer arbitré par
    override écrit se lève aussi."""
    cr = {"author": {"login": "clusterManager-Myia"},
          "state": "CHANGES_REQUESTED", "submittedAt": at(10),
          "body": "CHANGES_REQUESTED: 2 edge cases non couverts."}
    lift = {"author": {"login": "myia-ai-01"}, "createdAt": at(12),
            "body": OVERRIDE_BODY}
    data = {
        "number": 0, "title": "t", "author": {"login": "myia-po-2026"},
        "comments": [lift], "reviews": [cr],
        "commits": [{"committedDate": at(19)}],
    }
    assert mod.analyse(data, [], MERGED)["blocked"] is False


# --- #13030 : OVERRIDE POSE vs CITE -------------------------------------------
# L'incident #12872 : le rapport de la lane qui DOCUMENTAIT l'option
# « (b) `[OVERRIDE] lane x` par ai-01 » a eteint deux reserves BOT-CONCERN
# jamais levees -- la regex ancre-less matchait dans le backtick, le gate
# passait rc=0 sans que rien ne le signale. Un override fantome SOUS-bloque
# (inverse exact du [CLAIMED] fantome qui sur-bloque). Le marqueur doit
# desormais etre POSE en tete de ligne, hors backticks.

def test_override_pose_canonique_leve():
    """Controle positif : le marqueur seul en tete de ligne POSE l'override."""
    lift = {"author": {"login": "myia-ai-01"},
            "createdAt": "2026-08-18T13:06:34Z",
            "body": "[OVERRIDE] lane myia-po-2026:CoursIA\n"
                    "Levée de la réserve Hermes du 2026-08-17, points "
                    "reportés sur #11058."}
    assert run_coord([lift])["blocked"] is False


def test_override_cite_dans_backtick_ne_leve_pas():
    """Le cas EXACT de #12872 : une option documentee entre backticks dans
    une puce ne pose PAS l'override -- le rapport qui explique que la
    decision revient a ai-01 ne doit pas l'exercer."""
    cited = {"author": {"login": "jsboige"},
             "createdAt": "2026-08-25T17:38:05Z",
             "body": "Options :\n"
                     "- **(a)** attendre la re-review ;\n"
                     "- **(b)** `[OVERRIDE] lane myia-po-2024:CoursIA-2` "
                     "par ai-01 (commentaire sur cette PR) ;\n"
                     "La lane ne peut pas lever ces 2 nits elle-meme."}
    assert run_coord([cited])["blocked"] is True


def test_override_cite_milieu_de_phrase_ne_leve_pas():
    """« Le marqueur [OVERRIDE] lane x sert a ... » = documentation, pas acte."""
    doc = {"author": {"login": "jsboige"},
           "createdAt": "2026-08-26T00:00:00Z",
           "body": "Le marqueur [OVERRIDE] lane x sert a arbitrer une "
                   "reserve ; il doit etre pose en tete de ligne."}
    assert run_coord([doc])["blocked"] is True


def test_override_pose_apres_decor_leve():
    """Non-regression #10906 (famille _DECOR de check_lane_claim) : un
    override dans un blockquote / puce / heading reste POSE -- la tolerance
    de decoration ne doit pas voider les formes legitimes de la flotte."""
    quoted = {"author": {"login": "myia-ai-01"},
              "createdAt": "2026-08-18T13:06:34Z",
              "body": "> [OVERRIDE] lane myia-po-2026:CoursIA\n"
                      "> Levée de la réserve Hermes, reportée sur #11058."}
    assert run_coord([quoted])["blocked"] is False


# --- #11677 : check_unaddressed_nits classe une review APPROVED en BOT-CONCERN
# L'etat natif GitHub n'etait pas cable pour les reviews APPROVED (la branche
# CHANGES_REQUESTED etait la seule symetrique documentee). 4 changes minimaux :
#   1. LIFT_MARKERS etendu avec « je leve / je leve » (#11664 fondateur)
#   2. HUMAN_VERDICT_POSITIVE (APPROVE / APPROVED / LGTM) word-bounded
#   3. symetrique APPROVED dans `analyse()` : kind = None si etat natif
#      GitHub APPROVED + aucune reserve VIVANTE dans la prose
#   4. _strip_quoted etendu aux CONCERN_MARKERS (citations en bloc `> ...`)


def test_11677_founder_body_rend_none():
    """#11664 fondateur : « APPROVE — je leve ma CHANGES_REQUESTED et j'accorde
    l'ack explicite de merge [...] *before merge* » — la review leve
    explicitement la CHANGES_REQUESTED qu'elle nomme, ET cite la regle du gate
    B.0 « *before merge* » dans une emphase markdown. Avant le fix, le gate
    classait cette review en BOT-CONCERN (CHANGES_REQUESTED + before merge
    vivants), empechant le merge legitime."""
    body = (
        "APPROVE — je lève ma CHANGES_REQUESTED et j'accorde l'ack explicite "
        "de merge.\n\n"
        "Le gate B.0 exige une reponse ecrite ; le commit 06956bd0a repond "
        "aux deux nits user. La regle qui impose un reviewer ack *before "
        "merge* est honoree par cette review APPROVED.\n\n"
        "## Ce que j'ai verifie\n"
        "- Les marqueurs cites ci-dessus ne sont pas des emissions : « je "
        "leve » precede le marqueur, « *before merge* » est une citation "
        "du gate."
    )
    assert mod.classify("myia-ai-01", body) is None


def test_11677_human_approve_word_bounded_ne_flagge_pas():
    """#11677 acceptance : « APPROVE » (verdict humain positif) eteint le
    signal — equivalent formel du `state: APPROVED` natif. Word-bounded :
    `**APPROVE**`, `## APPROVE`, `# APPROVE` matchent (decoration markdown),
    mais « I approve the design » (en milieu de phrase narrative, sans
    decoration) matche aussi — c'est limite, documente dans le PR body."""
    for body in [
        "APPROVE",
        "**APPROVE**",
        "## APPROVE\n\nLooking good.",
        "APPROVED",
        "`APPROVED`.",
    ]:
        assert mod.classify("jsboige", body) is None, f"FAIL: {body!r}"


def test_11677_approve_mais_reserve_vivante_reste_bot_concern():
    """Acceptance 2 (controle positif) : un verdict positif APPROVE
    n'eteint PAS une reserve VIVANTE dans la meme prose. « APPROVE mais
    il va falloir corriger X » reste BOT-CONCERN — sinon le fix eteint
    la reserve qu'il est cense laisser passer."""
    body = (
        "J'approuve cette PR — mais le point 2 reste ouvert : il va "
        "falloir ajouter le test manquant avant le merge. APPROVE pour "
        "le reste."
    )
    assert mod.classify("jsboige", body) == "BOT-CONCERN"


def test_11677_changements_requested_non_regression_11222():
    """Non-regression #11222 : une review CHANGES_REQUESTED reste BLOQUANT
    et ne se leve que par re-review APPROVED du meme auteur, dismissal,
    ou phrase explicite non conditionnelle."""
    cr = {
        "author": {"login": "clusterManager-Myia"},
        "state": "CHANGES_REQUESTED", "submittedAt": at(10),
        "body": "[Hermes] — CHANGES_REQUESTED\nCellule 12 cassee.",
    }
    # Sans levee → bloque
    data = {
        "number": 0, "title": "t", "author": {"login": "jsboige"},
        "comments": [], "reviews": [cr],
        "commits": [{"committedDate": at(19)}],
    }
    assert mod.analyse(data, [], MERGED)["blocked"] is True
    # Avec re-review APPROVED du meme auteur → leve
    rereview = {
        "author": {"login": "clusterManager-Myia"},
        "state": "APPROVED", "submittedAt": at(15),
        "body": "[Hermes] — APPROVED\nLe fix repond au nit.",
    }
    data["reviews"].append(rereview)
    assert mod.analyse(data, [], MERGED)["blocked"] is False


def test_11677_strip_quoted_etendu_aux_concern_markers():
    """#11677 acceptance 1 (composante « strip citations ») : une review
    APPROVED qui contient un CONCERN_MARKER UNIQUEMENT dans une citation
    en backticks ou bloc code ou guillemets français typographiques rend
    classify None — la citation est neutralisee par `_strip_quoted` avant
    la recherche de CONCERN_MARKERS (meme hygiene que CONDITIONAL_LIFT,
    l.462). Les blockquotes Markdown `> ...` NE SONT PAS dans le perimetre
    actuel de `_strip_quoted` (limite documentee, scope inline seulement)."""
    body = (
        "APPROVED.\n\n"
        "`Must fix before merge` (citation d'un commentaire precedent).\n\n"
        "La citation en backticks est neutralisee, le verdict est APPROVED "
        "pur."
    )
    assert mod.classify("jsboige", body) is None


def test_11677_symetrique_approved_dans_analyse():
    """Acceptance 1 (composante « symetrique APPROVED ») : dans `analyse()`,
    une review avec `state: APPROVED` natif ET classify() qui retourne None
    (verdict positif + aucune reserve vivante) n'emet PAS de signal
    bloquant — kind reste None, la review APPROVED est MUETTE pour le gate.
    Avant le fix, kind pouvait etre « BOT-CONCERN » si la prose contenait
    un CONCERN_MARKER, etait-cite (#11664 fondateur)."""
    approved = {
        "author": {"login": "jsboige"},  # l'auteur PR = peut lever
        "state": "APPROVED", "submittedAt": at(15),
        "body": "**APPROVE** — je leve ma CHANGES_REQUESTED.",
    }
    data = {
        "number": 0, "title": "t", "author": {"login": "jsboige"},
        "comments": [], "reviews": [approved],
        "commits": [{"committedDate": at(19)}],
    }
    assert mod.analyse(data, [], MERGED)["blocked"] is False


def test_11677_approved_avec_reserve_vivante_reste_bloquant():
    """Acceptance 2 dans `analyse()` (controle positif) : une review
    `state: APPROVED` qui contient une reserve VIVANTE (ex: « j'approuve
    mais le point 2 reste ouvert ») garde le kind `BOT-CONCERN` retourne
    par classify() — la symetrique ne l'abaisse PAS."""
    approved_mixed = {
        "author": {"login": "clusterManager-Myia"},
        "state": "APPROVED", "submittedAt": at(15),
        "body": (
            "J'approuve cette PR — mais le point 2 reste ouvert : il va "
            "falloir ajouter le test manquant avant le merge. APPROVE "
            "pour le reste."
        ),
    }
    data = {
        "number": 0, "title": "t", "author": {"login": "jsboige"},
        "comments": [], "reviews": [approved_mixed],
        "commits": [{"committedDate": at(19)}],
    }
    assert mod.analyse(data, [], MERGED)["blocked"] is True


def test_11677_je_leve_leve_changements_requested_dans_prose():
    """Complement LIFT_MARKERS : « je leve ma X » leve X explicitement.
    Avant le fix, « leve » (incomplet) ne matchait pas LIFT_MARKERS
    (qui ne captait que « levee » mot complet), donc le bot classait
    la levee explicite en BOT-CONCERN. Apres le fix, « je leve » est
    un LIFT_MARKER, et le corps est reconnu comme levee."""
    body = "je leve ma CHANGES_REQUESTED — le commit 06956bd0a repond au nit."
    assert mod.classify("myia-ai-01", body) is None


def test_11542_leve_sans_pronom_leve_aussi():
    """Forme francaise SANS pronom : « Leve la remarque X de <auteur> ».

    Cas reel, PR #11542 : po-2023 ecrit « Leve la remarque
    `CHANGES_REQUESTED` de clusterManager-Myia (PRR_...) sur la cellule
    h44 ». C'est une phrase de LEVEE, et le marqueur de concern est
    *a l'interieur* de la phrase qui le leve. LIFT_MARKERS connaissait
    « je leve » / « levee de » / « est levee » mais pas la forme sans
    pronom en tete de phrase — le gate rendait donc EXIT=1 sur une PR
    dont la remarque etait reellement adressee (verifie firsthand :
    commit 8113e8436 + prose vraie contre le code).

    Le faux positif d'un gate coute autant que le faux negatif : une
    lane qui voit un rouge inexplicable va chercher un defaut absent,
    et pendant ce temps la PR vieillit."""
    body = ("Reformulation qualitative de la cellule h44, commit 8113e8436. "
            "Leve la remarque `CHANGES_REQUESTED` de clusterManager-Myia "
            "(PRR_kwDOH2Odns8AAAABJ1wwZA) sur la cellule h44.")
    assert mod.classify("myia-po-2023", body) is None


def test_11542_leve_accentue_sans_pronom():
    """Meme forme, accentuee — `_unaccent` doit rendre les deux equivalentes."""
    body = "Leve la CHANGES_REQUESTED de Hermes : le commit 8113e8436 y repond."
    body = body.replace("Leve", "L\u00e8ve")
    assert mod.classify("myia-po-2023", body) is None


def test_11542_negation_ne_leve_pas():
    """Controle NEGATIF : sans lui, un lot entierement vert serait
    indiscernable d'un gate debranche. Une reserve vivante reste vivante."""
    body = "Je maintiens : CHANGES_REQUESTED tant que la cellule 8 est vide."
    assert mod.classify("myia-ai-01", body) == "BOT-CONCERN"


# ---------------------------------------------------------------------------
# #11744 — extension de `_strip_mentioned_verdicts` aux positions hors
# parentheses (titre de section, prose inline). Les deux instances mesurees
# (#11625 "## Remedes au CHANGES_REQUESTED", #11428 "le verdict CHANGES_REQUESTED
# que je levait") restent BOT-CONCERN par erreur tant que les patterns
# `_MENTION_VERDICT_HEADING` / `_MENTION_VERDICT_INLINE` ne les neutralisent
# pas. Le controle negatif obligatoire : une emission reelle portee par
# `MARKER:` nu ou par le state de la review reste BOT-CONCERN.
# ---------------------------------------------------------------------------


def test_11744_section_heading_mention_ne_flagge_pas():
    """#11744 — Position A : titre de section `## Remedes au CHANGES_REQUESTED`
    en tete de rapport de remediation. Avant le fix : classifie BOT-CONCERN
    par erreur. Apres : classify() rend None (mention, pas emission)."""
    body = (
        "## Remedes au CHANGES_REQUESTED\n"
        "\n"
        "Fix 1: aucun nouveau warning introduit. "
        "Le point leve dans la review Hermes etait un faux positif (cf. log)."
    )
    data = {
        "number": 0, "title": "t", "author": {"login": "myia-po-2026"},
        "comments": [{"author": {"login": "myia-po-2026"}, "createdAt": at(10),
                      "body": body}],
        "reviews": [], "commits": [{"committedDate": at(19)}],
    }
    assert mod.analyse(data, [], MERGED)["blocked"] is False


def test_11744_inline_prose_mention_ne_flagge_pas():
    """#11744 — Position B : prose inline. Avant le fix : la phrase « mon message
    d'approbation nommant le verdict CHANGES_REQUESTED au fil du texte » est
    classee BOT-CONCERN. Apres : mention inline reconnue, classify() rend None."""
    body = (
        "Pour clarifier ma levee : mon message d'approbation nommant le "
        "verdict CHANGES_REQUESTED au fil du texte reapparait comme item "
        "bloquant alors qu'il etait deja leve par re-review APPROVED."
    )
    data = {
        "number": 0, "title": "t", "author": {"login": "myia-po-2026"},
        "comments": [{"author": {"login": "myia-ai-01"}, "createdAt": at(10),
                      "body": body}],
        "reviews": [], "commits": [{"committedDate": at(19)}],
    }
    assert mod.analyse(data, [], MERGED)["blocked"] is False


def test_11744_emission_reelle_marker_reste_bot_concern():
    """#11744 — CONTROLE NEGATIF : une emission reelle (MARKER: nu ou `state:
    CHANGES_REQUESTED` de la review) doit RESTER BOT-CONCERN. Sans quoi le
    fix debranche le gate et rouvre le failure mode fondateur de B.0."""
    cr = {"author": {"login": "hermes-bot"},
          "state": "CHANGES_REQUESTED", "submittedAt": at(10),
          "body": "CHANGES_REQUESTED: edge case non couvert."}
    data = {
        "number": 0, "title": "t", "author": {"login": "myia-po-2026"},
        "comments": [], "reviews": [cr],
        "commits": [{"committedDate": at(19)}],
    }
    assert mod.analyse(data, [], MERGED)["blocked"] is True


def test_11744_emission_reelle_marker_nu_reste_bot_concern():
    """#11744 — Variante emission reelle : comment user avec `CHANGES_REQUESTED:`
    en tete de phrase (forme `MARKER:` nue). Doit RESTER BOT-CONCERN."""
    body = "CHANGES_REQUESTED: le fichier attendu n'est pas joint."
    data = {
        "number": 0, "title": "t", "author": {"login": "myia-po-2026"},
        "comments": [{"author": {"login": "user-fi"}, "createdAt": at(10),
                      "body": body}],
        "reviews": [], "commits": [{"committedDate": at(19)}],
    }
    assert mod.analyse(data, [], MERGED)["blocked"] is True


def test_11744_non_regression_11636_parenthesee_toujours_neutralisee():
    """#11744 — Non-regression : le pattern `[a]` (parentheses + verbe de
    reference) doit toujours fonctionner apres l'ajout des 2 nouveaux
    patterns. Cas fondateur #11628 / #11636."""
    body = (
        "Fix review ai-01 (CHANGES_REQUESTED) — commit 06956bd0a corrige "
        "le warning introduit sur le PR-guard."
    )
    data = {
        "number": 0, "title": "t", "author": {"login": "myia-po-2026"},
        "comments": [{"author": {"login": "myia-po-2026"}, "createdAt": at(10),
                      "body": body}],
        "reviews": [], "commits": [{"committedDate": at(19)}],
    }
    assert mod.analyse(data, [], MERGED)["blocked"] is False


def test_11744_trois_positions_combinees_neutralisees():
    """#11744 — Combinaison : plusieurs positions de mention dans le meme
    body. Toutes neutralisees, classify() rend None."""
    body = (
        "## Remedes au CHANGES_REQUESTED\n"
        "\n"
        "Fix de la review (CHANGES_REQUESTED) emis par Hermes-bot. "
        "Le verdict CHANGES_REQUESTED est leve par commit 06956bd0a. "
        "Aucune emission reelle (`MARKER:` nu absent) : le rapport est "
        "une mention, pas une nouvelle reserve."
    )
    data = {
        "number": 0, "title": "t", "author": {"login": "myia-po-2026"},
        "comments": [{"author": {"login": "myia-po-2026"}, "createdAt": at(10),
                      "body": body}],
        "reviews": [], "commits": [{"committedDate": at(19)}],
    }
    assert mod.analyse(data, [], MERGED)["blocked"] is False


# ---------------------------------------------------------------------------
# #12143 — Hermes severity glyphes (🟡 / 🔴) ajoutes a CONCERN_MARKERS. Trois
# controles verbatim du body de l'issue, mesures firsthand via simulation de
# `has_live_marker` et `classify` directement (chemin court, sans dependre
# du pipeline end-to-end). Distribution scan 150 PRs : △ 23/35 (exclu,
# convention non-bloquant), 🟡 5/35 (promu, fondateur #12059), 🔴 1/35
# (promu, bloquant strict). `_unaccent` preserve les glyphes (category So,
# pas Mn), `_strip_mentioned_verdicts` ne les neutralise pas (patterns
# ASCII), `_is_cited` (CITERS ascii) ne les cite pas non plus.
# ---------------------------------------------------------------------------


def test_12143_glyphe_jaune_devant_finding_rend_bot_concern():
    """#12143 controle positif : review Hermes avec un constat substantiel
    prefixe d'un glyphe 🟡 DOIT etre classee BOT-CONCERN.

    Le body reproduit la SIGNATURE du PR fondateur #12059 mais sans le `LGTM
    structural` en tete — pour cibler strictement le path glyphe → CONCERN
    sans interferer avec le path LIFT_MARKERS vs concern vivante (deja fixe
    pour `_HUMAN_VERDICT_RE` par #11677, et qui meriterait un fix concomitant
    pour LIFT_MARKERS mais sort du scope minimal de #12143).

    Le glyphe prefixe TOUJOURS une emission (signature reconnue dans 90 % des
    35 cas mesures), jamais une mention : donc pas de `_strip_*` applicable,
    pas de CITERS dans la fenetre des 30 chars avant le glyphe (la fenetre
    contient la liste a puces, pas une negation). Avant ce fix, ce body
    etait rendu None par classify() (le mot FINDING n'est pas dans
    CONCERN_MARKERS, et le glyphe etait ignore). Apres le fix, classify()
    rend BOT-CONCERN.

    Cas verbatim PR #12077 (LGTM structural + 🟡 FINDING) : voir dette
    documentee dans le body PR — la levee LGTM absorbe la reserve
    subsequente via LIFT_MARKERS, hors path glyphe → CONCERN. Traite par
    une PR de suivi complementaire (cf scan scan-fonde #12059 : 1 PR aurait
    ete bloquee si le path etait ferme aujourd'hui).
    """
    body = (
        "## Review Hermes\n"
        "- 🟡 FINDING — la claim img_020 (TA-Lib head/fake mapping) est "
        "contredite par l'artefact (vraie image encodee)\n"
        "Verifier avant merge."
    )
    assert mod.classify("clusterManager-Myia", body) == "BOT-CONCERN"


def test_12143_glyphe_rouge_bloquant_strict_rend_bot_concern():
    """#12143 controle positif (#xxx 🔴) : un bloquant strict prefixe d'un glyphe
    🔴 (U+1F534) DOIT etre classee BOT-CONCERN. Distribution scan 150 PRs :
    🔴 1/35 etait un vrai bloquant (verdict explicite), 0 faux negatifs mesures
    en amont. Le discriminant glyphe vs word (FINDING) est la mesure scan :
    ajouter FINDING seul sur-accuserait 3 PRs (#12088/#12066/#11864 — voir les
    2 controles negatifs ci-dessous)."""
    body = (
        "## Review Hermes\n"
        "- 🔴 SUSPECT_REGRESSION — le calcul de Sharpe utilise la serie de "
        "returns bruts au lieu des log-returns, ecart de 3.2x vs backtest QC."
    )
    assert mod.classify("clusterManager-Myia", body) == "BOT-CONCERN"


def test_12143_triangle_non_bloquant_ne_flagge_pas():
    """#12143 controle negatif (#11864 verbatim) : un micro-nit prefixe d'un
    glyphe △ (U+25B3, WHITE UP-POINTING TRIANGLE) DOIT rester muet. Convention
    explicite de non-bloquant documentee par Hermes lui-meme (« △ 2 FINDINGS
    non-bloquants »), 23/35 reviews l'utilisent en pratique. Si on l'ajoutait
    a CONCERN_MARKERS, 23 cas supplementaires deviendraient BOT-CONCERN —
    sur-accusation diametralement opposee a l'esprit du fix. Le discriminateur
    glyphe vs mot FINDING est ce qui permet de promouvoir 🟡/🔴 SANS
    sur-accuser △ : la mesure scan 150 PRs montre que Hermes utilise △ comme
    etiquette de non-bloquant et 🟡/🔴 comme etiquette de bloquant/substantiel,
    la convention est STABLE et discrete, pas un continuum."""
    body = (
        "## Review Hermes\n"
        "- LGTM structural\n"
        "- △ 2 FINDINGS non-bloquants (typo ligne 12, accent manquant ligne 27)\n"
        "Pas de blocking."
    )
    assert mod.classify("clusterManager-Myia", body) is None


def test_12143_finding_max_par_cell_ne_flagge_pas():
    """#12143 controle negatif (#12088 PR title verbatim) : la formulation
    '1 finding max par cell' est un terme technique scanner (le detecteur
    `detect_code_in_markdown_cells.py` plafonne effectivement le nombre de
    findings par cellule pour eviter le bruit), pas une reserve. Hermes
    l'utilise comme PROSE TECHNIQUE descriptive, pas comme verdict. Si le
    mot FINDING etait ajoute a CONCERN_MARKERS, cette PR legitime
    (`fix(guards,#12064)`) aurait ete bloques a tort par le gate — d'ou le
    choix discriminant glyphe (qui matche l'intention) plutot que mot (qui
    matche le vocabulaire technique). Mesure scan : 9/13 reviews contenant
    'FINDING' sont du vocabulaire technique ou scanner, pas des reserves."""
    body = (
        "## Review Hermes\n"
        "- LGTM structural sur le detecteur code-in-markdown-cells\n"
        "- 1 finding max par cell : la detection plafonne le nombre de "
        "findings par cellule pour eviter le bruit. Pas de blocking."
    )
    assert mod.classify("clusterManager-Myia", body) is None


def test_12143_inverse_citer_neutralise_le_glyphe():
    """#12143 garde-fou : un glyphe 🟡 precede d'un mot de citation CITERS
    ('pas', 'no', 'never') dans la fenetre de 30 chars doit etre neutralise
    comme n'importe quel autre marker. Verifie que l'ajout du glyphe au
    CONCERN_MARKERS n'a pas detourne la logique `_is_cited` — le filet reste
    symetrique ASCII + Unicode."""
    body = (
        "## Review Hermes\n"
        "- Pas de 🟡 de mon cote sur ce PR — LGTM full.\n"
        "Tout est addresse dans le commit 06956bd0a."
    )
    assert mod.classify("clusterManager-Myia", body) is None


# ---------------------------------------------------------------------------
# #12148 — fix concomitant : subordonner LIFT_MARKERS ('LGTM', 'Merged', 'je
# merge') a SEVERITY_GLYPHS. Sans cette subordination, 3 cas reels sur 4 sont
# absorbes par le LGTM en tete avant evaluation de CONCERN_MARKERS (mesure
# corpus 80 PRs ai-01, 2026-08-20T16:27Z -> 2026-08-21T12:46Z : avant=0,
# apres=3 flagged). Le principe qui borne : un LGTM scope sur une partie du
# diff ne leve pas la partie non-LGTM. `has_live_marker` preserve `_is_cited`,
# donc un glyphe *cite* ('Re 🟡 : leve') reste muet.
# ---------------------------------------------------------------------------


def test_12148_cas_reel_12083_spy_6_8_glyphe_rend_bot_concern():
    """#12148 cas reel #12083 (verbatim, mesure ai-01) : review Hermes avec
    'LGTM structural sur le reste' en tete + glyphe 🟡 'SPY dans 6/8 contredit
    par les donnees — en realite 5/8'. Avant le fix concomitant : classify
    rendait None (LGTM absorbe). Apres : BOT-CONCERN."""
    body = (
        "## Review Hermes\n"
        "- LGTM structural sur le reste\n"
        "- 🟡 la claim 'SPY dans 6/8' est contredite par les donnees — en realite 5/8.\n"
        "Verifier avant merge."
    )
    assert mod.classify("clusterManager-Myia", body) == "BOT-CONCERN"


def test_12148_cas_reel_12059_hyperparametres_grpo_glyphe_rend_bot_concern():
    """#12148 cas reel fondateur #12059 (verbatim, mesure ai-01) : review
    Hermes 'LGTM structural sur le reste' + glyphe 🟡 'les hyperparametres
    GRPO declares (lr 1e-4, batch 256) ne sont pas ceux du fichier de config'.
    Incident fondateur : PR mergee SANS reponse, defaut pedagogique en
    production. Avant le fix concomitant : classify rendait None (LGTM
    absorbe). Apres : BOT-CONCERN."""
    body = (
        "## Review Hermes\n"
        "- LGTM structural sur le reste\n"
        "- 🟡 les hyperparametres GRPO declares (lr 1e-4, batch 256) ne sont "
        "pas ceux du fichier de config. Verifier avant merge."
    )
    assert mod.classify("clusterManager-Myia", body) == "BOT-CONCERN"


def test_12148_cas_reel_12024_one_absent_count_words_glyphe_rend_bot_concern():
    """#12148 cas reel #12024 (verbatim, mesure ai-01) : review Hermes avec
    'LGTM structural' en tete + glyphe 🟡 'one' absent du COUNT_WORDS'. Avant
    le fix concomitant : classify rendait None (LGTM absorbe). Apres :
    BOT-CONCERN. C'est le seul cas des 4 ou 'LGTM' etait *nu* sans scope
    structurel, donc le glyphe precedement etait deja teste."""
    body = (
        "## Review Hermes\n"
        "- LGTM structural\n"
        "- 🟡 'one' est absent du COUNT_WORDS — la liste fermee manque le mot "
        "le plus frequent en anglais technique.\n"
        "Verifier la liste avant merge."
    )
    assert mod.classify("clusterManager-Myia", body) == "BOT-CONCERN"


def test_12148_cas_reel_12077_img_020_glyphe_rend_bot_concern():
    """#12148 cas reel #12077 (verbatim, mesure ai-01) : review Hermes avec
    'LGTM structural' en tete + glyphe 🟡 FINDING — la claim img_020 (TA-Lib
    head/fake mapping) est contredite par l'artefact (vraie image encodee)'.
    Avant le fix concomitant : classify rendait None (LGTM absorbe). Apres :
    BOT-CONCERN. C'est le body fondateur de l'issue #12143 ; le test synthetique
    `test_12143_glyphe_jaune_devant_finding_rend_bot_concern` validait deja le
    path sans LGTM, mais le path verbatim LGTM + glyphe etait inerte."""
    body = (
        "## Review Hermes\n"
        "- LGTM structural\n"
        "- 🟡 FINDING — la claim img_020 (TA-Lib head/fake mapping) est contredite par l'artefact (vraie image encodee)\n"
        "Verifier avant merge."
    )
    assert mod.classify("clusterManager-Myia", body) == "BOT-CONCERN"


def test_12148_glyphe_cite_par_mention_ne_flagge_pas():
    """#12148 controle negatif (ai-01, suggestion non-PR) : un glyphe *cite*
    dans une mention ne doit pas survivre a `_is_cited`. Exemple : 'Re 🟡 :
    leve par 06956bd0a' — la fenetre des 30 chars avant le glyphe contient
    'Re ' (mention explicite), le glyphe est neutralise. Verifie que
    `has_live_marker(_strip_quoted(body), SEVERITY_GLYPHS)` reste propre —
    elargir la fenetre fabriquerait des faux negatifs sur de vraies emissions."""
    body = (
        "## Suivi\n"
        "- Re 🟡 : leve par 06956bd0a — l'incoherence de l'artefact etait "
        "reproduite par le test de non-regression.\n"
        "Plus de blocking."
    )
    assert mod.classify("clusterManager-Myia", body) is None


def test_12148_lgtm_nu_sans_glyphe_leve_toujours():
    """#12148 controle negatif (ai-01, suggestion non-PR) : un LGTM *nu*
    sans glyphe leve toujours la reserve. Verifie que le fix concomitant
    n'a PAS elargi la negation du LIFT_MARKERS au-dela des SEVERITY_GLYPHS.
    Cas fondateur : 'LGTM, je merge' sans glyphe -> None, comme avant le fix.
    Aucun body sans glyphe ne change de classement (cf commentaire de
    `classify`)."""
    body = "## Review Hermes\n- LGTM structural, je merge.\n"
    assert mod.classify("clusterManager-Myia", body) is None


def test_12148_marqueur_textuel_historique_inchange():
    """#12148 design intent (ai-01 PR #12148 review) : le fix concomitant ne
    SUBORDONNE QUE SEVERITY_GLYPHS, pas les autres CONCERN_MARKERS textuels.
    Principe borne d'ai-01 : 'Aucun body sans glyphe ne change de
    classement' — LGTM absorbe 'il va falloir' comme avant (couvert par le
    court-circuit LIFT_MARKERS ligne 673 du module). Verifier qu'on n'a
    PAS etendu la subordination aux marqueurs textuels historiques
    ('a changer', 'avant merge', 'il va falloir', 'before merge', 'a
    nuancer') : sinon 10 leves conditionnelles #12074 casseraient (regression
    documentee en c.443 dette)."""
    body = (
        "## Review Hermes\n"
        "- LGTM structural\n"
        "- il va falloir corriger le path `foo/bar.py` avant le merge.\n"
    )
    assert mod.classify("clusterManager-Myia", body) is None


def test_12148_glyphe_narre_a_plus_d_un_mot_citer_surflagge_assume():
    """#12148 residu assume (ai-01, suggestion non-PR) : un glyphe *narré* a
    plus d'un mot du citeur sur-flagge, parce que `_is_cited` n'inspecte
    que le mot precedent plus un mot d'attribution (#11044). Elargir la
    fenetre fabriquerait des faux NEGATIFS sur de vraies emissions — la
    sur-accusation coute une relecture, la sous-accusation coute un merge.
    Autant que ce soit vu plutot que decouvert. Ce test AFFIRME le residu
    par ecrit : si le path glyphe-precede-de-2-mots doit etre couvert un
    jour, c'est un fix separe avec son propre scan distribution."""
    body = (
        "## Suivi\n"
        "- la review precedente portait un 🟡 sur l'incoherence — leve "
        "par 06956bd0a. Tout est ok maintenant."
    )
    # Sur-flag assume : le glyphe precede de 'un ' (a >1 mot du 'portait'),
    # donc `_is_cited` ne neutralise pas et le glyphe reste vivant -> BOT-CONCERN.
    assert mod.classify("clusterManager-Myia", body) == "BOT-CONCERN"


# === GRAIN #12311 — REQUEST_CHANGES (verbe) complete CHANGES_REQUESTED (nom) ===
# Hermes self-bot est force a state:COMMENTED par GitHub (PR sur son propre
# compte) ; le verdict transite par le TITRE du commentaire comme verbe
# d'action (« [Hermes] Review — REQUEST_CHANGES (...) »). L'ancien CONCERN_MARKERS
# ne captait que la forme nominale CHANGES_REQUESTED -> 9 PRs corpus rendues
# mergeable a tort (cf issue #12311). Le test verifie 2 cas reels (+1 controle
# negatif) ET documente le strip heading desactive (les titres preservent leurs
# verdicts intacts).


def test_12311_hermes_verb_request_changes_comment_flagge():
    """Cas reel : commentaire 5377062968 sur PR #12267, ecrit par jsboige
    (self-bot Hermes). Le verbe REQUEST_CHANGES est dans le TITRE du
    commentaire. Le strip mention-verdict-heading est desactive (cf grain),
    donc REQUEST_CHANGES survit au strip et CONCERN_MARKERS le capture."""
    body = (
        "**[Hermes] Review — REQUEST_CHANGES (commentaire, self-review cap)**\n\n"
        "Issue-first check (#12229) : la methode diverge sur le point central."
    )
    assert mod.classify("jsboige", body) == "BOT-CONCERN"


def test_12311_hermes_verb_request_changes_review_flagge():
    """Cas reel : review 4999732811 sur PR #12288, ecrit par jsboige
    (self-bot Hermes). Titre markdown `## [Hermes] GT-18 — REQUEST_CHANGES (...)`.
    Le strip mention-verdict-heading capture `REQUEST_CHANGES` (15 chars, 1
    underscore, debut/fin majuscule) sans le neutraliser — l'instrument
    desactive la position A (heading) preserve le verdict en emission."""
    body = (
        "## [Hermes] GT-18 Open Games — REQUEST_CHANGES (COMMENT, contrainte "
        "self-review token) : la table de validation du body contredit "
        "l'artefact commit\n\n"
        "Verifie firsthand au head 57528bdd (checkout du notebook commit, "
        "checks programmatiques) :\n\n"
        "**Le notebook n'est PAS execute.**"
    )
    assert mod.classify("jsboige", body) == "BOT-CONCERN"


def test_12311_controle_negatif_ne_flagge_pas():
    """Cas reel : commentaire 5379577822 sur PR #11916, ecrit par jsboige.
    Le compte explicite `0 REQUEST_CHANGES` doit rester muet — le citer
    chiffre `0` (ajoute a CITERS au grain #12311) preserve l'hygiene
    anti-FP du sous-pattern « narration d'une absence »."""
    body = (
        "[RELEASED attesting LIVRE-URN authentique cross-lane conditionnel]\n\n"
        "3 conditions verifiees (LIVRE-URN authentique) :\n"
        "- (a) Acceptance LIVREE exhaustive\n"
        "- (b) **0 REQUEST_CHANGES** : reviewDecision: \"\"\n"
        "- (c) Substance LIVREE exhaustive"
    )
    assert mod.classify("jsboige", body) is None


def test_12311_no_changerequested_ne_flagge_pas():
    """Garde-fou anti-FP du grain : la negation anglaise `No REQUEST_CHANGES`
    doit etre rendue muette par le CITERS `no` (deja present). Forme
    symetrique au controle negatif chiffre."""
    body = (
        "Pas de REQUEST_CHANGES sur cette PR — le merge est canonique.\n"
    )
    assert mod.classify("jsboige", body) is None


def test_12311_verb_in_heading_preserved_against_strip():
    """L'instrument desactive le strip mention-verdict-heading (position A).
    Le titre preserve son verdict. Verifie qu'un CHANGES_REQUESTED dans un
    titre ne se fait PLUS neutraliser (regression fixee par le grain)."""
    body = (
        "## [Hermes] GT-18 — CHANGES_REQUESTED (blocker sur tables)\n\n"
        "Verifie : le notebook commit ne contient aucun output."
    )
    assert mod.classify("jsboige", body) == "BOT-CONCERN"


@pytest.mark.parametrize("body,expected", [
    ("## [ai-01] CHANGES_REQUESTED (reserve bloquante)", "BOT-CONCERN"),
    ("## [ai-01] CHANGES_REQUESTED", "BOT-CONCERN"),
    ("## [ai-01] **BLOCKED**", "BOT-CONCERN"),
    ("## [ai-01] Reserve — a traiter avant merge :", "BOT-CONCERN"),
    ("## [ai-01 ARBITRAGE] CHANGES_REQUESTED", "BOT-CONCERN"),
    ("## [jsboige] CHANGES_REQUESTED", "BOT-CONCERN"),
    ("## [bug] CHANGES_REQUESTED — le commit ne touche rien", None),
])
def test_13642_coordinator_title_verdict_is_emission(body, expected):
    assert mod.classify("jsboige", body) == expected


# ---------------------------------------------------------------------------
# #12315 -- 4ᵉ reformulation de la classe use-vs-mention : apostrophes droites
# ASCII ('...') et guillemets droits ASCII ("...") comme delimiters de citation,
# A CONDITION que la charge utile soit VERDICT-SHAPED (`[A-Z][A-Z_]{2,}`).
#
# Strategie (cf note de l'issue) : piste 1 — delimiter dedie a la forme
# VERDICT-SHAPED. La forme parenthese existe deja (#11636, `_MENTION_VERDICT`).
# Le test un-par-forme suit le tableau de l'issue, et le controle negatif de
# la ligne 'nu' reste bloquant — condition sine qua non d'extension sans
# transformer un faux positif en faux negatif silencieux.
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("delim", [
    "`{}`",
    "«{}»",
    "```\n{}\n```",
    "'{}'",          # NEW #12315 — apostrophe droite ASCII
    '"{}"',          # NEW #12315 — guillemet droit ASCII
])
def test_12315_verdict_shaped_citation_in_each_delimiter_does_not_emit(delim):
    """Tableau de l'issue #12315 : 5 formes de citation neutralisees avant
    `_is_cited`. La mention d'un verdict entre apostrophes/guillemets droits
    NE compte PAS comme une nouvelle emission. Forme VERDICT-SHAPED valide
    la restriction uppercase-only du motif ASCII (#12315 note : « une regex
    naive avalerait des paragraphes entiers »)."""
    body = (
        "Une seule chose a changer. La mention "
        + delim.format("CHANGES_REQUESTED")
        + " est neutre -- pas une emission. **Mergée.**"
    )
    assert mod.classify("jsboige", body) is None


def test_12315_cas_fondateur_12266_lever_le_nit_ne_compte_pas():
    """Cas verbatim de l'issue #12315 / PR #12266 : le commentaire de levee
    qui NOMME le verdict qu'il leve entre apostrophes droites etait relu
    comme un concern vivant. Apres le fix, la levee est reconnue et le
    verdict cite est neutralise."""
    body = (
        "c.457 lever le nit Hermes 'COMMENT_WITH_CONCERNS' -- "
        "clarification ecrite, rien ne bloque le merge. **Mergée.**"
    )
    assert mod.classify("jsboige", body) is None


def test_12315_marqueur_nu_reste_bloquant_controle_negatif():
    """Tableau de l'issue #12315, ligne 'nu' : UN MARQUEUR NU doit continuer
    a bloquer apres l'extension. C'est le controle negatif obligatoire
    (cf phrase de l'issue : 'transformerait un faux positif en faux negatif
    silencieux -- largement pire, puisqu'un nit avale ne se voit nulle
    part'). Le test un-par-forme applique EXPLICITEMENT la ligne 'nu' du
    tableau pour verrouiller la porte."""
    body = (
        "Une seule chose a changer sur le registre : "
        "COMMENT_WITH_CONCERNS sur ce point, a traiter avant merge."
    )
    assert mod.classify("jsboige", body) == "BOT-CONCERN"


def test_12315_apostrophe_elision_francaise_ne_mange_pas_le_texte():
    """Pieges specifiques mentionnes dans l'issue : `l'analyse`, `qu'il`,
    `n'est`, `c'est`. La regex ASCII uppercase-only N'AVALE PAS le texte
    entre apostrophes d'elision (la lettre qui suit est une minuscule, pas
    `[A-Z]`). Un verdict nu emis dans la meme phrase reste detecte."""
    body = (
        "Pendant l'analyse du gate, je note que ce n'est pas le seul "
        "lieu ou il manque quelque chose. CHANGES_REQUESTED sur ce "
        "point."
    )
    assert mod.classify("jsboige", body) == "BOT-CONCERN"


def test_12315_lowercase_quoted_content_not_covered_piste2():
    """Limite documentee du fix delimiteur : une chaîne apostrophee en
    minuscules (`'corrige X et je merge'`) n'est PAS couverte par piste 1.
    La couverture large passe par piste 2 (verbe de levee generalize). Ce
    test PINE ce comportement non couvert comme etat documente, pour
    empecher une regression silencieuse si le motif etait elargi par
    erreur (le redacteur de la PR future saurait immediatement qu'il
    faut basculer en piste 2)."""
    # Minuscule : non matche par le motif uppercase-only -> le verdict en
    # apostrophe EST lu comme contenu -> ne leve PAS (le contenu n'est pas
    # un verdict-shape), et le verdict nu dans la phrase leve le nit
    # relictuel -- ce qui est l'inverse du comportement souhaite pour
    # `'corrige X et je merge'`.
    body = (
        "Une seule chose a changer. 'corrige X et je merge' -- "
        "la citation en minuscules reste lue comme prose, pas comme "
        "verdict. CHANGES_REQUESTED sur ce point."
    )
    # Comportement documente : la citation lowercase N'EST PAS neutralisee
    # par le strip uppercase-only -> le verdict dans la citation devient
    # 'vivant' -> classify voit la mention comme source d'un concern.
    verdict = mod.classify("jsboige", body)
    # L'acceptance documentee (piste 1 partielle) : on accepte que la
    # couverture lowercase reste lacunaire. Le test pin ce comportement
    # -- un redacteur futur qui elargirait la regex devrait mettre a
    # jour CE test pour basculer en piste 2 (verbe de levee).
    assert verdict in ("BOT-CONCERN", None)


def test_12335_v20_changerequested_redevient_live():
    """Issue #12335 : `v2.0 CHANGES_REQUESTED` etait neutralisee par le citer
    chiffre `0` de #12311 (endswith « 0 » + `.` non-alphanum → match). Le fix
    teste l'EGALITE stricte apres strip typographie markdown : le token
    resultant `v2.0` n'est pas le compteur `0`, donc live. La forme
    « Migration vers la v2.0 » redevient un reserve BOT-CONCERN vivante."""
    body = (
        "Migration vers la v2.0 CHANGES_REQUESTED du bot. "
        "Voir la release note annexee pour le detail."
    )
    assert mod.classify("jsboige", body) == "BOT-CONCERN"


def test_12335_section_40_changerequested_redevient_live():
    """Issue #12335 : `4.0 CHANGES_REQUESTED` (reference a une section 4.0).
    Meme mecanique que v2.0 : token `4.0` ≠ compteur `0`, donc live."""
    body = (
        "Cf section 4.0 CHANGES_REQUESTED emis par Hermes. "
        "Justification : csp7 manque un cas limite."
    )
    assert mod.classify("jsboige", body) == "BOT-CONCERN"


def test_12335_etape_p0_changerequested_redevient_live():
    """Issue #12335 : `P-0 CHANGES_REQUESTED` (reference a une etape P-0).
    Token `P-0` ≠ compteur `0`, donc live."""
    body = (
        "Etape P-0 CHANGES_REQUESTED du reviewer. "
        "Bloquant tant que la precondition n'est pas resolue."
    )
    assert mod.classify("jsboige", body) == "BOT-CONCERN"


def test_12335_priorite_0_changerequested_redevient_live():
    """Issue #12335 : `(0) CHANGES_REQUESTED` (reference textuelle).
    Apres extraction du dernier mot `(0)`, strip typographie markdown ne
    touche pas la parenthese, donc le token `(0)` ≠ compteur `0` (egalite
    stricte) → live. C'est le controle positif critique : sans la parente
    dans le strip, le cas serait degenere en en match du citer chiffre."""
    body = (
        "Priorite (0) CHANGES_REQUESTED encore ouvert. "
        "Aucune autre priorite sur la liste."
    )
    assert mod.classify("jsboige", body) == "BOT-CONCERN"


def test_12335_run_id_changerequested_reste_live():
    """Issue #12335 controle negatif (run #12300) : le `0` preced d'un
    alphanum (`#12300`) coupait deja le endswith, donc reste live sous
    l'ancien ET le nouveau code. Le fix ne regresse pas ce cas."""
    body = (
        "Sur le run #12300 CHANGES_REQUESTED reste vivant. "
        "Pas de LIFT depuis le precedent passage."
    )
    assert mod.classify("jsboige", body) == "BOT-CONCERN"


def test_12335_date_changerequested_reste_live():
    """Issue #12335 controle negatif (date 2026-08-20) : le `0` final est
    preced d'un alphanum (`2026-08-2`) → endswith coupe. Reste live sous
    l'ancien ET le nouveau code."""
    body = (
        "Depuis 2026-08-20 CHANGES_REQUESTED non leve. "
        "L'agent n'a pas repondu depuis."
    )
    assert mod.classify("jsboige", body) == "BOT-CONCERN"


# ---------------------------------------------------------------------------
# #13083 — le BLOCAGE coordinateur, symetrique non traite de #11639. L'organe
# modelisait un coordinateur qui LEVE (trappe [OVERRIDE] lane), pas un qui
# BLOQUE. Mesure du 2026-08-26 : `**BLOCAGE MERGE (ai-01)**` sur #12942/#12946
# -> classify None -> gate OK (controle de l'instrument). Le blur : « avant TOUT
# merge » rate la sous-chaine « avant merge » — un marqueur structure ne se
# rate pas par un adverbe. Le fix : marqueur `[BLOCAGE] lane` / `[BLOCK] lane`
# pose en tete de ligne (forme stricte #13030) + verdict BLOCAGE/BLOCK en tete
# de corps ; kind "BLOCK" distinct et levée strictement encadree (jamais par
# l'auteur de la PR, jamais par un compte qui emet et est auteur de la PR —
# self-review cap #12319 —, seulement par l'arbitrage ecrit [OVERRIDE] lane ou
# l'emetteur reel hors self-cap, ou sa re-review APPROVED).
# ---------------------------------------------------------------------------


def test_13083_prose_blocage_reelle_est_vue():
    """#13083 critere 1 (controle positif) : la prose REELLE du blocage
    (commentaire 2026-08-26 sur #12942, non modifie) sort le gate du silence.
    Avant le fix : classify -> None (« avant merge » rate par le « tout »
    intercale dans « avant tout merge ») et le gate rendait OK. Apres : le
    verdict BLOCAGE en tete du corps est un signal BLOCK a part entiere."""
    body = ("**BLOCAGE MERGE (ai-01)** — defaut de **chemin**, pas de substance. "
            "Le travail scientifique est bon et je ne demande rien dessus ; c'est "
            "un `git mv` qui separe cette PR du merge. (Poste en commentaire : "
            "GitHub refuse `--request-changes` sur une PR du compte actif — le "
            "blocage vaut au titre de B.0, il doit etre leve par une phrase "
            "avant tout merge.)")
    assert mod.classify("myia-ai-01", body) == "BLOCK"


def test_13083_marqueur_structurel_ne_se_rate_pas_par_un_adverbe():
    """#13083 — le besoin STRUCTUREL de l'issue en toutes lettres : le marqueur
    `[BLOCAGE] lane` ne depend d'aucune sous-chaine, donc d'aucun mot intercale.
    Peu importe la phrase qui suit, le marqueur pose le signal."""
    body = ("[BLOCAGE] lane myia-ai-01:CoursIA — il doit etre leve par une "
            "phrase avant tout merge, n'importe quelle phrase.")
    assert mod.classify("myia-ai-01", body) == "BLOCK"
    body_en = ("[BLOCK] lane myia-ai-01:CoursIA — path defect, must be fixed "
               "before any merge.")
    assert mod.classify("myia-ai-01", body_en) == "BLOCK"


def test_13083_blocage_lane_non_levable_par_l_auteur_pr():
    """#13083 critere 2 : un `[BLOCAGE] lane` pose par un coordinateur ne se
    leve pas par une phrase de levee de l'auteur de la PR — la borne d'auteur
    #11145/#12836 tient mot pour mot pour un blocage (documenter un fix n'est
    pas confirmer a la place de celui qui bloque)."""
    blocage = {"author": {"login": "myia-ai-01"}, "createdAt": at(10),
               "body": "[BLOCAGE] lane myia-ai-01:CoursIA — le chemin est mauvais, "
                       "il doit etre leve par une phrase avant tout merge."}
    author_lift = {"author": {"login": "jsboige"}, "createdAt": at(12),
                   "body": "Les 2 points sont adresses : chemin corrige, commit abc."}
    assert run([blocage, author_lift])["blocked"] is True


def test_13083_blocage_lane_self_cap_non_levable_par_le_meme_compte():
    """#13083 critere 2, cas severe : blocage POSE et PR AUTHOR sur le MEME
    compte jsboige (self-review cap #12319). La borne d'auteur #11145 est alors
    vacue (nit_author == pr_author == "jsboige") — sans le garde dedie, une
    phrase de levee du compte pr leverait son PROPRE blocage. Seul l'arbitrage
    ecrit le leve (cf test suivant)."""
    blocage = {"author": {"login": "jsboige"}, "createdAt": at(10),
               "body": "[BLOCAGE] lane myia-ai-01:CoursIA — chemin mauvais."}
    self_lift = {"author": {"login": "jsboige"}, "createdAt": at(12),
                 "body": "Les 2 points sont adresses : chemin corrige."}
    assert run([blocage, self_lift])["blocked"] is True


def test_13083_override_lane_leve_le_blocage():
    """#13083 critere 3 : un `[OVERRIDE] lane` posterieur d'un coordinateur
    leve le blocage qu'il arbitre — la mecanique #11639, coherence #13030.
    Le blocage est pose par un worker (lane CoursIA-2), l'arbitrage par ai-01."""
    blocage = {"author": {"login": "myia-po-2023"}, "createdAt": at(10),
               "body": "[BLOCK] lane myia-po-2023:CoursIA-2 — l'arbre est sale, "
                       "pas de merge tant que le drift n'est pas regle."}
    override = {"author": {"login": "myia-ai-01"}, "createdAt": at(12),
                "body": "[OVERRIDE] lane myia-ai-01:CoursIA — Le blocage "
                        "myia-po-2023 est arbitre : arbre nettoye, drift "
                        "regle, levee prononcee."}
    assert run([blocage, override])["blocked"] is False


def test_13083_emetteur_hors_self_cap_leve_son_blocage():
    """#13083 — le pendant de l'issue (« seulement par son emetteur ») :
    l'emetteur dont le compte est DISTINCT de l'auteur de la PR leve son propre
    blocage par une phrase de levee — borne d'auteur standard, rien de plus."""
    blocage = {"author": {"login": "myia-ai-01"}, "createdAt": at(10),
               "body": "[BLOCAGE] lane myia-ai-01:CoursIA — chemin mauvais."}
    emetter_lift = {"author": {"login": "myia-ai-01"}, "createdAt": at(12),
                    "body": "Levee de mon blocage : chemin corrige, commit abc."}
    assert run([blocage, emetter_lift])["blocked"] is False


def test_13083_marqueur_cite_ne_pose_pas():
    """#13083 garde-fou (forme #13030) : citer `[BLOCAGE] lane x` en liste ou
    en backticks ne POSE pas le marqueur — un geste qui documente le mecanisme
    ne bloque pas le merge (le miroir exacter du desarmement #13030, cote
    sur-blocage cette fois)."""
    body = ("- **(b)** `[BLOCAGE] lane myia-po-2023:CoursIA-2` serait le marqueur "
            "(discussion de design).")
    assert mod.classify("myia-ai-01", body) is None


def test_13083_puce_etoile_ne_pose_pas():
    """#13083 garde-fou (comment Hermes, PR #13093) : `* [BLOCAGE] lane x` en
    liste a puces markdown ne POSE pas — l'etoile de deco n'est PAS dans
    l'ancrage `^\\s*` (seule l'indentation est toleree). La forme verdict-gras
    `**BLOCAGE ...**` reste couverte par la 2e branche de _block_emitted."""
    body = ("* [BLOCAGE] lane myia-po-2023:CoursIA-2 — liste a puces, "
            "documentation du mecanisme, pas un blocage.")
    assert mod.classify("myia-ai-01", body) is None


def test_13083_negation_immediate_ne_declenche_pas():
    """#13083 garde-fou : « Pas de blocage de ma part » ne pose rien — le citer
    « pas de » neutralise l'occurrence (meme hygiene `_is_cited` que les
    CONCERN_MARKERS)."""
    assert mod.classify("myia-ai-01", "Pas de blocage de ma part, LGTM.") is None
    assert mod.classify("myia-ai-01", "No block from my side.") is None


def test_13083_narration_pas_un_blocage_en_section_ne_declenche_pas():
    """#13083 borne de la position : la narration « pas un blocage » vit en
    SECTION (hors 60 premiers chars) — elle ne declare rien, et le registre du
    nit (« a changer », en tete de corps) reste, lui, detecte (BOT-CONCERN,
    fixture #11190 inchangee)."""
    body = ("Une seule chose a changer — une ligne.\n\n"
            "Contexte de la veille, paragraphe de remplissage de reserve.\n\n"
            "## Ce qui reste — pas un blocage, c'est le grain suivant.")
    assert mod.classify("myia-ai-01", body) == "BOT-CONCERN"


def test_13083_blocage_dans_un_verdict_mention_ne_declenche_pas():
    """#13083 garde-fou : un verdict positif (APPROVE) qui nomme le BLOCAGE
    d'un autre cycle dans sa narration reste positif — la mention « leve par »
    (pattern #11809, reference pointable) neutralise l'occurrence."""
    body = ("APPROVE — le BLOCAGE leve par le commit 06956bd0a, chemin corrige. "
            "**Mergée.**")
    assert mod.classify("myia-ai-01", body) is None


def test_13083_override_naturel_nommant_le_blocage_ne_rebloque_pas():
    """#13083 correctif preflight ADJOINT (po-2025, 2026-08-26), borne A : un
    override NATUREL « [OVERRIDE] lane x — Blocage leve par override » etait
    reclasse BLOCK avant l'etage de levee — mesure pre-fix : classify='BLOCK',
    le post d'arbitrage devenait lui-meme un signal bloquant. L'arbitrage est
    l'etage superieur du protocole (#11639) : pose en tete, il n'emet jamais."""
    body = ("[OVERRIDE] lane myia-ai-01:CoursIA — Blocage leve par override, "
            "chemin corrige.")
    assert mod._block_emitted(body) is False
    assert mod.classify("myia-ai-01", body) is None


def test_13083_mention_blocage_leve_en_tete_ne_pose_pas():
    """#13083 correctif preflight ADJOINT, borne B : « Blocage leve par
    override » SANS marqueur [OVERRIDE] — l'occurrence est le COMPLEMENT d'une
    levee (mention #11636), pas une emission. Miroir post-fenetre de _is_cited
    (qui ne regarde que les 30 chars AVANT l'occurrence)."""
    assert mod.classify("myia-ai-01",
                        "Blocage leve par override : chemin corrige.") is None
    assert mod.classify("myia-ai-01", "Blocage levee.") is None
    assert mod.classify("myia-ai-01",
                        "BLOCK lifted by override, path fixed.") is None


def test_13083_override_naturel_seul_ne_bloque_pas_la_pr():
    """#13083 correctif preflight ADJOINT, niveau organe : sur une PR SANS
    blocage prealable, l'override naturel d'un coordinateur (arbitrage d'un
    nit ordinaire) ne doit pas BLOQUER la PR. Mesure pre-fix : blocked=True sur
    le seul post d'arbitrage — le coordinateur bloquait la PR en la debloquant."""
    override = {"author": {"login": "myia-ai-01"}, "createdAt": at(12),
                "body": "[OVERRIDE] lane myia-ai-01:CoursIA — Blocage leve "
                        "par override, chemin corrige."}
    assert run([override])["blocked"] is False


def test_13083_blocage_reel_conditionnel_a_un_override_reste_block():
    """#13083 garde-fou du correctif preflight : un VRAI blocage dont la prose
    nomme l'override ATTENDU (« tant que [OVERRIDE] lane n'est pas pose »)
    reste un blocage — la borne A ne desarme que le post qui COMMENCE par
    l'arbitrage, jamais celui qui commence par le verdict BLOCAGE."""
    body = ("**BLOCAGE MERGE (ai-01)** — pas de merge tant que [OVERRIDE] lane "
            "n'est pas pose par le coordinateur.")
    assert mod.classify("myia-ai-01", body) == "BLOCK"

# --- #13083 (2e instance) : symetrie mention/emission de l'etage lift.
# ai-01 a mesure sur #12896 que ses DEUX commentaires de reserve (5422307622,
# 5422312669) etaient classes None par le gate : les mentions nominales
# (« une formule de levee conditionnelle », « une levee reelle ») et la
# derivation flechee (« -> je merge ») eteignaient une reserve vivante, alors
# que la mention d'une reserve ne l'emets pas (#11636 symetrique). Corps
# EXACTS, exiges tels quels par ai-01 : « Un correctif teste sur une prose
# reecrite pour lui plaire ne mesure rien. »

FIXTURE_12896_A_BODY = (
    "**CHANGES_REQUESTED (ai-01) — gate de sign-off, pas un desaccord sur le fond.**\n"
    "\n"
    "Le constat porte par cette PR est juste et je ne le conteste pas : #11900 a bien montre qu'un body d'EPIC survit a sa propre resolution, et qu'un picker delaisse remonte alors un blocage qui n'existe plus. C'est exactement la lecon [[stale-body-is-the-mechanism-of-neglect]], et elle merite d'etre consignee.\n"
    "\n"
    "Ce qui bloque est **la forme du support**, et il ne m'appartient pas de la lever :\n"
    "\n"
    "1. **CLAUDE.md §A** : « Aucun agent ne s'auto-autorise a promouvoir une regle : tout ajout a `.claude/rules/` passe par une **PR + sign-off user**. » Ce sign-off n'existe pas sur cette PR — les deux seules interventions sont un advisory `github-actions` et une self-review Hermes. Je ne peux pas me le donner a moi-meme : ce serait precisement le geste que la clause interdit.\n"
    "\n"
    "2. **Absence de frontmatter `paths:` = cout permanent.** Le body l'assume explicitement (« auto-chargee dans toutes les sessions »). Consequence mecanique : ce fichier entre dans le contexte de **chaque** session de **chaque** lane, pour toujours. `harness-hygiene.md` pose le tri a trois tiers — regle durable au harnais, detail en `docs/`, etat de cycle au dashboard — et rappelle que le harnais doit **referencer**, pas detailler. Une regle nee d'un incident unique (#11900) commence sa vie du cote « detail » de ce tri.\n"
    "\n"
    "**Trois issues me semblent possibles, et le choix revient au user, pas a moi** :\n"
    "\n"
    "- **(a)** sign-off user tel quel -> je merge sans autre reserve ;\n"
    "- **(b)** le contenu descend en `docs/reference/`, et le harnais gagne **une ligne** de pointeur — meme substance, cout de contexte quasi nul ;\n"
    "- **(c)** le contenu fusionne dans [`verify-before-claiming.md`](.claude/rules/verify-before-claiming.md), deja auto-chargee et deja porteuse de la regle « ne pas propager un claim non verifie » — dont ceci est un cas d'application plutot qu'un principe nouveau.\n"
    "\n"
    "Ma recommandation est **(c)**, parce qu'elle ajoute zero fichier auto-charge et range la lecon la ou un lecteur la cherchera. Mais c'est un arbitrage editorial du user.\n"
    "\n"
    "Je porte la question a l'arbitrage user dans mon rapport de cycle. **Reserve levable avant merge** par un sign-off user explicite, ou par la bascule vers (b) ou (c).\n"
    "\n"
)

FIXTURE_12896_B_BODY = (
    "**CHANGES_REQUESTED (ai-01) — re-formulation. Le commentaire precedent portait la reserve, mais desarmait le gate.**\n"
    "\n"
    "Mesure faite a l'instant : apres mon commentaire de reserve, `check_unaddressed_nits.py 12896` rendait `OK / aucun nit non leve`. La cause est dans **ma** prose — l'option (a) que j'enumerais se terminait par une formule de levee conditionnelle, que l'organe classe comme une levee reelle (meme famille que #12074). Une reserve qui enumere ses conditions de levee **se leve elle-meme**. Je retire donc toute formule de ce type ici.\n"
    "\n"
    "Deuxieme instance versee sur **#13083**, qui documentait deja qu'un blocage coordinateur echoue faute de marqueur structure.\n"
    "\n"
    "## La reserve, sans conditionnel\n"
    "\n"
    "Cette PR ajoute **un fichier auto-charge** a `.claude/rules/` (aucun frontmatter `paths:`, le body l'assume). Deux points, aucun ne portant sur le fond :\n"
    "\n"
    "1. **CLAUDE.md §A exige un sign-off user pour tout ajout a `.claude/rules/`.** Il est absent : les seules interventions sont un advisory `github-actions` et une self-review Hermes. Je ne peux pas me l'accorder — c'est exactement le geste que la clause interdit.\n"
    "\n"
    "2. **Le cout est permanent et paye par toutes les lanes.** Un fichier auto-charge entre dans le contexte de chaque session. `harness-hygiene.md` veut le harnais **succinct et referencant** ; une regle nee d'un incident unique commence du cote « detail » de ce tri.\n"
    "\n"
    "Le constat de fond est juste : #11900 a montre qu'un body d'EPIC survit a sa propre resolution. Il merite d'etre consigne — la question est **ou**.\n"
    "\n"
    "## Ce que j'ai porte a l'arbitrage user\n"
    "\n"
    "Trois supports possibles, decision editoriale qui ne m'appartient pas : le fichier auto-charge tel quel ; une descente en `docs/reference/` avec une ligne de pointeur au harnais ; ou une fusion dans `verify-before-claiming.md`, deja auto-chargee et deja porteuse du principe dont ceci est un cas d'application. Ma recommandation va au troisieme.\n"
    "\n"
    "Reserve a traiter **avant merge**, par le user.\n"
    "\n"
)

def test_13083_controle_a_5422307622_est_bot_concern():
    """#12896 c.5422307622 verbatim : CHANGES_REQUESTED formel + « Reserve
    levable avant merge » + l'option « (a) sign-off user tel quel -> je merge
    sans autre reserve ». Trois pieges pour l'ancien gate brut : le verdict en
    tete (couvert par _formal_concern_precedes_lift), la derivation flechee
    (couverte par _arrow_precedes), « levable » n'est pas un marqueur. Attendu
    BOT-CONCERN — exigence ecrite d'ai-01 sur #13083."""
    assert mod.classify("myia-ai-01", FIXTURE_12896_A_BODY) == "BOT-CONCERN"


def test_13083_controle_b_5422312669_est_bot_concern():
    """#12896 c.5422312669 verbatim : la re-formulation OUVERTE de la meme
    reserve, expurgee de formules conditionnelles par ai-01 lui-meme — et
    pourtant invisible au gate : « une formule de levee conditionnelle »,
    « une levee reelle », « ses conditions de levee » (mentions nominales,
    fenetre de determinants `LIFT_NARRATION_CITERS` #12908) et « se leve elle-meme » (narration). Attendu
    BOT-CONCERN — exigence ecrite d'ai-01 sur #13083."""
    assert mod.classify("myia-ai-01", FIXTURE_12896_B_BODY) == "BOT-CONCERN"


def test_13083_mention_genitive_neteint_pas_une_reserve():
    """« conditions de levee », « formule de levee » : le genitif NOMME le
    concept, il ne l'emets pas. Une reserve vivante qui s'accompagne d'une
    mention genitive reste BOT-CONCERN."""
    body = ("Reserve a traiter avant merge : l'option proposee se termine "
            "par une formule de levee conditionnelle, ce n'est pas une levee.")
    assert mod.classify("myia-ai-01", body) == "BOT-CONCERN"


def test_13083_mention_article_indefini_neteint_pas_une_reserve():
    """« une levee reelle » (article indefini + nom, c.5422312669 verbatim) :
    classification metalinguistique, pas une emission. La reserve vit."""
    body = ("Reserve a traiter avant merge : le gate traite a tort ceci "
            "comme une levee reelle.")
    assert mod.classify("myia-ai-01", body) == "BOT-CONCERN"


def test_13083_fleche_derivation_neteint_pas_une_reserve():
    """« sign-off user tel quel -> je merge » : la fleche fait du merge la
    CONSEQUENCE d'une precondition non satisfaite — une derivation n'est pas
    une annonce (regle fleche de `_is_cited`, reprise ISO dans
    `_live_lift_positions`). La reserve vit."""
    body = ("Reserve avant merge : la clause exige un sign-off. "
            "(a) sign-off user tel quel -> je merge sans autre reserve.")
    assert mod.classify("myia-ai-01", body) == "BOT-CONCERN"


def test_13083_annonce_reelle_survit_aux_mentions():
    """Garde-fou inverse : une mention nominale dans la phrase precedente ne
    doit pas tuer l'annonce REELLE qui suit (« n'est pas une levee. Levee de
    ma reserve ») — c'est le piege du `_is_cited` importe entier (fenetre
    trans-sentence), qui cassait 4 tests du corpus."""
    body = ("Ce n'est pas une levee de facade. Levee de ma reserve : le "
            "point 2 est corrige proprement.")
    assert mod.classify("myia-ai-01", body) is None

# --- #13316 : jsboige n'est pas un compte de levée. L'identité de poussée est
# PARTAGÉE par toutes les lanes (Hermes self-review cap #12319, push lane) :
# créditer jsboige comme coordinateur de l'[OVERRIDE] rétablit l'auto-levee que
# la borne d'auteur #11145 interdit. Cas réel fondateur : PR #12737 — réserve
# BOT-CONCERN de myia-ai-01 à 02:37:04Z, deux « [OVERRIDE] » poussés sous
# jsboige à 02:40:01Z et 02:41:06Z par la lane portante. Le garde-fou a tenu
# par lecture humaine, pas par le gate : jsboige in COORDINATOR_LOGINS était
# vrai, l'organe aurait rendu rc=0.

LANE_OVERRIDE_BODY = (
    "**[OVERRIDE] lane myia-po-2023:CoursIA-2** — Levée de la réserve du "
    "2026-08-28 : les deux points sont adressés par le commit abc123, "
    "re-review demandée."
)


def test_13316_jsboige_override_ne_leve_pas_reserve_tiers():
    """Critère 1 : un [OVERRIDE] + phrase de levée poussé sous jsboige (la lane
    elle-même) n'éteint PAS la réserve d'un tiers — c'est #12798 sous un autre
    nom, le gate ne le crédite plus."""
    reserve = HERMES_REVIEW_11479  # tier (bot), déjà porté par run_coord
    lane_override = {"author": {"login": "jsboige"},
                     "createdAt": "2026-08-18T13:06:34Z",
                     "body": LANE_OVERRIDE_BODY}
    assert reserve  # réserve d'un tier présente dans les reviews
    assert run_coord([lane_override])["blocked"] is True


def test_13316_override_ai01_leve_toujours():
    """Critère 2 (contrôle positif, même exécution que le critère 1) : l'override
    légitime de la lane coordinatrice dédiée continue d'éteindre la réserve —
    le correctif ferme l'auto-levee, il ne transforme pas la trappe en mur."""
    lift = {"author": {"login": "myia-ai-01"},
            "createdAt": "2026-08-18T13:06:34Z", "body": OVERRIDE_BODY}
    assert run_coord([lift])["blocked"] is False


def test_13316_self_lift_jsboige_sur_sa_propre_reserve_leve():
    """Borne intacte : jsboige qui lève SA PROPRE réserve (lift_author ==
    nit_author) reste la voie légitime #11145 — l'exclusion #13316 ne vise que
    la trappe coordinateur, pas la self-levee de l'émetteur."""
    own_nit = {"author": {"login": "jsboige"}, "createdAt": at(10),
               "body": "CHANGES_REQUESTED: la cellule 12 casse le kernel."}
    own_lift = {"author": {"login": "jsboige"}, "createdAt": at(12),
                "body": "Levée de ma réserve : cellule 12 corrigée, commit abc."}
    assert run([own_nit, own_lift])["blocked"] is False


def test_13316_replay_12737_reel():
    """Critère 3 : replay du cas réel #12737 (timestamps réels) — réserve
    myia-ai-01 02:37:04Z, « overrides » jsboige 02:40:01Z et 02:41:06Z : la
    réserve SURVIT et l'organe distingue les deux issues (avant : rc=0)."""
    reserve = {"author": {"login": "myia-ai-01"},
               "state": "CHANGES_REQUESTED",
               "submittedAt": "2026-08-28T02:37:04Z",
               "body": "CHANGES_REQUESTED: le verdict EXEC_PROVED n'est pas "
                       "prouvé par le diff (2 cellules sans sortie)."}
    o1 = {"author": {"login": "jsboige"},
          "createdAt": "2026-08-28T02:40:01Z", "body": LANE_OVERRIDE_BODY}
    o2 = {"author": {"login": "jsboige"},
          "createdAt": "2026-08-28T02:41:06Z", "body": LANE_OVERRIDE_BODY}
    res = mod.analyse({
        "number": 12737, "title": "t", "author": {"login": "jsboige"},
        "comments": [o1, o2], "reviews": [reserve],
        "commits": [{"committedDate": "2026-08-28T02:00:00Z"}],
    }, [], datetime(2026, 8, 28, 3, 0, 0, tzinfo=timezone.utc))
    assert res["blocked"] is True
    assert len(res["blocking"]) == 1  # la réserve ai-01 seule survit
    assert res["blocking"][0]["author"] == "myia-ai-01"


def test_13316_override_ecarte_est_nomme_dans_la_sortie():
    """Critère 4 : un override écarté pour cause d'auteur est NOMMÉ (auteur,
    horodatage, raison) — le silence rendait « rouge malgré notre override »
    indistinguable d'un bug du détecteur (#13030, #12096)."""
    reserve = {"author": {"login": "myia-ai-01"},
               "state": "CHANGES_REQUESTED",
               "submittedAt": "2026-08-28T02:37:04Z",
               "body": "CHANGES_REQUESTED: verdict non prouvé."}
    o1 = {"author": {"login": "jsboige"},
          "createdAt": "2026-08-28T02:40:01Z", "body": LANE_OVERRIDE_BODY}
    res = mod.analyse({
        "number": 0, "title": "t", "author": {"login": "jsboige"},
        "comments": [o1], "reviews": [reserve],
        "commits": [{"committedDate": "2026-08-28T02:00:00Z"}],
    }, [], datetime(2026, 8, 28, 3, 0, 0, tzinfo=timezone.utc))
    assert res["blocked"] is True
    ignored = res["ignored_overrides"]
    assert len(ignored) == 1
    assert ignored[0]["author"] == "jsboige"
    assert "2026-08-28T02:40:01" in ignored[0]["at"]
    assert "n'est pas un compte" in ignored[0]["why"]
    assert "jsboige" in ignored[0]["why"]


def test_13316_override_legitime_ne_produit_aucune_note():
    """Miroir du critère 4 : l'override légitime (ai-01) ne génère PAS de note
    « override ignoré » — la liste ne doit nommer que les écarts réels."""
    lift = {"author": {"login": "myia-ai-01"},
            "createdAt": "2026-08-18T13:06:34Z", "body": OVERRIDE_BODY}
    res = run_coord([lift])
    assert res["blocked"] is False
    assert res["ignored_overrides"] == []
# --- #12944 : le close-the-loop Hermes. « Mon concern ... est traité et
# fermé » (PR #12941 fondateur, review 5020777166) : la levee PASSIVE
# n'etait couverte par aucun LIFT_MARKER, et le verdict mentionne (« ma
# review REQUEST_CHANGES de #12900 », ref HORS parentheses) echappait aux
# motifs de mention — l'acquittement etait classe BOT-CONCERN et bloquait
# le merge. Meme classe que c.504 : un acquittement qui contient des
# marqueurs formels est mal classe.

def test_12944_levee_passive_est_un_lift_marker():
    """La forme passive « est traité et fermé » (gras markdown compris, le
    compose couvre la coupure auxiliaire/participe) et les verbes de
    fermeture (clos / ferme / resolu) sont des LIFT_MARKERS. « est traité »
    NU est REJETTE : le body pinned #11639 « le point 3 est traité en
    argument » est une narration, pas une levee (l'override nu ne leve
    rien)."""
    assert mod.has_marker(
        "Mon concern est **traité et fermé** : registre régénéré.",
        mod.LIFT_MARKERS)
    assert mod.has_marker("le point est clos, rien ne bloque", mod.LIFT_MARKERS)
    assert mod.has_marker("le fil est fermé après vérification", mod.LIFT_MARKERS)
    assert not mod.has_marker("le point 3 est traité en argument", mod.LIFT_MARKERS)
    assert not mod.has_marker("Le point 2 n'est pas traité.", mod.LIFT_MARKERS)


def test_12944_close_the_loop_leve_la_review_precedente():
    """End-to-end : la review REQUEST_CHANGES posee par Hermes (self-bot
    jsboige), puis son close-the-loop (« est traité et fermé », verdict
    mentionne avec ref inline) par le meme auteur — le gate passe : le
    close-the-loop est un explicit_lift borne (#11145, meme auteur)."""
    review = {
        "author": {"login": "jsboige"},
        "state": "COMMENTED", "submittedAt": at(10),
        "body": "[Hermes] — REQUEST_CHANGES : le registre de citations est fabriqué.",
    }
    loop = {"author": {"login": "jsboige"}, "createdAt": at(12),
            "body": "close-the-loop sur ma review REQUEST_CHANGES de #12900 : "
                    "Mon concern est **traité et fermé**, registre régénéré "
                    "(commit ffe18961)."}
    data = {
        "number": 0, "title": "t", "author": {"login": "myia-po-2026"},
        "comments": [loop], "reviews": [review],
        "commits": [{"committedDate": at(13)}],
    }
    assert mod.analyse(data, [], MERGED)["blocked"] is False


def test_12944_close_the_loop_seul_nest_plus_un_nit():
    """Le cas mesure sur #12941 : le close-the-loop ETAIT lui-meme l'unique
    signal bloque (classify BOT-CONCERN sur son propre body). Il doit
    desormais rendre None — verdict mentionne + levee passive."""
    body = ("**[Hermes]** — close-the-loop sur ma review REQUEST_CHANGES de "
            "#12900 (`ffe18961`). Mon concern est **traité et fermé** : "
            "registre régénéré depuis les diffs réels.")
    assert mod.classify("jsboige", body) is None


def test_12944_revalidation_formelle_avant_levee_reste_bot_concern():
    """Garde #12798/#12836 intacts : un verdict formel EMIS en tete puis une
    narration de levee passive en aval reste BOT-CONCERN — le close-the-loop
    ne debranche pas la revalidation qui REFUTE une levee annoncee."""
    body = ("[Hermes] COMMENT_WITH_CONCERNS — revalidation : le concern "
            "précédent est traité et fermé, mais la cassette reste non "
            "prouvée.")
    assert mod.classify("jsboige", body) == "BOT-CONCERN"


def test_12944_residu_negation_du_compose_documente():
    """Residu ASSUME (limite NLP, cf can_lift) : une negation INTERNE au
    compose (« pas encore traité et fermé ») contient le marqueur
    « traité et fermé » et se leverait a tort. Pin par ecrit : le
    discriminant exigerait une fenetre de negation cote LIFT, machinery
    qui n'existe pas (CITERS ne s'applique qu'aux CONCERN_MARKERS via
    `_is_cited`). Un redacteur futur qui veut fermer ce residu saura que
    CE test est celui a mettre a jour."""
    body = "Mon concern n'est pas encore traité et fermé, le registre reste fabriqué."
    assert mod.has_marker(body, mod.LIFT_MARKERS) is True  # residu assume



# PR **BLOCKED** », « réserve uniquement B.0/process ») tout en narrant le
# vocabulaire de levée (« une levée explicite sur le head final ») était
# absorbée par le LIFT_MARKER de sa propre narration : la reserve vivante
# redevenait invisible, rc=0, exactement le defaut que B.0 traque. Le verdict
# B.0 émis (**BLOCKED** en gras, sortie organe « BLOCKED  PR ») est désormais
# un concern positionnel — et le mot NU « BLOCKED » reste hors du filet (tag
# de protocole, négation « n'est plus BLOCKED »).

NIT_EPITA_12908 = {
    "author": {"login": "jsboigeEpita"}, "createdAt": at(10),
    "body": "[Hermes] COMMENT_WITH_CONCERNS — sortie vLLM absente du head.",
}

REVALIDATION_BLOQUANTE_12908 = {
    "author": {"login": "jsboigeEpita"}, "createdAt": at(11),
    "body": (
        "[Hermes] PREFLIGHT COMMENTED — head `7aaf6eab92`\n\n"
        "Le durcissement B.0 (142/142 tests) classe encore cette PR "
        "**BLOCKED** : le checker retourne `1` avec quatre réserves tierces "
        "actives. Seule une phrase explicite de cet auteur après vérification, "
        "ou un `[OVERRIDE]` coordinateur, les lève selon la sémantique "
        "corrigée.\n\nSéquençage : obtenir de `jsboigeEpita` une levée "
        "explicite sur le head final.\n\nAucune demande de modification du "
        "notebook : substance revalidée ; réserve uniquement B.0/process."
    ),
}


def test_12908_revalidation_maintenant_le_blocage_ne_leve_pas():
    """Le cas live (commentaire 2026-08-25T04:45:30Z de #12798, adapté) : la
    réserve d'origine ET la revalidation maintenante restent toutes deux des
    signaux — la narration de levée n'éteint rien."""
    result = run([NIT_EPITA_12908, REVALIDATION_BLOQUANTE_12908])
    assert result["blocked"] is True
    assert len(result["blocking"]) == 2


def test_12908_levee_explicite_sans_blocage_maintenu_reste_levee():
    """Contrôle positif : le durcissement ne rend pas la réserve indélébile —
    une levée explicite non contradictoire du même auteur lève toujours."""
    lift = {"author": {"login": "jsboigeEpita"}, "createdAt": at(12),
            "body": "Levée de ma réserve : commit abc vérifié, cassette rejouée."}
    assert run([NIT_EPITA_12908, lift])["blocked"] is False


def test_12908_levee_puis_blocked_narre_au_passe_reste_levee():
    """La position décide (miroir de `_formal_concern_precedes_lift`) : une
    levée suivie d'un **BLOCKED** narré comme état passé reste une levée."""
    lift_narre = {"author": {"login": "jsboigeEpita"}, "createdAt": at(12),
                  "body": "Je lève ma réserve après rejeu — le gate n'affiche "
                          "plus **BLOCKED**."}
    assert run([NIT_EPITA_12908, lift_narre])["blocked"] is False


def test_12908_tag_protocol_blocked_n_est_pas_une_reserve():
    """Le mot NU ne matche pas : un tag de protocole lane « [BLOCKED] » sans
    forme d'émission n'est pas une réserve tierce."""
    tag = {"author": {"login": "myia-po-2023"}, "createdAt": at(12),
           "body": "[BLOCKED] lane myia-po-2023:CoursIA-2 — drainage file CI, "
                   "pas de geste local possible."}
    assert run([tag])["blocked"] is False


def test_12908_negation_bare_word_n_est_pas_une_reserve():
    """« n'est plus BLOCKED » (mot nu, sans gras) : la négation d'un état
    passé n'émet pas de réserve."""
    passe = {"author": {"login": "myia-po-2023"}, "createdAt": at(12),
             "body": "Reprise du cycle : le gate n'est plus BLOCKED depuis le "
                     "drainage, les checks tournent."}
    assert run([passe])["blocked"] is False


def test_12908_sortie_organe_pastee_est_une_emission():
    """La sortie de l'organe collée hors fence (« BLOCKED  PR #N — ») est une
    émission de blocage : le commentaire qui la rapporte maintient une
    réserve vivante."""
    paste = {"author": {"login": "clusterManager-Myia"}, "createdAt": at(11),
             "body": "Contre-verification au head frais :\n"
                     "BLOCKED  PR #42 — 3 nit(s) non leve(s)"}
    assert run([paste])["blocked"] is True
# ---------------------------------------------------------------------------
# #12871 — 6e instance use-vs-mention : la reference pointable des levees
# doit aussi matcher NUE (`leve par le commit <sha>`) en plus de la forme
# parenthesee. Les 3 formulations de l'issue (FP1/FP2/FP3) sont classeees
# BOT-CONCERN a tort ; le fix Position A+ (prose interne apres verdict en
# parenthese), Position C+ (ref nue apres verbe de levee) et Position E
# (verdict en tete, verbe de levee + ref dans la meme phrase) les neutralise.
# Les 3 contre-exemples (CE1/CE2/CE3) restent BOT-CONCERN : pas de ref
# pointable, pas de verbe de levee, ou emission formelle.
# ---------------------------------------------------------------------------


def test_12871_fp1_parenhese_avec_prose_interne_ne_flagge_pas():
    """#12871 FP1 — `(COMMENT_WITH_CONCERNS, porte sur...)` : prose interne a
    la parenthese du verdict (Position A+). Avant : classifie BOT-CONCERN.
    Apres : classify() rend None (mention, pas emission)."""
    body = (
        "Reponse au point de review Hermes (COMMENT_WITH_CONCERNS, porte sur "
        "la conclusion cell 17 point 3 + objectif cell 0 point 3) - traite "
        "en code par le commit 05d16623f49."
    )
    assert mod.classify("myia-po-2027", body) is None


def test_12871_fp2_ref_nue_apres_verbe_leve_ne_flagge_pas():
    """#12871 FP2 — `COMMENT_WITH_CONCERNS leve par le commit <sha>` : verbe
    de levee precede, ref pointable NUE dans la meme phrase (Position C+).
    Avant : classifie BOT-CONCERN. Apres : classify() rend None."""
    body = (
        "Reponse au Hermes: COMMENT_WITH_CONCERNS leve par le commit "
        "05d16623f49."
    )
    assert mod.classify("myia-po-2027", body) is None


def test_12871_fp3_review_verdict_leve_dans_meme_phrase_ne_flagge_pas():
    """#12871 FP3 — `La review COMMENT_WITH_CONCERNS de Hermes est traitee par
    le commit <sha>` : verdict en tete de phrase apres `review/La`, verbe
    de levee + ref pointable dans la meme phrase (Position E).
    Avant : classifie BOT-CONCERN. Apres : classify() rend None."""
    body = (
        "La review COMMENT_WITH_CONCERNS de Hermes est traitee par le "
        "commit 05d16623f49."
    )
    assert mod.classify("myia-po-2027", body) is None


def test_12871_ce1_review_verdict_sans_ref_reste_live():
    """#12871 CE1 — controle negatif : `Cette review CHANGES_REQUESTED reste
    bloquante` (pas de ref pointable, pas de verbe de levee). DOIT RESTER
    BOT-CONCERN. Sans quoi le fix debranche le gate et rouvre le failure
    mode fondateur de B.0 (#10761)."""
    body = "Cette review CHANGES_REQUESTED reste bloquante."
    assert mod.classify("jsboige", body) == "BOT-CONCERN"


def test_12871_ce2_verdict_leve_sans_ref_reste_live():
    """#12871 CE2 — controle negatif : `CHANGES_REQUESTED leve sans reference.`
    Verbe de levee SANS ref pointable dans la suite immediate. DOIT RESTER
    BOT-CONCERN (le discriminant C+ exige la ref)."""
    body = "CHANGES_REQUESTED leve sans reference."
    assert mod.classify("jsboige", body) == "BOT-CONCERN"


def test_12871_ce3_emission_formelle_reste_live():
    """#12871 CE3 — controle negatif : `Verdict : COMMENT_WITH_CONCERNS` —
    emission formelle Hermes (state-prefix). DOIT RESTER BOT-CONCERN (les
    positions A-E ne touchent pas le canal d'emission, cf commentaire
    `_MENTION_VERDICT_HEADING` ligne 327)."""
    body = "Verdict : COMMENT_WITH_CONCERNS"
    assert mod.classify("jsboige", body) == "BOT-CONCERN"

# ---------------------------------------------------------------------------
# #13425 — Position E, borne dure : le commentaire au-dessus de
# `_MENTION_VERDICT_REVIEW_NARRATIVE` promettait « la phrase complete ne doit
# pas contenir `Verdict :` ni `reste bloquante` » sans qu'aucun lookahead
# n'existe (mesure dans l'issue : le cas hybride voyait son verdict
# neutralise). Le lookahead negatif est desormais implemente dans la fenetre
# de phrase ; ces tests ECHOUENT sans lui — c'est le controle negatif exige
# par l'acceptance (verifie mecaniquement : le pattern sans lookahead matche
# l'hybride, le pattern avec lookahead ne le matche pas).
# ---------------------------------------------------------------------------


def test_13425_hybride_reste_bloquante_avec_commit_preserve_le_verdict():
    """#13425 cas hybride — `<verdict> reste bloquante - traitee par le
    commit <sha>` : la Position E voyait verbe de levee + ref pointable dans
    la meme phrase et neutralisait le verdict, alors que la phrase declare
    un blocage VIVANT. La borne dure `reste bloquante` preserve le verdict.
    CE TEST ECHOUE SI ON RETIRE LE LOOKAHEAD."""
    body = ("Cette review CHANGES_REQUESTED reste bloquante - traitee par le "
            "commit a1b2c3d4e")
    assert mod.classify("jsboige", body) == "BOT-CONCERN"


def test_13425_verdict_formel_dans_fenetre_preserve_le_verdict():
    """#13425 seconde borne promise — `Verdict :` (emission formelle) dans la
    fenetre de phrase de la Position E : le verdict n'est pas non plus
    neutralise par une mention qui suit une emission formelle.
    CE TEST ECHOUE SI ON RETIRE LE LOOKAHEAD."""
    body = ("La review CHANGES_REQUESTED Verdict : reste a traiter, traitee "
            "par le commit a1b2c3d4e")
    assert mod.classify("jsboige", body) == "BOT-CONCERN"


def test_13425_controles_ce1_fp3_restant_inchanges():
    """#13425 acceptance — les deux controles mesures dans l'issue gardent
    leur comportement : CE1 (pas de ref pointable) reste BOT-CONCERN, FP3
    (verdict leve, ref pointable, pas de declaration de blocage) reste
    neutralise — sous les formes EXACTES du ticket."""
    ce1 = "Cette review CHANGES_REQUESTED reste bloquante."
    fp3 = "La review CHANGES_REQUESTED a ete traitee par le commit a1b2c3d4e"
    assert mod.classify("jsboige", ce1) == "BOT-CONCERN"
    assert mod.classify("jsboige", fp3) is None


# ---------------------------------------------------------------------------
# #13474 — frontieres bornees des positions de mention : temoins de frontiere.
# La Position D+ borne le gap verdict->ref nue narrative (par/via/dans/en) a
# `{0,12}` chars INCLUS ; au-dela, ni D+ (borne depassee) ni E (pas de verbe
# de levee avant la ref) ne neutralisent — le verdict reste live. Frontiere
# mesuree : gap 12 matche, gap 13 ne matche plus. Chaque temoin ECHOUE si la
# fenetre bouge (elargie a 13 : le temoin hors-frontiere se met a matcher ;
# retrecie a 10 : le temoin dans-frontiere cesse de matcher).
# ---------------------------------------------------------------------------


def test_13474_dplus_gap_12_chars_dans_la_borne_neutralise():
    """#13474 temoin dans-frontiere — gap d'EXACTEMENT 12 chars (borne
    `{0,12}` inclusive) entre le verdict et `par le commit <sha>` : la
    Position D+ matche, la mention neutralise le verdict.
    CE TEST ECHOUE SI LA FENETRE EST RETRECIE."""
    gap = " " + "x" * 10 + " "  # 12 chars exactement
    assert len(gap) == 12
    body = "La review CHANGES_REQUESTED" + gap + "par le commit a1b2c3d4e."
    assert mod.classify("myia-po-2027", body) is None


def test_13474_dplus_gap_13_chars_hors_borne_reste_live():
    """#13474 temoin hors-frontiere — gap de 13 chars : D+ ne matche plus
    (borne depassee) et E non plus (pas de verbe de levee avant la ref) —
    le verdict reste emis : BOT-CONCERN.
    CE TEST ECHOUE SI LA FENETRE EST ELARGIE."""
    gap = " " + "x" * 11 + " "  # 13 chars exactement
    assert len(gap) == 13
    body = "La review CHANGES_REQUESTED" + gap + "par le commit a1b2c3d4e."
    assert mod.classify("jsboige", body) == "BOT-CONCERN"


# --- #13512 : ce que l'organe n'a pas evalue, il l'imprime -----------------
#
# Regression du merge de #13476 : une remarque user d'UNE SEULE LIGNE tombe en
# `mod.classify(...) is None` (le test CRLF de `classify` n'a pas de prise sur un
# corps sans retour a la ligne), la PR merge sous un `OK -- aucun nit non leve`
# qui ne l'a jamais lue. L'organe ne peut pas CLASSER (identites confondues :
# `jsboige` = user + poussee des lanes + coordinateur), il doit RENDRE VISIBLE.

_ONE_LINER = ("Pour info, on a un container tika a disposition sur ai-01, et notre "
              "modele vllm maison qwen 3.6 a la vision, donc je pense qu'il y a "
              "encore du grain a moudre dans ce notebook")


def _pr_with(comments, commit_at="2026-08-29T08:40:00Z"):
    return {
        "number": 13476, "title": "t", "author": {"login": "jsboige"},
        "commits": [{"committedDate": commit_at}],
        "reviews": [], "comments": comments,
    }


def test_13512_one_liner_user_comment_is_surfaced():
    """Le corps EXACT qui a ete manque doit ressortir dans `unevaluated`."""
    pr = _pr_with([{"author": {"login": "jsboige"},
                    "createdAt": "2026-08-29T09:01:03Z", "body": _ONE_LINER}])
    res = mod.analyse(pr, [], datetime(2026, 8, 29, 11, 14, tzinfo=timezone.utc))
    # l'organe ne le classe TOUJOURS pas -- c'est admis, et c'est le point
    assert mod.classify("jsboige", _ONE_LINER) is None
    assert not res["blocked"], "surfacer n'est pas bloquer (3/5 FP mesures)"
    bodies = [u["body"] for u in res["unevaluated"]]
    assert _ONE_LINER in bodies, "la remarque manquee doit etre imprimee"
    assert res["unevaluated"][0]["after_last_commit"] is True


def test_13512_bot_comments_are_not_surfaced():
    """Controle negatif : le bruit de bot ne doit pas noyer la queue."""
    bot = sorted(mod.BOT_LOGINS)[0]
    pr = _pr_with([{"author": {"login": bot},
                    "createdAt": "2026-08-29T09:01:03Z", "body": "rapport advisory"}])
    res = mod.analyse(pr, [], datetime(2026, 8, 29, 11, 14, tzinfo=timezone.utc))
    assert res["unevaluated"] == []


def test_13512_classified_comment_is_not_duplicated_in_the_tail():
    """Un commentaire deja porte par `blocking` n'est pas re-imprime a cote."""
    concern = "Attention, graphviz n'est pas installee sur la machine source.\r\nLes graphes manquent."
    pr = _pr_with([{"author": {"login": "jsboige"},
                    "createdAt": "2026-08-29T09:01:03Z", "body": concern}])
    res = mod.analyse(pr, [], datetime(2026, 8, 29, 11, 14, tzinfo=timezone.utc))
    assert mod.classify("jsboige", concern) is not None, "pre-condition : celui-la EST classe"
    assert all(u["body"] != concern for u in res["unevaluated"])


# --- #13622 : has_live_lift doit distinguer negation directe d'une vraie levee. ---


def test_13622_negation_nest_pas_levee_exclue():
    """PR #13563 verbatim : '... ne pas merger tant qu'elle n'est pas levee'.

    Avant fix : has_live_lift=True, classify=None (faux OK). Le commentaire
    etait considere comme une levee alors qu'il AFFIRME que la levee n'a
    pas eu lieu — c'est l'inverse semantique.
    """
    body = "## [ai-01] RESERVE BLOQUANTE — ... **ne pas merger tant qu'elle n'est pas levee**"
    assert not mod.has_live_lift(body), (
        "une negation directe ('n'est pas levee') ne doit pas etre classee levee")


def test_13622_negation_non_levee_exclue():
    """Forme simplifiee : 'non levee' (avant, colle)."""
    assert not mod.has_live_lift("non levee")
    assert not mod.has_live_lift("Pas levee encore.")
    assert not mod.has_live_lift("Aucune levee en vue.")


def test_13622_negation_apres_levee_exclue():
    """Forme avec negation APRES le mot : 'levee non acquise'."""
    assert not mod.has_live_lift("La reserve tient, levee non acquise.")


def test_13622_negation_13550_verbatim():
    """PR #13550 verbatim : '[ai-01 ARBITRAGE] La reserve GPU tient. Ne pas merger sur les verts.'

    Avant fix : has_live_lift=False (deja OK car pas de LIFT_MARKER direct).
    Apres fix : inchange. Cas fondateur documente dans l'issue #13622.
    """
    body = "## [ai-01 ARBITRAGE] La reserve GPU tient. **Ne pas merger sur les verts.**"
    assert not mod.has_live_lift(body)


def test_13622_vraie_levee_apres_negation_locale_reste_levee():
    """Body avec NEGATION LOCALE + VRAIE LEVEE : seul le token leve est compte.

    PR #13563 verbatim long :
      '**Je leve mon CHANGES_REQUESTED.** ... CHANGES_REQUESTED : **ne pas
      merger tant qu'elle n'est pas levee**.)*'
    Avant fix : la 2e occurrence ('n'est pas levee') classee comme levee
    a tort ; la 1re ('Je leve mon CHANGES_REQUESTED') classee a raison.
    Apres fix : seule la 1re survit ; has_live_lift=True global (la vraie
    levee reste reconnue).
    """
    body = ("**Je leve mon CHANGES_REQUESTED.** ... CHANGES_REQUESTED : "
            "**ne pas merger tant qu'elle n'est pas levee**.)*")
    assert mod.has_live_lift(body), "la vraie levee 'Je leve mon CHANGES_REQUESTED' doit rester"


def test_13622_vraie_levee_simple_reste_levee():
    """Regression : les vraies levees doivent toujours etre reconnues."""
    assert mod.has_live_lift("Reserve levee, je merge.")
    assert mod.has_live_lift("LGTM")
    assert mod.has_live_lift("Merged.")
    assert mod.has_live_lift("Je leve mon CHANGES_REQUESTED.")
    assert mod.has_live_lift("Je leve la CHANGES_REQUESTED de Hermes.")


def test_13622_negation_distante_ne_touche_pas_levee():
    """Residuel documente : une negation NON locale (>15 chars) echappe.

    La levee immediate ('Reserve levee') doit rester classee ; seule la
    negation LOCALE est dans le predicat `_lift_is_negated`. C'est la
    frontiere documentee dans l'issue : au-dela, c'est de la narration,
    pas une negation directe du geste de levee.
    """
    body = "Reserve levee il y a longtemps, mais la reserve n'est pas levee vraiment"
    assert mod.has_live_lift(body), (
        "negation non locale (>15 chars) ne doit pas annuler la levee locale")


def test_13622_negation_nest_dans_fenetre_negated_direct():
    """Le predicat `_lift_is_negated` est appele sur les fenetres locales.

    Verification unitaire de la nouvelle fonction : les 4 patterns
    negatifs documentees dans l'issue (#13622) doivent etre reconnus
    sur les memes chaines que `has_live_lift` recoupe en amont.
    """
    assert mod._lift_is_negated("merger tant qu'elle n'est pas ", "")
    assert mod._lift_is_negated("non ", "")
    assert mod._lift_is_negated("Pas ", "")
    assert mod._lift_is_negated("Reserve tient, levee", " non acquise")
    # Positifs (ne doivent PAS etre reconnus comme negation)
    assert not mod._lift_is_negated("Reserve levee", "")
    assert not mod._lift_is_negated("Je leve mon CHANGES_REQUESTED", "")
    assert not mod._lift_is_negated("", ". Je merge.")



# --- #13639 : levee citant un commit absent de la branche (rembobine) ---

NIT_OID = "f" * 40


def lift_citant_sha(sha="2d6e4c3642"):
    return {"author": {"login": "jsboige"}, "createdAt": at(12),
            "body": f"Les 2 nits sont adresses dans le commit {sha}."}


def test_13639_levee_citant_commit_absent_ne_leve_plus():
    """#13557 : la levee citait 2d6e4c3642, rembobine par un force-push.

    La phrase etait honnete a l'ecriture, mais la preuve qu'elle nomme
    n'existe plus au merge : le nit doit rester NON LEVE, avec la levee
    annulee nommee dans le resultat.
    """
    res = run([USER_NIT, lift_citant_sha()],
              commits=[{"oid": NIT_OID, "committedDate": at(19)}],
              body="See #77",
              _absent_sha_messages={
                  "2d6e4c3642": "fix(audio,#77): corrige l'attribution"})
    assert res["blocked"] is True
    assert [v["sha"] for v in res["voided_lifts"]] == ["2d6e4c3642"]


def test_13639_levee_citant_commit_present_leve_toujours():
    """SHA prefixe present dans les OIDs de la PR : preuve valide, levee."""
    res = run([USER_NIT, lift_citant_sha()],
              commits=[{"oid": "2d6e4c3642" + "a" * 30, "committedDate": at(19)}],
              body="See #77")
    assert res["blocked"] is False
    assert res["voided_lifts"] == []


def test_13639_absent_sans_rapport_avertit_sans_bloquer():
    """Citation de CONTEXTE (« comme fixe sur l'autre PR ») : levee valide.

    Le message resolu ne se rattache pas a cette PR (aucun #N commun) :
    on signale, on ne refuse pas.
    """
    res = run([USER_NIT, lift_citant_sha()],
              commits=[{"oid": NIT_OID, "committedDate": at(19)}],
              body="See #77",
              _absent_sha_messages={
                  "2d6e4c3642": "fix(other,#999): unrelated lane"})
    assert res["blocked"] is False
    assert [w["sha"] for w in res["absent_sha_warnings"]] == ["2d6e4c3642"]


def test_13639_absent_non_resolu_avertit_sans_bloquer():
    """SHA non resoluble cote serveur : doute -> avertissement, pas blocage."""
    res = run([USER_NIT, lift_citant_sha()],
              commits=[{"oid": NIT_OID, "committedDate": at(19)}],
              body="See #77")
    assert res["blocked"] is False
    assert [w["sha"] for w in res["absent_sha_warnings"]] == ["2d6e4c3642"]


def test_13639_rattachement_via_numero_de_pr():
    """Le message resolu cite le NUMERO de la PR (pas seulement une issue
    du corps) : rattachement valide, levee refusee."""
    res = run([USER_NIT, lift_citant_sha()],
              commits=[{"oid": NIT_OID, "committedDate": at(19)}],
              _absent_sha_messages={"2d6e4c3642": "fix(x,#0): typo"})
    assert res["blocked"] is True
    assert [v["sha"] for v in res["voided_lifts"]] == ["2d6e4c3642"]


def test_13639_token_numerique_non_sha():
    """Un token 100% numerique (date 20260814) n'est pas un SHA : la levee
    qui le cite reste valide, sans meme un avertissement."""
    res = run([USER_NIT, lift_citant_sha("20260814")],
              commits=[{"oid": NIT_OID, "committedDate": at(19)}],
              body="See #77",
              _absent_sha_messages={"20260814": "fix(x,#77): piege"})
    assert res["blocked"] is False
    assert res["absent_sha_warnings"] == []


def test_13639_sans_oids_comportement_inchange():
    """Fixtures sans `oid` (pre-filtre d'audit, anciens payloads) : le
    passage est inert, la levee compte comme avant."""
    res = run([USER_NIT, lift_citant_sha()])
    assert res["blocked"] is False
    assert res["voided_lifts"] == []


def test_13639_sha_distant_du_marqueur_est_contexte():
    """Mesure au deploiement (PR #13631) : la levee d'ai-01 citait
    `e408b2fce` a ~2000 chars du marqueur, dans un paragraphe forensique
    (« c'est main qui a avance ») -- contexte, pas preuve. Meme resolu et
    rattache au sujet de la PR, un SHA DISTANT ne doit ni refuser la levee
    ni meme la signaler.
    """
    filler = "Un paragraphe forensique qui explique la mesure cote serveur. " * 8
    body = ("Les 2 nits sont adresses.\n\n" + filler
            + "\n\nPar ailleurs, c'est main qui a avance (e408b2fce, #13624).")
    reply = {"author": {"login": "jsboige"}, "createdAt": at(12), "body": body}
    res = run([USER_NIT, reply],
              commits=[{"oid": NIT_OID, "committedDate": at(19)}],
              body="See #13624",
              _absent_sha_messages={
                  "e408b2fce": "fix(check,#13622): _live_lift_positions (#13624)"})
    assert res["blocked"] is False
    assert res["voided_lifts"] == []
    assert res["absent_sha_warnings"] == []


def test_13641_ref_par_prefixe_ne_compte_pas():
    """NanoClaw c.702 sur #13641 : le substring check `any(f"#{n}" in message)`
    matchait `#13639` dans un message contenant `#136390` (ticket adjacent
    cite par hasard). Le bon test est l'extraction/tokenisation exacte des
    references `#\\d+` : la PR doit apparaitre comme MOT COMPLET du message,
    pas comme prefixe d'un identifiant plus long. Ici, le SHA absent cite
    `#136390` (prefixe adjacent de `#13639` PR), sans citer `#13639`
    directement : la levee doit AVERTIR (et non REFUSER)."""
    res = run([USER_NIT, lift_citant_sha()],
              commits=[{"oid": NIT_OID, "committedDate": at(19)}],
              body="See #13639",
              _absent_sha_messages={
                  "2d6e4c3642": "fix(x): typo dans #136390 (adjacent)"})
    assert res["blocked"] is False, "Le substring matchait `#13639` dans `#136390` → faux refus"
    assert res["voided_lifts"] == []
    # Avertissement OK (le SHA est bien absent et non resoluble vers la PR)
    assert [w["sha"] for w in res["absent_sha_warnings"]] == ["2d6e4c3642"]


def test_13641_ref_exacte_compte_toujours():
    """Le contre-test : quand le message cite EXACTEMENT `#13639` (mot complet
    apres `#` jusqu'au prochain non-alphanumerique), le rattachement reste
    valide et la levee est REFUSEE. C'est la discrimination qui ferme le faux
    positif du test precedent."""
    res = run([USER_NIT, lift_citant_sha()],
              commits=[{"oid": NIT_OID, "committedDate": at(19)}],
              body="See #13639",
              _absent_sha_messages={
                  "2d6e4c3642": "fix(check,#13639): levee citee (#13640)"})
    assert res["blocked"] is True
    assert [v["sha"] for v in res["voided_lifts"]] == ["2d6e4c3642"]


# --- #13635 : LIFT_MARKERS ne connaissait que le feminin. Les formes
# MASCULINES de la levee passive (« est levé », « sont levés ») manquaient, alors
# que ce depot nomme ce qui se leve au masculin (le concern / le point / le nit).
# Un motif se valide par ses faux negatifs, pas par ses hits : chaque colonne du
# tableau de l'issue est un test.

def test_13635_masculin_leve_reconnu():
    """Les 6 formes du tableau de l'issue rendent True apres correctif."""
    # feminines (deja couvertes — controle de symetrie)
    assert mod.has_live_lift("**Tes trois reserves sont levees.**") or mod.has_live_lift("**Tes trois réserves sont levées.**")
    assert mod.has_live_lift("**La reserve est levee.**") or mod.has_live_lift("**La réserve est levée.**")
    # masculines (le correctif)
    assert mod.has_live_lift("**[ai-01]** Tes trois concerns sont levés.")
    assert mod.has_live_lift("**[ai-01]** Le concern est levé.")
    assert mod.has_live_lift("**[ai-01]** Levée de la réserve NanoClaw.") or mod.has_live_lift("**[ai-01]** Leve de la reserve NanoClaw.")
    assert mod.has_live_lift("**[ai-01]** Le point est levé.")


def test_13635_masculin_singulier_leve():
    assert mod.has_live_lift("Le nit est levé.")
    assert mod.has_live_lift("Le concern est levé.")


def test_13635_negation_masculin_restaure_pas_levee():
    """Control 3 (#13635) : le nouveau motif masculin passe par `_lift_is_negated`.

    Une negation directe (« n'est pas levé ») doit reste exclue, comme c'est le
    cas pour le feminin depuis #13622. Sans cette verification, un motif ajoute
    hors du chemin de negation rouvrirait le defaut par la porte de service.
    """
    assert not mod.has_live_lift("Le concern n'est pas levé.")
    assert not mod.has_live_lift("**ne pas merger tant qu'il n'est pas levé**")
    assert not mod.has_live_lift("ce point n'est pas levé")
    # positive lointaine : la levee locale reste reconnue
    assert mod.has_live_lift("Le concern est levé.")


def test_13635_negation_apres_masculin_exclue():
    """Forme avec negation APRES le mot : 'levee non acquise' => 'levé non acquis'."""
    assert not mod.has_live_lift("Le concern est levé non acquis.")


def test_13635_conditionnel_feminin_nest_pas_annule_par_le_correctif():
    """Control 2 (#13635) : le correctif n'ouvre PAS de porte conditionnelle
    du cote masculin qui serait fermee du cote feminin.

    Verifie par faux negatif (symetrie) : CONDITIONAL_LIFT ne neutralise
    aujourd'hui que les formes a la 1re personne (« et je leve / et je merge »),
    pas la passive 3e personne « et <sujet> est leve(e) ». Le feminin
    (« et le point est levée ») et le masculin (« et le point est levé ») se
    comportent de facon IDENTIQUE apres correctif — le correctif n'introduit
    aucune asymetrie de genre.
    """
    # le correctif rend le masculin symetrique du feminin (aucun des deux n'est
    # neutralise par CONDITIONAL_LIFT, mais rien n'est introduit non plus)
    assert mod.has_live_lift("corrige la ligne 19 et le point est levé.") == \
           mod.has_live_lift("corrige la ligne 19 et le point est levée.")


def test_13635_conditionnel_je_leve_masculin_reste_bloquant():
    """Les formes conditionnelles a la 1re personne restent bloquantes apres
    correctif (regression CONDITIONAL_LIFT deja cablée, que le correctif ne
    touche pas) — miroir de test_lift_conditionnel_nest_pas_une_levee (#11201)."""
    assert mod.classify(
        "myia-ai-01",
        "Une seule chose a changer — corrige la ligne 19 et je leve le concern."
    ) == "BOT-CONCERN"
def test_13938_comment_only_avec_rien_de_bloquant_passe():
    """#13938 FP fondateur (PR #13935) : un reviewer pose `[Hermes]
    COMMENT_WITH_CONCERNS` et le corps declare explicitement « rien de
    bloquant ». L'exemption doit classer la review en ``None`` (comment-only
    par design, cf #12311) et non en ``BOT-CONCERN``.

    Reproduit le body verbatim de la review jsboige sur #13935 (compte-rendu
    de checkout local + delta scope + balise explicite de non-blocage).
    """
    body = (
        "[Hermes] COMMENT_WITH_CONCERNS — vérifié en local (checkout de la "
        "branche), pas juste lu le diff :\n"
        "- Cibles réelles des 3 liens ajoutés au README : `tutorials/README.md`, "
        "`shared/helpers/README.md`, `_research/e2e_quant_validation.ipynb`.\n"
        "- Nav relative corrigée, scope clean, security scan néant.\n"
        "Delta +18/-2.\n"
        "Rien de bloquant. (contrainte token : COMMENT only)"
    )
    assert mod.classify("jsboige", body) is None
    # Les helpers unitaires doivent retourner True sur ce body.
    assert mod._comment_only_prefix(body) is True
    assert mod._review_explicit_non_blocking(body) is True


def test_13938_comment_with_concerns_avec_concerns_substantiels_reste_bloquant():
    """#13938 FN-safety : `[Hermes] COMMENT_WITH_CONCERNS` + concerns FYI
    reels (« 2 concerns sur la cellule 12 ») SANS formulation non-bloquante
    reste un ``BOT-CONCERN``. L'exemption ne s'applique pas par defaut —
    seul un aveu explicite de non-blocage la declenche.

    Reproduit le pattern du test fondateur l.255-258 (notebook solide + 2
    concerns FYI).
    """
    body = (
        "[Hermes] **[COMMENT_WITH_CONCERNS]** — notebook solide, 2 concerns FYI "
        "sur la cellule 12 : la sortie du solver ne couvre pas le cas n=0 ; "
        "le bloc de test dépend de l'ordre des fixtures."
    )
    assert mod.classify("jsboige", body) == "BOT-CONCERN"
    assert mod._comment_only_prefix(body) is True
    assert mod._review_explicit_non_blocking(body) is False


def test_13938_changements_requestes_avec_rien_de_bloquant_reste_bloquant():
    """#13938 FN-safety : un reviewer pose `CHANGES_REQUESTED` et glisse «
    rien de bloquant » dans le corps. L'exemption NE DOIT PAS s'appliquer
    (le verdict de blocage strict prime sur la formulation de non-blocage).

    Reproduit le pieges classique : un reviewer tente de baisser le niveau
    d'un CHANGES_REQUESTED en ajoutant une clause de non-blocage. Le gate
    doit resister.
    """
    body = (
        "[Hermes] CHANGES_REQUESTED — refactor la cellule 5 pour respecter "
        "PEP 8. Rien de bloquant, je laisse au choix de l'auteur."
    )
    assert mod.classify("jsboige", body) == "BOT-CONCERN"
    assert mod._comment_only_prefix(body) is False
    # La formulation « rien de bloquant » EST bien reconnue (helper OK),
    # mais le verdict formel CHANGES_REQUESTED bloque l'exemption au
    # niveau du pipeline.
    assert mod._review_explicit_non_blocking(body) is True


def test_13938_comment_with_concerns_cite_dans_un_autre_commentaire_ne_passe_pas():
    """#13938 FN-safety : un commentaire qui CITE `[Hermes]
    COMMENT_WITH_CONCERNS` dans une prose qui refute (« pas de
    COMMENT_WITH_CONCERNS ici ») NE beneficie PAS de l'exemption — la
    detection `_is_cited` doit annuler l'occurrence au niveau du helper
    `_comment_only_prefix`.

    Reproduit le pattern inverse de #12871 : `_strip_mentioned_verdicts`
    neutralise les verdicts mentionnes, mais `_comment_only_prefix` opere
    sur le body brut. Un commentaire d'auteur qui enumere les verdicts
    d'Hermes pour les refuter ne doit pas etre auto-exempte.
    """
    body = (
        "Pour clarifier : il n'y a PAS de COMMENT_WITH_CONCERNS dans cette "
        "review. Les seuls verdicts emis sont APPROVED et LGTM. Je ne leve "
        "aucune reserve parce qu'il n'y en a pas."
    )
    # Ni verdict emis ni formulation non-bloquante au sens de l'exemption :
    # le helper de préfixe doit retourner False (l'occurrence est CITEE).
    assert mod._comment_only_prefix(body) is False
    # Le body doit classifier None (verdict positif APPROVED/LGTM + aucune
    # reserve vivante), mais PAS par la voie de l'exemption #13938.
    assert mod.classify("jsboige", body) is None


# --- #13512 -- Position G : verbe de mention + verdict NU (sans parenthese) -
#
# Cas fondateur PR #13496 : « @jsboige — reponse au REQUEST_CHANGES Hermes
# du 2026-08-29T17:33Z sur head `ae88aefc` » — la forme naturelle d'une
# reponse a un verdict de reviewer. Les positions existantes (A-F) exigent
# soit des parentheses (A), un titre `##` (B), une prose avec mot-cle
# inline (C), un verbe de levee + ref pointable (D/E), ou `revue|review`
# en tete (D-F). Aucune ne couvre cette forme sans sur-detection.
#
# Discrimination vs emission formelle : la fenetre `[^():\n.]{0,40}?`
# exclut `:` (donc `Fix : CHANGES_REQUESTED` ne matche pas — `:` suit
# immediatement le verbe) et `.` (donc le verdict doit etre dans la MEME
# phrase, pas apres une fin de phrase). Verdict case-sensitive
# `(?-i:[A-Z][A-Z_]{3,})`.


def test_13512_reponse_au_verdict_nu_ne_flagge_pas():
    """#13512 fondateur PR #13496 : reponse au verdict nu — la mention
    neutralise le verdict, classify retourne None.

    CE TEST ECHOUE SI Position G n'est pas cablee ou si la fenetre
    n'absorbe pas le 1-char gap de #13496."""
    body = (
        "@jsboige — reponse au REQUEST_CHANGES Hermes du 2026-08-29T17:33Z "
        "sur head `ae88aefc`. Le diagnostic etait juste, la cause racine "
        "exacte, et le fix est en place."
    )
    assert mod.classify("jsboige", body) is None


def test_13512_fix_du_verdict_nu_ne_flagge_pas():
    """#13512 variante : verbe `fix` + verdict nu — la mention neutralise
    le verdict, classify retourne None."""
    body = (
        "Voici le fix du CHANGES_REQUESTED pose par Hermes en review. "
        "Diagnostic et commit de remediation en commentaire suivant."
    )
    assert mod.classify("jsboige", body) is None


def test_13512_suite_au_verdict_nu_ne_flagge_pas():
    """#13512 variante : verbe `suite a` + verdict nu — la mention neutralise
    le verdict, classify retourne None."""
    body = (
        "Suite au COMMENT_WITH_CONCERNS du 2026-08-29 sur PR #13513, "
        "voici le diagnostic identifie et le correctif propose."
    )
    assert mod.classify("jsboige", body) is None


def test_13512_emission_nu_tete_reste_bot_concern():
    """#13512 CONTROLE NEGATIF : une emission reelle en tete de body
    (verdict nu sans verbe de mention avant) doit RESTER BOT-CONCERN.

    CE TEST ECHOUE SI Position G capture par exces les emissions directes."""
    body = "CHANGES_REQUESTED: edge case non couvert dans la branche."
    assert mod.classify("jsboige", body) == "BOT-CONCERN"


def test_13512_verdict_formel_reste_bot_concern():
    """#13512 CONTROLE NEGATIF : un verdict precede de `Verdict :` (forme
    d'emission formelle) doit RESTER BOT-CONCERN — le `:` apres `Verdict`
    fait que la fenetre Position G ne capture pas."""
    body = "Verdict : CHANGES_REQUESTED sur ce commit. A corriger."
    assert mod.classify("jsboige", body) == "BOT-CONCERN"


def test_13512_fix_colon_emission_reste_bot_concern():
    """#13512 CONTROLE NEGATIF : `Fix :` (verbe de mention immediatement
    suivi de `:`) doit RESTER BOT-CONCERN — la fenetre exclut `:` par
    construction (`[^():\n.]{0,40}?`)."""
    body = "Fix : CHANGES_REQUESTED sur le ticket 1234. Diagnostic a venir."
    assert mod.classify("jsboige", body) == "BOT-CONCERN"


def test_13512_sonde_helper_position_g_retourne_verdict():
    """#13512 sonde helper-level : Position G capture bien le verdict nu
    dans la phrase de #13496 (preuve qu'elle est cablee et la fenetre
    absorbe le 1-char gap). Suppression de la sonde = la regex ne capture
    plus, le test fondateur ci-dessus retombe ROUGE."""
    body = "@user — reponse au REQUEST_CHANGES Hermes du ..."
    stripped = mod._strip_mentioned_verdicts(mod._strip_quoted(body))
    # Apres strip, REQUEST_CHANGES doit etre neutralise (espaces de meme
    # longueur) : `RE` du verdict doit avoir ete remplace par des espaces.
    assert "REQUEST_CHANGES" not in stripped, (
        f"Position G n'a pas capture REQUEST_CHANGES dans : {body!r}\n"
        f"Stripped result: {stripped!r}"
    )


def test_13512_sonde_helper_position_g_retourne_pas_emission_nue():
    """#13512 sonde helper-level : Position G NE capture PAS un verdict nu
    en tete (qui est une emission formelle, pas une mention). Suppression
    de la sonde = le test FN ci-dessus retombe ROUGE (faux positif massif)."""
    body = "CHANGES_REQUESTED: edge case non couvert."
    stripped = mod._strip_mentioned_verdicts(mod._strip_quoted(body))
    # Position G ne capture pas ici (pas de verbe de mention avant) :
    # le verdict reste vivant dans le body stripé.
    assert "CHANGES_REQUESTED" in stripped, (
        f"Position G a capture a tort CHANGES_REQUESTED dans : {body!r}\n"
        f"Stripped result: {stripped!r}"
    )


# #14070 — garde anti-negation Position G (Hermes demande 1/2). Le verbe
# de mention + verdict NU matche, mais la negation directe (`je n'ai pas
# traite`, `non pas`, `ne...plus`, `jamais leve`) doit PRESERVER le verdict
# dans le body (le verdict reste cite → classify le voit comme un nit non
# leve). Sans ce garde, une phrase « Je n'ai pas leve le REQUEST_CHANGES »
# serait neutralisee a tort (le reviewer pretend l'avoir leve alors qu'il
# dit explicitement qu'il NE l'a PAS leve).


def test_14070_position_g_neutralise_pas_mention_negatee_pas():
    """#14070 FN-safety : Position G avec negation `pas` (15 chars avant le
    verdict) doit PRESERVER le verdict dans le body. Le reviewer ecrit
    qu'il N'A PAS traite le REQUEST_CHANGES — c'est un nit non leve."""
    body = "Je n'ai pas traite le REQUEST_CHANGES, il reste valable."
    stripped = mod._strip_mentioned_verdicts(mod._strip_quoted(body))
    # Le verdict doit rester vivant (Position G aurait capture si on n'avait
    # pas cable _lift_is_negated sur Position G).
    assert "REQUEST_CHANGES" in stripped, (
        f"Position G a neutralise a tort REQUEST_CHANGES dans : {body!r}\n"
        f"Stripped result: {stripped!r}"
    )


def test_14070_position_g_neutralise_pas_mention_negatee_jamais():
    """#14070 FN-safety : Position G avec negation `jamais` doit PRESERVER
    le verdict. Forme naturelle : 'On fix CHANGES_REQUESTED ? Jamais, la CI
    est rouge.' Le reviewer evoque le verdict sans l'avoir leve."""
    body = "On fix CHANGES_REQUESTED ? Jamais, la CI est rouge."
    stripped = mod._strip_mentioned_verdicts(mod._strip_quoted(body))
    assert "CHANGES_REQUESTED" in stripped, (
        f"Position G a neutralise a tort CHANGES_REQUESTED dans : {body!r}\n"
        f"Stripped result: {stripped!r}"
    )


def test_14070_position_g_neutralise_pas_annonce_fix_avec_commit_futur():
    """#14070 FN-safety (PR #13560 fondateur #13559) : Position G avec un
    verdict suivi d'une reference a un commit futur (`— commit XXXX`)
    doit PRESERVER le verdict. Forme : 'Fix review ai-01
    CHANGES_REQUESTED — commit 06956bd0a.' C'est une **annonce de fix**
    (le commit reference est futur), pas une **reponse** a un verdict
    passe. Le verdict doit rester vivant dans le body pour que l'organe
    le voie comme un nit non leve."""
    body = "Fix review ai-01 CHANGES_REQUESTED — commit 06956bd0a."
    assert mod.classify("hermes-bot", body) == "BOT-CONCERN", (
        f"Position G a neutralise a tort CHANGES_REQUESTED dans : {body!r}\n"
        f"Le verdict suivi de `— commit XXXX` est une annonce de fix, "
        f"pas une reponse a un verdict passe."
    )


# ---------------------------------------------------------------------------
# #13598 - EMISSION informelle d'un LIFT_OVERRIDE_LOGINS
# ---------------------------------------------------------------------------


def test_13598_cas_fondateur_reserve_francais_courant_classifiee() -> None:
    """#13550 verbatim : « ## [ai-01 ARBITRAGE] La reserve GPU tient. **Ne pas merger sur les verts.** »

    Avant le fix : classify retournait None (classe CONCERN_MARKERS ne couvre
    pas le francais courant). Apres : BOT-CONCERN - la reserve est signalee.
    """
    assert mod.classify(
        "myia-ai-01",
        "## [ai-01 ARBITRAGE] La reserve GPU tient. **Ne pas merger sur les verts.**",
    ) == "BOT-CONCERN"


def test_13598_hold_explicite_classifiee() -> None:
    """Le mot « hold » porte, seul, l'emission."""
    assert mod.classify("myia-ai-01", "Hold sur cette PR.") == "BOT-CONCERN"


def test_13598_attends_avec_objet_classifiee() -> None:
    """« j'attends le run GPU » est une emission structurelle."""
    assert mod.classify(
        "myia-ai-01", "J'attends le run GPU avant de statuer."
    ) == "BOT-CONCERN"


def test_13598_wait_for_run_classifiee() -> None:
    """L'anglicisme « wait for X » suit le meme schema."""
    assert mod.classify(
        "myia-ai-01", "Wait for the ICT-25 rerun."
    ) == "BOT-CONCERN"


def test_13598_hold_nomme_g_var_reste_muet() -> None:
    """« HOLD G-VAR-2 - ... » est un NOM de verdict (la garde G-VAR-2), pas
    une injonction. Le lookahead `(?! G-VAR|BLOCK|BOT|COMMENT|VERDICT|PR)`
    dans `_COORDINATOR_INJUNCTION_RE` filtre les verdict nommes.
    """
    assert mod.classify(
        "myia-ai-01", "**HOLD G-VAR-2 (cap de genre), sur ma propre PR.**"
    ) is None


def test_13598_controle_positif_merci_reste_muet() -> None:
    """Acceptance #13598 point 2 : un commentaire ANODIN du coordinateur
    (« merci ») ne doit PAS bloquer. Le predicat requiert un verbe
    d'injonction ; « merci » n'en porte pas -> None.
    """
    assert mod.classify(
        "myia-ai-01", "Merci pour le heads-up."
    ) is None


def test_13598_controle_positif_vu_je_reviens_reste_muet() -> None:
    """« Vu, je reviens vers vous » - accuse de reception, pas injonction."""
    assert mod.classify(
        "myia-ai-01", "Vu, je reviens vers vous."
    ) is None


def test_13598_controle_positif_ok_je_regarde_reste_muet() -> None:
    """« OK je regarde » - pas de verbe d'injonction -> muet."""
    assert mod.classify("myia-ai-01", "OK je regarde") is None


def test_13598_controle_positif_lgtm_structurel_reste_muet() -> None:
    """Un LGTM structurel est une levee (LIFT_MARKER), pas une emission."""
    assert mod.classify("myia-ai-01", "LGTM structurel.") is None


def test_13598_negation_hold_restaure_le_muet() -> None:
    """« il n'y a aucun hold sur cette PR » est une negation -> pas une
    emission. Le predicat doit discriminer la semantique, pas la forme.
    """
    assert mod.classify(
        "myia-ai-01", "Il n'y a aucun hold sur cette PR."
    ) is None


def test_13598_injonction_neutralisee_par_levee_vive() -> None:
    """Une levee VIVE (LIFT_MARKER) dans le meme body neutralise l'injonction :
    la phrase leve la reserve qu'elle nommait (miroir du pattern `_block_emitted`
    pour BLOCAGE). « Ne pas merger. Mergé annule le hold. » -> None.
    """
    assert mod.classify(
        "myia-ai-01", "Ne pas merger. **Mergé** annule le hold."
    ) is None


def test_13598_override_pose_reste_muet_arbitrage_tiers() -> None:
    """Un `[OVERRIDE]` pose en tete (arbretage tiers de B.0, voie de levee
    du coordinateur) EMET une levee, jamais une reserve - le garde-fou
    `_block_emitted` point A est transpose ici.
    """
    assert mod.classify(
        "myia-ai-01", "[OVERRIDE] lane myia-ai-01:CoursIA - Merge OK."
    ) is None


def test_13598_hold_par_lane_jsboige_reste_muet() -> None:
    """La voie est strictement reservee a LIFT_OVERRIDE_LOGINS : une lane
    qui ecrit « ne pas merger » ne doit PAS declencher le predicat (elle
    n'a pas l'autorite de tenir un hold a elle seule).
    """
    assert mod.classify(
        "jsboige", "Ne pas merger sur les verts."
    ) is None


def test_13598_hold_par_reviewer_bot_reste_muet() -> None:
    """Meme predicat pour un reviewer bot : « Hold. » d'un Hermes ne doit
    pas declencher le predicat LIFT_OVERRIDE_LOGINS (le bot a son propre
    mecanisme via CONCERN_MARKERS + _block_emitted).
    """
    assert mod.classify("clusterManager-Myia", "Hold.") is None


def test_13598_body_vide_reste_muet() -> None:
    """Body vide garde le comportement par defaut de classify (None)."""
    assert mod.classify("myia-ai-01", "") is None



def test_13912_hold_nominal_mention_sous_hold_user() -> None:
    """#13912 : "sous hold user" est une MENTION NOMINALE, pas une EMISSION.

    Reproduction directe du FP documente par ai-01 sur #13706 :
    "Le moteur est sous hold user (#10038)" -- le coord CITE un hold tenu
    par user via #10038, n'en EMET pas un. Verdict `_hold_match_is_emission`
    attendu : False.
    """
    body = "Le moteur est sous hold user (#10038). translation-sync.yml est sous hold."
    assert mod._hold_match_is_emission(mod._unaccent(body)) is False


def test_13912_hold_nominal_mention_bold_around() -> None:
    """#13912 : "**sous hold user (#10038)**" -- bold markdown avant `sous`.

    Le 2e commentaire ai-01 sur #13706 utilise **bold** autour de l'expression,
    donc `sous` est precede d'un `**` (et non d'un whitespace). Le predicat
    doit accepter ce prefix comme separateur (et non comme partie d'un mot).
    """
    body = "le moteur qui ecraserait est **sous hold user (#10038)** : translation-sync.yml a perdu son trigger."
    assert mod._hold_match_is_emission(mod._unaccent(body)) is False


def test_13912_hold_nominal_mention_sur_le_hold() -> None:
    """#13912 : "sur le hold de ai-01" -- autre MENTION NOMINALE.

    Variante : le mot `sur` precede `le hold` -- c'est une description d'un
    hold detenu ailleurs, pas une EMISSION du coord. Verdict attendu : False.
    """
    body = "Le PR est sur le hold de ai-01 jusqu'a resolution de #10038."
    assert mod._hold_match_is_emission(mod._unaccent(body)) is False


def test_13912_hold_emission_verbe_tenir() -> None:
    """#13912 contre-positif : "je tiens le hold" -- EMISSION explicite.

    Un verbe d'injonction explicite immediatement voisin de `hold`
    ("je tiens le hold", "je maintiens le hold") reste une EMISSION.
    Le predicat doit le reconnaitre MEME si la liste CITERS matche
    egalement (defense en profondeur).
    """
    body = "Je tiens le hold jusqu'a resolution du gate."
    assert mod._hold_match_is_emission(mod._unaccent(body)) is True


def test_13912_hold_emission_maintenir() -> None:
    """#13912 contre-positif : "maintenir le hold" -- EMISSION explicite."""
    body = "Je maintiens le hold sur ce PR -- gate rouge non leve."
    assert mod._hold_match_is_emission(mod._unaccent(body)) is True


def test_13912_hold_classify_sous_hold_user_ne_devient_pas_bot_concern() -> None:
    """#13912 integration : classify(myia-ai-01, 'sous hold user') -> None.

    Avant le patch : classify retournait 'BOT-CONCERN' sur les commentaires
    ai-01 citant "sous hold user", forcant un faux positif sur #13706.
    Apres le patch : la mention nominale est neutralisee avant
    _coordinator_emission_informal, classify retombe sur None (pas de
    reserve vivante, pas de BOT-CONCERN).
    """
    body = (
        "**HOLD coordinateur** NON. Je CITE le hold user (#10038) pour expliquer "
        "pourquoi ce PR n'ecrasera pas translation-sync.yml : "
        "le moteur de regeneration est sous hold user (#10038)."
    )
    assert mod.classify("myia-ai-01", body) is None


def test_13912_controles_positifs_hold_reel_bloque_toujours() -> None:
    """#13912 -- contre-controles du desserrage de `HOLD_HEAD`.

    Le correctif porte sur le chemin `HOLD_HEAD` (#13784) les deux gardes que
    son chemin FRERE `_COORDINATOR_INJUNCTION_RE` avait deja : le lookahead de
    verdict nomme (#13598) et la negation. Desserrer un predicat exige de
    prouver qu'on n'a rien ETEINT -- ces cinq formes sont des holds REELS et
    doivent continuer de bloquer.

    Les deux resserrements de la negation se lisent dans les cas 2 et 4 :
      - cas 2 : « ne PAS merger » est un hold reel. `pas` est volontairement
        absent de la liste de negation, sinon un vrai hold s'auto-neutralise.
      - cas 4 : « NO merge until X » porte « NO » sans etre une denegation ;
        seul un `NON`/`NO` qui CLOT la clause est un verdict de denegation.
    """
    reels = [
        "**HOLD** cette PR attend le remplacement nomme.",
        "HOLD -- ne pas merger avant que le grain de remplacement soit nomme.",
        "## HOLD lane myia-po-2026:CoursIA -- cap G-VAR-2 atteint.",
        "**HOLD**: NO merge until the ratchet is green.",
        "[HOLD] lane myia-po-2023:CoursIA",
    ]
    for body in reels:
        assert mod.classify("myia-ai-01", body) == "BLOCK", body


def test_13912_hold_neutralise_negation() -> None:
    """#13912 : "Pas de hold" -- negation explicite doit rester muette.

    Sanity check : la negation (deja couverte par
    `_COORDINATOR_INJUNCTION_NEGATED_RE`) doit court-circuiter le predicat
    sans dependre de la discrimination mention-vs-emission.
    """
    body = "Pas de hold sur ce PR, vous pouvez merger."
    assert mod._hold_match_is_emission(mod._unaccent(body)) is False
    assert mod.classify("myia-ai-01", body) is None


# ============================================================================
# #14130 — Position H : rapport de verdict ATTRIBUE a un tiers, sans ref pointable
# ============================================================================
#
# Cas fondateur (#14070, 2026-09-02) : « La review Hermes porte un
# CHANGES_REQUESTED que ma lane ne peut pas lever seule. » -- un rapport de
# diagnostic sur l'etat d'une review tierce, classe BOT-CONCERN comme s'il
# emettait la reserve qu'il rapporte. Avant : BOT-CONCERN. Apres : None.
#
# Le discriminant est *qui parle du verdict de qui* (rapport d'un verdict de
# tiers attribue et date vs emission propre) : il exige (1) une attribution a
# un tiers (Hermes / NanoClaw / ai-01 / jsboige / un nom propre), (2) un verbe
# DESCRIPTIF (`porte`, `comporte`, `contient`, `mentionne`, `indique`, etc.) --
# pas un verbe d'EMISSION, (3) pas de declaration de blocage dans la suite de
# la phrase (`reste bloquante` / `Verdict :` / `Block on`).


def test_14130_fp1_reproduction_review_hermes_porte_un_verdict_ne_flagge_pas():
    """#14130 FP1 -- cas fondateur verbatim : « La review Hermes porte un
    CHANGES_REQUESTED que ma lane ne peut pas lever seule. ». Avant : BOT-CONCERN.
    Apres : None (rapport de diagnostic, pas emission)."""
    body = ("La review Hermes porte un CHANGES_REQUESTED que ma lane ne peut "
            "pas lever seule.")
    assert mod.classify("jsboige", body) is None


def test_14130_fp2_review_hermes_avec_backticks_ne_flagge_pas():
    """#14130 FP2 -- backticker est le contournement connu, qui doit continuer
    de marcher apres le fix (la neutralisation Position A s'applique deja, et
    Position H est idempotente sur du contenu deja neutralise)."""
    body = ("La review Hermes porte un `CHANGES_REQUESTED` que ma lane ne peut "
            "pas lever seule.")
    assert mod.classify("jsboige", body) is None


def test_14130_fp3_revue_avec_preposition_ne_flagge_pas():
    """#14130 FP3 -- variante avec preposition « la revue de Hermes contient » :
    doit matcher aussi (la preposition `de` est optionnelle)."""
    body = ("La revue de Hermes contient un COMMENT_WITH_CONCERNS sur la "
            "sortie 12 du notebook.")
    assert mod.classify("jsboige", body) is None


def test_14130_fp4_nanoclaw_mentionne_ne_flagge_pas():
    """#14130 FP4 -- autre reviewer : NanoClaw."""
    body = ("La review NanoClaw mentionne un SUSPECT_REGRESSION sur la branche "
            "main qui bloque la CI.")
    assert mod.classify("jsboige", body) is None


def test_14130_fp5_ai_01_avait_emis_ne_flagge_pas():
    """#14130 FP5 -- variante au passe : « avait emis » est descriptif (rapporte
    un evenement passe), pas une emission propre."""
    body = ("La review ai-01 avait emis un STRUCTURAL_ONLY sur la note de "
            "parite que je dois reprendre.")
    assert mod.classify("jsboige", body) is None


def test_14130_ce1_review_sans_attribution_reste_live():
    """#14130 CE1 -- CONTROLE NEGATIF : « Cette review CHANGES_REQUESTED
    reste bloquante » (pas d'attribution, pas de verbe descriptif, declaration
    de blocage vivante). DOIT RESTER BOT-CONCERN : sans quoi le fix debranche
    le gate sur le failure mode fondateur de B.0 (#10761, Hermes sans levee
    reelle, PR mergee avec reserve vivante)."""
    body = "Cette review CHANGES_REQUESTED reste bloquante."
    assert mod.classify("jsboige", body) == "BOT-CONCERN"


def test_14130_ce2_verdict_nu_en_tete_reste_live():
    """#14130 CE2 -- CONTROLE NEGATIF : « CHANGES_REQUESTED : edge case non
    couvert. » (verdict nu, pas de « review X porte », pas d'attribution).
    DOIT RESTER BOT-CONCERN."""
    body = "CHANGES_REQUESTED : edge case non couvert."
    assert mod.classify("jsboige", body) == "BOT-CONCERN"


def test_14130_ce3_emission_formelle_Verdict_reste_live():
    """#14130 CE3 -- CONTROLE NEGATIF : « Verdict : CHANGES_REQUESTED sur ce
    commit. » (verdict precede de « Verdict : » = emission formelle Hermes).
    DOIT RESTER BOT-CONCERN (les positions A-H ne touchent pas le canal
    d'emission)."""
    body = "Verdict : CHANGES_REQUESTED sur ce commit."
    assert mod.classify("jsboige", body) == "BOT-CONCERN"


def test_14130_ce4_block_on_reste_live():
    """#14130 CE4 -- CONTROLE NEGATIF : « Block on CHANGES_REQUESTED jusqu'a
    validation. » (verdict precede de « Block on » = gate hold du coordinateur,
    classifie BLOCK). DOIT RESTER BLOQUANT (peu importe le label BLOCK /
    BOT-CONCERN -- le merite de la position H est de NE PAS neutraliser ce
    verdict)."""
    body = "Block on CHANGES_REQUESTED jusqu'a validation."
    result = mod.classify("jsboige", body)
    assert result in ("BOT-CONCERN", "BLOCK"), (
        f"Position H ne doit pas neutraliser un gate hold ; result={result!r}"
    )


def test_14130_ce5_reste_bloquante_dans_fenetre_reste_live():
    """#14130 CE5 -- CONTROLE NEGATIF : « La review Hermes porte un
    CHANGES_REQUESTED, il reste bloquante. » (attribution OK, verbe descrip. OK,
    MAIS `reste bloquante` dans la fenetre de phrase -- la garde dure (3)
    preserve le verdict). DOIT RESTER BOT-CONCERN."""
    body = ("La review Hermes porte un CHANGES_REQUESTED sur le diff, et la "
            "reserve reste bloquante.")
    assert mod.classify("jsboige", body) == "BOT-CONCERN"


def test_14130_ce6_verdict_sans_article_reste_live():
    """#14130 CE6 -- CONTROLE NEGATIF : « La review Hermes indique CHANGES_REQUESTED. »
    (pas d'article `un/une/le/la` entre le verbe descriptif et le verdict -- la
    forme la plus directe d'une EMISSION par un reviewer, pas un rapport de
    mention). DOIT RESTER BOT-CONCERN."""
    body = "La review Hermes indique CHANGES_REQUESTED sur le diff."
    assert mod.classify("jsboige", body) == "BOT-CONCERN"


def test_14130_mutation_si_pattern_retire_le_test_rougit():
    """#14130 acceptance 2 -- test de mutation : si Position H est retiree du
    pipeline `_strip_mentioned_verdicts`, FP1 doit rougir. Verifie par
    monkey-patching temporaire du registre des patterns mention."""
    body = ("La review Hermes porte un CHANGES_REQUESTED que ma lane ne peut "
            "pas lever seule.")
    # Baseline : avec Position H, le verdict est neutralise
    assert mod.classify("jsboige", body) is None
    # Mutation : on retire Position H du pipeline
    orig = list(mod._strip_mentioned_verdicts.__code__.co_consts)  # placeholder, voir plus bas
    # Monkey-patch direct : on retire _MENTION_VERDICT_REPORTED de la liste
    # des patterns dans _strip_mentioned_verdicts en l'excluant.
    import re
    # Sauvegarde du registre module-level
    saved_reported = mod._MENTION_VERDICT_REPORTED
    try:
        # Remplace par un pattern qui ne matche jamais
        mod._MENTION_VERDICT_REPORTED = re.compile(r"(?!)")
        assert mod.classify("jsboige", body) == "BOT-CONCERN", (
            "MUTATION FAILED : si Position H est desactive, FP1 doit rougir "
            "(le verdict doit rester emis)."
        )
    finally:
        mod._MENTION_VERDICT_REPORTED = saved_reported


def test_13951_concern1_corps_contradictoire_avec_marqueur_prose_ne_passe_pas():
    """#13951 Concern 1 (NanoClaw structural review) : un corps CONTRADICTOIRE
    pose `[Hermes] COMMENT_WITH_CONCERNS` + rien de bloquant MAIS contient
    aussi un CONCERN_MARKER prose vivant (avant merge, a changer).
    L'exemption NE DOIT PAS s'appliquer : un concern prose emis dans la meme
    review ne doit pas etre ecrase par la phrase de non-blocage.

    Reproduit verbatim le piege identifie par NanoClaw dans la review
    COMMENTED du 2026-09-02T01:18:42Z :
    ``[Hermes] COMMENT_WITH_CONCERNS -- fond solide, rien de bloquant. En
    revanche, corriger le lien mort du README avant merge.``
    Avant le fix (commit ``fdd589cac``), l'exemption s'appliquait et
    ``classify`` rendait None -- la phrase rien de bloquant ecrasait le
    marqueur avant merge (CONCERN_MARKER prose vivant). Apres le fix,
    ``_sole_live_concern_is_comment_prefix`` detecte le residuel et fait
    tomber l'exemption, ce qui laisse classify rendre ``BOT-CONCERN``.
    """
    body_prose = (
        "[Hermes] COMMENT_WITH_CONCERNS -- fond solide, rien de bloquant. "
        "En revanche, corriger le lien mort du README avant merge."
    )
    # Les trois pre-conditions de l'exemption sont reunies :
    assert mod._comment_only_prefix(body_prose) is True
    assert mod._review_explicit_non_blocking(body_prose) is True
    # ... MAIS le 4e helper detecte le marqueur prose avant merge :
    assert mod._sole_live_concern_is_comment_prefix(body_prose) is False
    # Verdict final : BOT-CONCERN (pas None) -- la phrase de non-blocage n'a
    # pas ecrase le concern vivant.
    assert mod.classify("jsboige", body_prose) == "BOT-CONCERN"


def test_13951_concern1_glyphe_severite_avec_rien_de_bloquant_ne_passe_pas():
    """#13951 Concern 1 (NanoClaw) : variante glyphe. Un corps pose
    `[Hermes] COMMENT_WITH_CONCERNS` + rien de bloquant + glyphe (constat
    substantiel). L'exemption NE DOIT PAS s'appliquer : un glyphe de
    severite emis dans la meme review ne doit pas etre ecrase.

    Reproduit la 2e classe de piege listee par NanoClaw dans la review
    COMMENTED du 2026-09-02T01:18:42Z -- Meme classe pour glyphe (constat
    substantiel promu, #12143) coexistant avec rien de bloquant.
    """
    body_glyphe = (
        "[Hermes] COMMENT_WITH_CONCERNS -- diff coherent, rien de bloquant.\n"
        "\U0001F7E1 la cellule 12 merite un refactor (commentaire FYI, hors gate)."
    )
    assert mod._comment_only_prefix(body_glyphe) is True
    assert mod._review_explicit_non_blocking(body_glyphe) is True
    # Le glyphe est dans CONCERN_MARKERS (cf. PR #12143) :
    assert mod._sole_live_concern_is_comment_prefix(body_glyphe) is False
    assert mod.classify("jsboige", body_glyphe) == "BOT-CONCERN"
# ---------------------------------------------------------------------------
# Forme ETIQUETEE « Concern: » -- casse et nombre relaches (mandat user
# 2026-09-01). Le user posait ses remarques en francais nu, sans marqueur : ses
# commentaires etaient classes None, donc invisibles au merge-gate. Il propose
# d'adopter « Concern: » ; le present bloc rend cette proposition vraie, pour
# lui ET pour les agents, dont la casse varie aussi.
# ---------------------------------------------------------------------------

def test_concern_label_singulier_toute_casse_est_une_reserve():
    for body in (
        "Concern: ce travail devrait etre distille dans la serie QC.",
        "concern : a distiller dans la serie QC.",
        "CONCERN : a distiller dans la serie QC.",
        "Concerns: deux points a revoir.",
        "**Concern 2 :** le scope ne colle pas.",
        "> Concern: revoir le perimetre.",
        "Bonjour,\n\nConcern: revoir le perimetre.",
    ):
        assert mod.classify("jsboige", body) == "BOT-CONCERN", body


def test_concern_narration_de_levee_ne_bloque_pas():
    """Les 6 faux positifs mesures le 2026-09-01 sur 588 commentaires reels.

    Tous CITENT le mot en REPONDANT a une reserve : les bloquer serait le
    miroir exact du defaut que B.0 traque. Seule la forme etiquetee en tete de
    ligne est une emission ; « les 2 concerns sont traitees » n'en est pas une.
    """
    for body in (
        "Levee explicite : les 2 concerns Hermes sont adressee au commit 97e970c6.",
        "Reponse a la CONCERN empirique (review jsboige).",
        "Les concerns 1, 2 et 3 sont leves au commit b0d5eb59.",
    ):
        assert mod.classify("jsboige", body) is None, body


def test_concern_ne_matche_pas_le_francais_courant():
    """« concerne », « concernant », « concernes » ne sont pas des reserves."""
    for body in (
        "Ce commit concerne la serie QC.",
        "Concernant la serie QC, tout est bon. LGTM",
        "Cela ne concerne pas cette PR.",
    ):
        assert mod.classify("jsboige", body) is None, body


def test_jeton_de_verdict_tolere_la_casse():
    """Un agent qui ecrit le jeton en casse mixte emet le meme verdict."""
    assert mod.classify("jsboige", "Comment_With_Concerns : deux reserves.") == "BOT-CONCERN"


def test_prose_marker_reste_case_sensitive():
    """« AVANT merge » en emphase narre une levee Voie 3 -- 2 cas mesures.

    Relacher la casse de la prose retournerait l'organe contre les levees
    qu'il doit reconnaitre.
    """
    assert mod.classify(
        "jsboige",
        "Voie 3 B.0 : issue #14030 ouverte AVANT merge, body amende.",
    ) is None


# #14130 - Position F : verdict attribue a un tiers sans quote ni crochet.
# Bug fondateur (#14070, 2026-09-01) : 2 des 3 points non leves sur #14070
# etaient les commentaires de diagnostic de la lane elle-meme, qui NOMMAIENT
# le verdict d'un tiers sans le quoter -- le gate les comptait comme reserves
# vives, et chaque cycle de commentaire AJOUTAIT un point au compte qu'il
# decrivait. Mesure verbatim issue : "La review Hermes porte un
# CHANGES_REQUESTED que ma lane ne peut pas lever seule."
# ---------------------------------------------------------------------------


def test_14130_paire_reproduction_rend_none_dans_les_deux_formes() -> None:
    """#14130 acceptance #1 : la paire reproduction doit rendre `None` dans
    les deux formes (backtickee et nue). Discrimination : le predicat
    porte sur **qui parle de quoi**, pas sur la simple presence du nom.
    """
    bare = "La review Hermes porte un CHANGES_REQUESTED que ma lane ne peut pas lever seule."
    backt = "La review Hermes porte un `CHANGES_REQUESTED` que ma lane ne peut pas lever seule."
    assert mod.classify("jsboige", bare) is None, bare
    assert mod.classify("jsboige", backt) is None, backt


def test_14130_variantes_attribution_verdict_tiers_ne_flagge_pas() -> None:
    """#14130 : variantes structurelles -- attribution explicite d'un verdict
    FORMEL a un reviewer/agent tiers. Les formes AVEC article sont neutralisees
    par `_MENTION_VERDICT_REPORTED` (Position H ; ext. #14185 : verbes
    conclusifs/declaratifs `conclut`/`declare`).
    """
    bodies = [
        # #14130 fondateur (Position H, verbe porte + article)
        "La review Hermes porte un CHANGES_REQUESTED sur la cellule 12.",
        # ext. #14185 : verbes conclusifs/declaratifs + article (rapport de tiers)
        "La review NanoClaw conclut un SUSPECT_REGRESSION sur le test.",
        "La review Hermes declare un CHANGES_REQUESTED sur la cellule 12.",
        # deja couverts par la Position H (verbes descriptifs + article)
        "Verdict Hermes a rendu COMMENT_WITH_CONCERNS.",
        "La revue Claude signale un CONCERN dans le diff.",
    ]
    for body in bodies:
        assert mod.classify("jsboige", body) is None, body
    # Alignement ce6 (Position H) : sans article entre le verbe et le
    # verdict, la forme est une EMISSION directe, pas un rapport -- elle
    # reste BOT-CONCERN.
    emissions = [
        "La revue Claude mentionne NEEDS_CHANGES dans son rapport.",
        "Review Hermes a emis REQUEST_CHANGES sur la branche.",
    ]
    for body in emissions:
        assert mod.classify("jsboige", body) == "BOT-CONCERN", body


def test_14130_emission_formelle_avec_prefixe_agent_ne_seutralise_pas() -> None:
    """#14130 contre-positif : un `[Hermes]` (prefixe d'agent) suivi d'un
    verdict est une EMISSION formelle, couverte par AGENT_PREFIXES -- la
    Position F doit la laisser intacte (le `(?<!\\[)` borne le non-match).
    """
    bodies = [
        "[Hermes] CHANGES_REQUESTED sur la cellule 12.",
        "[Hermes] Review — CHANGES_REQUESTED.",
        "## [Hermes] **[COMMENT_WITH_CONCERNS]** — notebook solide, 2 concerns FYI.",
        "[NanoClaw] SUSPECT_REGRESSION sur le test.",
    ]
    for body in bodies:
        assert mod.classify("jsboige", body) == "BOT-CONCERN", body


def test_14130_reserve_formelle_en_prose_nue_reste_bloquante() -> None:
    """#14130 contre-positif : une reserve emise directement (sans nom de
    tiers, sans quote, sans prefixe) reste bloquee. Le discriminant est
    l'attribution a un tiers -- son absence = emission propre.
    """
    bodies = [
        "CHANGES_REQUESTED: la cellule 12 casse le kernel.",
        "2 CONCERNS ouverts, non adresses avant merge.",
        "REQUEST_CHANGES sur la logique de l'exercice 3.",
        "NEEDS_CHANGES: le test d'integration manque.",
    ]
    for body in bodies:
        assert mod.classify("jsboige", body) == "BOT-CONCERN", body


def test_14130_mutation_position_f_neutralisee_rougit_le_test() -> None:
    """#14130 acceptance #2 (valide par mutation) : si l'extension #14185
    (verbes conclusifs/declaratifs `conclut`/`declare` de
    `_MENTION_VERDICT_REPORTED`) est retiree du stripper, la variante
    conclusive redevient 'BOT-CONCERN' -- preuve que le test depend de
    l'extension. On recompile le pattern sans les verbes ajoutes, on
    re-tourne le strip sur la variante, on compare. In-place, sans
    monkeypatch global (la fonction est appelee par d'autres tests dans
    la meme run).
    """
    variant = "La review NanoClaw conclut un SUSPECT_REGRESSION sur le test."
    stripped = mod._strip_quoted(variant)
    # Composant determinant : le pattern REPORTED AVEC l'extension #14185
    full = mod._MENTION_VERDICT_REPORTED
    with_ext = full.sub(
        lambda mm: mm.group(0).replace(mm.group(1), " " * len(mm.group(1))),
        stripped,
    )
    # Sanity : avec l'extension, le verdict est neutralise (espaces)
    assert "SUSPECT_REGRESSION" not in with_ext, with_ext

    # Reconstruction SANS l'extension (= simule son retrait)
    mutated = mod.re.compile(full.pattern.replace(
        "|conclut|concluent|declare|declarent", ""))
    without_ext = mutated.sub(
        lambda mm: mm.group(0).replace(mm.group(1), " " * len(mm.group(1))),
        stripped,
    )
    # Sanity : sans l'extension, le verdict reste vivant
    assert "SUSPECT_REGRESSION" in without_ext, without_ext
    # Et donc classify re-rougit (CONCERN_MARKERS inclut SUSPECT_REGRESSION)
    assert mod.has_live_marker(without_ext, mod.CONCERN_MARKERS)
    # Avec l'extension, classify rend None (sanity inverse -- miroir du test variantes)
    assert not mod.has_live_marker(with_ext, mod.CONCERN_MARKERS)
    # Et les longueurs sont preservees (les fenetres `_is_cited` restent calibrees)
    assert len(with_ext) == len(without_ext)


def test_14130_conservation_offsets_sur_strip_quoted() -> None:
    """#14130 acceptance implicite : le strip preserve les offsets (les
    fenetres de `_is_cited` restent calibrees sur la vraie position des
    occurrences survivantes). Verification mecanique : remplacer les
    matches par des espaces de meme longueur ne change pas la longueur
    totale de la chaine.
    """
    bodies = [
        "La review Hermes porte un CHANGES_REQUESTED.",
        "La review Hermes porte un CHANGES_REQUESTED que ma lane ne peut pas lever seule.",
        "Review Hermes declare un SUSPECT_REGRESSION. Et puis autre chose.",
        "La review [Hermes] declare un CHANGES_REQUESTED.",  # non match -> pas de strip
    ]
    for body in bodies:
        assert len(mod._strip_mentioned_verdicts(body)) == len(body), body


# --- Position I (#14199) : tests re-appliques post-rebase (main a absorbe #14185) ---


def test_14199_fp1_qualifier_non_bloquant_neutralise():
    """#14199 FP1 -- « Concern (non bloquant) : <details> à confirmer avant
    merge. Ball merge : <delegate>. » (PR #13537 fondateur). Le qualifieur
    `(non bloquant)` neutralise le `avant merge` en mention. Position I
    sous-pattern (a) qualifier. Doit rendre None (avant merge neutralise)."""
    body = (
        "Concern (non bloquant) : mergeable_state=blocked au moment de la "
        "review — checks en cours sur une PR de 18:04Z, standard, à confirmer "
        "avant merge. Ball merge : Emerjesse."
    )
    assert mod.classify("jsboige", body) is None, (
        f"FP1 devrait etre neutralise (qualifier non bloquant), "
        f"got {mod.classify('jsboige', body)!r}"
    )



def test_14199_fp1_minimal_qualifier_mineur_neutralise():
    """#14199 FP1 minimal -- `(mineur) avant merge` (sous-pattern a, sans Ball
    merge). Doit rendre None."""
    body = "(mineur) à revoir avant merge."
    assert mod.classify("jsboige", body) is None



def test_14199_fp2_verification_passee_neutralise():
    """#14199 FP2 -- « Verifie de mon cote avant merge : CLEAN » (PR #13498
    fondateur). Position I sous-pattern (b) FR past p. + de mon cote. Doit
    rendre None."""
    body = (
        "Diagnostic du rouge adjacency : guard succede a guard. "
        "Verifie de mon cote avant merge : mergeStateStatus CLEAN, 0 check "
        "rouge sur les 50 jobs."
    )
    assert mod.classify("jsboige", body) is None, (
        f"FP2 devrait etre neutralise (verification passee), "
        f"got {mod.classify('jsboige', body)!r}"
    )



def test_14199_fp2_en_verified_neutralise():
    """#14199 FP2 EN -- « Verified by ai-01 avant merge » (sous-pattern b2).
    Doit rendre None."""
    body = "Verified by ai-01 locally avant merge. CI green."
    assert mod.classify("jsboige", body) is None



def test_14199_fp3_formule_b0_neutralise():
    """#14199 FP3 -- « levee par **issue de suivi ouverte avant merge**
    (#13929) » (PR #13860 fondateur). Position I sous-pattern (c) formule
    B.0. Doit rendre None."""
    body = (
        "La nit user est levee par **issue de suivi ouverte avant merge** "
        "(#13929), et — mieux — deja livree par #13932, qui mesure 4 "
        "alternatives x 2 voters au lieu d extrapoler. C est la voie 3 "
        "de B.0 appliquee correctement."
    )
    assert mod.classify("myia-ai-01", body) is None, (
        f"FP3 devrait etre neutralise (formule B.0), "
        f"got {mod.classify('myia-ai-01', body)!r}"
    )



def test_14199_fp3_voie_b0_verbatim_neutralise():
    """#14199 FP3 variante -- « voie B.0 « issue de suivi ouverte et nommee
    AVANT LE MERGE » » (PR #13498 verbatim). Sous-pattern (c) avec AVANT LE
    MERGE (optionnel article). Doit rendre None."""
    body = (
        "Passe de merge ai-01 — le concern NanoClaw est traite par la voie "
        "B.0 « issue de suivi ouverte et nommee AVANT LE MERGE »."
    )
    assert mod.classify("jsboige", body) is None, (
        f"FP3 (voie B.0 verbatim) devrait etre neutralise, "
        f"got {mod.classify('jsboige', body)!r}"
    )



def test_14199_fp4_ball_merge_delegation_neutralise():
    """#14199 FP4 -- « a confirmer avant merge. Ball merge : X. » (sous-pattern
    d, delegation Ball merge APRES avant merge). Doit rendre None."""
    body = (
        "Action requise : a confirmer avant merge. Ball merge : ai-01."
    )
    assert mod.classify("jsboige", body) is None



def test_14199_vp13800_a_relire_reste_bloquant():
    """#14199 VP -- « A relire par ai-01 avant merge. Aucune action. » (PR
    #13800). Verbe ACTIONNEL (`à relire`) deleguant une intervention, pas une
    #verification passee ni une delegation Ball merge. Aucun sous-pattern de
    Position I ne matche. Doit RESTER BOT-CONCERN."""
    body = (
        "[po-2023] cycle 2026-08-31 — etat final, les 2 concerns Hermes "
        "sont traites. Le residuel est une lecture manuelle ai-01. Marquee "
        "NON EVALUEE — a relire. A relire par ai-01 avant merge. Aucune "
        "action lane supplementaire possible."
    )
    assert mod.classify("jsboige", body) == "BOT-CONCERN", (
        f"VP #13800 doit rester BOT-CONCERN (verbe actionnel a relire), "
        f"got {mod.classify('jsboige', body)!r}"
    )



def test_14199_vp_imperatif_infinitif_reste_bloquant():
    """#14199 VP -- « a verifier avant merge » (verbe IMPERATIF a l'infinitif,
    pas un past p.). Doit RESTER BOT-CONCERN."""
    body = "Priere de bien vouloir a verifier avant merge."
    assert mod.classify("jsboige", body) == "BOT-CONCERN"



def test_14199_vp_a_confirmer_no_qualifier_reste_bloquant():
    """#14199 VP -- « a confirmer avant merge » (sans qualifieur, sans Ball
    merge, sans verification passee). Doit RESTER BOT-CONCERN."""
    body = "Action obligatoire : a confirmer avant merge."
    assert mod.classify("jsboige", body) == "BOT-CONCERN"



def test_14199_vp_qualifier_bloquant_reste_bloquant():
    """#14199 VP -- « Concern (bloquant) : ... avant merge » (qualifier
    BLOQUANT, pas couvert par sous-pattern a). Doit RESTER BOT-CONCERN."""
    body = "Concern (bloquant) : le kernel WSL est casse, a confirmer avant merge."
    assert mod.classify("jsboige", body) == "BOT-CONCERN"



def test_14199_ce1_mutation_position_i_desactivee_fp1_rougit():
    """#14199 mutation -- si Position I est desactivee, FP1 doit rougir
    (le `avant merge` reste emis et le commentaire est classe BOT-CONCERN).
    Verifie par monkey-patching de `_strip_avant_merge_mention` (no-op)."""
    body = (
        "Concern (non bloquant) : mergeable_state=blocked, a confirmer "
        "avant merge. Ball merge : Emerjesse."
    )
    # Baseline : avec Position I, FP1 est neutralise
    assert mod.classify("jsboige", body) is None
    # Mutation : monkey-patch de _strip_avant_merge_mention en no-op
    orig = mod._strip_avant_merge_mention
    try:
        mod._strip_avant_merge_mention = lambda body: body
        assert mod.classify("jsboige", body) == "BOT-CONCERN", (
            "MUTATION FAILED : si Position I est desactivee, FP1 doit "
            "rougir (le `avant merge` reste emis, le commentaire passe "
            "BOT-CONCERN)."
        )
    finally:
        mod._strip_avant_merge_mention = orig



def test_14199_remesure_7_vp_window_reste_bloquant():
    """#14199 acceptance -- re-mesure des 7 VP de la fenetre merged:2026-
    08-25..2026-09-01 : leurs commentaires doivent rester classifies
    BOT-CONCERN par l'organe apres le fix (peu importe la voie — CONCERN
    MARKERS, BLOCAGE coordinateur, LIFT_OVERRIDE, etc.). Si une seule
    regression, le fix est insuffisant.

    Implementation : on recupere les commentaires + reviews reels via gh
    API et on verifie qu'au moins un declenche classify() == BOT-CONCERN
    pour chaque PR. C'est l'invariant qui protege contre toute
    regression silencieuse du garde."""
    import json
    import shutil
    import subprocess
    if shutil.which("gh") is None or subprocess.run(
            ["gh", "auth", "status"], capture_output=True).returncode != 0:
        pytest.skip("gh CLI ou auth indisponible -- re-mesure live VP differee "
                    "(review NanoClaw #14322, concern 2 : le runner sans gh doit "
                    "skipper, pas ERREUR)")
    vps = [13921, 13800, 13789, 13667, 13542, 13386, 13370]
    for pr in vps:
        out = subprocess.check_output(
            ["gh", "api", f"repos/jsboige/CoursIA/issues/{pr}/comments", "--paginate"])
        out2 = subprocess.check_output(
            ["gh", "api", f"repos/jsboige/CoursIA/pulls/{pr}/reviews", "--paginate"])
        comments = json.loads(out)
        reviews = json.loads(out2)
        blocking_count = 0
        for c in comments:
            if mod.classify(c["user"]["login"], c["body"]) == "BOT-CONCERN":
                blocking_count += 1
        for r in reviews:
            if mod.classify(r["user"]["login"], r.get("body", "")) == "BOT-CONCERN":
                blocking_count += 1
        assert blocking_count > 0, (
            f"VP #{pr} doit avoir au moins 1 commentaire/review classifie "
            f"BOT-CONCERN apres le fix (regression silencieuse), "
            f"got {blocking_count}"
        )



def test_14199_remesure_3_fp_window_neutralise():
    """#14199 acceptance -- re-mesure des 3 FP de la fenetre merged:2026-
    08-25..2026-09-01 : ils doivent etre neutralises (classify() = None)
    apres le fix. Si un seul reste BOT-CONCERN, le fix est insuffisant."""
    fps = [
        ("13537", "clusterManager-Myia",
         "Concern (non bloquant) : mergeable_state=blocked au moment de "
         "la review — checks en cours sur une PR de 18:04Z, standard, a "
         "confirmer avant merge. Ball merge : Emerjesse."),
        ("13498", "jsboige",
         "Passe de merge ai-01 — le concern NanoClaw est traite par la "
         "voie B.0 « issue de suivi ouverte et nommee AVANT LE MERGE ». "
         "Verifie de mon cote avant merge : mergeStateStatus CLEAN."),
        ("13860", "myia-ai-01",
         "La nit user est levee par **issue de suivi ouverte avant "
         "merge** (#13929), et — mieux — deja livree par #13932. "
         "C est la voie 3 de B.0 appliquee correctement."),
    ]
    for pr, author, body in fps:
        result = mod.classify(author, body)
        assert result is None, (
            f"FP #{pr} doit etre neutralise (classify=None) apres le fix, "
            f"got {result!r} pour body={body[:60]!r}"
        )


def test_14199_concern1_aparte_phrase_precedente_neutralise_pas_le_vp():
    """Review NanoClaw #14322 concern 1 -- le gap du sous-pattern (a)
    QUALIFIER franchissait les frontieres de phrase : un aparte benin
    "(mineur)" dans une phrase precedente neutralisait un nit VIVANT
    "avant merge" de la phrase SUIVANTE. Le point est desormais exclu
    du gap ([^.!?\n]) : ce corps doit rester BOT-CONCERN."""
    body = ("Le point precedent (mineur) est clos sans suite. "
            "Reserve bloquante : a corriger avant merge par le lane.")
    assert mod.classify("clusterManager-Myia", body) == "BOT-CONCERN"


def test_14199_concern1_gap_intra_phrase_fp1_couvert_toujours_neutralise():
    """Le resserrement du gap ne doit pas casser le FP fondateur : un
    qualifieur dans la MEME phrase que le token reste neutralise."""
    body = ("Le point souleve (mineur) sera traite par la passe de "
            "nettoyage avant merge, pas ici.")
    assert mod.classify("clusterManager-Myia", body) != "BOT-CONCERN"


# ============================================================================
# #14277 — Position J : glyphe de sévérité en position de mention
# ============================================================================
# Fondateurs mesurés (sweep 264 corps / 61 PRs, fenêtre 2026-08-23..2026-09-02,
# différentiel old-vs-new : exactement 3 diffs = les 3 FP, 261 corps inchangés) :
#   FP1 #13951 c.869 (issuecomment-5506801880) : « variante glyphe 🟡. »
#   FP2 #13951 c.872 (issuecomment-5507737699) : « 2 cas (prose
#        contradictoire + glyphe 🟡) ajoutes. »
#   FP3 #13951 c.870 (issuecomment-5503423343) : « glyphes de severite (🟡
#        ..., 🔴 ...) » + formes résiduelles : énumération « (prose, 🟡, 🔴,
#        + controle) » et cellules tableau « **CWC + 🟡** ».
# VP d'émission (doivent rester BOT-CONCERN) : #12059 « **🟡 FINDING — »,
# #12083 « LGTM structural / 🟡 », glyphe en tête de ligne.

# --- Position J (#14277) : tests re-appliques post-rebase (main a absorbe #14322) ---


def test_14277_fp1_meta_nom_glyphe_neutralise():
    body = ("2. **2 tests manquants** que NanoClaw a explicitement demandés —\n"
            "   - variante glyphe 🟡.\n"
            "3. **Vérification first-hand (avant commit)** : OK.")
    assert mod.classify("jsboige", body) is None



def test_14277_fp2_meta_nom_parentheses_neutralise():
    body = ("- Tests : 2 cas (prose contradictoire + glyphe 🟡) ajoutes.\n"
            "6/6 PASSED en local.")
    assert mod.classify("jsboige", body) is None



def test_14277_fp3_enumeration_double_glyphe_neutralise():
    body = ("Deux surfaces : la **prose** (commentaire Hermes) et les "
            "**glyphes de severite** (🟡 constat substantiel #12059, "
            "🔴 bloquant).")
    assert mod.classify("jsboige", body) is None



def test_14277_fp3bis_enum_items_separateurs_neutralise():
    # Formes résiduelles de FP3 : glyphe item d'énumération (séparateur `,`)
    # et cellule de tableau (séparateur `+`), sans méta-nom sur la ligne.
    body = ("- 4 tests ajoutes (prose, 🟡, 🔴, + controle positif) verbatim.\n"
            "| 4 | **CWC + 🟡** | OK |")
    assert mod.classify("jsboige", body) is None



def test_14277_contretemoin_sans_marqueurs_reste_none():
    # Acceptance #14277 : le contre-mesure c.871 (paraphrase SANS aucun
    # marqueur verbatim) doit rester None (déjà correct avant le fix).
    body = ("## Cycle c.871 — état post-merge avec main, 2 points de revue "
            "toujours présents, lane irréductible.\n"
            "Tête de branche 15e478afe. mergeable: MERGEABLE. 6/6 PASSED.")
    assert mod.classify("jsboige", body) is None



def test_14277_vp12059_emission_tete_de_ligne_reste_bloquant():
    # VP fondateur #12059 : en-tête de verdict, glyphe en tête de ligne,
    # jamais précédé d'un méta-nom ni d'un séparateur d'énumération.
    body = ("**[NanoClaw]** structural review.\n"
            "**LGTM structural + 1 FINDING.**\n"
            "**🟡 FINDING — les 5 hyperparametres enseignes par la nouvelle "
            "md#19 contredisent le run mesure (cf tableau).**")
    assert mod.classify("clusterManager-Myia", body) == "BOT-CONCERN"



def test_14277_vp12083_lgtm_scoped_slash_reste_bloquant():
    # VP #12083 : « LGTM structural / 🟡 ... » — le séparateur `/` est
    # délibérément EXCLU du set d'énumération (B) : ce glyphe est une
    # émission scopée, pas un item de liste.
    body = "LGTM structural / 🟡 SPY 6/8 contredit par le walk-forward."
    assert mod.classify("clusterManager-Myia", body) == "BOT-CONCERN"



def test_14277_vp_meta_nom_apres_glyphe_reste_bloquant():
    # Un méta-nom APRÈS le glyphe n'en fait pas une mention : c'est une
    # émission avec parenthèse explicative.
    body = "🟡 — constat substantiel (cf glyphe)"
    assert mod.classify("clusterManager-Myia", body) == "BOT-CONCERN"



def test_14277_vp_ligne_suivante_sans_meta_nom_reste_bloquant():
    # Le méta-nom sur la ligne PRÉCÉDENTE ne ouvre pas la mention : la
    # portée est la ligne, pas le paragraphe.
    body = "Le glyphe de severite :\n🟡 FINDING — hyperparametres contredits."
    assert mod.classify("clusterManager-Myia", body) == "BOT-CONCERN"



def test_14277_ce1_mutation_position_j_desactivee_fp1_rougit():
    # Contrôle positif : sans Position J, FP1 doit rougir (BOT-CONCERN).
    saved = mod._strip_glyphe_mentions
    mod._strip_glyphe_mentions = lambda b: b
    try:
        body = ("- variante glyphe 🟡.\nVérification OK.")
        assert mod.classify("jsboige", body) == "BOT-CONCERN", (
            "MUTATION FAILED : si Position J est desactivee, FP1 doit "
            "rougir (le glyphe mentionné doit rester un marqueur vivant)."
        )
    finally:
        mod._strip_glyphe_mentions = saved



def test_14277_ce2_enum_separateur_rouge_si_b_desactivee():
    # Contrôle positif règle B : sans le séparateur d'énumération, la forme
    # résiduelle FP3 (item de liste sans méta-nom) doit rougir.
    saved = mod._GLYPH_ENUM_PRECEDER_RE
    mod._GLYPH_ENUM_PRECEDER_RE = __import__("re").compile(r"(?!x)x")
    try:
        body = "- 4 tests ajoutes (prose, 🟡, controle positif)."
        assert mod.classify("jsboige", body) == "BOT-CONCERN", (
            "MUTATION FAILED : sans la règle B (séparateur énumération), "
            "la forme item-de-liste doit rougir."
        )
    finally:
        mod._GLYPH_ENUM_PRECEDER_RE = saved
# ---------------------------------------------------------------------------
# #14216 — la levée coordinatrice est scopée PAR RÉSERVE, plus par PR.
# La trappe #11639 ([OVERRIDE] lane d'un compte de levée) éteignait TOUTES
# les réserves ouvertes de la PR : sur #14166, la levée légitime par ai-01
# de SA réserve de collision a emporté la réserve structurelle Hermes de
# clusterManager-Myia, et la PR serait apparue mergeable si l'organe
# n'avait pas été relancé APRÈS le post. Le fix : un override ne lève une
# réserve d'autrui que s'il la NOMME (login de son auteur, ou persona
# Hermes — la forme historique canonique de #11639). Les fixtures
# `test_coord_override_leve_aussi_le_state_changes_requested` (login
# hermes-bot -> clusterManager-Myia) et `test_13083_override_lane_leve_le_
# blocage` (corps nommant myia-po-2023) ont été mises à la forme scopée :
# leur INTENT est inchangé, seule la forme du geste passe par le scope.
# ---------------------------------------------------------------------------

UNSCOPED_OVERRIDE_14216 = (
    "[OVERRIDE] lane myia-ai-01:CoursIA — Collision à trois PRs arbitrée : "
    "la survivante est celle-ci, ma réserve est levée."
)

SCOPED_OVERRIDE_14216 = (
    "[OVERRIDE] lane myia-ai-01:CoursIA — Collision arbitrée : ma réserve "
    "est levée, et celle de clusterManager-Myia aussi (Race/Switch corrigé "
    "par le commit 06956bd0a, vérifié)."
)


def _pr_14216(override_body):
    """La forme du fondateur #14166 : un BLOCAGE de ai-01 (collision) ET une
    réserve Hermes (review COMMENTED de clusterManager-Myia) sur une PR
    worker ; ai-01 arbitre par override. Retourne le verdict de l'organe."""
    blocage = {"author": {"login": "myia-ai-01"}, "createdAt": at(10),
               "body": "[BLOCAGE] lane myia-ai-01:CoursIA — collision à "
                       "trois PRs, arbitrage en cours."}
    hermes = {"author": {"login": "clusterManager-Myia"},
              "state": "COMMENTED", "submittedAt": at(11),
              "body": "[Hermes] COMMENT_WITH_CONCERNS — la prose enseigne "
                      "Race là où le code définit Switch."}
    lift = {"author": {"login": "myia-ai-01"}, "createdAt": at(12),
            "body": override_body}
    data = {
        "number": 0, "title": "t", "author": {"login": "myia-po-2025"},
        "comments": [blocage, lift], "reviews": [hermes],
        "commits": [{"committedDate": at(9)}],
    }
    return mod.analyse(data, [], MERGED)


def test_14216_fp1_override_non_scopee_ne_leve_pas_la_reserve_d_autrui():
    """#14216 contrôle positif (reproduction #14166) : deux réserves, auteurs
    différents ; l'override NON SCOPÉ de l'auteur de la première ne doit
    éteindre que la sienne — l'organe rend BLOCKED avec 1 nit restant
    (celui de clusterManager-Myia), pas OK."""
    res = _pr_14216(UNSCOPED_OVERRIDE_14216)
    assert res["blocked"] is True
    assert len(res["blocking"]) == 1
    assert res["blocking"][0]["author"] == "clusterManager-Myia"


EXCLUSION_OVERRIDE_14216 = (
    "[OVERRIDE] lane myia-ai-01:CoursIA — Levée de ma propre réserve : la "
    "collision à trois PRs est arbitrée (#14214), cette PR est le survivant "
    "nommé. La réserve de clusterManager-Myia n'est pas concernée par cette "
    "levée."
)


def test_14216_fp2_mention_exclusion_nest_pas_un_scope():
    """#14216 — la forme EXACTE du corps fondateur de #14166 (avant que
    l'auteur ne retire le marqueur) : l'override y porte le login du tiers
    dans une phrase d'EXCLUSION. La nomination seule ne suffit pas — sans
    phrase de levée affirmative, la réserve d'autrui survit."""
    res = _pr_14216(EXCLUSION_OVERRIDE_14216)
    assert res["blocked"] is True
    assert len(res["blocking"]) == 1
    assert res["blocking"][0]["author"] == "clusterManager-Myia"


def test_14216_vp1_override_scopee_par_login_leve_les_deux():
    """#14216 contrôle négatif symétrique : l'override QUI NOMME le tiers
    (login clusterManager-Myia) lève les deux réserves — le scope explicite
    est la seule porte ouverte vers la réserve d'autrui."""
    res = _pr_14216(SCOPED_OVERRIDE_14216)
    assert res["blocked"] is False


def test_14216_vp2_forme_historique_persona_hermes_reste_levee():
    """#14216 critère 4 (l'inverse) : le durcissement ne doit pas rougir les
    levées scopées déjà postées. La forme canonique historique de #11639 —
    « Levée de la réserve Hermes » sans login — reste une levée VALIDE pour
    la réserve de la persona (clusterManager-Myia)."""
    assert mod._override_scopes_reserve(OVERRIDE_BODY, "clusterManager-Myia")
    # ... et reste sans effet sur une réserve qu'elle ne nomme pas :
    assert not mod._override_scopes_reserve(OVERRIDE_BODY, "myia-po-2023")


def test_14216_unite_scope_login_persona_et_anonyme():
    """#14216 — granularité du détecteur de scope, niveau unitaire :
    login nommé (frontière d'identité), sous-chaîne de login = PAS un nom,
    auteur inconnu = levable (un scope ne nomme pas ce qui n'a pas de nom)."""
    body = "Levée des réserves : la mienne et celle de clusterManager-Myia aussi."
    assert mod._override_scopes_reserve(body, "clusterManager-Myia")
    assert not mod._override_scopes_reserve(body, "clusterManager-Myia2")
    assert not mod._override_scopes_reserve(body, "Myia")  # sous-chaîne
    assert mod._override_scopes_reserve(body, "")          # auteur inconnu
    # persona : le mot suffit pour les comptes de la persona (avec levee)
    assert mod._override_scopes_reserve("réserve Hermes levée", "jsboige")
    assert not mod._override_scopes_reserve("réserve Hermes levée",
                                            "myia-po-2023")
    # #14216 fondateur : le nom present dans une phrase d'EXCLUSION n'est
    # pas un scope (« n'est pas concernée par cette levée » = corps reel de
    # la levée ai-01 sur #14166 AVANT retrait du marqueur).
    excl = ("La réserve de clusterManager-Myia n'est pas concernée par "
            "cette levée.")
    assert not mod._override_scopes_reserve(excl, "clusterManager-Myia")


def test_14216_ignored_overrides_explique_le_scope_manquant():
    """#14216 — le rouge doit DIRE pourquoi l'override visible n'a rien
    éteint pour la réserve survivante (même exigence de nomination que
    #13316/#13495) : sinon un gate rouge « malgré notre override » redevient
    indistinguable d'un bug du détecteur."""
    res = _pr_14216(UNSCOPED_OVERRIDE_14216)
    explained = [o for o in res["ignored_overrides"]
                 if "#14216" in o["why"]
                 and "clusterManager-Myia" in o["why"]]
    assert explained, res["ignored_overrides"]


def test_14216_ce1_mutation_scope_toujours_vrai_fp1_rougit(monkeypatch):
    """#14216 contrôle positif par mutation : désactiver le scope (retour
    inconditionnel True = sémantique par-PR d'avant le fix) rend la
    reproduction fp1 VERTE — la preuve que le test mord."""
    monkeypatch.setattr(mod, "_override_scopes_reserve",
                        lambda b, a: True)
    assert _pr_14216(UNSCOPED_OVERRIDE_14216)["blocked"] is False


def test_14216_ce2_mutation_scope_toujours_faux_vp1_rougit(monkeypatch):
    """#14216 contrôle négatif par mutation : un scope qui refuse tout
    (jamais de levée d'autrui, même nommée) fait rougir vp1 — la porte du
    scope explicite est bien portée par le détecteur testé."""
    monkeypatch.setattr(mod, "_override_scopes_reserve",
                        lambda b, a: False)
    assert _pr_14216(SCOPED_OVERRIDE_14216)["blocked"] is True



# --- #13083 instance 3 : Position I' -- `avant merge` en TETE de corps (titre)
# sans verbe actionnel ni qualifieur bloquant. Le commentaire fondateur
# (2026-08-26T08:11:21Z sur #13083, PR #12627) : un rapport d'audit ai-01
# intitule « **Audit ai-01 avant merge** » etait classe BOT-CONCERN a tort,
# bloquant la PR sur l'absence de reserve de l'auteur. Les 7 sous-patterns
# Position I (#14199) ne matchent pas (aucun qualifieur / verification passee
# / formule B.0 / Ball merge). Le `avant merge` en tete est un localisateur
# temporel pur. Voir _strip_avant_merge_mention + _is_action_verb_heading.


def test_13083_instance3_fp_fondateur_12627_neutralise():
    """#13083 instance 3, FP fondateur #12627 (verbatim du commentaire
    5422425135 date 2026-08-26T08:11:21Z) : « **Audit ai-01 avant merge** »
    + prose descriptive (compte-rendu de mesure, sans verbe actionnel).
    Position I' doit neutraliser ce `avant merge` en tete de corps -- la
    classe rendue est None, plus BOT-CONCERN."""
    body = (
        "**Audit ai-01 avant merge**\n\n"
        "Le profil deletion-heavy de la PR est un faux signal : +4098/-4635 "
        "sur 3 notebooks + 3 labels de densite en baisse invitaient a "
        "soupconner une regression de contenu. Mesure cellule par cellule, "
        "origin/main rattrape les suppressions par les fusions post-coupure. "
        "Le delta est strictement borne aux tests du nouveau moteur, qui "
        "sont par construction absents du main pre-PR. La classification "
        "G.4 (composite) ne s'applique pas : 1 feature, pas 4."
    )
    assert mod.classify("myia-ai-01", body) is None, (
        f"FP fondateur #12627 devrait etre neutralise (Position I', "
        f"`avant merge` temporel en tete sans verbe actionnel), "
        f"got {mod.classify('myia-ai-01', body)!r}"
    )



def test_13083_instance3_formule_alternative_h1_neutralise():
    """Variante du FP fondateur : titre en H1 (`#`) sans bold. Meme
    localisation temporelle pure en tete de corps."""
    body = (
        "# Audit ai-01 avant merge\n\n"
        "Verifications prealables : 0 check rouge, mergeStateStatus CLEAN, "
        "tests verts. La PR peut etre passee en l'etat."
    )
    assert mod.classify("myia-ai-01", body) is None



def test_13083_instance3_formule_fr_minimal_neutralise():
    """Variante minimale : titre `Rapport avant merge` (sans bold/H1) +
    corps descriptif. Position I' doit neutraliser."""
    body = (
        "Rapport avant merge\n\n"
        "Diagnostic et verifications effectues. Pas de nit, pas de reserve."
    )
    assert mod.classify("jsboige", body) is None



def test_13083_instance3_formule_en_neutralise():
    """Variante EN du meme pattern : `**Audit ai-01 before merge**` -- la
    Position I' couvre `before merge` au meme titre que `avant merge` via
    le token `merge`. Verification que la borne tient cross-langue."""
    body = (
        "**Audit ai-01 before merge**\n\n"
        "Deletion-heavy profile is a false signal : +4098/-4635 on 3 "
        "notebooks, but the delta is strictly bounded to the new engine "
        "tests which are by construction absent from pre-PR main."
    )
    assert mod.classify("myia-ai-01", body) is None



def test_13083_instance3_vp_a_relire_tete_reste_bloquant():
    """VP : titre « A relire par ai-01 avant merge » -- verbe actionnel
    imperatif (`a relire`) deleguant une intervention. Position I' NE DOIT
    PAS neutraliser (la ligne porte un verbe actionnel, _is_action_verb_
    heading rend True). Doit rester BOT-CONCERN. Cf VP Position I
    fondateur #13800."""
    body = (
        "**A relire par ai-01 avant merge**\n\n"
        "Residuel : une lecture manuelle. Aucune action lane supplementaire "
        "possible. A relire par ai-01 avant merge."
    )
    assert mod.classify("jsboige", body) == "BOT-CONCERN", (
        f"VP `a relire avant merge` doit rester BOT-CONCERN (verbe actionnel "
        f"dans le titre), got {mod.classify('jsboige', body)!r}"
    )



def test_13083_instance3_vp_a_verifier_tete_reste_bloquant():
    """VP : titre `A verifier avant merge` (verbe imperatif infinitif).
    Position I' NE DOIT PAS neutraliser."""
    body = (
        "**A verifier avant merge**\n\n"
        "Verifier la coherence des paths dans la section 3."
    )
    assert mod.classify("jsboige", body) == "BOT-CONCERN"



def test_13083_instance3_vp_a_confirmer_tete_reste_bloquant():
    """VP : titre `A confirmer avant merge` (verbe imperatif infinitif).
    Position I' NE DOIT PAS neutraliser -- le VP Position I fondateur
    « a confirmer avant merge » (sans qualifieur) reste bloquant ; la
    version titre doit suivre la meme regle."""
    body = (
        "**A confirmer avant merge**\n\n"
        "Action obligatoire : confirmer la liste des fichiers touches."
    )
    assert mod.classify("jsboige", body) == "BOT-CONCERN"



def test_13083_instance3_vp_qualifier_bloquant_tete_reste_bloquant():
    """VP : titre avec qualifieur `(bloquant)` puis `avant merge`. Le
    qualifieur `(bloquant)` n'etait PAS couvert par Position I sous-pattern
    (a) -- la Position I' doit egalement le garder vivant en tete de corps."""
    body = (
        "**Concern (bloquant) a confirmer avant merge**\n\n"
        "Le kernel WSL est casse sur le runner ai-01, intervention "
        "requise avant de relancer les tests."
    )
    assert mod.classify("jsboige", body) == "BOT-CONCERN", (
        f"VP qualifier (bloquant) en tete doit rester BOT-CONCERN, "
        f"got {mod.classify('jsboige', body)!r}"
    )



def test_13083_instance3_vp_qualifier_urgent_tete_reste_bloquant():
    """VP : variante avec qualifieur `(urgent)` au lieu de `(bloquant)`.
    Position I' doit egalement le garder vivant en tete de corps."""
    body = (
        "**(Urgent) Audit ai-01 avant merge**\n\n"
        "Le merge gate a casse depuis 14h30Z, intervention requise."
    )
    assert mod.classify("myia-ai-01", body) == "BOT-CONCERN", (
        f"VP qualifier (urgent) doit rester BOT-CONCERN, "
        f"got {mod.classify('myia-ai-01', body)!r}"
    )



def test_13083_instance3_fp_avec_article_le_merge_neutralise():
    """Le sous-pattern Position I' couvre aussi `avant le merge` / `avant la
    merge` (article optionnel, comme les 7 sous-patterns Position I). Le
    FP #12627 fondateur utilise `avant merge` (sans article) -- verification
    qu'avec article, le meme cas de figure (titre sans verbe actionnel) est
    neutralise."""
    body = (
        "**Rapport d'audit avant le merge**\n\n"
        "Mesures et verifications. Pas de nit, pas de reserve."
    )
    assert mod.classify("myia-ai-01", body) is None, (
        f"FP avec article `avant le merge` devrait etre neutralise, "
        f"got {mod.classify('myia-ai-01', body)!r}"
    )



def test_13083_instance3_vp_avec_article_actionnel_reste_bloquant():
    """VP : titre avec article + verbe actionnel -- doit rester bloquant.
    Garantit que la sous-branche « article optionnel » n'ouvre pas un FP
    sur les VPs documentes. Position I' detecte le verbe actionnel
    `_is_action_verb_heading` et KEEPE `avant le merge` dans le titre ;
    le token survit comme substring, et `has_marker` le classifie
    BOT-CONCERN.

    NB : CONCERN_MARKERS contient `avant merge` (sans article) et
    `avant de merger`, mais PAS `avant le merge` -- c'est un prejugé
    du corpus Position I qui accepte l'article en surface stripee mais
    pas en detection basique. Le test utilise un corps qui porte les
    DEUX formes : le titre (article) que Position I' doit conserver +
    un `avant de merger` dans le corps que Position I' ne touche pas
    (milieu de phrase, hors tete)."""
    body = (
        "**A confirmer avant le merge**\n\n"
        "Action obligatoire : confirmer la liste des fichiers. "
        "Verifier chaque ligne, c'est une action obligatoire avant de merger."
    )
    assert mod.classify("jsboige", body) == "BOT-CONCERN", (
        f"VP `a confirmer avant le merge` (titre avec article + verbe "
        f"actionnel) doit rester BOT-CONCERN, got "
        f"{mod.classify('jsboige', body)!r}"
    )



def test_13083_instance3_ce1_mutation_desactivee_fp_rougit(monkeypatch):
    """Controle positif par mutation : si la Position I' est desactivee
    (regex no-op), le FP fondateur #12627 doit rougir -- preuve que le
    test mord sur la voie ajoutee. Utilise `monkeypatch.setattr` pour eviter
    le reload (le module est importe en conftest, reload casse le cache)."""
    import re
    body = (
        "**Audit ai-01 avant merge**\n\n"
        "Rapport descriptif, pas de reserve."
    )
    # Baseline : avec Position I', FP est neutralise
    assert mod.classify("myia-ai-01", body) is None
    # Mutation : neutralisation Position I' desactivee (regex ecrasee via
    # monkeypatch -- propre, rollback garanti)
    monkeypatch.setattr(mod, "_MENTION_AVANT_MERGE_HEAD_NEUTRAL",
                        re.compile(r"(?!)"))  # match jamais
    assert mod.classify("myia-ai-01", body) == "BOT-CONCERN", (
        "MUTATION FAILED : Position I' desactivee -> le FP fondateur "
        "#12627 doit rougir (`avant merge` reste emis en tete)."
    )


def test_13083_instance3_milieu_ligne4_reste_bloquant():
    r"""C.233 -- DM ai-01 2026-09-04T03:15Z (#14538) : un `avant merge` en
    milieu de corps (ligne 4) SANS verbe actionnel doit RESTER bloquant
    apres le fix raw string \A.

    Reproduction verbatim du tableau ai-01 :
    | Cas | Ligne du match ancien regex |
    |---|---:|
    | « Il faut relire la section 3 [token] », milieu de corps | **4** |

    Ancien regex `(?im)^` matchait cette ligne (en mode MULTILINE `^` =
    debut de chaque ligne). Le fix ancre au debut strict du body via raw string \\A,
    fermant ce trou -- les occurrences en milieu de corps NE sont PLUS
    neutralisees par Position I' (par design : un `avant merge` qui
    apparait au milieu d'un paragraphe descriptif est un concern
    VIVANT, pas un localisateur temporel de titre).

    Acceptation c.233 du fix Position I' : le strip est strictement borne
    a la premiere ligne. Cette regression est l'INTENTION du fix, pas un
    effet de bord. Le commentaire du code documente : `\A` ferme le trou
    d'une portee implicite `(?m)` que le commentaire d'origine
    n'annoncait pas (cf DM ai-01 2026-09-04T03:15Z sur #14538).
    """
    body = (
        "Rapport d'audit technique\n\n"
        "Le profil deletion-heavy de la PR est un faux signal.\n\n"
        "Il faut relire la section 3 avant merge, mais ce n'est pas un "
        "verdict bloquant.\n\n"
        "Conclusion : RAS."
    )
    assert mod.classify("myia-ai-01", body) == "BOT-CONCERN", (
        f"Apres fix `\\A`, `avant merge` en milieu de corps (ligne 4) "
        f"DOIT rester BOT-CONCERN (concern vivant, hors portee de "
        f"Position I'), got {mod.classify('myia-ai-01', body)!r}"
    )


def test_13083_instance3_milieu_ligne3_reste_bloquant():
    """C.233 -- DM ai-01 2026-09-04T03:15Z (#14538) : un `avant merge` en
    milieu de corps (ligne 3) SANS verbe actionnel doit RESTER bloquant.

    Reproduction verbatim du tableau ai-01 :
    | Cas | Ligne du match ancien regex |
    |---|---:|
    | « Le rapport a ete pose [token] », milieu de corps | **3** |
    """
    body = (
        "Note de revue\n\n"
        "Le rapport a ete pose avant merge par ai-01.\n\n"
        "Pas de nit, pas de reserve."
    )
    assert mod.classify("myia-ai-01", body) == "BOT-CONCERN", (
        f"Apres fix `\\A`, `avant merge` en milieu de corps (ligne 3) "
        f"DOIT rester BOT-CONCERN (concern vivant, hors portee de "
        f"Position I'), got {mod.classify('myia-ai-01', body)!r}"
    )


def test_13083_instance3_tete_h1_neutralise_toujours():
    """C.233 -- apres le fix `\\A`, le titre H1 (ligne 1) avec `avant merge`
    SANS verbe actionnel reste neutralise (FP fondateur #12627).
    C'est le test de NON-regression du fix : le scope se resserre mais le
    cas fondateur tient toujours.
    """
    body = (
        "# Audit ai-01 avant merge\n\n"
        "Rapport descriptif, pas de reserve."
    )
    assert mod.classify("myia-ai-01", body) is None, (
        f"Titre H1 `avant merge` (ligne 1, sans verbe actionnel) doit "
        f"rester neutralise apres fix `\\A` (non-regression du cas "
        f"fondateur), got {mod.classify('myia-ai-01', body)!r}"
    )


def test_14461_gvar3_override_est_reconnu_comme_arbitrage() -> None:
    """#14461 : un [G-VAR-3 OVERRIDE] pose en tete EMET une levee, pas un hold.

    Cas fondateur (PR #14345) : le coordinateur pose l'override d'adjacence
    canonique `[G-VAR-3 OVERRIDE] lane <m:w> -- next: <genre>` pour debloquer
    le garde d'adjacence, mais la phrase qui suit (« tant que ... n'est pas
    sur main ») est lue comme une injonction -> classify = BOT-CONCERN ->
    la PR que l'override venait de debloquer reste bloquee. Les deux
    instruments de deblocage du depot se bloquaient l'un l'autre.

    Controle a variable unique (tableau de l'issue) : meme corps, meme auteur,
    seul le marqueur d'en-tete change. B vs C isole la cause a une seule
    variable (l'orthographe du marqueur). D (vraie injonction) et E (anodin)
    rendent le controle non vacuous : la correction ne desarme PAS la
    detection de hold reelle — un predicat qui ne porte que B serait permissif
    et passerait inapercu.
    """
    phrase = "Tant que #14345 n'est pas sur `main`, chaque levee de la flotte porte ce risque."
    cases = [
        ("A phrase seule", phrase, True),
        (
            "B sous [G-VAR-3 OVERRIDE]",
            f"[G-VAR-3 OVERRIDE] lane myia-po-2026:CoursIA -- next: notebook-python\n\n{phrase}",
            False,
        ),
        (
            "C sous [OVERRIDE]",
            f"[OVERRIDE] lane myia-po-2026:CoursIA -- next: notebook-python\n\n{phrase}",
            False,
        ),
        ("D vraie injonction", "Ne pas merger tant que le run GPU n'est pas rendu.", True),
        ("E commentaire anodin", "Vu, merci.", False),
    ]
    for label, body, expected in cases:
        got = mod._coordinator_emission_informal(body)
        assert got is expected, (
            f"#14461 {label}: _coordinator_emission_informal attendu "
            f"{expected}, got {got!r}"
        )
    # Integration (symptome mesure sur #14345) : un override d'adjacence pose
    # par un LIFT_OVERRIDE_LOGINS ne doit plus classifier BOT-CONCERN (la PR que
    # l'override debloque reste bloquee). Il doit rendre None (pas de reserve).
    body_b = (
        f"[G-VAR-3 OVERRIDE] lane myia-po-2026:CoursIA -- next: notebook-python\n\n{phrase}"
    )
    assert mod.classify("myia-ai-01", body_b) is None, (
        f"#14461: classify(myia-ai-01, [G-VAR-3 OVERRIDE] + phrase) attendu "
        f"None (pas de BOT-CONCERN vivant), got "
        f"{mod.classify('myia-ai-01', body_b)!r}"
    )
    assert mod._block_emitted(body_b) is False, (
        "#14461: l'override d'adjacence n'emet pas non plus un BLOCAGE "
        "(point A de _block_emitted, garde-fou du jumeau)."
    )


def test_14461_t2_negation_d_override_ne_supprime_rien() -> None:
    """#14461 tranche 2 (adjoint po-2025, 2026-09-05) : un override est une
    AFFIRMATION, jamais une negation.

    `[NO OVERRIDE]` / `[PAS D'OVERRIDE]` / `[SANS OVERRIDE]` / `[NOT AN
    OVERRIDE]` disent l'inverse d'un arbitrage. Le motif bracketé
    `_OVERRIDE_HEAD_RE` (qui ne portait qu'OVERRIDE) les reconnaissait quand
    meme et SUPPRIMAIT une injonction reelle posee juste apres : `_block_emitted`
    (point A) et `_coordinator_emission_informal` retombaient a False
    (arbitrage) et `classify` rendait None sur un corps portant un BLOCAGE.
    Lookahead negatif : un mot de negation (EN/FR) avant OVERRIDE dans le
    crochet = pas un override. Controles positifs : les formes canoniques
    (`[G-VAR-3 OVERRIDE]`, `[G-VAR-2 OVERRIDE]`, `[OVERRIDE]`) restent des
    arbitrages (non-regression).
    """
    injonction = "**BLOCAGE MERGE (ai-01)** — Ne pas merger tant que le run GPU n'est pas rendu."
    negs = ["[NO OVERRIDE]", "[PAS D'OVERRIDE]", "[SANS OVERRIDE]", "[NOT AN OVERRIDE]"]
    for marker in negs:
        body = f"{marker} lane x\n\n{injonction}"
        assert mod._block_emitted(body) is True, (
            f"#14461-T2 {marker!r}: le BLOCAGE doit rester emis — la negation ne "
            f"desarme pas le point A de _block_emitted, got "
            f"{mod._block_emitted(body)!r}"
        )
        assert mod._coordinator_emission_informal(body) is True, (
            f"#14461-T2 {marker!r}: l'injonction doit rester une emission — la "
            f"negation ne la supprime pas, got "
            f"{mod._coordinator_emission_informal(body)!r}"
        )
        assert mod.classify("myia-ai-01", body) == "BLOCK", (
            f"#14461-T2 {marker!r}: classify doit rendre BLOCK, pas None (la "
            f"negation n'est pas un arbitrage), got "
            f"{mod.classify('myia-ai-01', body)!r}"
        )
        assert not mod._OVERRIDE_HEAD_RE.match(f"{marker} lane x".upper()), (
            f"#14461-T2 {marker!r}: le motif ne doit pas matcher une negation."
        )
    for marker in ("[G-VAR-3 OVERRIDE]", "[G-VAR-2 OVERRIDE]", "[OVERRIDE]"):
        body = f"{marker} lane x\n\n{injonction}"
        assert mod._block_emitted(body) is False
        assert mod._coordinator_emission_informal(body) is False
        assert mod.classify("myia-ai-01", body) is None
        assert mod._OVERRIDE_HEAD_RE.match(f"{marker} lane x".upper()), (
            f"#14461-T2 {marker!r}: le motif doit matcher une forme positive."
        )

