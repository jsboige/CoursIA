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
    cr = {"author": {"login": "hermes-bot"},
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
                "body": OVERRIDE_BODY}
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


def test_14070_position_g_negation_non_pas_encore_bout_en_bout():
    """#14070 FN-safety, corps VERBATIM de la table Hermes (review
    2026-09-01T15:34:29Z, demande 1/2). Deux ecarts avec les tests
    voisins, et c'est pour eux que ce test existe :

    1. Le token de negation est `non` + `pas` (les voisins couvrent `pas`
       seul et `jamais`). `_LIFT_NEGATION_TOKENS` les porte tous les
       trois, mais un seul chemin etait exerce par corps.
    2. L'assertion porte sur `classify()` de bout en bout, pas sur
       `_strip_mentioned_verdicts` seul : c'est la surface que la table
       Hermes a mesuree (`None` cote PR vs `BOT-CONCERN` cote main).
       Un garde cable correctement au niveau du strip mais avale plus
       bas resterait invisible aux deux voisins.
    """
    body = "On fix CHANGES_REQUESTED ? Non, pas encore, la CI est rouge."
    assert mod.classify("clusterManager-Myia", body) == "BOT-CONCERN", (
        f"Le verdict est evoque sous negation (`Non, pas encore`) : il "
        f"n'est PAS leve, l'organe doit le voir vivant. Corps : {body!r}"
    )


def test_14070_position_g_negation_pas_bout_en_bout():
    """#14070 FN-safety, corps VERBATIM de la table Hermes (ligne 1).

    Jumeau end-to-end de `..._negatee_pas`, qui n'assertait qu'au niveau
    du strip. La paire prouve que le verdict survit AU STRIP *et* reste
    visible a `classify()` -- les deux etages, pas seulement le premier.
    """
    body = "Je n'ai pas traite le REQUEST_CHANGES, il reste valable."
    assert mod.classify("clusterManager-Myia", body) == "BOT-CONCERN", (
        f"Le reviewer dit explicitement N'AVOIR PAS traite le verdict : "
        f"c'est un nit non leve. Corps : {body!r}"
    )
