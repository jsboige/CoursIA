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
        "number": 0, "title": "t", "comments": [], "reviews": reviews,
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
        "number": 0, "title": "t", "comments": list(comments),
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


def test_cr_cas4_phrase_de_levee_leve():
    """La reponse ecrite que B.0 exige : l'auteur de la PR repond AVEC un
    marqueur de levee (« sont adresses ») — l'etat se leve."""
    fix = {"author": {"login": "jsboige"}, "createdAt": at(12),
           "body": "Les 2 points sont adresses : cellule 19 remplacee par "
                   "strip_lean_comments, commit abc123."}
    assert run_cr([fix])["blocked"] is False


def test_cr_cas5_rereview_approved_meme_auteur_leve():
    approved = {"author": {"login": "myia-ai-01"}, "state": "APPROVED",
                "submittedAt": at(15), "body": "Verifie apres re-exec : APPROVED."}
    assert run_cr(reviews=[approved])["blocked"] is False


def test_cr_dismissed_nest_pas_un_signal():
    """Levee (b) : une dismissal GitHub n'est possible que par l'auteur de la
    review (ou un admin) — formellement retiree des la collecte."""
    data = {
        "number": 0, "title": "t", "comments": [],
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
    """Non-regression : le durcissement ne touche QUE l'etat de review. Un nit
    porte par un COMMENTAIRE reste leve par une reponse humaine (regime
    general, limite NLP de can_lift)."""
    reply = {"author": {"login": "jsboige"}, "createdAt": at(12),
             "body": "Bien vu, corrige."}
    assert run([USER_NIT, reply])["blocked"] is False
