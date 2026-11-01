"""Tests de l'organe de mesure du debit UDP des runners (check_dns_rate, #22937).

Deterministes et SANS Docker : tout ce qui fonde un verdict est exerce sur des
series synthetiques, et l'acces Docker passe par un executeur injecte.

Les cinq controles d'acceptance du volet 5.1 :
  - une serie stable sous le seuil rend OK ;
  - une rafale n'est PAS masquee par la moyenne (WARN, puis RED a 5x) ;
  - un compteur qui recule est signale et ne rend jamais un debit negatif ;
  - zero conteneur alors que des slots sont attendus vaut UNREADABLE, jamais OK ;
  - un moteur Docker absent (ou introuvable) vaut UNREADABLE.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
if str(CI_DIR) not in sys.path:
    sys.path.insert(0, str(CI_DIR))

import check_dns_rate as organ

from check_dns_rate import (  # noqa: E402
    RED_FACTOR,
    STATUS_NOT_APPLICABLE,
    STATUS_OK,
    STATUS_RED,
    STATUS_MEASURED,
    STATUS_UNREADABLE,
    STATUS_WARN,
    STATUS_WIRED,
    BURST_WINDOW_S,
    Measurement,
    Sample,
    coverage_report,
    decide_status,
    degraded_slots,
    effective_verdict,
    expected_missing_slots,
    fold_samples,
    is_slot_name,
    list_slots,
    measure,
    parse_snmp_udp_out_datagrams,
    pool_applicability,
    read_udp_out_datagrams,
    resolve_pool,
    run_cmd,
    slot_sort_key,
    socket_present_for,
    verdict,
    window_is_unreadable,
    windows_unix_socket_guard,
)

SNMP_SAMPLE = """Ip: Forwarding DefaultTTL InReceives InHdrErrors
Ip: 2 64 1000 0
Icmp: InMsgs InErrors InCsumErrors InDestUnreachs OutMsgs
Icmp: 5 0 0 5 3
Udp: InDatagrams NoPorts InErrors OutDatagrams RcvbufErrors SndbufErrors InCsumErrors IgnoredMulti MemErrors
Udp: 18 0 0 18 0 0 0 0 0
UdpLite: InDatagrams NoPorts InErrors OutDatagrams RcvbufErrors SndbufErrors InCsumErrors IgnoredMulti MemErrors
UdpLite: 0 0 0 0 0 0 0 0 0
"""


# ---------------------------------------------------------------------------
# Parsing du compteur
# ---------------------------------------------------------------------------

def test_parse_par_nom_de_colonne():
    """La colonne est reperee par son NOM, donc insensible a un noyau qui insere des colonnes."""
    assert parse_snmp_udp_out_datagrams(SNMP_SAMPLE) == 18


def test_parse_repli_sur_la_colonne_5():
    """En-tete sans `OutDatagrams` : repli sur la position historique (colonne 5)."""
    text = "Udp: A B C D E F\nUdp: 1 2 3 4 77 6\n"
    assert parse_snmp_udp_out_datagrams(text) == 77


def test_parse_illisible_rend_none():
    """Une valeur non entiere ou absente n'est jamais convertie en zero."""
    assert parse_snmp_udp_out_datagrams("") is None
    assert parse_snmp_udp_out_datagrams("Udp: A B\n") is None
    assert parse_snmp_udp_out_datagrams("Udp: x y z w q\n") is None


def test_parsing_de_udp_et_non_udplite():
    """`UdpLite:` ne doit pas etre lu comme `Udp:` (il ne commence pas par `Udp:`)."""
    text = ("UdpLite: InDatagrams NoPorts InErrors OutDatagrams\n"
            "UdpLite: 0 0 0 999\n"
            "Udp: InDatagrams NoPorts InErrors OutDatagrams\n"
            "Udp: 4 0 0 7\n")
    assert parse_snmp_udp_out_datagrams(text) == 7


# ---------------------------------------------------------------------------
# Perimetre des slots
# ---------------------------------------------------------------------------

def test_filtre_de_slot_strict():
    """Un slot est EXACTEMENT `<prefixe>-<numero>` ; ni suffixe, ni prefixe nu."""
    prefix = "myia-ai-01-wsl"
    assert is_slot_name("myia-ai-01-wsl-1", prefix)
    assert is_slot_name("myia-ai-01-wsl-14", prefix)
    assert not is_slot_name("myia-ai-01-wsl-backup", prefix)
    assert not is_slot_name("myia-ai-01-wsl-4x", prefix)
    assert not is_slot_name("myia-ai-01-wsl", prefix)
    assert not is_slot_name("myia-po-2025-linux-docker-1", prefix)


def test_tri_numerique_des_slots():
    """`-2` avant `-10` : un tri alphabetique ferait passer 10 avant 2."""
    names = ["myia-ai-01-wsl-10", "myia-ai-01-wsl-2", "myia-ai-01-wsl-1"]
    assert sorted(names, key=slot_sort_key) == [
        "myia-ai-01-wsl-1", "myia-ai-01-wsl-2", "myia-ai-01-wsl-10"]


# ---------------------------------------------------------------------------
# Calcul des debits
# ---------------------------------------------------------------------------

def test_serie_stable_sous_le_seuil_rend_ok():
    """1 datagramme toutes les 2 s sur 15 s : 0,47 q/s en moyenne, 0,6 q/s en rafale."""
    samples = [Sample(float(t), {"s1": t // 2}) for t in range(16)]
    m = fold_samples(samples)
    assert m.sufficient
    assert round(m.average_qps, 4) == round(7 / 15, 4)
    assert m.burst_qps is not None and m.burst_qps < 1.0
    assert m.resets == []
    assert verdict(m.average_qps, m.burst_qps, 1.0, 10.0) == STATUS_OK


def test_rafale_non_masquee_par_la_moyenne():
    """60 datagrammes en une seconde sur 120 s : moyenne 0,5 q/s, rafale 12 q/s.

    C'est le controle central : la moyenne est CONFORTABLE (< 1 q/s), et le
    verdict est pourtant WARN. Un organe qui ne mesurerait que la moyenne
    rendrait OK ici, exactement le defaut que le volet 5 corrige.
    """
    samples = [Sample(float(t), {"s1": 0 if t <= 9 else 60}) for t in range(121)]
    m = fold_samples(samples)
    assert round(m.average_qps, 4) == 0.5
    assert m.burst_qps is not None and round(m.burst_qps, 4) == 12.0
    assert round(m.burst_span_s, 4) == BURST_WINDOW_S
    assert verdict(m.average_qps, m.burst_qps, 1.0, 10.0) == STATUS_WARN


def test_debit_cinq_fois_le_seuil_rougit():
    """6 q/s en moyenne pour un seuil de 1 : rapport 6x -> RED (facteur 5)."""
    samples = [Sample(float(t), {"s1": 6 * t}) for t in range(121)]
    m = fold_samples(samples)
    assert round(m.average_qps, 4) == 6.0
    assert verdict(m.average_qps, m.burst_qps, 1.0, 10.0) == STATUS_RED
    assert RED_FACTOR == 5.0


def test_compteur_qui_recule_signale_et_jamais_negatif():
    """100 -> 105 -> 5 -> 9 -> 14 : recul signale, intervalle exclu du debit."""
    values = [100, 105, 5, 9, 14]
    samples = [Sample(float(t), {"s1": v}, {"s1": "abc"}) for t, v in enumerate(values)]
    m = fold_samples(samples)
    assert len(m.resets) == 1
    reset = m.resets[0]
    assert reset.kind == "reset"
    assert (reset.before, reset.after) == (105, 5)
    # 5 + 0 (recul) + 4 + 5 = 14 sur 4 s.
    assert m.datagrams_total == 14
    assert round(m.average_qps, 4) == 3.5
    assert m.average_qps >= 0.0


def test_recyclage_distingue_du_recul_de_compteur():
    """Un changement d'ID de conteneur vaut `recycle`, pas `reset` : autre netns."""
    values = [100, 105, 0, 5]
    ids = ["conteneur-a", "conteneur-a", "conteneur-b", "conteneur-b"]
    samples = [Sample(float(t), {"s1": v}, {"s1": i})
               for t, (v, i) in enumerate(zip(values, ids))]
    m = fold_samples(samples)
    assert [r.kind for r in m.resets] == ["recycle"]
    # 5 (avant recyclage) + 0 (recyclage) + 5 (nouveau conteneur).
    assert m.datagrams_total == 10


def test_fenetre_trop_courte_rafale_non_observable():
    """Sous 5 s d'historique, `burst_qps` vaut None : on ne fabrique pas un zero."""
    samples = [Sample(float(t), {"s1": t}) for t in range(4)]
    m = fold_samples(samples)
    assert m.sufficient
    assert m.burst_qps is None
    assert m.burst_span_s is None
    assert verdict(m.average_qps, m.burst_qps, 1.0, 10.0) == STATUS_WARN  # 1 q/s pile
    assert verdict(0.2, None, 1.0, 10.0) == STATUS_OK


def test_slot_absent_d_un_echantillon_ne_comble_pas_un_zero():
    """Un slot disparu est compte comme absent ; son compteur reste la reference.

    Ce n'est pas un zero fabrique : le conteneur est le MEME (meme ID), donc les
    datagrammes sortis pendant l'absence ont bien eu lieu et le delta qui les
    couvre est legitime. Si le conteneur avait ete recree, l'ID aurait change et
    l'intervalle serait exclu (test suivant).
    """
    samples = [
        Sample(0.0, {"s1": 10}, {"s1": "a"}),
        Sample(1.0, {"s1": 20}, {"s1": "a"}),
        Sample(2.0, {}, {}),
        Sample(3.0, {"s1": 30}, {"s1": "a"}),
    ]
    m = fold_samples(samples)
    assert m.missing_samples == {"s1": 1}
    # 10 (0->1) + 10 (1->3, l'absence ne casse pas la continuite du conteneur).
    assert m.datagrams_total == 20
    assert m.average_qps >= 0.0


# ---------------------------------------------------------------------------
# Statut de lecture : « je n'ai pas mesure » n'est jamais « c'est calme »
# ---------------------------------------------------------------------------

def test_zero_conteneur_alors_que_des_slots_sont_attendus_est_unreadable():
    """Le piege principal : un mauvais moteur rend 0 slot, et un 0 n'est pas une mesure."""
    status, reason = decide_status(
        read_error=None, socket_present=True, found_slots=0,
        expected_slots=14, counters_read=0)
    assert status == STATUS_UNREADABLE
    assert status != STATUS_OK
    assert "14" in reason
    assert "0 requete/s" in reason


def test_moteur_docker_absent_est_unreadable():
    """`docker` introuvable : l'executeur rend rc=None et le statut est UNREADABLE."""
    def run_introuvable(cmd, docker_host, timeout_s=15.0):
        return None, "", "docker introuvable dans le PATH"

    slots, err = list_slots("unix:///var/run/docker-ce.sock", "myia-ai-01-wsl",
                            run=run_introuvable)
    assert slots == {}
    assert err and "introuvable" in err
    status, reason = decide_status(
        read_error=err, socket_present=None, found_slots=0,
        expected_slots=14, counters_read=0)
    assert status == STATUS_UNREADABLE
    assert "introuvable" in reason


def test_binaire_injoignable_rend_rc_none():
    """`run_cmd` sur un binaire inexistant : FileNotFoundError -> rc=None, jamais une exception."""
    code, out, err = run_cmd(["definitivement-pas-un-binaire-22937"], None)
    assert code is None
    assert "introuvable" in err


def test_socket_absent_est_unreadable():
    """Socket unix absent : fait mesure, et motif propre (pas de docker appele).

    Le couple exerce est celui que `main()` forme quand le socket manque : un
    socket absent fait echouer `docker ps`, donc `read_error` est renseigne en
    meme temps que `socket_present` vaut `False`. Le couple « `read_error` vide
    + socket absent » ne se produirait qu'en course (socket retire entre le
    dernier listing et le test d'existence) : il n'est plus cadenasse ici, et
    c'est le predicat socket, teste en premier, qui decide -- verrouille de bout
    en bout par `test_socket_absent_prime_depuis_main`.
    """
    assert socket_present_for("unix:///chemin/inexistant-22937.sock") is False
    assert socket_present_for("tcp://127.0.0.1:2375") is None
    status, reason = decide_status(
        read_error="docker ps a echoue (rc=1) : Cannot connect to the Docker "
                   "daemon at unix:///chemin/inexistant-22937.sock",
        socket_present=False, found_slots=0,
        expected_slots=14, counters_read=0)
    assert status == STATUS_UNREADABLE
    assert "socket" in reason


def test_aucun_compteur_lisible_est_unreadable():
    """Des slots existent mais aucun `docker exec` n'aboutit : rien n'a ete mesure."""
    status, reason = decide_status(
        read_error=None, socket_present=True, found_slots=14,
        expected_slots=14, counters_read=0)
    assert status == STATUS_UNREADABLE
    assert "compteur" in reason


def test_mesure_reelle_est_measured():
    """Le chemin nominal : des slots vus et des compteurs lus."""
    status, reason = decide_status(
        read_error=None, socket_present=True, found_slots=14,
        expected_slots=14, counters_read=14)
    assert status == "MEASURED"
    assert reason == ""


def test_un_echec_de_listing_prime_sur_tout():
    """Un listing en echec rend UNREADABLE meme si d'autres champs sont verts."""
    status, _ = decide_status(
        read_error="docker ps a echoue (rc=1) : Cannot connect to the Docker daemon",
        socket_present=True, found_slots=14, expected_slots=14, counters_read=14)
    assert status == STATUS_UNREADABLE


# ---------------------------------------------------------------------------
# Couche Docker (executeur injecte)
# ---------------------------------------------------------------------------

def test_list_slots_filtre_et_rend_les_ids():
    def run(cmd, docker_host, timeout_s=15.0):
        assert cmd[:2] == ["docker", "ps"]
        return 0, ("myia-ai-01-wsl-1\tdeadbeef\n"
                   "myia-ai-01-wsl-14\tcafe\n"
                   "claudish-sidecar\t1234\n"
                   "myia-ai-01-wsl-backup\t5678\n"), ""

    slots, err = list_slots("unix:///var/run/docker-ce.sock", "myia-ai-01-wsl", run=run)
    assert err is None
    assert slots == {"myia-ai-01-wsl-1": "deadbeef", "myia-ai-01-wsl-14": "cafe"}


def test_list_slots_remonte_le_rc_du_demon():
    def run(cmd, docker_host, timeout_s=15.0):
        return 1, "", "Cannot connect to the Docker daemon at unix:///x.sock"

    slots, err = list_slots("unix:///x.sock", "myia-ai-01-wsl", run=run)
    assert slots == {}
    assert err and "docker ps a echoue" in err


def test_read_udp_out_datagrams_lit_le_conteneur():
    def run(cmd, docker_host, timeout_s=15.0):
        assert cmd[:2] == ["docker", "exec"]
        assert cmd[2] == "myia-ai-01-wsl-3"
        return 0, SNMP_SAMPLE, ""

    value, err = read_udp_out_datagrams("myia-ai-01-wsl-3", None, run=run)
    assert (value, err) == (18, "")


def test_read_udp_out_datagrams_exec_en_echec():
    def run(cmd, docker_host, timeout_s=15.0):
        return 1, "", "Error: No such container: myia-ai-01-wsl-3"

    value, err = read_udp_out_datagrams("myia-ai-01-wsl-3", None, run=run)
    assert value is None
    assert "docker exec a echoue" in err


# ---------------------------------------------------------------------------
# Couverture : une fenetre presque entierement non lue n'est pas une mesure
# ---------------------------------------------------------------------------

def test_fenetre_presque_entierement_non_lue_est_unreadable():
    """exec lu au 1er echantillon puis en echec : 15 manquants sur 16 -> non lu.

    Sans ce seuil, la moyenne valait 0,0 q/s et le verdict `OK` a code 0 : une
    fenetre non lue rendait un vert parfaitement faux.
    """
    cov = coverage_report({"s1": 15}, ["s1"], 16)
    assert cov["degraded"] == ["s1"]
    assert window_is_unreadable(cov) is True
    assert degraded_slots({"s1": 15}, ["s1"], 16) == ["s1"]


def test_seuil_de_couverture_est_strict_a_la_moitie():
    """8 manquants sur 16 = 50 % pile : la moitie de la fenetre suffit, pas degrade."""
    assert degraded_slots({"s1": 8}, ["s1"], 16) == []
    assert window_is_unreadable(coverage_report({"s1": 8}, ["s1"], 16)) is False
    assert degraded_slots({"s1": 9}, ["s1"], 16) == ["s1"]


def test_un_seul_slot_degrade_ne_rend_pas_la_fenetre_non_lue():
    """Deux slots, un seul degrade : la mesure tient, mais elle est degradee."""
    cov = coverage_report({"s1": 0, "s2": 15}, ["s1", "s2"], 16)
    assert cov["degraded"] == ["s2"]
    assert window_is_unreadable(cov) is False


def test_une_reserve_durcit_ok_en_warn_jamais_l_inverse():
    """Les reserves AJOUTENT un motif : elles ne peuvent pas adoucir un verdict."""
    assert effective_verdict(STATUS_OK, coverage_degraded=False,
                             pool_incomplete=False) == STATUS_OK
    assert effective_verdict(STATUS_OK, coverage_degraded=True,
                             pool_incomplete=False) == STATUS_WARN
    assert effective_verdict(STATUS_OK, coverage_degraded=False,
                             pool_incomplete=True) == STATUS_WARN
    assert effective_verdict(STATUS_WARN, coverage_degraded=True,
                             pool_incomplete=True) == STATUS_WARN
    assert effective_verdict(STATUS_RED, coverage_degraded=False,
                             pool_incomplete=True) == STATUS_RED


# ---------------------------------------------------------------------------
# Pool : attendus, vus, et la reserve qui interdit un OK sans le dire
# ---------------------------------------------------------------------------

def test_pool_incomplet_nomme_les_slots_attendus_et_non_vus():
    """2 slots vivants sur 14 : les 12 autres sont NOMMES, et le pool est partiel."""
    seen = {"myia-ai-01-wsl-1": "a", "myia-ai-01-wsl-2": "b"}
    missing = expected_missing_slots(seen, "myia-ai-01-wsl", 14)
    assert len(missing) == 12
    assert missing[0] == "myia-ai-01-wsl-3"
    assert "myia-ai-01-wsl-1" not in missing
    assert "myia-ai-01-wsl-2" not in missing
    # Aucun parc declare : on ne fabrique pas des noms qu'on n'attend pas.
    assert expected_missing_slots(seen, "myia-ai-01-wsl", 0) == []


def test_pool_complet_n_ajoute_aucune_reserve():
    seen = {f"myia-ai-01-wsl-{i}": str(i) for i in range(1, 15)}
    assert expected_missing_slots(seen, "myia-ai-01-wsl", 14) == []


# ---------------------------------------------------------------------------
# Hors ai-01 : un parc absent n'est pas une panne
# ---------------------------------------------------------------------------

def test_parc_non_attendu_hors_ai01_est_non_applicable():
    """Sur une autre machine, le parc par defaut d'ai-01 n'est pas une panne."""
    applicable, reason = pool_applicability(
        "myia-po-2025", explicit_expected=False, explicit_prefix=False)
    assert applicable is False
    assert "myia-ai-01" in reason
    assert STATUS_NOT_APPLICABLE != STATUS_UNREADABLE


def test_parc_attendu_sur_ai01_quelle_que_soit_la_casse():
    """Le nom mesure depuis WSL est `MyIA-AI-01` : normalise, il designe ai-01."""
    assert pool_applicability("MyIA-AI-01", explicit_expected=False,
                              explicit_prefix=False) == (True, "")
    assert pool_applicability("myia-ai-01.domain.local", explicit_expected=False,
                              explicit_prefix=False) == (True, "")


def test_un_parc_declare_rend_la_machine_applicable():
    """Declarer le parc (prefixe ou attendus) leve la non-applicabilite."""
    assert pool_applicability("myia-po-2025", explicit_expected=True,
                              explicit_prefix=False)[0] is True
    assert pool_applicability("myia-po-2025", explicit_expected=False,
                              explicit_prefix=True)[0] is True


def test_resolve_pool_defauts_par_machine_et_declaration_explicite():
    prefix, expected, explicit_prefix, explicit_expected = resolve_pool(
        cli_expected_slots=None, cli_name_prefix=None, env={}, machine="MyIA-AI-01")
    assert (prefix, expected, explicit_prefix, explicit_expected) == (
        "myia-ai-01-wsl", 14, False, False)

    _, expected, _, _ = resolve_pool(
        cli_expected_slots=None, cli_name_prefix=None, env={}, machine="myia-po-2025")
    assert expected == 0

    prefix, expected, explicit_prefix, explicit_expected = resolve_pool(
        cli_expected_slots=4, cli_name_prefix="myia-po-2025-linux-docker",
        env={}, machine="myia-po-2025")
    assert (prefix, expected, explicit_prefix, explicit_expected) == (
        "myia-po-2025-linux-docker", 4, True, True)

    prefix, expected, explicit_prefix, explicit_expected = resolve_pool(
        cli_expected_slots=None, cli_name_prefix=None,
        env={"COURSIA_RUNNER_EXPECTED_SLOTS": "6",
             "COURSIA_RUNNER_NAME_PREFIX": "autre-parc"},
        machine="myia-po-2025")
    assert (prefix, expected, explicit_prefix, explicit_expected) == (
        "autre-parc", 6, True, True)


# ---------------------------------------------------------------------------
# Composition measure() -> decide_status : le seul endroit ou les deux champs
# (slots LISTES et compteurs LUS) sont calcules ensemble
# ---------------------------------------------------------------------------

def test_listing_a_14_et_exec_en_echec_nomme_la_bonne_cause():
    """`docker ps` voit 14 slots, tous les `exec` echouent : la cause est l'exec.

    Au head, `main()` passait `len(m.slots)` (compteurs lus) a `decide_status`,
    ce qui rendait « 0 conteneur ... mauvais moteur Docker » alors que 14
    conteneurs etaient listes. Le motif doit dire « aucun compteur lu ».
    """
    def run(cmd, docker_host, timeout_s=15.0):
        if cmd[:2] == ["docker", "ps"]:
            return 0, "".join(
                f"myia-ai-01-wsl-{i}\t{i:04x}\n" for i in range(1, 15)), ""
        if cmd[:2] == ["docker", "exec"]:
            return 1, "", f"Error: No such container: {cmd[2]}"
        raise AssertionError(cmd)

    m, listing_error, slot_note, seen = measure(
        "unix:///var/run/docker-ce.sock", "myia-ai-01-wsl", 0.0, 1.0, run=run)
    assert listing_error == ""
    assert len(seen) == 14
    assert m.slots == []
    assert m.counters_read == 0
    assert slot_note.startswith("myia-ai-01-wsl-1 : ")

    status, reason = decide_status(
        read_error=listing_error or None, socket_present=True,
        found_slots=len(seen), expected_slots=14, counters_read=m.counters_read)
    assert status == STATUS_UNREADABLE
    assert "aucun compteur" in reason
    assert "14 conteneur(s) de runner liste(s)" in reason
    assert "mauvais moteur" not in reason

    # Le meme cas mesure avec le champ du head (0 slot lu) : c'est CE motif qui
    # etait faux, et c'est ce que l'assertion ci-dessus remplace.
    status_head, reason_head = decide_status(
        read_error=None, socket_present=True,
        found_slots=len(m.slots), expected_slots=14, counters_read=m.counters_read)
    assert status_head == STATUS_UNREADABLE
    assert "mauvais moteur" in reason_head


def test_socket_absent_prime_sur_un_echec_de_listing():
    """Socket absent + `docker ps` en echec : le motif nomme le socket, pas l'exec.

    La branche socket etait inatteignable au head (elle exigeait `read_error`
    vide, que main ne produit jamais avec un socket absent) : elle est
    desormais le premier predicat, donc atteignable.
    """
    status, reason = decide_status(
        read_error="Cannot connect to the Docker daemon at unix:///absent.sock",
        socket_present=False, found_slots=0, expected_slots=14, counters_read=0)
    assert status == STATUS_UNREADABLE
    assert "socket" in reason


# ---------------------------------------------------------------------------
# Garde de plateforme : le UNREADABLE cote Windows est nomme, pas subi
# ---------------------------------------------------------------------------

def test_garde_de_plateforme_windows_sur_un_socket_unix():
    assert windows_unix_socket_guard("unix:///var/run/docker-ce.sock",
                                     is_windows=True)
    assert windows_unix_socket_guard("unix:///x.sock", is_windows=False) == ""
    assert windows_unix_socket_guard("tcp://127.0.0.1:2375", is_windows=True) == ""
    assert windows_unix_socket_guard(None, is_windows=True) == ""


def test_decide_status_dry_run_rend_wired_sans_faux_compteur():
    """En dry-run, le predicat « aucun compteur » est hors sujet : statut WIRED.

    Aucun compteur de synthese n'est fabrique pour traverser la branche : c'est
    le mode (`dry_run=True`) qui la declare hors sujet. Le meme appel hors
    dry-run, avec 0 compteur lu, reste UNREADABLE -- le predicat n'est pas
    supprime, il est seulement mis hors sujet la ou aucun `exec` n'est tente.
    """
    status, reason = decide_status(
        read_error=None, socket_present=None, found_slots=14,
        expected_slots=14, counters_read=0, dry_run=True)
    assert (status, reason) == (STATUS_WIRED, "")
    status_mesure, reason_mesure = decide_status(
        read_error=None, socket_present=None, found_slots=14,
        expected_slots=14, counters_read=0)
    assert status_mesure == STATUS_UNREADABLE
    assert "aucun compteur" in reason_mesure


def test_dry_run_avec_slots_rend_wired_et_code_zero(monkeypatch, capsys):
    """De bout en bout : un `--dry-run` qui voit les slots publie WIRED, code 0.

    Au head, le meme cas publiait `"status": "MEASURED"` avec un code 0 : un
    dry-run vert se lisait « debit sous le seuil » alors qu'aucune mesure
    n'avait eu lieu. Aucun compteur lu, et pourtant zero indication que rien
    n'avait ete mesure.
    """
    listing = {f"myia-ai-01-wsl-{i}": f"{i:04x}" for i in range(1, 15)}
    monkeypatch.setattr(organ, "list_slots",
                        lambda *a, **k: (dict(listing), None))
    code = organ.main(["--dry-run", "--json",
                       "--name-prefix", "myia-ai-01-wsl",
                       "--expected-slots", "14",
                       "--docker-host", "tcp://127.0.0.1:2375"])
    payload = json.loads(capsys.readouterr().out)
    assert code == 0
    assert payload["status"] == STATUS_WIRED
    assert payload["status"] != STATUS_MEASURED
    assert len(payload["slots_present"]) == 14


def test_main_publie_le_listing_et_nomme_la_vraie_cause(monkeypatch, capsys):
    """De bout en bout : 14 slots listes, aucun compteur lu.

    C'est le cas du defaut du head. `main()` passait `len(m.slots)` (compteurs
    lus) a `decide_status` et construisait `slots_seen` depuis `m.slots`, d'ou
    « 0 slot(s) vu(s) », `"slots_seen": []` et « mauvais moteur Docker » --
    alors que 14 conteneurs etaient listes et que la cause reelle etait un
    `docker exec` en echec sur chaque slot.
    """
    listing = {f"myia-ai-01-wsl-{i}": f"{i:04x}" for i in range(1, 15)}
    mesure = Measurement(times=[0.0, 1.0], totals=[0.0, 0.0])
    mesure.slots = []
    mesure.counters_read = 0
    monkeypatch.setattr(organ, "measure", lambda *a, **k: (
        mesure, "", "myia-ai-01-wsl-1 : docker exec a echoue (rc=1)",
        dict(listing)))
    monkeypatch.setattr(organ, "count_slots_on_default_engine",
                        lambda *a, **k: 14)
    code = organ.main(["--json", "--name-prefix", "myia-ai-01-wsl",
                       "--expected-slots", "14", "--window", "1",
                       "--docker-host", "tcp://127.0.0.1:2375"])
    payload = json.loads(capsys.readouterr().out)
    assert code == 2
    assert payload["status"] == STATUS_UNREADABLE
    assert "aucun compteur" in payload["reason"]
    assert "mauvais moteur" not in payload["reason"]
    # `slots_seen` ET le diagnostic viennent du MEME listing.
    assert len(payload["slots_seen"]) == 14
    assert payload["slots"] == []
    assert "moteur epingle : 14 slot(s) au listing" in (
        payload["diagnostics"]["moteur par defaut"])


def test_socket_absent_prime_depuis_main(monkeypatch, capsys):
    """De bout en bout : socket absent + listing en echec -> motif « socket ».

    Au head, `read_error` etait teste avant `socket_present` : la branche
    « socket absent » etait inatteignable depuis `main()`, et le motif recopiait
    l'erreur de `docker ps` (« Cannot connect ... ») au lieu de nommer la cause
    racine. Le couple exerce ici est celui que `main()` forme : un socket absent
    fait aussi echouer `docker ps`.
    """
    mesure = Measurement(times=[], totals=[])
    monkeypatch.setattr(organ, "measure", lambda *a, **k: (
        mesure,
        "docker ps a echoue (rc=1) : Cannot connect to the Docker daemon",
        "", {}))
    monkeypatch.setattr(organ, "socket_present_for", lambda host: False)
    monkeypatch.setattr(organ, "count_slots_on_default_engine",
                        lambda *a, **k: None)
    monkeypatch.setattr(organ, "windows_unix_socket_guard",
                        lambda host, **k: "")
    code = organ.main(["--json", "--name-prefix", "myia-ai-01-wsl",
                       "--expected-slots", "14", "--window", "1",
                       "--docker-host", "unix:///var/run/absent-22948.sock"])
    payload = json.loads(capsys.readouterr().out)
    assert code == 2
    assert payload["status"] == STATUS_UNREADABLE
    assert "socket du moteur natif absent" in payload["reason"]


def test_slot_liste_mais_jamais_lu_ne_rend_pas_un_ok(monkeypatch, capsys):
    """De bout en bout : 14 slots listes, 13 lus, 1 jamais lu -> WARN.

    Au head, un slot liste dont le `docker exec` echoue a chaque tour sortait
    de TOUS les champs structures -- ni `coverage.by_slot`, ni
    `missing_samples`, ni `slots_expected_missing` -- et `pool_complete`
    restait `true`. L'organe publiait alors « 0 requete/s, OK » sur un parc
    dont il n'avait pas lu un slot : le « zero non mesure » que le document
    promet de ne jamais rendre, au seuil de fermeture de 1 q/s.

    Ce test rougit au head et verdit au remede.
    """
    listing = {f"myia-ai-01-wsl-{i}": f"{i:04x}" for i in range(1, 15)}
    mesure = Measurement(times=[0.0, 1.0, 2.0], totals=[0.0, 0.0, 0.0])
    mesure.slots = [f"myia-ai-01-wsl-{i}" for i in range(1, 14)]
    mesure.counters_read = 13
    mesure.missing_samples = {}
    mesure.average_qps = 0.0
    mesure.datagrams_total = 0
    monkeypatch.setattr(organ, "measure", lambda *a, **k: (
        mesure, "", "myia-ai-01-wsl-14 : docker exec a echoue (rc=1)",
        dict(listing)))
    monkeypatch.setattr(organ, "count_slots_on_default_engine",
                        lambda *a, **k: 14)
    code = organ.main(["--json", "--name-prefix", "myia-ai-01-wsl",
                       "--expected-slots", "14", "--window", "1",
                       "--docker-host", "tcp://127.0.0.1:2375"])
    payload = json.loads(capsys.readouterr().out)
    assert code == 1
    assert payload["status"] == STATUS_MEASURED
    assert payload["verdict"] == STATUS_WARN
    # Le slot listee et jamais lu est nomme partout ou il doit l'etre.
    assert payload["slots_listed_never_read"] == ["myia-ai-01-wsl-14"]
    assert payload["pool_complete"] is False
    assert "myia-ai-01-wsl-14" in payload["coverage"]["degraded"]
    assert payload["missing_samples"]["myia-ai-01-wsl-14"] == 3
    assert any("jamais lu" in r for r in payload["reserves"])
    # Le listing et les compteurs lus restent deux choses distinctes.
    assert len(payload["slots_seen"]) == 14
    assert len(payload["slots"]) == 13


def test_pool_incomplet_ressort_de_bout_en_bout(monkeypatch, capsys):
    """De bout en bout : 12 slots vus sur 14 attendus -> reserve + rc 1.

    Le chemin des RESERVES n'etait couvert par aucun test de bout en bout :
    les trois appels a `main()` du fichier ne traversaient pas `reserves`. Le
    mutant neutralisant `expected_missing_slots(...)` -- donc toute la reserve
    « pool incomplet » et le durcissement `OK` -> `WARN` -- survivait a
    l'integralite des tests. Ce temoin le tue.
    """
    listing = {f"myia-ai-01-wsl-{i}": f"{i:04x}" for i in range(1, 13)}
    mesure = Measurement(times=[0.0, 1.0, 2.0], totals=[0.0, 0.0, 0.0])
    mesure.slots = list(listing)
    mesure.counters_read = 12
    mesure.missing_samples = {}
    mesure.average_qps = 0.0
    mesure.datagrams_total = 0
    monkeypatch.setattr(organ, "measure", lambda *a, **k: (
        mesure, "", "", dict(listing)))
    monkeypatch.setattr(organ, "count_slots_on_default_engine",
                        lambda *a, **k: 12)
    code = organ.main(["--json", "--name-prefix", "myia-ai-01-wsl",
                       "--expected-slots", "14", "--window", "1",
                       "--docker-host", "tcp://127.0.0.1:2375"])
    payload = json.loads(capsys.readouterr().out)
    assert code == 1
    assert payload["status"] == STATUS_MEASURED
    assert payload["verdict"] == STATUS_WARN
    assert payload["pool_complete"] is False
    assert payload["slots_expected_missing"] == ["myia-ai-01-wsl-13",
                                                  "myia-ai-01-wsl-14"]
    assert any("pool incomplet" in r for r in payload["reserves"])
