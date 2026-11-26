# -*- coding: utf-8 -*-
"""Tests de l'organe communication_channels (distillation sas EPITA, EPIC #4960).

Fige les comportements mesures du carnet source : priorite inversee,
filtres fail-loud, routage sans routes mortes, correlation requete-reponse.
"""

import unittest
from datetime import datetime, timedelta

from communication_channels import (
    AgentLevel,
    Channel,
    ChannelType,
    LocalChannel,
    Message,
    MessagePriority,
    MessageType,
    create_response,
    determine_channel,
)

T0 = datetime(2026, 1, 1, 12, 0, 0)


def msg(priority=MessagePriority.NORMAL, ts=T0, **kw):
    return Message(
        MessageType.INFORMATION, "sender", AgentLevel.SYSTEM, {},
        priority=priority, timestamp=ts, **kw
    )


class TestMessageFormat(unittest.TestCase):
    """Le format message : id derive, ordonnancement inverse, serialisation."""

    def test_id_prefix(self):
        """Banc id_prefix : l'id est derive du type."""
        m = Message(MessageType.COMMAND, "s", AgentLevel.STRATEGIC, {})
        self.assertEqual(m.id.split("-")[0], "command")

    def test_priority_order_inverted(self):
        """Banc priority_order_inverted_timestamps : CRITICAL d'abord, meme arrive en dernier."""
        msgs = [
            msg(priority=MessagePriority.LOW, ts=T0),
            msg(priority=MessagePriority.CRITICAL, ts=T0 + timedelta(seconds=5)),
            msg(priority=MessagePriority.HIGH, ts=T0 + timedelta(seconds=3)),
            msg(priority=MessagePriority.NORMAL, ts=T0 + timedelta(seconds=2)),
        ]
        ordered = sorted(msgs)
        self.assertEqual([m.priority for m in ordered], [
            MessagePriority.CRITICAL, MessagePriority.HIGH,
            MessagePriority.NORMAL, MessagePriority.LOW])

    def test_equal_priority_oldest_first(self):
        """Banc equal_priority_oldest_first : FIFO a priorite egale."""
        a = msg(ts=T0)
        b = msg(ts=T0 + timedelta(seconds=5))
        self.assertEqual(sorted([b, a]), [a, b])

    def test_dict_round_trip(self):
        """Banc dict_round_trip : to_dict/from_dict preserve l'identite."""
        m = Message(MessageType.INFORMATION, "tactical-1", AgentLevel.TACTICAL,
                    {"data": "result"}, recipient="strategic-1",
                    priority=MessagePriority.HIGH, timestamp=T0)
        r = Message.from_dict(m.to_dict())
        self.assertEqual(r.id, m.id)
        self.assertEqual(r.sender, m.sender)
        self.assertEqual(r.recipient, m.recipient)
        self.assertEqual(r.priority, m.priority)
        self.assertEqual(r.content, m.content)
        self.assertEqual(r, m)


class TestCorrelation(unittest.TestCase):
    """La convention de correlation requete-reponse."""

    def test_create_response_reversal(self):
        """Banc create_response_reversal : emetteur/destinataire inverses."""
        req = Message(MessageType.REQUEST, "strategic-1", AgentLevel.STRATEGIC,
                      {"request_type": "assistance"}, recipient="tactical-1",
                      message_id="request-demo", timestamp=T0)
        resp = create_response(req, AgentLevel.TACTICAL, {"result": "ok"})
        self.assertEqual(resp.type, MessageType.RESPONSE)
        self.assertEqual(resp.sender, "tactical-1")
        self.assertEqual(resp.recipient, "strategic-1")
        self.assertEqual(resp.metadata["reply_to"], "request-demo")


class TestFiltres(unittest.TestCase):
    """Le matcher de filtres : fail-loud, contrat par chaines."""

    def setUp(self):
        self.ch = LocalChannel("test")
        self.m = Message(MessageType.COMMAND, "tactical-1", AgentLevel.TACTICAL,
                         {"task": "analyse"}, priority=MessagePriority.HIGH, timestamp=T0)

    def test_scalar_type_match(self):
        """Banc scalar_type_match : le contrat parle en chaines."""
        self.assertTrue(self.ch.matches_filter(self.m, {"message_type": "command"}))

    def test_scalar_type_no_match(self):
        self.assertFalse(self.ch.matches_filter(self.m, {"message_type": "information"}))

    def test_list_type(self):
        """Banc list_type : une liste = OU logique."""
        self.assertTrue(self.ch.matches_filter(self.m, {"message_type": ["command", "information"]}))

    def test_unknown_key_raises(self):
        """Fail-loud (#2161) : une cle hors contrat leve, n'est pas ignoree."""
        with self.assertRaises(ValueError):
            self.ch.matches_filter(self.m, {"bogus_key": "value"})

    def test_content_filter(self):
        self.assertTrue(self.ch.matches_filter(self.m, {"content": {"task": "analyse"}}))
        self.assertFalse(self.ch.matches_filter(self.m, {"content": {"task": "autre"}}))


class TestCanalLocal(unittest.TestCase):
    """Le canal local : file d'attente, abonnes, notification."""

    def test_send_and_receive(self):
        ch = LocalChannel("test")
        m = msg(recipient="agent-1")
        ch.send_message(m)
        self.assertEqual(ch.receive_message("agent-1"), m)
        self.assertEqual(ch.receive_message("agent-1"), None)

    def test_broadcast_received_by_all(self):
        ch = LocalChannel("test")
        m = msg(recipient=None)
        ch.send_message(m)
        self.assertEqual(ch.receive_message("nimporte"), m)

    def test_subscribe_notified(self):
        ch = LocalChannel("test")
        received = []
        ch.subscribe("sub1", callback=received.append)
        ch.send_message(msg())
        self.assertEqual(len(received), 1)

    def test_subscribe_filtered(self):
        ch = LocalChannel("test")
        received = []
        ch.subscribe("sub1", callback=received.append, filter_criteria={"priority": "critical"})
        ch.send_message(msg(priority=MessagePriority.LOW))
        ch.send_message(msg(priority=MessagePriority.CRITICAL))
        self.assertEqual(len(received), 1)

    def test_unsubscribe(self):
        ch = LocalChannel("test")
        sid = ch.subscribe("sub1")
        self.assertTrue(ch.unsubscribe(sid))
        self.assertFalse(ch.unsubscribe(sid))

    def test_channel_info(self):
        ch = LocalChannel("test")
        ch.subscribe("sub1")
        ch.send_message(msg())
        info = ch.get_channel_info()
        self.assertEqual(info["subscribers"], 1)
        self.assertEqual(info["pending"], 1)


class TestRoutage(unittest.TestCase):
    """Le middleware decide du canal — sans routes mortes (#1571)."""

    def _msg(self, t, content=None, channel=None):
        return Message(t, "s", AgentLevel.SYSTEM, content or {}, channel=channel)

    def test_command_goes_hierarchical(self):
        self.assertEqual(determine_channel(self._msg(MessageType.COMMAND)), ChannelType.HIERARCHICAL)

    def test_information_with_analysis_goes_data(self):
        m = self._msg(MessageType.INFORMATION, {"info_type": "analysis_result"})
        self.assertEqual(determine_channel(m), ChannelType.DATA)

    def test_information_plain_goes_hierarchical(self):
        self.assertEqual(determine_channel(self._msg(MessageType.INFORMATION, {"info_type": "status"})), ChannelType.HIERARCHICAL)

    def test_request_assistance_goes_collaboration(self):
        m = self._msg(MessageType.REQUEST, {"request_type": "assistance"})
        self.assertEqual(determine_channel(m), ChannelType.COLLABORATION)

    def test_request_plain_goes_hierarchical(self):
        self.assertEqual(determine_channel(self._msg(MessageType.REQUEST, {"request_type": "query"})), ChannelType.HIERARCHICAL)

    def test_publication_goes_data(self):
        self.assertEqual(determine_channel(self._msg(MessageType.PUBLICATION)), ChannelType.DATA)

    def test_event_no_dead_route(self):
        """#1571 : EVENT ne route plus vers FEEDBACK (sans implementation)."""
        self.assertEqual(determine_channel(self._msg(MessageType.EVENT)), ChannelType.HIERARCHICAL)

    def test_explicit_channel_wins(self):
        m = self._msg(MessageType.COMMAND, channel="data")
        self.assertEqual(determine_channel(m), ChannelType.DATA)

    def test_invalid_channel_falls_back(self):
        m = self._msg(MessageType.COMMAND, channel="bogus")
        self.assertEqual(determine_channel(m), ChannelType.HIERARCHICAL)


class TestCanauxSansImplementation(unittest.TestCase):
    """Trois types de canal n'ont aucune implementation — le routage les evite."""

    def test_negotiation_feedback_system_never_returned(self):
        """Aucune regle de routage ne retourne un canal sans implementation."""
        for t in MessageType:
            ct = determine_channel(self._msg(t))
            self.assertNotIn(ct, {ChannelType.NEGOTIATION, ChannelType.FEEDBACK, ChannelType.SYSTEM})

    def _msg(self, t):
        return Message(t, "s", AgentLevel.SYSTEM, {})


if __name__ == "__main__":
    unittest.main(verbosity=2)
