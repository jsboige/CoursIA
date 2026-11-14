# -*- coding: utf-8 -*-
"""Bus de communication multi-agents — format message, canal, middleware.

Distillation deterministe du sas EPITA ``docs/coursia_contrib/
communication_channels.ipynb`` (tronc ``argumentation_analysis/core/
communication/``, 8 modules), mandat Triple Distillation (EPIC CoursIA
#4960, sous-grain ligne 12 du recensement sas du 2026-09-22T03:54Z).

Le carnet source mesure le bus reel du moteur de debat : un format de
message commun, un contrat de canal, quatre familles de canaux (hierarchique,
collaboration, donnees, pub/sub), un protocole requete-reponse, et le
middleware qui route le tout. Ici, le port est **deterministe** : aucun
reseau, aucun thread, aucun LLM — tout est rejouable a l'identique.

>>> m = Message(MessageType.COMMAND, "s", AgentLevel.STRATEGIC, {})
>>> m.id.startswith("command-")
True
>>> sorted([
...     Message(MessageType.INFORMATION, "s", AgentLevel.SYSTEM, {}, priority=MessagePriority.LOW, timestamp=datetime(2026,1,1)),
...     Message(MessageType.INFORMATION, "s", AgentLevel.SYSTEM, {}, priority=MessagePriority.CRITICAL, timestamp=datetime(2026,1,2)),
... ])[0].priority is MessagePriority.CRITICAL
True

Divergences mesurees sur les sources (contrat de fidelite) :

1. **Les quatre canaux concrets ne sont pas portes.** La distillation porte
   le **contrat** (`Channel` abstrait, `LocalChannel` memoire) et le
   **middleware** (`determine_channel`) ; les canaux hierarchique,
   collaboration, donnees, pub/sub sont des implementations du meme contrat
   dont les cas de comportement sont dans les bancs du sas (12 bancs, 45
   cas) — le notebook les cite sans les re-implementer.
2. **Le protocole requete-reponse n'est pas porte.** Il introduit des
   threads et des timeouts (cf. `RequestResponseProtocol` avec
   `timeout_thread` daemon) — hors d'un port deterministe. La seule chose
   portee est la *convention de correlation* (`create_response` inverse
   emetteur/destinataire, `reply_to` l'id de la requete).
3. **`EventMessage` / `CommandMessage` specialises ne sont pas portes.** Le
   sas les decrit comme des constructeurs avec des valeurs par defaut
   (priorite HIGH, `requires_ack=True`) ; le port documente ces valeurs
   dans le notebook sans ajouter de sous-classes.
4. **Trois types de canal n'ont aucune implementation** (NEGOTIATION,
   FEEDBACK, SYSTEM) : le tronc les a **retires du routage** (#1571) plutot
   que de les cabler a des classes vides (anti-#1019). Le port conserve ce
   choix : `determine_channel` ne les retourne jamais.
"""

from __future__ import annotations

import enum
import functools
import uuid
from datetime import datetime
from typing import Any, Callable, Dict, List, Optional

__all__ = [
    "MessageType",
    "MessagePriority",
    "AgentLevel",
    "ChannelType",
    "Message",
    "Channel",
    "LocalChannel",
    "create_response",
    "determine_channel",
]


class MessageType(enum.Enum):
    """Types de messages supportes par le systeme."""

    COMMAND = "command"
    INFORMATION = "information"
    REQUEST = "request"
    RESPONSE = "response"
    EVENT = "event"
    CONTROL = "control"
    PUBLICATION = "publication"
    SUBSCRIPTION = "subscription"


class MessagePriority(enum.Enum):
    """Niveaux de priorite des messages."""

    LOW = "low"
    NORMAL = "normal"
    HIGH = "high"
    CRITICAL = "critical"


class AgentLevel(enum.Enum):
    """Niveaux des agents dans l'architecture hierarchique."""

    STRATEGIC = "strategic"
    TACTICAL = "tactical"
    OPERATIONAL = "operational"
    SYSTEM = "system"


class ChannelType(enum.Enum):
    """Types de canaux supportes par le systeme."""

    HIERARCHICAL = "hierarchical"
    COLLABORATION = "collaboration"
    DATA = "data"
    NEGOTIATION = "negotiation"
    FEEDBACK = "feedback"
    SYSTEM = "system"
    LOCAL = "local"


_PRIORITY_ORDER = {
    MessagePriority.LOW: 0,
    MessagePriority.NORMAL: 1,
    MessagePriority.HIGH: 2,
    MessagePriority.CRITICAL: 3,
}


@functools.total_ordering
class Message:
    """Representation d'un message dans le systeme de communication.

    Format commun : type / emetteur / niveau / priorite / contenu, un id
    derive du type (``command-<hex8>``), et un **ordonnancement total
    inverse** : ``__lt__`` est ecrit pour que la priorite la plus HAUTE soit
    la plus « petite » — ``sorted()`` sort donc CRITICAL en premier, meme
    arrive en dernier. A priorite egale, le plus ancien passe d'abord (FIFO).
    """

    def __init__(
        self,
        message_type: MessageType,
        sender: str,
        sender_level: AgentLevel,
        content: Dict[str, Any],
        recipient: Optional[str] = None,
        channel: Optional[str] = None,
        priority: MessagePriority = MessagePriority.NORMAL,
        metadata: Optional[Dict[str, Any]] = None,
        message_id: Optional[str] = None,
        timestamp: Optional[datetime] = None,
    ):
        self.id = message_id or f"{message_type.value}-{uuid.uuid4().hex[:8]}"
        self.type = message_type
        self.sender = sender
        self.sender_level = sender_level
        self.recipient = recipient
        self.channel = channel
        self.priority = priority
        self.content = content
        self.metadata = metadata or {}
        self.timestamp = timestamp or datetime.now()

    def __eq__(self, other):
        if not isinstance(other, Message):
            return NotImplemented
        return (
            self.priority == other.priority
            and self.timestamp == other.timestamp
            and self.id == other.id
        )

    def __lt__(self, other):
        if not isinstance(other, Message):
            return NotImplemented
        # Priorite plus haute (valeur numerique plus grande) vient en premier
        if _PRIORITY_ORDER[self.priority] != _PRIORITY_ORDER[other.priority]:
            return _PRIORITY_ORDER[self.priority] > _PRIORITY_ORDER[other.priority]
        # A priorite egale, le plus ancien (timestamp plus petit) vient en premier
        return self.timestamp < other.timestamp

    def to_dict(self) -> Dict[str, Any]:
        """Convertit le message en dictionnaire (serialisation)."""
        return {
            "id": self.id,
            "type": self.type.value,
            "sender": self.sender,
            "sender_level": self.sender_level.value,
            "recipient": self.recipient,
            "channel": self.channel,
            "priority": self.priority.value,
            "content": self.content,
            "metadata": self.metadata,
            "timestamp": self.timestamp.isoformat(),
        }

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> "Message":
        """Recree un message depuis son dictionnaire."""
        return cls(
            message_type=MessageType(data["type"]),
            sender=data["sender"],
            sender_level=AgentLevel(data["sender_level"]),
            content=data["content"],
            recipient=data.get("recipient"),
            channel=data.get("channel"),
            priority=MessagePriority(data["priority"]),
            metadata=data.get("metadata"),
            message_id=data["id"],
            timestamp=datetime.fromisoformat(data["timestamp"]),
        )


def create_response(request: Message, sender_level: AgentLevel, content: Dict[str, Any]) -> Message:
    """Cree une reponse a une requete en inversant emetteur et destinataire.

    Convention de correlation : la reponse porte ``reply_to`` = ``id`` de la
    requete, et ``recipient`` = ``sender`` de la requete. L'emetteur de la
    reponse est le destinataire de la requete.
    """
    return Message(
        MessageType.RESPONSE,
        sender=request.recipient or "unknown",
        sender_level=sender_level,
        content=content,
        recipient=request.sender,
        channel=request.channel,
        priority=request.priority,
        metadata={"reply_to": request.id},
    )


class Channel:
    """Contrat de canal : envoi, reception, abonnement, gestion des messages.

    Un canal est identifie par un ``id`` et un ``ChannelType`` ; il maintient
    une file d'attente de messages et un registre d'abonnes avec filtres.
    Le matcher de filtre est **fail-loud** : une cle hors contrat leve
    ``ValueError`` plutot que d'etre ignoree (une cle ignoree elargit
    silencieusement le filtre — incident #2161).
    """

    #: Les seules cles de filtre honorees par ce matcher.
    FILTER_KEYS = frozenset(
        {"message_type", "sender", "priority", "sender_level", "content"}
    )

    def __init__(self, channel_id: str, channel_type: ChannelType, config: Optional[Dict[str, Any]] = None):
        self.id = channel_id
        self.type = channel_type
        self.config = config or {}
        self.subscribers: Dict[str, Dict[str, Any]] = {}
        self._message_queue: List[Message] = []

    def matches_filter(self, message: Message, filter_criteria: Dict[str, Any]) -> bool:
        """Teste un message contre un filtre. Fail-loud sur cle inconnue."""
        if not filter_criteria:
            return True
        for key, value in filter_criteria.items():
            if key not in self.FILTER_KEYS:
                raise ValueError(
                    f"Unknown filter criteria key {key!r} — honored keys: "
                    f"{sorted(self.FILTER_KEYS)}. A key the matcher ignores "
                    "would silently widen the filter (#2161)."
                )
            if key == "message_type":
                if isinstance(value, list):
                    if message.type.value not in value:
                        return False
                elif message.type.value != value:
                    return False
            elif key == "sender":
                if isinstance(value, list):
                    if message.sender not in value:
                        return False
                elif message.sender != value:
                    return False
            elif key == "priority":
                if isinstance(value, list):
                    if message.priority.value not in value:
                        return False
                elif message.priority.value != value:
                    return False
            elif key == "sender_level":
                if isinstance(value, list):
                    if message.sender_level.value not in value:
                        return False
                elif message.sender_level.value != value:
                    return False
            elif key == "content":
                for content_key, content_val in value.items():
                    if (
                        content_key not in message.content
                        or message.content[content_key] != content_val
                    ):
                        return False
        return True

    def send_message(self, message: Message) -> bool:
        """Envoie un message sur le canal : file + notification des abonnes."""
        self._message_queue.append(message)
        for sub_id, sub_info in list(self.subscribers.items()):
            callback = sub_info.get("callback")
            filter_criteria = sub_info.get("filter")
            if self.matches_filter(message, filter_criteria or {}):
                if callback:
                    callback(message)
        return True

    def receive_message(self, recipient_id: str, timeout: Optional[float] = None) -> Optional[Message]:
        """Recoit le premier message destine a ``recipient_id`` (None = broadcast)."""
        for i, msg in enumerate(self._message_queue):
            if msg.recipient in (None, recipient_id):
                return self._message_queue.pop(i)
        return None

    def subscribe(
        self,
        subscriber_id: str,
        callback: Optional[Callable[[Message], None]] = None,
        filter_criteria: Optional[Dict[str, Any]] = None,
    ) -> str:
        """Abonne un composant pour recevoir des messages."""
        self.subscribers[subscriber_id] = {"callback": callback, "filter": filter_criteria}
        return subscriber_id

    def unsubscribe(self, subscription_id: str) -> bool:
        """Desabonne un composant."""
        return self.subscribers.pop(subscription_id, None) is not None

    def get_pending_messages(self, recipient_id: str, max_count: Optional[int] = None) -> List[Message]:
        """Recupere les messages en attente pour un destinataire."""
        pending = [m for m in self._message_queue if m.recipient in (None, recipient_id)]
        if max_count is not None:
            return pending[:max_count]
        return pending

    def get_channel_info(self) -> Dict[str, Any]:
        """Informations sur l'etat du canal."""
        return {
            "id": self.id,
            "type": self.type.value,
            "subscribers": len(self.subscribers),
            "pending": len(self._message_queue),
        }


class LocalChannel(Channel):
    """Canal de communication local et en memoire.

    Implementation simple du contrat : file d'attente en memoire, notification
    synchrone des abonnes. Ideal pour la communication intra-processus, les
    tests, ou les scenarios sans reseau.
    """

    def __init__(self, channel_id: str, config: Optional[Dict[str, Any]] = None):
        super().__init__(channel_id, ChannelType.LOCAL, config)


# ── Routage : le middleware decide du canal ────────────────────────────────
#
# determine_channel est la seule partie du middleware portee (divergence 1) :
# les canaux concrets et le protocole requete-reponse restent sur le tronc.
# Trois types de canal (NEGOTIATION, FEEDBACK, SYSTEM) n'ont aucune
# implementation : le routage vers eux a ete retire (#1571) plutot que de
# les cabler a des classes vides.


def determine_channel(message: Message) -> ChannelType:
    """Determine le canal approprie pour un message.

    Regles de routage par defaut (canal explicite > type de message >
    contenu > canal par defaut). Les types sans implementation
    (NEGOTIATION/FEEDBACK/SYSTEM) ne sont jamais retournes (#1571).
    """
    # Si le canal est specifie dans le message, l'utiliser
    if message.channel:
        try:
            return ChannelType(message.channel)
        except ValueError:
            pass  # canal invalide : tomber sur les regles

    # Regles de routage par defaut basees sur le type de message
    if message.type == MessageType.COMMAND:
        return ChannelType.HIERARCHICAL
    elif message.type == MessageType.INFORMATION:
        if "analysis_result" in message.content.get("info_type", ""):
            return ChannelType.DATA
        return ChannelType.HIERARCHICAL
    elif message.type == MessageType.REQUEST:
        request_type = message.content.get("request_type", "")
        if "assistance" in request_type:
            return ChannelType.COLLABORATION
        return ChannelType.HIERARCHICAL
    elif message.type == MessageType.RESPONSE:
        return ChannelType.HIERARCHICAL
    elif message.type == MessageType.PUBLICATION:
        return ChannelType.DATA

    # #1571 : EVENT / CONTROL / SUBSCRIPTION ne routent plus vers FEEDBACK /
    # SYSTEM (canaux sans implementation). Ils tombent sur le bus par defaut.
    return ChannelType.HIERARCHICAL
