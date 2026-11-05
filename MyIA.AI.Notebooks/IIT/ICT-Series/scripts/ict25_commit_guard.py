"""Garde de commit ICT-25 -- mesure au prevol et surveillance pendant le run.

Origine : #24180 (garde de prevol) puis #24674 (le run reste sans protection
une fois demarre). La garde de prevol mesure la marge **une seule fois**, a la
naissance du process ; un bras ne pendant une heure creuse passe le seuil puis
reste nu pendant toute sa vie, et meurt exactement comme avant la garde quand
la pression monte (signature mesuree sur po-2027 le 02/11 : naissance 06:42:58Z
avec 20 Go de marge, puis 98,5 % a 07:49, 96,7 % a 08:54, 95,9 % a 13:34,
97,3 % a 17:29).

Module **pur** : aucune dependance lourde (ni torch, ni transformers), pour que
le contrat de la garde soit testable en CI sans GPU -- meme choix que
``ict25_records.py``.

Deux grandeurs, une seule source :

- la **marge de commit disponible** est la grandeur de decision. L'empreinte
  d'un bras est absolue (~11 Go), donc le plancher qui la protege l'est aussi ;
- le **plafond de commit** est porte a la telemetrie. Ce n'est pas une
  constante du jour : sur po-2027 il a varie de ~79,6 a ~95,6 Go le 02/11 au
  fil du cycle de pagefile (32 Go a 01:29Z, retour a 16 Go avant 05:14Z), donc
  un chiffre de marge nu se lit mal -- « 4,2 Go » ne dit pas la meme chose sur
  un plafond de 79,6 que sur un plafond de 95,6. Mesure Maintenance du 04/11
  versee en #24674.
"""

from __future__ import annotations

import sys
from dataclasses import dataclass
from typing import Callable

GO = 1024 ** 3

# Meme seuil qu'a la naissance (#24180, calibre sur le csv commit-pressure du
# 02/11) : le siege mort avait ~14 Go de marge AVANT le bras, donc 12 Go
# laissaient passer le run qui a tue la machine ; le defaut exige bras (~11 Go)
# + burst CI concurrent (~8-10 Go), soit ~20 Go.
DEFAULT_MIN_START_HEADROOM_GO = 20.0

# Plancher PENDANT le run. Il est volontairement beaucoup plus bas que le
# seuil de demarrage : a ce stade le bras a deja alloue ses ~11 Go, et exiger
# 20 Go en cours de route ferait avorter tout run sain. 4 Go est la marge ou
# le siege est encore vivant (le declencheur de mort observe est la saturation
# du commit, pas un seuil intermediaire) et ou tuer le bras coute moins que
# perdre la machine.
DEFAULT_MIN_RUN_HEADROOM_GO = 4.0

# Periode d'echantillonnage, en steps du trainer. GRPO loggue deja tous les 5
# steps : la garde coute alors une lecture de GlobalMemoryStatusEx par cycle de
# log, soit une mesure gratuite.
DEFAULT_GUARD_EVERY_STEPS = 5


class CommitGuardAbort(RuntimeError):
    """Leve quand la marge de commit passe sous le plancher pendant le run."""


@dataclass(frozen=True)
class CommitStatus:
    """Marge de commit disponible et plafond du siege, en octets.

    ``limit_bytes`` peut etre ``None`` : certains systemes exposent la marge
    sans exposer le plafond. La decision porte alors sur la marge seule, et la
    telemetrie le dit au lieu d'inventer un plafond.
    """

    avail_bytes: int
    limit_bytes: int | None = None

    @property
    def avail_gb(self) -> float:
        return self.avail_bytes / GO

    @property
    def limit_gb(self) -> float | None:
        if self.limit_bytes is None:
            return None
        return self.limit_bytes / GO

    @property
    def used_pct(self) -> float | None:
        """Part du plafond de commit deja consommee (None si plafond inconnu)."""
        if not self.limit_bytes:
            return None
        return round(100.0 * (1.0 - self.avail_bytes / self.limit_bytes), 1)

    def describe(self) -> str:
        # ``not`` et pas ``is None`` : ``limit_bytes=0`` donne ``limit_gb=0.0``,
        # qui n'est pas None mais n'est pas un plafond non plus -- formater
        # ``used_pct`` (None) avec ``:.1f`` levait TypeError precisement au
        # moment ou la garde doit parler (review #24711, point 2).
        if not self.limit_gb:
            return f"{self.avail_gb:.1f} Go disponibles (plafond non mesurable)"
        return (f"{self.avail_gb:.1f} Go disponibles sur {self.limit_gb:.1f} Go "
                f"({self.used_pct:.1f} % utilises)")


def _windows_status() -> CommitStatus | None:
    """Marge et plafond de commit Windows (GlobalMemoryStatusEx).

    ``ullAvailPageFile`` / ``ullTotalPageFile`` : le commit, pas seulement la
    RAM physique -- c'est le commit qui a sature le 02/11.
    """
    import ctypes

    class _MemoryStatusEx(ctypes.Structure):
        # Les neuf champs de MEMORYSTATUSEX, dans l'ordre, sans trou : la
        # structure doit faire 64 octets, sinon GlobalMemoryStatusEx rend
        # ERROR_INVALID_PARAMETER (87) et la garde se croit « non mesurable »
        # sur une machine ou elle mesure tres bien.
        _fields_ = [
            ("dwLength", ctypes.c_ulong),
            ("dwMemoryLoad", ctypes.c_ulong),
            ("ullTotalPhys", ctypes.c_ulonglong),
            ("ullAvailPhys", ctypes.c_ulonglong),
            ("ullTotalPageFile", ctypes.c_ulonglong),
            ("ullAvailPageFile", ctypes.c_ulonglong),
            ("ullTotalVirtual", ctypes.c_ulonglong),
            ("ullAvailVirtual", ctypes.c_ulonglong),
            ("ullAvailExtendedVirtual", ctypes.c_ulonglong),
        ]

    status = _MemoryStatusEx()
    status.dwLength = ctypes.sizeof(_MemoryStatusEx)
    if not ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(status)):
        return None
    plafond = int(status.ullTotalPageFile) or None
    return CommitStatus(int(status.ullAvailPageFile), plafond)


# Valeur de ``vm.overcommit_memory`` sous laquelle le noyau REFUSE une
# allocation qui ferait passer ``Committed_AS`` au-dessus de ``CommitLimit``.
# Sous 0 (heuristique, defaut du noyau) et 1 (toujours accepter), ``CommitLimit``
# est un chiffre de comptabilite que rien n'applique : ``Committed_AS`` le
# depasse couramment sans qu'aucune allocation n'echoue (#24800).
_STRICT_OVERCOMMIT = 2


def _linux_status_from_text(text: str,
                            overcommit_mode: int | None = None
                            ) -> CommitStatus | None:
    """Statut de commit depuis le contenu de ``/proc/meminfo``.

    La grandeur lue depend du mode ``vm.overcommit_memory`` du noyau, parce que
    la limite qui tue un run n'est pas la meme :

    - **mode 2 (strict)** : le noyau refuse toute allocation au-dela de
      ``CommitLimit``. La marge est ``CommitLimit - Committed_AS``, la meme
      grandeur que ``ullAvailPageFile`` sous Windows (review #24711, point 1).
    - **modes 0 et 1, ou mode inconnu** : ``CommitLimit`` n'est applique par
      personne. Mesure du 05/11 sur la VM WSL des runners d'ai-01, en mode 1 :
      ``Committed_AS`` 107,6 Gio contre ``CommitLimit`` 94,9 Gio, avec
      ``MemAvailable`` 64,8 Gio. La lecture par le commit y rendait une marge
      nulle sur une machine saine, et rougissait ``Scripts Tests (CPU)`` sur
      ``main`` (#24800). Ce qui manque en premier, dans ces modes, c'est la
      memoire physique et le swap (l'OOM killer) : la marge est
      ``MemAvailable + SwapFree``, sur un plafond ``MemTotal + SwapTotal``.
      ``MemAvailable`` compte le cache recuperable, et c'est voulu : c'est
      l'estimation du noyau de ce qu'une allocation neuve peut obtenir sans
      faire swapper.

    Un mode inconnu (``/proc/sys/vm/overcommit_memory`` illisible) se lit comme
    le defaut du noyau, le mode 0 : supposer un mode strict que rien ne prouve
    rendrait la garde aveugle par exces de prudence, comme ici.
    """
    valeurs: dict[str, list[str]] = {}
    for ligne in text.splitlines():
        cle, sep, reste = ligne.partition(":")
        if sep:
            valeurs[cle] = reste.split()
    if (overcommit_mode == _STRICT_OVERCOMMIT
            and "CommitLimit" in valeurs and "Committed_AS" in valeurs):
        try:
            limite = int(valeurs["CommitLimit"][0]) * 1024
            engage = int(valeurs["Committed_AS"][0]) * 1024
        except (IndexError, ValueError):
            return None
        return CommitStatus(max(limite - engage, 0), limite or None)
    disponible = 0
    total = 0
    lu = False
    for cle in ("MemAvailable", "SwapFree", "MemTotal", "SwapTotal"):
        if cle not in valeurs:
            continue
        try:
            valeur = int(valeurs[cle][0]) * 1024
        except (IndexError, ValueError):
            continue
        if cle in ("MemAvailable", "SwapFree"):
            disponible += valeur
            lu = True
        else:
            total += valeur
    if not lu:
        return None
    return CommitStatus(disponible, total or None)


def _linux_overcommit_mode() -> int | None:
    """Mode ``vm.overcommit_memory`` du noyau, ou ``None`` s'il est illisible."""
    try:
        with open("/proc/sys/vm/overcommit_memory", encoding="ascii") as fh:
            return int(fh.read().strip())
    except (OSError, ValueError):
        return None


def _linux_status() -> CommitStatus | None:
    """Marge et plafond de commit Linux (/proc/meminfo + mode d'overcommit)."""
    try:
        with open("/proc/meminfo", encoding="ascii") as fh:
            texte = fh.read()
    except OSError:
        return None
    return _linux_status_from_text(texte, _linux_overcommit_mode())


def commit_status() -> CommitStatus | None:
    """Marge et plafond de commit du siege, ou ``None`` si non mesurable."""
    if sys.platform == "win32":
        return _windows_status()
    return _linux_status()


def _default_log(message: str) -> None:
    print(message, flush=True)


class CommitWatch:
    """Echantillonne la marge de commit pendant le run et coupe avant la mort.

    ``status_fn`` et ``log`` sont injectables : le contrat se teste sans
    toucher a la memoire reelle du siege.
    """

    def __init__(
        self,
        min_run_headroom_go: float = DEFAULT_MIN_RUN_HEADROOM_GO,
        every_steps: int = DEFAULT_GUARD_EVERY_STEPS,
        status_fn: Callable[[], CommitStatus | None] = commit_status,
        log: Callable[[str], None] = _default_log,
    ) -> None:
        if every_steps < 1:
            raise ValueError("every_steps doit valoir >= 1")
        self.min_run_headroom_go = float(min_run_headroom_go)
        self.every_steps = int(every_steps)
        self._status_fn = status_fn
        self._log = log
        self.samples = 0
        self.min_avail_gb: float | None = None
        self.abort_reason: str | None = None
        self._warned_unmeasurable = False

    def maybe_sample(self, step: int) -> CommitStatus | None:
        """Mesure la marge si ``step`` tombe sur la periode.

        Retourne le statut echantillonne, ou ``None`` quand le step est hors
        periode ou que la marge n'est pas mesurable. Leve
        ``CommitGuardAbort`` quand la marge mesuree passe sous le plancher.
        """
        if step % self.every_steps != 0:
            return None
        statut = self._status_fn()
        if statut is None:
            if not self._warned_unmeasurable:
                self._warned_unmeasurable = True
                self._log("[ict25_arms] garde memoire: marge non mesurable "
                          "pendant le run, surveillance sautee")
            return None
        self.samples += 1
        if self.min_avail_gb is None or statut.avail_gb < self.min_avail_gb:
            self.min_avail_gb = statut.avail_gb
        self._log(f"[ict25_arms] garde memoire step {step}: {statut.describe()}")
        if statut.avail_gb < self.min_run_headroom_go:
            self.abort_reason = (
                f"marge de commit {statut.avail_gb:.1f} Go < plancher de run "
                f"{self.min_run_headroom_go:.1f} Go au step {step} "
                f"({statut.describe()})"
            )
            self._log(f"[ict25_arms] ARRET DE LA GARDE: {self.abort_reason}")
            raise CommitGuardAbort(self.abort_reason)
        return statut

    def summary(self) -> dict:
        """Etat de la surveillance, destine a la telemetrie de l'artefact."""
        return {
            "samples": self.samples,
            "min_avail_go": (None if self.min_avail_gb is None
                             else round(self.min_avail_gb, 2)),
            "min_run_headroom_go": self.min_run_headroom_go,
            "every_steps": self.every_steps,
            "aborted": self.abort_reason is not None,
            "abort_reason": self.abort_reason,
        }
