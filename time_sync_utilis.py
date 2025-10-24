"""Utility helpers for performing synchronized four-timestamp exchanges.

This module centralizes the active time-synchronization handshake that is
shared between the different TLS endpoints in the system.  It provides a
common readiness token, a ``recv_exact`` helper so callers can block until the
exact number of bytes is received, and ``perform_time_sync`` which implements a
four-timestamp round-trip exchange (similar to a simplified NTP exchange).
"""
from __future__ import annotations

from dataclasses import dataclass
import struct
import time
from typing import Callable, Optional

# One-byte cue letting the peer know the socket is idle and ready for the
# four-timestamp exchange to begin.  A fixed value keeps the protocol simple
# and unambiguous.
TIME_SYNC_READY_TOKEN = b"\x01"


class TimeSyncError(RuntimeError):
    """Raised when the socket closes unexpectedly during time sync."""


@dataclass(frozen=True)
class TimeSyncResult:
    """Container describing the outcome of ``perform_time_sync``."""

    offset_us: int
    delay_us: int
    t1: int
    t2: int
    t3: int
    t4: int


def _now_us() -> int:
    """Return the current time in microseconds as an integer."""
    return int(time.time() * 1_000_000)


def recv_exact(sock, size: int) -> bytes:
    """Receive exactly ``size`` bytes from ``sock``.

    ``socket.recv`` may return less data than requested, so this helper loops
    until the requested amount has been delivered or the connection is closed.
    A :class:`TimeSyncError` is raised if the peer closes the connection early.
    """

    data = bytearray()
    while len(data) < size:
        chunk = sock.recv(size - len(data))
        if not chunk:
            raise TimeSyncError(
                f"Socket closed while waiting for {size} bytes (received {len(data)})"
            )
        data.extend(chunk)
    return bytes(data)


def perform_time_sync(
    sock,
    role: str,
    logger: Optional[Callable[[str], None]] = None,
    log_prefix: str = "",
) -> TimeSyncResult:
    """Execute the four-timestamp time synchronisation exchange.

    Parameters
    ----------
    sock:
        Blocking socket used for the handshake.
    role:
        Either ``"client"`` or ``"server"`` depending on which side is calling
        this function.
    logger:
        Optional callable used for logging (e.g. ``logger.info``).  When
        provided the function emits a short summary once the exchange finishes.
    log_prefix:
        Prefix appended to log messages to help identify the peer.

    Returns
    -------
    :class:`TimeSyncResult`
        Object containing the computed offset (server - client), estimated
        network delay and the raw timestamps collected throughout the exchange.
    """

    if role not in {"client", "server"}:
        raise ValueError("role must be 'client' or 'server'")

    if role == "client":
        t1 = _now_us()
        sock.sendall(struct.pack("<Q", t1))

        payload = recv_exact(sock, 24)
        
        t1_echo, t2, t3 = struct.unpack("<QQQ", payload)
        if t1_echo != t1 and logger is not None:
            logger(
                f"{log_prefix}Time sync warning: echoed t1={t1_echo} differs from sent t1={t1}"
            )
        t4 = _now_us()
        sock.sendall(struct.pack("<Q", t4))
    else:  # role == "server"
        t1 = struct.unpack("<Q", recv_exact(sock, 8))[0]
        t2 = _now_us()
        t3 = _now_us()
        sock.sendall(struct.pack("<QQQ", t1, t2, t3))

        
        t4 = struct.unpack("<Q", recv_exact(sock, 8))[0]

    # Use the standard NTP-style calculations.
    offset = ((t2 - t1) + (t3 - t4)) / 2.0
    delay = (t4 - t1) - (t3 - t2)

    result = TimeSyncResult(
        offset_us=int(round(offset)),
        delay_us=int(round(delay)),
        t1=t1,
        t2=t2,
        t3=t3,
        t4=t4,
    )

    if logger is not None:
        logger(
            (
                f"{log_prefix}Time sync complete: offset={result.offset_us} μs, "
                f"delay={result.delay_us} μs, t1={t1}, t2={t2}, t3={t3}, t4={t4}"
            )
        )

    return result