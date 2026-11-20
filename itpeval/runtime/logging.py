"""Bound native logs by bytes while continuously draining process pipes."""


class LogTail:
    def __init__(self, limit: int):
        if limit <= 0:
            raise ValueError("log limit must be positive")
        self.limit = limit
        self.truncated = False
        self._buffer = bytearray()

    def append(self, chunk: bytes):
        self._buffer.extend(chunk)
        if len(self._buffer) > self.limit:
            del self._buffer[:-self.limit]
            self.truncated = True

    def text(self):
        return self._buffer.decode(errors="replace")
