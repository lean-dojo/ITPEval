"""Public verification entrypoints."""

from .policies import candidate_from_bytes
from .service import verify, verify_document

__all__ = ["candidate_from_bytes", "verify", "verify_document"]
