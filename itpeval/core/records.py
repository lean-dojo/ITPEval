"""Versioned JSON records with strict decoding and draft 2020-12 schemas."""
from __future__ import annotations

import dataclasses
import hashlib
import json
import types
from typing import Any, Literal, Union, get_args, get_origin, get_type_hints

VERSION = 1


def digest(value: Any) -> str:
    data = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False,
                      allow_nan=False).encode()
    return hashlib.sha256(data).hexdigest()


def _encode(value):
    if isinstance(value, Record):
        return value.to_dict()
    if isinstance(value, (tuple, list)):
        return [_encode(item) for item in value]
    if isinstance(value, dict):
        return {key: _encode(item) for key, item in value.items()}
    return value


def _decode(hint, value):
    origin, args = get_origin(hint), get_args(hint)
    if hint is Any:
        return value
    if origin in (Union, types.UnionType):
        for member in args:
            try:
                return _decode(member, value)
            except (ValueError, TypeError):
                continue
        raise ValueError(f"unexpected value for {hint!r}")
    if origin is Literal and value in args:
        return value
    if origin in (tuple, list) and isinstance(value, list):
        if origin is list or (len(args) == 2 and args[1] is Ellipsis):
            items = [_decode(args[0], item) for item in value]
        elif len(args) == len(value):
            items = [_decode(member, item) for member, item in zip(args, value)]
        else:
            raise ValueError("incorrect tuple length")
        return origin(items)
    if origin is dict and isinstance(value, dict):
        return {_decode(args[0], key): _decode(args[1], item) for key, item in value.items()}
    if isinstance(hint, type) and issubclass(hint, Record):
        return hint.from_dict(value)
    if type(value) is hint or (hint is float and type(value) is int):
        return value
    raise ValueError(f"unexpected value for {hint!r}")


def _schema(hint):
    origin, args = get_origin(hint), get_args(hint)
    if hint is Any:
        return {}
    if origin in (Union, types.UnionType):
        return {"anyOf": [_schema(member) for member in args]}
    if origin is Literal:
        return {"enum": list(args)}
    if origin in (tuple, list):
        if origin is list or (len(args) == 2 and args[1] is Ellipsis):
            return {"type": "array", "items": _schema(args[0])}
        return {"type": "array", "prefixItems": [_schema(member) for member in args],
                "minItems": len(args), "maxItems": len(args)}
    if origin is dict:
        return {"type": "object", "additionalProperties": _schema(args[1])}
    if isinstance(hint, type) and issubclass(hint, Record):
        return hint.json_schema()
    return {"type": {type(None): "null", bool: "boolean", str: "string", int: "integer",
                     float: "number"}[hint]}


class Record:
    def to_dict(self) -> dict:
        return {"schema_version": VERSION,
                **{f.name: _encode(getattr(self, f.name)) for f in dataclasses.fields(self)}}

    @classmethod
    def from_dict(cls, data):
        if not isinstance(data, dict) or type(data.get("schema_version")) is not int or data["schema_version"] != VERSION:
            raise ValueError(f"unsupported {cls.__name__} schema version")
        fields = {field.name for field in dataclasses.fields(cls)}
        if data.keys() - fields - {"schema_version"}:
            raise ValueError(f"unknown fields for {cls.__name__}")
        hints = get_type_hints(cls)
        return cls(**{key: _decode(hints[key], value) for key, value in data.items()
                      if key != "schema_version"})

    @classmethod
    def json_schema(cls) -> dict:
        fields = dataclasses.fields(cls)
        hints = get_type_hints(cls)
        return {"$schema": "https://json-schema.org/draft/2020-12/schema", "title": cls.__name__,
                "type": "object", "additionalProperties": False,
                "properties": {"schema_version": {"const": VERSION},
                               **{f.name: _schema(hints[f.name]) for f in fields}},
                "required": ["schema_version", *(f.name for f in fields
                             if f.default is dataclasses.MISSING and f.default_factory is dataclasses.MISSING)]}
