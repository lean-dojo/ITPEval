"""Locate the decoded clauses in an exact Sprig source file."""

import json
import re

from kernel import initial_clauses


def read_json(source):
    def unique_fields(pairs):
        result = dict(pairs)
        if len(result) != len(pairs):
            raise ValueError("duplicate Sprig JSON field")
        return result

    return json.loads(source.decode("utf-8"), object_pairs_hook=unique_fields)


def parse_problem(source):
    problem = read_json(source)
    initial_clauses(problem)
    text = source.decode("ascii")
    decoder = json.JSONDecoder()
    whitespace = re.compile(r"[ \t\r\n]*")

    def skip(position):
        return whitespace.match(text, position).end()

    cursor = skip(0) + 1
    members = {}
    for _ in range(2):
        key_start = skip(cursor)
        key, key_end = decoder.raw_decode(text, key_start)
        start = skip(skip(key_end) + 1)
        _, end = decoder.raw_decode(text, start)
        members[key] = key_start, start, end
        cursor = skip(end) + 1
    _, opening, _ = members["premises"]
    cursor = opening + 1
    premises = []
    for _ in problem["premises"]:
        start = skip(cursor)
        _, end = decoder.raw_decode(text, start)
        premises.append((start, end))
        cursor = skip(end) + 1
    key_start, _, end = members["goal"]
    return problem, premises, (key_start, end)
