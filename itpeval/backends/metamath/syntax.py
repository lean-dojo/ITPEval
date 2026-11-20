"""Tokenize Metamath source while retaining original byte offsets."""
import re


def tokens(raw):
    comment = False
    for match in re.finditer(rb"\S+", raw):
        word = match[0]
        if word == b"$(" and not comment:
            comment = True
        elif word == b"$)" and comment:
            comment = False
        elif not comment:
            yield word.decode("ascii"), match.start(), match.end()
    if comment:
        raise ValueError("unterminated Metamath comment")
