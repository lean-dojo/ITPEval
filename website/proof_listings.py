"""Typeset the native source excerpts on the prover guides."""
import re

from bs4 import BeautifulSoup
from pygments import format as format_tokens
from pygments.formatters import HtmlFormatter
from pygments.lexer import RegexLexer, words
from pygments.lexers import TextLexer, get_lexer_by_name
from pygments.util import ClassNotFound
from pygments.token import Comment, Keyword, Name, Number, Operator, Punctuation, String, Text, Whitespace


class MetamathLexer(RegexLexer):
    tokens = {"root": [
        (r"\$\([\s\S]*?\$\)", Comment.Multiline),
        (r"\$[cvdfeap]", Keyword.Declaration),
        (r"\$[.={}\[\]]", Punctuation),
        (r"\s+", Whitespace), (r"[^\s$]+", Name), (r".", Text),
    ]}


class MizarLexer(RegexLexer):
    tokens = {"root": [
        (r"::[^\n]*", Comment.Single),
        (words(("theorem", "for", "being", "holds", "by", "proof", "thus", "end", "let",
                "begin", "environ", "assume", "then", "hence", "definition"), suffix=r"\b"), Keyword),
        (r'"[^"\n]*"', String), (r"\d+", Number), (r"[\w']+", Name),
        (r"[=:<>]+", Operator), (r"\s+", Whitespace), (r".", Punctuation),
    ]}


class PVSLexer(RegexLexer):
    flags = re.IGNORECASE | re.MULTILINE
    tokens = {"root": [
        (r"%[^\n]*", Comment.Single), (r'"(?:\\.|[^"\\])*"', String),
        (words(("THEORY", "IMPORTING", "BEGIN", "END", "LEMMA", "THEOREM", "FORALL",
                "EXISTS", "TYPE", "AXIOM", "PROOF", "QED"), suffix=r"\b"), Keyword),
        (r"\d+(?:\.\d+)?", Number), (r"[\w?']+", Name),
        (r"[=<>|+*/-]+", Operator), (r"\s+", Whitespace), (r".", Punctuation),
    ]}


def highlight_proof(code, proof, soup):
    # A proof can start midway through a line and cross several highlighted tokens.
    source = code.get_text()
    if source.count(proof) != 1:
        raise ValueError(f"Expected one occurrence of the proof fragment {proof!r}")
    start = source.index(proof)
    end = start + len(proof)
    offset = 0
    for node in list(code.strings):
        left = max(0, start - offset)
        right = min(len(node), end - offset)
        offset += len(node)
        if left < right:
            mark = soup.new_tag("mark", attrs={"class": "formal-proof"})
            mark.string = node[left:right]
            node.replace_with(node[:left], mark, node[right:])


def on_page_content(html, page, **kwargs):
    if not (page.file.src_uri.startswith("provers/") or page.file.src_uri == "start/reading-proofs.md"):
        return html
    custom = {"metamath": MetamathLexer, "mizar": MizarLexer, "pvs": PVSLexer}
    aliases = {"acl2": "common-lisp", "hol-light": "ocaml", "hol4": "sml", "rocq": "coq"}
    commands = {"acl2": {"defthm", "defun", "defaxiom"}, "hol4": {"Theorem", "Proof", "QED", "Definition", "End"}}
    soup = BeautifulSoup(html, "html.parser")
    for figure in soup.select("figure.proof-listing"):
        prover = figure["data-listing"]
        try:
            lexer = custom[prover]() if prover in custom else get_lexer_by_name(aliases.get(prover, prover))
        except ClassNotFound:
            lexer = TextLexer()
        code = figure.select_one("pre code")
        tokens = ((Keyword if token in Name and value in commands.get(prover, ()) else token, value)
                  for token, value in lexer.get_tokens(code.get_text()))
        markup = format_tokens(tokens, HtmlFormatter(nowrap=True))
        code.clear()
        # Parse in a preformatted context so the HTML parser keeps indentation.
        fragment = BeautifulSoup("<pre>" + markup + "</pre>", "html.parser")
        code.extend(fragment.pre.contents[:])
        if proof := figure.attrs.pop("data-proof", None):
            highlight_proof(code, proof, soup)
        figure.pre["data-language"] = prover
        figure.figcaption.strong["data-prover"] = prover
    return str(soup)
