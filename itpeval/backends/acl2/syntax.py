"""Locations and leading symbols of top-level ACL2 forms."""
import re

_TOKEN = re.compile(rb';[^\n]*|#\||\|#|"(?:\\.|[^"\\])*"|\(|\)|[^\s();"#|]+|\S', re.DOTALL)
_HEAD = re.compile(rb'\(\s*([\w-]+)\s+(?:"([^"]+)"|([\w*+:./-]+))')


def _forms(raw, *, sections=False):
    # ACL2 validates the forms. Only top-level names and immediate DEFSECTION
    # children are proposed as public world events. LOCAL never exports a name.
    stack, comment = [], 0
    for m in _TOKEN.finditer(raw):
        data = m[0]
        if data == b"#|":
            comment += 1
        elif comment:
            if data == b"|#":
                comment -= 1
        elif data == b"(":
            stack.append(m.start())
        elif data == b")":
            if not stack:
                raise ValueError("unmatched closing parenthesis")
            start = stack.pop()
            if not stack or (sections and len(stack) == 1 and
                             re.match(rb'\(\s*defsection\s', raw[stack[0]:], re.IGNORECASE)):
                yield start, m.end(), raw[start:m.end()]
        elif not stack and not data.startswith(b";"):
            raise ValueError("only ACL2 book forms can be extracted")
    if stack or comment:
        raise ValueError("unterminated ACL2 form or comment")
