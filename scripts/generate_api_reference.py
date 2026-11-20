"""Refresh the documented Python signatures from the checkout."""

import argparse
from html import escape
from importlib import import_module
from inspect import Parameter, Signature, formatannotation, signature
from itertools import groupby
from pathlib import Path
import re
from typing import get_origin


REFERENCE = Path(__file__).resolve().parents[1] / "docs/reference/python/functions.md"
ENTRY = re.compile(
    r"^<!-- api-signature: (?P<module>itpeval(?:\.\w+)+):(?P<name>\w+(?:\.\w+)*) -->\n"
    r'<pre class="api-signature"><code>.*?</code></pre>',
    flags=re.MULTILINE | re.DOTALL,
)


def annotation_text(annotation):
    if isinstance(annotation, str):
        return annotation
    if get_origin(annotation) is None and isinstance(annotation, type):
        return annotation.__qualname__
    return formatannotation(annotation)


def parameter_text(parameter):
    if parameter.annotation is Parameter.empty:
        return str(parameter)
    name = str(parameter.replace(annotation=Parameter.empty, default=Parameter.empty))
    result = f"{name}: {annotation_text(parameter.annotation)}"
    if parameter.default is not Parameter.empty:
        result += f" = {parameter.default!r}"
    return result


def signature_text(module, name):
    target = import_module(module)
    for attribute in name.split("."):
        target = getattr(target, attribute)
    actual = signature(target, eval_str=False)
    parameters = tuple(actual.parameters.values())
    if "." in name and parameters and parameters[0].name == "self":
        parameters = parameters[1:]

    arguments = []
    varargs = False
    for kind, group in groupby(parameters, key=lambda parameter: parameter.kind):
        if kind == Parameter.KEYWORD_ONLY and not varargs:
            arguments.append("*")
        arguments.extend(parameter_text(parameter) for parameter in group)
        if kind == Parameter.POSITIONAL_ONLY:
            arguments.append("/")
        if kind == Parameter.VAR_POSITIONAL:
            varargs = True

    suffix = ""
    if actual.return_annotation is not Signature.empty and not isinstance(target, type):
        suffix = f" -> {annotation_text(actual.return_annotation)}"
    display = name if "." in name else f"{module}.{name}"
    compact = f"{display}({', '.join(arguments)}){suffix}"
    if len(compact) <= 88:
        return compact
    body = "".join(f"    {argument},\n" for argument in arguments)
    return f"{display}(\n{body}){suffix}"


def render(markdown):
    def replace(match):
        module, name = match.group("module", "name")
        value = escape(signature_text(module, name), quote=False)
        return f'<!-- api-signature: {module}:{name} -->\n<pre class="api-signature"><code>{value}</code></pre>'

    rendered, count = ENTRY.subn(replace, markdown)
    if count == 0 or count != markdown.count("<!-- api-signature:"):
        raise ValueError("Each API signature marker needs a qualified callable and a signature block")
    return rendered


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="report stale signatures without writing")
    args = parser.parse_args()
    original = REFERENCE.read_text(encoding="utf-8")
    updated = render(original)
    if args.check:
        if original != updated:
            raise SystemExit("Python API signatures are stale. Run python -m scripts.generate_api_reference.")
    elif original != updated:
        REFERENCE.write_text(updated, encoding="utf-8")


if __name__ == "__main__":
    main()
