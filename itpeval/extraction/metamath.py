"""Read verified Metamath statements, scoped hypotheses and direct proof references."""

import itertools
import re

from itpeval.backends.metamath.syntax import tokens as _tokens
from itpeval.corpus.contexts import METAMATH_PREFIX
from itpeval.corpus.storage import encode, object_id, project_file


def _proof_steps(proof, mandatory):
    if proof[0] != "(":
        return proof
    end = proof.index(")")
    labels = [*mandatory, *proof[1:end]]
    steps = []
    high = saved = 0
    for ch in "".join(proof[end + 1:]):
        if "U" <= ch <= "Y":
            high = 5 * high + ord(ch) - ord("U") + 1
        elif "A" <= ch <= "T":
            number = 20 * high + ord(ch) - ord("A") + 1
            if not 1 <= number <= len(labels) + saved:
                raise ValueError("invalid compressed proof reference")
            steps.append(labels[number - 1] if number <= len(labels)
                         else {"reuse": number - len(labels)})
            high = 0
        elif ch == "Z" and not high:
            saved += 1
            steps.append({"save": saved})
        else:
            raise ValueError("invalid compressed proof")
    if high:
        raise ValueError("unfinished compressed proof number")
    return steps


def _apply_proof(steps, labels, signatures, current_variables, disjoint, expected):
    """Expand compressed operations and check every substitution against its frame."""
    stack, saved, trace = [], [], []
    allowed = set(disjoint)

    def substitute(expression, substitution):
        return tuple(token for sym in expression for token in substitution.get(sym, (sym,)))

    for step in steps:
        before = len(stack)
        if isinstance(step, dict):
            if "save" in step:
                saved.append(stack[-1])
            else:
                stack.append(saved[step["reuse"] - 1])
        else:
            kind, _, expr = labels[step]
            if kind in {"$f", "$e"}:
                stack.append(tuple(expr))
            else:
                mandatory, constraints = signatures[step]
                if len(stack) < len(mandatory):
                    raise ValueError(f"stack underflow at {step}")
                arguments = stack[before - len(mandatory):]
                del stack[before - len(mandatory):]
                substitution = {}
                for h, arg in zip(mandatory, arguments):
                    hkind, _, hypothesis = labels[h]
                    if hkind == "$f":
                        if not arg or arg[0] != hypothesis[0]:
                            raise ValueError(f"typecode mismatch at {step}")
                        substitution[hypothesis[1]] = arg[1:]
                for h, arg in zip(mandatory, arguments):
                    hkind, _, hypothesis = labels[h]
                    if hkind == "$e" and substitute(hypothesis, substitution) != arg:
                        raise ValueError(f"essential hypothesis mismatch at {step}")
                for x, y in constraints:
                    for a in current_variables.intersection(substitution[x]):
                        for b in current_variables.intersection(substitution[y]):
                            if a == b or tuple(sorted((a, b))) not in allowed:
                                raise ValueError(f"disjoint variable violation at {step}")
                stack.append(substitute(expr, substitution))
        trace.append({"step": step, "height_before": before, "height_after": len(stack),
                      "top": list(stack[-1])})
    if stack != [tuple(expected)]:
        raise ValueError("proof stack did not produce the stated assertion")
    return trace


def extract(ctx, entrypoint):
    if ctx.prepared.spec.options or ctx.prepared.library_paths:
        raise ValueError("Metamath requires explicit includes within the locked project")
    labels = {}
    hypotheses = []
    disjoint = []
    active_vars = set()
    frames = []
    files = set()
    imports = []
    proofs = {}
    signatures = {}
    compact = ctx.context_storage == "compact"
    assertion_count = 0
    assertion_digest = object_id(METAMATH_PREFIX)

    # Read the includes from the locked project before invoking the native reader.
    def parse(path):
        nonlocal assertion_count, assertion_digest
        if path in files:
            return
        files.add(path)
        tokens = iter(_tokens(ctx.source(path)))
        for word, start, _ in tokens:
            if word == "${":
                frames.append((len(hypotheses), len(disjoint), active_vars.copy()))
                continue
            if word == "$}":
                hyp_len, dv_len, old_vars = frames.pop()
                del hypotheses[hyp_len:]
                del disjoint[dv_len:]
                active_vars.clear()
                active_vars.update(old_vars)
                continue
            if word == "$[":
                name = next(tokens)[0]
                if next(tokens)[0] != "$]":
                    raise ValueError("invalid include")
                target = project_file(ctx.prepared.project, name)
                rel = target.relative_to(ctx.prepared.project.resolve()).as_posix()
                imports.append(rel)
                parse(rel)
                ctx.edge(path, "import", rel, ctx.sources[rel])
                continue
            label = None
            if word not in {"$v", "$c", "$d"}:
                label, word = word, next(tokens)[0]
            terms = []
            for token, _, end in tokens:
                if token == "$.":
                    break
                terms.append(token)
            else:
                raise ValueError("unterminated Metamath statement")

            if word == "$v":
                active_vars.update(terms)
            elif word == "$d":
                disjoint.extend(tuple(sorted(pair)) for pair in itertools.combinations(terms, 2))
            elif word != "$c":
                if word not in {"$f", "$e", "$a", "$p"}:
                    raise ValueError(f"unexpected Metamath statement {word}")
                proof = None
                if word == "$p":
                    sep = terms.index("$=")
                    proof, terms = terms[sep + 1:], terms[:sep]
                    if not proof or "?" in "".join(proof):
                        raise ValueError(f"incomplete proof for {label}")
                disjoint_pairs = sorted(set(disjoint))
                if compact:
                    context = ctx.metamath_context(path, assertions=assertion_count,
                                                  assertion_digest=assertion_digest, imports=imports,
                                                  hypotheses=hypotheses, disjoint=disjoint_pairs)
                else:
                    active_hypotheses = set(hypotheses)
                    visible = [key for n, (kind, key, _) in labels.items()
                               if kind in {"$a", "$p"} or n in active_hypotheses]
                    context = ctx.context(path, visible=visible, imports=imports, hypotheses=hypotheses,
                                          disjoint=disjoint_pairs)
                status = {"$p": "proof_verified", "$f": "hypothesis", "$e": "hypothesis",
                          "$a": "axiom"}[word]
                key = ctx.declare(path, label, word, " ".join(terms), start, end, context, status)
                if word in {"$a", "$p"}:
                    needed = set(terms) & active_vars
                    for h in hypotheses:
                        kind, _, expr = labels[h]
                        if kind == "$e":
                            needed.update(set(expr) & active_vars)
                    mandatory = [h for h in hypotheses if labels[h][0] == "$e" or labels[h][2][1] in needed]
                    constraints = [(x, y) for x, y in disjoint if x in needed and y in needed]
                    signatures[label] = (mandatory, constraints)
                if proof:
                    mandatory, constraints = signatures[label]
                    steps = _proof_steps(proof, mandatory)
                    trace = _apply_proof(steps, labels, signatures, active_vars, disjoint, terms)
                    for ref in dict.fromkeys(step for step in steps if isinstance(step, str)):
                        ctx.edge(key, "proof_used_premise", ref, labels[ref][1])
                    proofs[key] = ctx.evidence(encode({"mandatory": mandatory, "disjoint": constraints,
                                                       "transitions": trace}))
                if word in {"$f", "$e"}:
                    hypotheses.append(label)
                elif compact:
                    assertion_count += 1
                    assertion_digest = object_id(METAMATH_PREFIX, assertion_digest, key)
                labels[label] = word, key, terms

    try:
        parse(entrypoint)
    except (IndexError, KeyError, StopIteration) as exc:
        raise ValueError(f"invalid Metamath input: {exc}") from exc
    if frames:
        raise ValueError("unclosed Metamath scope")
    if not re.fullmatch(r"[\w./-]+", entrypoint):
        raise ValueError("entrypoint contains unsupported Metamath CLI characters")
    stdout, _ = ctx.run([ctx.prepared.prefix / "metamath/bin/metamath", f"read {entrypoint}",
                         "verify proof *", "exit"])
    if ("?Error" in stdout or "No errors were found." not in stdout
            or "All proofs in the database were verified" not in stdout):
        raise ValueError(f"Metamath verification failed: {stdout[-1800:]}")
    ctx.structures.update(proofs)
    ctx.notes["succeeded"].extend(sorted(files))
    for field in ("names", "kinds", "source_mapping", "statements", "context", "imports", "proof_used_premises"):
        ctx.availability[field] = "observed"
    ctx.availability["action_traces"] = "reconstructed"
    ctx.availability["term_trees"] = "inapplicable"
    ctx.availability["generated_obligations"] = "inapplicable"
