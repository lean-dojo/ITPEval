"""Source spans reviewed against hash-pinned benchmark statement artifacts."""

# Each tuple contains the declaration identifier (None for anonymous declarations),
# native declaration kind, and an exact identifying fragment of the original source.
LOCATORS = {
    # miniF2F AIME 1983 P1.
    "1e415348eafea578a3621e93e793bfbe6bbab77ab2dc58c4921496c6d251856f": [
        ("aime-1983-p1-statement", "defun", "(defun aime-1983-p1-statement")],
    "6d46c58e94f64733a59a549c452756163ae2d3cd86ea59f87bf0a7723586c6aa": [
        ("aime_1983_p1", "theorem", "theorem aime_1983_p1 ")],
    # Putnam 1962 A2.
    "8c01c801d36c9fd1993c3981d4af1fa9fc3ef16ede29bc79d06be5bf69be577a": [
        ("putnambench-putnam-1962-a2", "$a", "putnambench-putnam-1962-a2 $a")],
    # The Babel-formal limits_uniqueness topic. Its index names two goals.
    "e36faaa709a18d21bee4648a6ddec09c35768156cbf4bdaa3933fb0e2c5f2509": [
        ("Limits.abs_sub_triangle", "theorem", "theorem abs_sub_triangle"),
        ("Limits.limit_unique", "theorem", "theorem limit_unique")],
    "9dae7cc0631964d433dbaabb892627348b9fea33061cfb437875a23fb2f3a72d": [
        ("abs_sub_triangle", "Lemma", "Lemma abs_sub_triangle"),
        ("limit_unique", "Theorem", "Theorem limit_unique")],
    "5b8835a9bb47c51576ec41ae3b8db9b4098c0d95cecc86fe3459bf6ca1380251": [
        ("abs_field.abs_sub_triangle", "lemma", "lemma abs_sub_triangle:"),
        ("abs_field.limit_unique", "theorem", "theorem limit_unique:")],
    "fe1118e666cc058cd1af6455fd818b1720fc76b3180dd42dd2e0bc54d008b2da": [
        ("abs_sub_triangle", "OCaml term binding", "let abs_sub_triangle ="),
        ("limit_unique", "OCaml term binding", "let limit_unique =")],
    "8ac02ee52caf9f7229252ba3a49888d860ebd4069af05d06a4b14876eef428fc": [
        ("limits-uniqueness-abs-sub-triangle-statement", "defun-sk",
         "(defun-sk limits-uniqueness-abs-sub-triangle-statement"),
        ("limits-uniqueness-statement", "defun-sk", "(defun-sk limits-uniqueness-statement")],
    "d373937d945cfae84051e2c486ddd3ae49d77c9fc4683d27f2095ed1d6b92e92": [
        ("Limits.abs-sub-triangle", "type-valued definition", "abs-sub-triangle : Set"),
        ("Limits.limit-unique", "type-valued definition", "limit-unique : Set")],
    "4d5c5ee382833219d08216ec868573e5aacf4905189bc05a06f662c4ca10453e": [
        ("abs_sub_triangle", "SML term binding", "val abs_sub_triangle ="),
        ("limit_unique", "SML term binding", "val limit_unique =")],
    "b2354edaf6b8404a097ad6bd1a34299ccf87c00de8c623e1f868076d336e1b4d": [
        ("abs-sub-triangle", "$a", "abs-sub-triangle $a"),
        ("limit-unique", "$a", "limit-unique $a")],
    "90269b0657fdcf05470fc6da7ec6d33d1387db0ba8e0b3f68104ab32bc3ccc64": [
        (None, "theorem", "\ntheorem\n")],
    "3284730d530ce9a2fd3ef96f5882851312ef7eea1e6f213a24f21a3594e596cb": [
        ("limits_uniqueness.abs_sub_triangle", "Boolean constant definition", "abs_sub_triangle: bool ="),
        ("limits_uniqueness.limit_unique", "Boolean constant definition", "limit_unique: bool =")],
}


def locate(raw, key):
    targets = []
    for name, kind, text in LOCATORS.get(key, ()):
        anchor = text.encode()
        if raw.count(anchor) != 1:
            raise ValueError(f"reviewed anchor is ambiguous or absent: {text!r}")
        start = raw.index(anchor)
        targets.append({"name": name, "actual_kind": kind, "benchmark_role": "target_specification",
                        "checking_status": "statement_only", "evidence_sha256": key,
                        "start_byte": start, "end_byte": start + len(anchor)})
    return targets
