#!/usr/bin/env python3
"""lean_nocomment_v1.py: Lean 4 source with all comments removed, for checking
that a release edit is comment-only. Removes `--` line comments and `/- ... -/` block comments (nested; this includes
`/--` docstrings and `/-!` module docs); keeps string literals ("...", escapes) and char literals ('x', '\\n') intact. The
normal form then drops trailing whitespace and blank lines.
usage: lean_nocomment_v1.py A.lean [B.lean]   one file: print its normal form; two: exit 0 iff the normal forms are equal
       lean_nocomment_v1.py --selftest"""
import re, sys

IDCH = re.compile(r"[A-Za-z0-9_'!?Ͱ-Ͽἀ-῿⁰-₟℀-⅏ᵉc-ᵙf]")

def strip(src):
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        c = src[i]
        if depth:
            if src.startswith('/-', i): depth += 1; i += 2
            elif src.startswith('-/', i): depth -= 1; i += 2
            else:
                if c == '\n': out.append('\n')   # keep line structure
                i += 1
            continue
        if src.startswith('/-', i): depth = 1; i += 2; continue
        if src.startswith('--', i):
            j = src.find('\n', i)
            i = n if j < 0 else j
            continue
        if c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == '\\' else 1
            out.append(src[i:j + 1]); i = j + 1; continue
        if c == "'" and (i == 0 or not IDCH.match(src[i - 1])):
            m = re.match(r"'(\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^'\\\n])'", src[i:])
            if m: out.append(m.group(0)); i += len(m.group(0)); continue
        out.append(c); i += 1
    if depth: raise ValueError('unterminated block comment')
    return ''.join(out)

def normal(src):
    return '\n'.join(l.rstrip() for l in strip(src).split('\n') if l.strip())

def selftest():
    cases = [
        ('a -- c\nb', 'a\nb'),
        ('/- x /- nested -/ y -/z', 'z'),
        ('/-- doc -/ def f := 1', ' def f := 1'),   # indentation is kept as is (only trailing space and blank lines go)
        ('/-! mod\ndoc -/\nx', 'x'),
        ('s := "a -- not a comment /- nor this -/"', 's := "a -- not a comment /- nor this -/"'),
        ('t := "esc \\" -- still string" -- gone', 't := "esc \\" -- still string"'),
        ("c := '-' -- c", "c := '-'"),
        ("q := '\"' -- quote char", "q := '\"'"),
        ("h' := h' -- prime ident", "h' := h'"),
        ("x  \n\n  y   ", "x\n  y"),
    ]
    bad = 0
    for src, want in cases:
        got = normal(src)
        if got != want: print('SELFTEST FAIL', repr(src), repr(got), repr(want)); bad += 1
    try:
        strip('/- open'); print('SELFTEST FAIL unterminated not caught'); bad += 1
    except ValueError: pass
    print('selftest', 'PASS' if not bad else 'FAIL %d' % bad)
    return bad == 0

if __name__ == '__main__':
    if sys.argv[1:] == ['--selftest']:
        sys.exit(0 if selftest() else 1)
    a = normal(open(sys.argv[1], encoding='utf-8').read())
    if len(sys.argv) == 2:
        print(a); sys.exit(0)
    b = normal(open(sys.argv[2], encoding='utf-8').read())
    print('EQUAL' if a == b else 'DIFFER'); sys.exit(0 if a == b else 1)
