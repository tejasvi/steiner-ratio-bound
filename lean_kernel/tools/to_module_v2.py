#!/usr/bin/env python3
"""to_module_v2.py: mechanical module-form copy of a plain Lean file.
usage: python3 -I to_module_v2.py IN.lean OUT.lean
The copy = 'module' + a blank line, then the original text with every header line `import X` turned into
`public import X`, then `@[expose] public section` + a blank line right after the last import line, then the rest of the
text unchanged, then a blank line and `end`. Nothing else changes (the diff to the original is exactly those lines).
A file with no import line gets `@[expose] public section` right after `module` (v2 = v1 + that case).
Refuses an existing OUT and a file with an import after the first non-import, non-blank, non-comment line."""
import os, sys
src, dst = sys.argv[1], sys.argv[2]
if os.path.exists(dst):
    sys.exit('ERROR: %s exists' % dst)
lines = open(src).read().split('\n')
imp = [i for i, l in enumerate(lines) if l.startswith('import ')]
last = imp[-1] if imp else -1
for i in range(last):
    l = lines[i].strip()
    if l and not lines[i].startswith('import ') and not l.startswith('--'):
        sys.exit('ERROR: %s: line %d before the last import is not an import/blank/comment' % (src, i + 1))
out = ['module', ''] + (['@[expose] public section', ''] if last < 0 else [])
for i, l in enumerate(lines):
    out.append('public ' + l if l.startswith('import ') else l)
    if i == last:
        out += ['', '@[expose] public section']
body = '\n'.join(out).rstrip('\n')
os.makedirs(os.path.dirname(os.path.abspath(dst)), exist_ok=True)
open(dst, 'w').write(body + '\n\nend\n')
