#!/usr/bin/env python3
"""py_nodoc_v1.py: are two Python files the same program up to comments and
docstrings? Compares ast.dump of both after deleting docstrings (first-statement string constants of the module, classes
and functions); comments never reach the AST. usage: py_nodoc_v1.py A.py B.py -> EQUAL/DIFFER (exit 0 iff EQUAL)."""
import ast, sys
def norm(path):
    t = ast.parse(open(path, encoding='utf-8').read())
    for n in ast.walk(t):
        if isinstance(n, (ast.Module, ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)) and n.body:
            b = n.body[0]
            if isinstance(b, ast.Expr) and isinstance(b.value, ast.Constant) and isinstance(b.value.value, str):
                n.body = n.body[1:] or [ast.Pass()]
    return ast.dump(t, include_attributes=False)
a, b = norm(sys.argv[1]), norm(sys.argv[2])
print('EQUAL' if a == b else 'DIFFER'); sys.exit(0 if a == b else 1)
