"""libbuild_v2.py: compile the checker library without lake (lean options from LIBOPTS, default
-DautoImplicit=false -DElab.async=false): the import closure of the TARGETs inside SRCROOT, in topological order, NPAR at a time, with
`lean $LIBOPTS --root=SRCROOT -o OUTROOT/<M>.olean <M>.lean` (cwd SRCROOT). LEAN_PATH must hold OUTROOT;
LEAN = the lean binary. Writes OUTROOT/libbuild_outputs.txt (olean paths relative to OUTROOT).
usage: libbuild_v2.py SRCROOT OUTROOT NPAR TARGET..."""
import os, re, sys, subprocess, time
src, out, npar = os.path.abspath(sys.argv[1]), os.path.abspath(sys.argv[2]), int(sys.argv[3]); targets = sys.argv[4:]
LEAN = os.environ.get('LEAN', 'lean')
OPTS = os.environ.get('LIBOPTS', '-DautoImplicit=false -DElab.async=false').split()
IMP = re.compile(r'^(?:public\s+|meta\s+|private\s+)*import\s+(?:all\s+)?(\S+)', re.M)
def rel(m): return os.path.join(*m.split('.')) + '.lean'
deps = {}
def visit(m):
    if m in deps: return
    ds = [d for d in IMP.findall(open(os.path.join(src, rel(m))).read()) if os.path.exists(os.path.join(src, rel(d)))]
    deps[m] = ds
    for d in ds: visit(d)
for t in targets: visit(t)
done, failed, running = set(), set(), {}
t0 = time.time()
while len(done) + len(failed) < len(deps):
    for m in [m for m in deps if m not in done | failed and m not in running and all(d in done for d in deps[m])]:
        if len(running) >= npar: break
        o = os.path.join(out, *m.split('.')) + '.olean'; os.makedirs(os.path.dirname(o), exist_ok=True)
        lg = open(os.path.join(out, 'libbuild_' + m + '.log'), 'w')
        running[m] = (subprocess.Popen([LEAN] + OPTS + [f'--root={src}', '-o', o, rel(m)], cwd=src, stdout=lg, stderr=subprocess.STDOUT), time.time())
    if not running:   # nothing runnable: a dependency failed
        failed |= {m for m in deps if m not in done}; break
    time.sleep(0.5)
    for m, (p, ts) in list(running.items()):
        if p.poll() is not None:
            del running[m]
            (done if p.returncode == 0 else failed).add(m)
            print(f'{m} rc={p.returncode} {time.time() - ts:.1f}s', flush=True)
with open(os.path.join(out, 'libbuild_outputs.txt'), 'w') as f:
    for m in sorted(done): f.write(os.path.join(*m.split('.')) + '.olean\n')
print(f'LIBBUILD done {len(done)} failed {len(failed)} of {len(deps)} wall {time.time() - t0:.0f}s', flush=True)
sys.exit(0 if not failed else 1)
