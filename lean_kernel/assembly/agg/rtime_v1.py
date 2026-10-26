#!/usr/bin/env python3
"""rtime_v1.py OUT UNIT TAG CMD...: run CMD, append "UNIT rc wall_s peak_rss_kB TAG" to OUT (rc = exit code, -N = signal N);
exit 0 iff CMD exited 0 (os.wait4 rusage; no /usr/bin/time needed)"""
import os, subprocess, sys, time
out, unit, tag, cmd = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4:]
t0 = time.time()
p = subprocess.Popen(cmd)
_, st, ru = os.wait4(p.pid, 0)
rc = os.waitstatus_to_exitcode(st)
with open(out, "a") as f:
    f.write("%s %d %.2f %d %s\n" % (unit, rc, time.time() - t0, ru.ru_maxrss, tag))
sys.exit(0 if rc == 0 else 1)
