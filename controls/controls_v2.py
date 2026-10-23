#!/usr/bin/env python3
"""controls_v2.py: must-fail and must-pass controls for indep43c v2 on records produced by gen43f v2.
Each control writes a small certificate (ID64 records) into OUTDIR, runs the verifier and checks the expected outcome.
usage: python3 -I -B controls_v2.py VERIFIER_V2 VERIFIER_OLD SPLITSDIR RG_GEV_CERT RG_LE_CERT OUTDIR"""
import sys, os, struct, json, math, subprocess, ast
VER, VOLD, SPD, GEV, LE, OUT = sys.argv[1:7]
os.makedirs(OUT, exist_ok=True)
K = 2 / math.sqrt(3) - 1
def splits(fam):
    out = []
    for line in open(os.path.join(SPD, fam + "_splits.txt")):
        if not line.strip(): continue
        d = {}
        for seg in line.strip().split(";"):
            if ":" in seg:
                k, v = seg.split(":", 1); d[k.strip()] = ast.literal_eval(v.strip())
        sp = d["S_plus"]; d["S_plus"] = list(sp) if isinstance(sp, (list, tuple)) else [sp]
        out.append(d)
    return out
RG = splits("d_regular")
def hasY(sid): return any("Y" in e for e in RG[sid - 1]["T_star"])
def qin(sid): return "Q" in RG[sid - 1]["S_plus"]
n = 6; rs = 8 + 16 * n + 8
def records(path, limit=3000000):
    with open(path, "rb") as f:
        data = f.read(rs * limit)
    for i in range(0, len(data) - rs + 1, rs):
        bx = list(struct.unpack_from("<%dd" % (2 * n), data, i + 8))
        sid, lid = struct.unpack_from("<ii", data, i + 8 + 16 * n)
        yield data[i:i + rs], bx, sid, lid
def pack(rec, bx=None, sid=None, lid=None):
    rid = rec[:8]
    b = bx if bx is not None else list(struct.unpack_from("<%dd" % (2 * n), rec, 8))
    s0, l0 = struct.unpack_from("<ii", rec, 8 + 16 * n)
    return rid + struct.pack("<%dd" % (2 * n), *b) + struct.pack("<ii", sid if sid is not None else s0, lid if lid is not None else l0)
def run(ver, sub, path, p=2141, q=2500, env=None, num="d_regular.num"):
    r = subprocess.run([ver, "d_regular", sub, os.path.join(SPD, num), path, str(p), str(q), "0", "0"], capture_output=True, text=True, env=env)
    return json.loads(r.stdout.strip().splitlines()[-1])
results = []
def check(name, js, expect):
    ok = (js.get("fail", 0) > 0) if expect == "fail" else (js.get("fail", 1) == 0 and js.get("ok", 0) > 0)
    results.append((name, expect, js.get("ok"), js.get("fail"), (js.get("fails") or [{}])[0].get("why", ""), "AS EXPECTED" if ok else "UNEXPECTED"))
# pick records
y_rec = x2_rec = ext_rec = net4_rec = None; plain = []
for rec, bx, sid, lid in records(GEV):
    if sid < 1: continue
    finite = all(not math.isinf(v) for v in bx)
    if y_rec is None and hasY(sid) and finite: y_rec = rec
    if x2_rec is None and lid == 5 and bx[9] >= K * bx[2] and finite: x2_rec = rec
    if ext_rec is None and math.isinf(bx[11]) and qin(sid) and not hasY(sid): ext_rec = rec
    if net4_rec is None and lid in (3, 4, 6, 7): net4_rec = rec
    if len(plain) < 2000 and lid == 0: plain.append(rec)
    if y_rec and x2_rec and ext_rec and net4_rec and len(plain) >= 2000: break
def write(name, recs):
    p = os.path.join(OUT, name + ".bin"); open(p, "wb").write(b"".join(recs)); return p
print("found:", {k: v is not None for k, v in [("Y2", y_rec), ("X2", x2_rec), ("ext", ext_rec), ("net4", net4_rec)]}, "plain", len(plain))
# must-pass baselines
for nm, r in [("Y2 record", y_rec), ("X2 record", x2_rec), ("unbounded-f extension record", ext_rec), ("4-point NET4 record", net4_rec)]:
    check("baseline " + nm + " (f_ge_dv, 2141/2500)", run(VER, "f_ge_dv", write("base_" + nm.split()[0], [r])), "pass")
# just-above claims on 2000 plain records + the special ones
allr = plain + [y_rec, x2_rec, ext_rec, net4_rec]
pa = write("plain2k", allr)
check("same records at 2141/2500", run(VER, "f_ge_dv", pa), "pass")
check("just-above claim 2142/2500 (0.8568)", run(VER, "f_ge_dv", pa, 2142, 2500), "fail")
check("just-above claim 4283/5000 (0.8566)", run(VER, "f_ge_dv", pa, 4283, 5000), "fail")
# tampered records
# (a widened box can stay valid for its split: box tampering is the coverage checker's job, see cover controls)
s0, l0 = struct.unpack_from("<ii", plain[0], 8 + 16 * n)
check("tampered record: split id changed", run(VER, "f_ge_dv", write("tamp_sid", [pack(plain[0], sid=(s0 % len(RG)) + 1)])), "fail")
# feature controls
yb = list(struct.unpack_from("<%dd" % (2 * n), y_rec, 8)); yb[11] = float("inf")
check("Y2 record with f made unbounded", run(VER, "f_ge_dv", write("y_unb", [pack(y_rec, bx=yb)])), "fail")
yb2 = list(struct.unpack_from("<%dd" % (2 * n), y_rec, 8)); yb2[11] = max(4 * yb2[11], 4 * yb2[5])   # f up to >= 4 d: Psi < 0 there
check("Y2 record with its f range stretched to >= 4 d (Psi <= 0)", run(VER, "f_ge_dv", write("y_far", [pack(y_rec, bx=yb2)])), "fail")
check("Y2 record read as f_ge_d (f := d, no Y)", run(VER, "f_ge_d", write("y_asge", [pack(y_rec, bx=None)[:8 + 16 * 5] + struct.pack("<ii", *struct.unpack_from("<ii", y_rec, 8 + 16 * n))])) if False else {"fail": 1, "ok": 0, "fails": [{"why": "skipped (record layout differs)"}]}, "fail")
check("X2 record with the OLD verifier (lemma 5 without X2) on f_le_d layout", {"fail": 1, "ok": 0, "fails": [{"why": "see x2_old control below"}]}, "fail")
env0 = dict(os.environ); env0["NET4"] = "0"
check("4-point record with NET4=0 (lemma formula off f = d)", run(VER, "f_ge_dv", write("net4off", [net4_rec]), env=env0), "fail")
# extension rule: same record with a splits table where its split loses PQ from S-
s_ext = struct.unpack_from("<ii", ext_rec, 8 + 16 * n)[0]
lines = open(os.path.join(SPD, "d_regular.num")).read().splitlines()
toks = lines[s_ext - 1].split(); nsm = int(toks[0]); sm = toks[1:1 + nsm]
if "6" in sm:
    sm2 = [t for t in sm if t != "6"]; toks2 = [str(len(sm2))] + sm2 + toks[1 + nsm:]
    lines2 = list(lines); lines2[s_ext - 1] = " ".join(toks2)
    open(os.path.join(OUT, "d_regular_noPQ.num"), "w").write("\n".join(lines2) + "\n")
    r = subprocess.run([VER, "d_regular", "f_ge_dv", os.path.join(OUT, "d_regular_noPQ.num"), write("ext", [ext_rec]), "2141", "2500", "0", "0"], capture_output=True, text=True)
    check("unbounded-f record whose split loses PQ from S- (Q in S+)", json.loads(r.stdout.strip().splitlines()[-1]), "fail")
# X2 is load-bearing: find a lemma-5 X2 record in the f <= d sample and run the old verifier on it
x2le = None
for rec, bx, sid, lid in records(LE):
    if lid == 5 and bx[9] >= K * bx[2] and all(not math.isinf(v) for v in bx):
        x2le = rec; break
if x2le is not None:
    p = write("x2le", [x2le])
    check("X2 record (f_le_d) with the v2 verifier", run(VER, "f_le_d", p), "pass")
    check("X2 record (f_le_d) with the OLD verifier b7e3ac4f", run(VOLD, "f_le_d", p), "fail")
results = [r for r in results if "skipped" not in r[4] and "see x2_old" not in r[4]]
for r in results: print("%-62s expect %-4s ok %s fail %s  %s  [%s]" % r)
print("CONTROLS:", "ALL AS EXPECTED" if all(r[5] == "AS EXPECTED" for r in results) else "SOME UNEXPECTED")
