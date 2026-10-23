# tamper2.py SRC DST FAMILY SUBCASE K: copy the ID64 record file SRC to DST with record K's split id changed.
# Prints "tampered K old_split S new_split T", or "skip K <reason>" when indep43c would skip record K (symmetry / subcase rules)
# or K has no split, in which case DST is not written.
import sys, struct
src, dst, fam, sub, k = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4], int(sys.argv[5])
st = fam == 'd_steiner'
fval = {'f_ge_d': 2, 'f_le_d': 1, 'f_ge_dv': 3}[sub]
nv = 8 if st else 6
nb = nv - 1 if fval == 2 else nv
rs = 8 + 16 * nb + 8
vb, vd, vf = 0, 2, nv - 1
d = bytearray(open(src, 'rb').read())
lo = [struct.unpack_from('<d', d, k * rs + 8 + 16 * i)[0] for i in range(nb)]
hi = [struct.unpack_from('<d', d, k * rs + 16 + 16 * i)[0] for i in range(nb)]
sid, lid = struct.unpack_from('<ii', d, k * rs + 8 + 16 * nb)
if st and max(lo[4], lo[5]) > max(hi[vb], 1.0):
    print('skip', k, 'symmetry'); sys.exit(0)
if (fval == 1 and lo[vf] > hi[vd]) or (fval == 3 and hi[vf] < lo[vd]):
    print('skip', k, 'subcase'); sys.exit(0)
if sid < 1:
    print('skip', k, 'split id', sid); sys.exit(0)
new = sid % 150 + 1
if new == sid:
    new = sid % 150 + 2
struct.pack_into('<i', d, k * rs + 8 + 16 * nb, new)
open(dst, 'wb').write(d)
print('tampered', k, 'old_split', sid, 'new_split', new)
