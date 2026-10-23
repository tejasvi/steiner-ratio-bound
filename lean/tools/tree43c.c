/* tree43c.c: convert a certificate (ID64 records + child file) into the compact DFS code stream read by the
 * Lean checker (S43Core.Tree). Walk = cover43's top-down walk (roots: id = mask + 1, variable i in [1, inf] if bit i of mask is
 * set, else [0, 1]; split along the widest side, an infinite side [lo, inf] counting 1/lo, at the midpoint or at 2 lo; lower
 * half first); every leaf box is compared with its record, as in cover43. Output, one character per internal node and three per
 * leaf, for the roots in order: internal node splitting variable k: '!' + k; leaf: 'p' + lemma id ('y' for -1), then the split
 * id in two base-64 digits chr(48 + v) (split id -1 -> 0). The Lean side recomputes every box from the root and the codes, so
 * the stream is untrusted data.
 * usage: tree43c CERT.bin CHILD.bin n OUT.txt */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#define MAXN 8
typedef uint64_t idt;
#define IDB 8
typedef struct { double lo[MAXN], hi[MAXN]; idt id; } Node;
static void die(const char *m) { fprintf(stderr, "FAIL: %s\n", m); printf("FAIL: %s\n", m); exit(1); }
int main(int argc, char **argv) {
  if (argc != 5) die("usage: tree43c CERT.bin CHILD.bin n OUT.txt");
  int n = atoi(argv[3]); size_t rs = IDB + 16 * (size_t)n + 8;
  int fc = open(argv[1], O_RDONLY), fh = open(argv[2], O_RDONLY); if (fc < 0 || fh < 0) die("open");
  struct stat sc, sh; fstat(fc, &sc); fstat(fh, &sh);
  if (sc.st_size % rs || sh.st_size % 16) die("sizes");
  uint64_t R = sc.st_size / rs, N = sh.st_size / 16;
  unsigned char *cert = mmap(NULL, sc.st_size, PROT_READ, MAP_SHARED, fc, 0);
  idt *ch = mmap(NULL, sh.st_size, PROT_READ, MAP_SHARED, fh, 0);
  uint64_t *pos = calloc(N + 1, sizeof(uint64_t)); if (!pos) die("alloc");
  for (uint64_t r = 0; r < R; r++) { idt id; memcpy(&id, cert + r * rs, 8); if (id == 0 || id > N || pos[id]) die("ids"); pos[id] = r + 1; }
  FILE *fo = fopen(argv[4], "w"); if (!fo) die("out");
  Node *stack = malloc(sizeof(Node) * 4096); uint64_t leaves = 0, internal = 0;
  for (uint64_t mask = 0; mask < (1ull << n); mask++) {
    int sp = 0; Node rt; rt.id = mask + 1;
    for (int i = 0; i < n; i++) { if ((mask >> i) & 1) { rt.lo[i] = 1; rt.hi[i] = INFINITY; } else { rt.lo[i] = 0; rt.hi[i] = 1; } }
    stack[sp++] = rt;
    while (sp) {
      Node b = stack[--sp];
      idt L = ch[2 * (N - b.id)], Rr = ch[2 * (N - b.id) + 1];
      if (L == 0 && Rr == 0) {
        if (!pos[b.id]) die("leaf without record");
        const unsigned char *p = cert + (pos[b.id] - 1) * rs;
        for (int i = 0; i < n; i++) { double lo, hi; memcpy(&lo, p + 8 + 16 * i, 8); memcpy(&hi, p + 16 + 16 * i, 8); if (lo != b.lo[i] || hi != b.hi[i]) die("leaf box mismatch"); }
        int32_t sid, lid; memcpy(&sid, p + 8 + 16 * n, 4); memcpy(&lid, p + 12 + 16 * n, 4);
        if (sid < -1 || sid >= 4096 || lid < -1 || lid > 8) die("split or lemma id out of range");
        int s = sid < 0 ? 0 : sid;
        fputc(lid < 0 ? 'y' : 'p' + lid, fo); fputc(48 + (s >> 6), fo); fputc(48 + (s & 63), fo);
        leaves++; continue;
      }
      if (L == 0 || Rr == 0 || L == Rr || pos[b.id]) die("bad node");
      internal++;
      int dim = 0; double best = -1;
      for (int i = 0; i < n; i++) { double sep = isinf(b.hi[i]) ? 1.0 / b.lo[i] : b.hi[i] - b.lo[i]; if (sep > best) { best = sep; dim = i; } }
      fputc('!' + dim, fo);
      Node l = b, r = b; l.id = L; r.id = Rr;
      double m = isinf(b.hi[dim]) ? 2 * b.lo[dim] : (b.lo[dim] + b.hi[dim]) / 2;
      if (!(m > b.lo[dim] && m < b.hi[dim])) die("degenerate split");
      l.hi[dim] = m; r.lo[dim] = m;
      if (sp + 2 >= 4096) die("stack");
      stack[sp++] = r; stack[sp++] = l;
    }
  }
  fclose(fo);
  if (leaves != R) die("records not all reached");
  printf("OK leaves %llu internal %llu bytes %llu\n", (unsigned long long)leaves, (unsigned long long)internal, (unsigned long long)(internal + 3 * leaves));
  return 0;
}
