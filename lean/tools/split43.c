/* split43.c: cut the compact DFS code stream of one case (tree43c output, root subtrees in order) into a
 * skeleton and shards for the Lean data layer (S43Core.Tree: walkTopSkel, shardOKPar).
 * A subtree with at most J leaves (and every leaf met above the cut) becomes a job: the skeleton gets 'z', the job's bytes
 * go to the current shard; a shard is closed when it holds at least S leaves. Output in OUTDIR: skel.txt, shard_NNNNN.txt,
 * ranges.txt (one line per shard: first job index, number of jobs, leaves, bytes), stats on stdout.
 * usage: split43 TREE.txt NB J S OUTDIR */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
static const unsigned char *buf; static uint64_t len, pos, nint; static int nb; static uint32_t *cnt;
static uint64_t J, S; static const char *outdir;
static FILE *fskel, *fsh, *fr; static uint64_t shardNo, shardJobs, shardLeaves, shardBytes, jobNo, jobStart0;
static void die(const char *m) { fprintf(stderr, "FAIL: %s at %llu\n", m, (unsigned long long)pos); printf("FAIL: %s\n", m); exit(1); }
static int isInt(unsigned char c) { return c >= 33 && c < 33 + nb; }
static int isLeaf(unsigned char c) { return c >= 112 && c <= 121; }
/* pass 1: leaves per internal node (DFS order) */
static uint64_t count(int depth) {
  if (depth > 250) die("depth");
  if (pos >= len) die("truncated");
  unsigned char c = buf[pos];
  if (isInt(c)) {
    uint64_t me = nint++; pos++;
    uint64_t a = count(depth + 1), b = count(depth + 1);
    cnt[me] = (a + b > 0xFFFFFFFFull) ? 0xFFFFFFFFu : (uint32_t)(a + b);
    return a + b;
  }
  if (isLeaf(c)) { if (pos + 2 >= len) die("truncated leaf"); pos += 3; return 1; }
  die("bad code"); return 0;
}
/* skip a subtree structurally, counting internal nodes */
static void skip(int depth) {
  if (depth > 250) die("depth");
  unsigned char c = buf[pos];
  if (isInt(c)) { nint++; pos++; skip(depth + 1); skip(depth + 1); return; }
  if (isLeaf(c)) { pos += 3; return; }
  die("bad code");
}
static void openShard(void) {
  char p[4096]; snprintf(p, sizeof p, "%s/shard_%05llu.txt", outdir, (unsigned long long)shardNo);
  fsh = fopen(p, "w"); if (!fsh) die("open shard"); shardJobs = 0; shardLeaves = 0; shardBytes = 0; jobStart0 = jobNo;
}
static void closeShard(void) {
  if (!fsh) return;
  fclose(fsh); fsh = NULL;
  fprintf(fr, "%llu %llu %llu %llu\n", (unsigned long long)jobStart0, (unsigned long long)shardJobs,
          (unsigned long long)shardLeaves, (unsigned long long)shardBytes);
  shardNo++;
}
static void job(uint64_t leaves) {
  uint64_t start = pos;
  skip(0);
  if (!fsh) openShard();
  fwrite(buf + start, 1, pos - start, fsh);
  fputc('z', fskel);
  jobNo++; shardJobs++; shardLeaves += leaves; shardBytes += pos - start;
  if (shardLeaves >= S) closeShard();
}
static void emit(int depth) {
  unsigned char c = buf[pos];
  if (isInt(c)) {
    uint64_t me = nint;
    if (cnt[me] <= J) { job(cnt[me]); return; }
    nint++; pos++; fputc(c, fskel); emit(depth + 1); emit(depth + 1); return;
  }
  if (isLeaf(c)) { job(1); return; }
  die("bad code");
}
int main(int argc, char **argv) {
  if (argc != 6) die("usage: split43 TREE.txt NB J S OUTDIR");
  nb = atoi(argv[2]); J = strtoull(argv[3], 0, 10); S = strtoull(argv[4], 0, 10); outdir = argv[5];
  int fd = open(argv[1], O_RDONLY); if (fd < 0) die("open");
  struct stat st; fstat(fd, &st); len = st.st_size;
  buf = mmap(NULL, len, PROT_READ, MAP_SHARED, fd, 0); if (buf == MAP_FAILED) die("mmap");
  cnt = malloc(sizeof(uint32_t) * (len / 4 + 16)); if (!cnt) die("alloc");  /* internal nodes <= len / 4 */
  uint64_t roots = 1ull << nb, leaves = 0;
  pos = 0; nint = 0;
  for (uint64_t r = 0; r < roots; r++) leaves += count(0);
  if (pos != len) die("stream not used up");
  uint64_t internal = nint;
  char p[4096];
  snprintf(p, sizeof p, "%s/skel.txt", outdir); fskel = fopen(p, "w");
  snprintf(p, sizeof p, "%s/ranges.txt", outdir); fr = fopen(p, "w");
  if (!fskel || !fr) die("open out");
  pos = 0; nint = 0;
  for (uint64_t r = 0; r < roots; r++) emit(0);
  closeShard();
  if (pos != len || nint != internal) die("second pass mismatch");
  long skelBytes = ftell(fskel);
  fclose(fskel); fclose(fr);
  printf("OK leaves %llu internal %llu jobs %llu shards %llu skel_bytes %ld\n", (unsigned long long)leaves,
         (unsigned long long)internal, (unsigned long long)jobNo, (unsigned long long)shardNo, skelBytes);
  return 0;
}
