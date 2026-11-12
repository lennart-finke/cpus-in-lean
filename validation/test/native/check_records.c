/* Host build of the oracle's input validation (record_check.h), run by `native_fp.py prepare` on every
 * campaign file. Same output as `oracle check` on the target:
 *   CHECK <count>, then one "REJECT <index> <value> <reason>" line per refused record, then END <refused>
 * (numbers in 16-digit hex). Exit 0 when every record is accepted, 3 when some are refused, 1 when the
 * file is malformed.
 *   check_records [--amd] [--misalign-sse] < campaign.bin
 */
#include <stdio.h>
#include <string.h>
#include "record_check.h"

int main(int argc, char **argv) {
 unsigned target = 0;
 for (int i = 1; i < argc; i++) {
  if (!strcmp(argv[i], "--amd")) target |= RC_AMD;
  else if (!strcmp(argv[i], "--misalign-sse")) target |= RC_MISALIGN_SSE;
  else { fprintf(stderr, "usage: check_records [--amd] [--misalign-sse] < campaign.bin\n"); return 2; }
 }
 unsigned char header[8], rec[776];
 if (fread(header, 1, 8, stdin) != 8) { fprintf(stderr, "ERROR: truncated input\n"); return 1; }
 unsigned long long count = rc_le(header, 8);
 int v2 = count >> 63;
 count &= ~(1ull << 63);
 if (!count || count > 1000000) { fprintf(stderr, "ERROR: invalid count\n"); return 1; }
 size_t size = v2 ? 776 : 648;
 unsigned long long refused = 0;
 printf("CHECK %016llx\n", count);
 for (unsigned long long index = 0; index < count; index++) {
  if (fread(rec, 1, size, stdin) != size) { fprintf(stderr, "ERROR: truncated input\n"); return 1; }
  unsigned long long value;
  const char *why = record_check(rec, rec + 440, target, &value);
  if (why) { printf("REJECT %016llx %016llx %s\n", index, value, why); refused++; }
 }
 if (fgetc(stdin) != EOF) { fprintf(stderr, "ERROR: trailing input\n"); return 1; }
 printf("END %016llx\n", refused);
 return refused ? 3 : 0;
}
