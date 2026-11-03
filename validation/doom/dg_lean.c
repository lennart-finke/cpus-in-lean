// doomgeneric platform for the Lean x86 model.
//   -hash      print "F <n> <crc32>" per frame (virtual clock)
//   -win       for doom/DoomRun: per frame print ESC _ DG <buffer address> ESC \, then read
//              key events (1 k = down, 2 k = up) until the host's 0 ack; the host reads the
//              frame from guest memory while doom is blocked
//   -frames N  exit after N frames
#include "doomgeneric.h"
#include "doomkeys.h"
#include "m_argv.h"
#include <stdio.h>
#include <string.h>
#include <termios.h>
#include <time.h>
#include <unistd.h>

static int hash, win, frames = -1, nframe;
static struct termios t0;
static uint16_t q[256]; static int qn, qi;  // -win key events

static void restore(void) { tcsetattr(0, TCSANOW, &t0); }

void DG_Init(void) {
  hash = M_CheckParm("-hash"); win = M_CheckParm("-win");
  int i = M_CheckParmWithArgs("-frames", 1); if (i) frames = atoi(myargv[i + 1]);
  if (!win) return;
  struct termios t; tcgetattr(0, &t0); t = t0; cfmakeraw(&t); t.c_oflag |= OPOST | ONLCR;
  tcsetattr(0, TCSANOW, &t); atexit(restore);
}

static uint32_t crc32(const uint8_t *p, size_t n) {
  uint32_t c = ~0u;
  while (n--) { c ^= *p++; for (int k = 0; k < 8; k++) c = c >> 1 ^ (0xEDB88320 & -(c & 1)); }
  return ~c;
}

void DG_DrawFrame(void) {
  nframe++;
  if (win) {
    printf("\033_DG%08x\033\\", (unsigned)DG_ScreenBuffer); fflush(stdout);
    unsigned char c, k;
    while (read(0, &c, 1) == 1 && c)
      if (read(0, &k, 1) == 1 && qn < 256) q[qn++] = c << 8 | k;
  } else if (hash) printf("F %d %08x\n", nframe, crc32((uint8_t *)DG_ScreenBuffer, DOOMGENERIC_RESX * DOOMGENERIC_RESY * 4));
  fflush(stdout);
  if (frames >= 0 && nframe >= frames) exit(0);
}

// -hash uses a virtual clock (1 ms per query, sleeps advance it) so frames don't depend on speed.
static uint32_t vt;
void DG_SleepMs(uint32_t ms) { if (hash) vt += ms; else usleep(ms * 1000); }

uint32_t DG_GetTicksMs(void) {
  if (hash) return vt++;
  struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

int DG_GetKey(int *pressed, unsigned char *key) {
  if (!win || qi == qn) { qi = qn = 0; return 0; }
  *pressed = q[qi] >> 8 == 1; *key = q[qi++]; return 1;
}

void DG_SetWindowTitle(const char *title) { (void)title; }

int main(int argc, char **argv) {
  doomgeneric_Create(argc, argv);
  for (;;) doomgeneric_Tick();
}
