# DOOM

An unmodified static i386 build of [doomgeneric](https://github.com/ozkl/doomgeneric) with the shareware `doom1.wad`, running under Linux on the IA-32 model.

```
$ limactl shell kbuild -- bash doom/build.sh    # builds doom and initramfs.cpio
$ doom/test.sh 100                              # first 100 demo frames: QEMU vs. model
$ doom/play.command                             # play in a window
```

Controls: arrows to move, Ctrl or `f` to fire, space to use, Shift to run, Alt to strafe.

Expect about 1.7 frames per second. The model runs at about 5M instructions per second, but guest time assumes 100M, so the game also runs in slow motion. The `-hash` mode replaces wall-clock time with a virtual clock, so the frame sequence is the same on any machine.

## Files
- `dg_lean.c`: the doomgeneric platform layer (`-win`, `-hash`, `-frames N`).
- `DoomRun.lean`, `view.py`: read each frame from guest memory and show it in a window with key events.
- `build.sh`, `test.sh`, `play.command`: build, differential test, play.
