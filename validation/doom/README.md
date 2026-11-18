# DOOM

Unmodified static i386 [doomgeneric](https://github.com/ozkl/doomgeneric) with shareware `doom1.wad`, under Linux on the IA-32 model.

```
$ limactl shell kbuild -- bash doom/build.sh    # builds doom and initramfs.cpio
$ doom/test.sh 100                              # first 100 demo frames: QEMU vs. model
$ doom/play.command                             # play in a window
```

Arrows move, Ctrl/`f` fires, space uses, Shift runs, Alt strafes. About 1.7 fps, in slow motion (the model does ~5M instructions/s, guest time assumes 100M). `-hash` uses a virtual clock, so frames are identical on any machine.

Files: `dg_lean.c` (platform layer: `-win`, `-hash`, `-frames N`); `DoomRun.lean`, `view.py` (show guest frames, pass keys); `build.sh`, `test.sh`, `play.command`.
