#!/bin/zsh
# Boot Linux on the Lean x86 model straight into DOOM, shown in a window (view.py, python3 +
# tkinter). Arrows move, Ctrl or f fires, space opens, Shift runs, Alt strafes, Enter/Esc for
# menus; close the window to quit.
cd -- "${0:A:h}/.." || exit 1
[ -x doom/.lake/build/bin/doomrun ] || (cd doom && lake build doomrun) || exit 1
exec doom/.lake/build/bin/doomrun guest/bzImage doom/initramfs.cpio python3 doom/view.py
