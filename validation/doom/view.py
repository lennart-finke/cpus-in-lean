# Window for doom/DoomRun: PPM frames on stdin, key events (1 k = down, 2 k = up) on stdout.
import os, sys, threading, tkinter as tk
K = {'Up': 0xad, 'Down': 0xaf, 'Left': 0xac, 'Right': 0xae, 'Control_L': 0xa3, 'Control_R': 0xa3,
     'space': 0xa2, 'Shift_L': 0xb6, 'Shift_R': 0xb6, 'Alt_L': 0xb8, 'Alt_R': 0xb8,
     'Option_L': 0xb8, 'Option_R': 0xb8, 'Return': 13, 'Escape': 27, 'Tab': 9,
     'BackSpace': 0x7f, 'comma': 0xa0, 'period': 0xa1, 'f': 0xa3, 'minus': 0x2d, 'equal': 0x3d,
     **{f'F{i}': 0x80 + c for i, c in zip(range(1, 13), [*range(0x3b, 0x45), 0x57, 0x58])}}
root = tk.Tk(); root.title('DOOM on the Lean x86 model'); root.configure(bg='black')
lbl = tk.Label(root, bd=0, width=960, height=600, bg='black'); lbl.pack()
frame, down = [None], set()

def reader():
    f = sys.stdin.buffer
    while (h := f.read(15)) and len(h) == 15: frame[0] = h + f.read(320 * 200 * 3)
    os._exit(0)

def tick():
    if frame[0]:
        img = tk.PhotoImage(data=frame[0], format='ppm').zoom(3); frame[0] = None
        lbl.configure(image=img); lbl.img = img
    root.after(10, tick)

def key(e, d):
    k = K.get(e.keysym) or (ord(e.keysym.lower()) if len(e.keysym) == 1 and e.keysym.isprintable() else 0)
    if not k or (k in down) == d: return
    (down.add if d else down.discard)(k)
    sys.stdout.buffer.write(bytes([1 if d else 2, k])); sys.stdout.flush()

root.bind('<KeyPress>', lambda e: key(e, True)); root.bind('<KeyRelease>', lambda e: key(e, False))
threading.Thread(target=reader, daemon=True).start(); tick(); root.mainloop(); os._exit(0)
