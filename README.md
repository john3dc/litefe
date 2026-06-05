# litefe

A minimal terminal text editor for Linux

- mouse support
- real selection
- copy / cut / paste, multi-level undo / redo, find, go-to-line

![litefe editing its own README](images/screenshot.png)


## Build

Needs only a C compiler + libc:

```sh
cc -O2 -Wall -o litefe litefe.c
```

### Install (optional)

```sh
sudo cp litefe /usr/local/bin/
```

## Keys

| Key | Action |
|-----|--------|
| `Ctrl-S` / `Ctrl-Q` | save / quit |
| `Ctrl-F` · `Ctrl-N`/`F3` | find · find next |
| `Ctrl-G` | go to line |
| `Ctrl-C` `Ctrl-X` `Ctrl-V` `Ctrl-A` | copy · cut · paste · select all |
| `Ctrl-Z` / `Ctrl-Y` | undo / redo |
| `Ctrl-D` / `Ctrl-K` | duplicate line · cut line |
| `Shift`+arrows | select · `Ctrl`+`Left`/`Right` word jump |
| `Ctrl-T` | set mark, then move to select (for terminals that eat `Shift`+arrow, e.g. macOS Terminal.app); `Esc` cancels |
| `Ctrl-B` | toggle mouse mode |
| `Ctrl-H` | help |

Press **`Ctrl-H`** inside the editor for the full list.

## Mouse modes

Toggle with **`Ctrl-B`**:

- **Desktop** (default): the terminal owns the mouse, so native
  drag-select and the right-click menu work and copy plain text. Line
  numbers are hidden so a selection stays clean, and the mouse wheel
  scrolls the document.
- **In-app**: click places the cursor, drag makes an editor selection,
  the wheel scrolls, and line numbers are shown.

Copy / cut also push to the system clipboard via OSC 52.
