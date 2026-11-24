"""Small source-policy utilities; these do not replace Lean or Comparator."""
from pathlib import Path
import os


def source_files(root: Path):
    for directory, children, names in os.walk(root, followlinks=False):
        children[:] = sorted(
            name for name in children
            if name not in {".git", ".lake", "generated", "__pycache__"}
            and not (Path(directory) / name).is_symlink()
        )
        for name in sorted(names):
            if name.endswith(".lean"):
                yield Path(directory) / name


def code_only(text: str) -> str:
    """Blank nested comments and strings, retaining offsets and line breaks."""
    out = list(text)
    index = 0
    depth = 0
    string = False
    while index < len(text):
        if depth:
            if text.startswith("/-", index):
                out[index:index + 2] = "  "
                depth += 1
                index += 2
            elif text.startswith("-/", index):
                out[index:index + 2] = "  "
                depth -= 1
                index += 2
            else:
                if text[index] != "\n":
                    out[index] = " "
                index += 1
        elif string:
            if text[index] == "\\" and index + 1 < len(text):
                out[index] = " "
                if text[index + 1] != "\n":
                    out[index + 1] = " "
                index += 2
            else:
                string = text[index] != '"'
                if text[index] != "\n":
                    out[index] = " "
                index += 1
        elif text.startswith("/-", index):
            out[index:index + 2] = "  "
            depth = 1
            index += 2
        elif text.startswith("--", index):
            end = text.find("\n", index)
            if end < 0:
                end = len(text)
            out[index:end] = " " * (end - index)
            index = end
        elif text[index] == '"':
            out[index] = " "
            string = True
            index += 1
        else:
            index += 1
    return "".join(out)
