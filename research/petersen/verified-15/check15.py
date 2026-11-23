"""From the pinned proof project's lean directory, run: lake env python3 /path/to/check15.py"""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
MODULES = (
    "CompactSearch", "FastCompact", "SplitCompact", "C5Seven",
    "SixNumeric0", "SixNumeric1", "SixNumeric2", "SixNumeric3", "SixOpposite",
    "AssemblyCore", "AssemblyComplete",
)
def main():
    lean = shutil.which("lean")
    if not lean or "LEAN_PATH" not in os.environ:
        raise SystemExit("Run inside the project's pinned lake environment.")
    deps = [str(Path(p).resolve()) for p in os.environ["LEAN_PATH"].split(os.pathsep) if p]
    with tempfile.TemporaryDirectory(prefix="petersen-lean-") as directory:
        env = dict(os.environ, LEAN_PATH=os.pathsep.join([directory, *deps]))
        for mod in MODULES:
            source = f"{mod}.lean"
            shutil.copyfile(ROOT / source, Path(directory) / source)
            subprocess.run([lean, "-j", "1", "-o", f"{mod}.olean", source],
                           cwd=directory, env=env, check=True)
    print("Verified both Petersen 15-gate lower bounds in Lean.")

if __name__ == "__main__":
    main()
