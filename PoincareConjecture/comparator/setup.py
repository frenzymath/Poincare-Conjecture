"""Build pinned Landrun and Nanoda locally; requires Go >= 1.24 and recent Rust."""

import json
from pathlib import Path
import shutil
import subprocess

root = Path(__file__).resolve().parent.parent
tools = json.loads((root / "comparator/provenance.json").read_text())["tools"]
for executable in ("git", "go", "cargo"):
    if shutil.which(executable) is None:
        raise SystemExit(f"Missing {executable}; see comparator/README.md")

build = root / ".lake/comparator-tools"
binary_dir = build / "bin"
binary_dir.mkdir(parents=True, exist_ok=True)
for name, pin in tools.items():
    source = build / "src" / name
    if not source.exists():
        subprocess.run(["git", "clone", "--no-checkout", pin["repository"], str(source)],
                       check=True)
        subprocess.run(["git", "checkout", "--detach", pin["commit"]], cwd=source, check=True)
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=source, text=True).strip()
    dirty = subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=no"],
                                    cwd=source, text=True)
    if revision != pin["commit"] or dirty:
        raise SystemExit(f"Expected clean pinned source at {source}; preserve and inspect it")
    if name == "landrun":
        subprocess.run(["go", "build", "-mod=readonly", "-o", str(binary_dir / "landrun"),
                        "./cmd/landrun"], cwd=source, check=True)
    else:
        subprocess.run(["cargo", "build", "--locked", "--release", "--bin", "nanoda_bin"],
                       cwd=source, check=True)
        shutil.copy2(source / "target/release/nanoda_bin", binary_dir / "nanoda_bin")
print(f"Pinned Landrun and Nanoda installed in {binary_dir}")
