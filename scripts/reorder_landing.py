#!/usr/bin/env python3
"""Place the generated project index immediately after the landing hero."""
from __future__ import annotations

import sys
from pathlib import Path

OVERVIEW_START = '<section class="overview">'
PROJECTS_START = '  <h2 class="sec">Projects</h2>'
LEGEND_START = '  <div class="legend">'
BLOCK_END = '  </div>'


def reorder(html: str) -> str:
    overview_at = html.index(OVERVIEW_START)
    projects_at = html.index(PROJECTS_START)
    if projects_at < overview_at:
        return html

    legend_at = html.index(LEGEND_START, projects_at)
    projects_end = html.index(BLOCK_END, legend_at) + len(BLOCK_END)
    projects = html[projects_at:projects_end]
    without_projects = html[:projects_at] + html[projects_end:]
    overview_at = without_projects.index(OVERVIEW_START)
    return without_projects[:overview_at] + projects + "\n" + without_projects[overview_at:]


def main(paths: list[str]) -> int:
    if not paths:
        print("usage: reorder_landing.py INDEX.html [...]", file=sys.stderr)
        return 2
    for raw_path in paths:
        path = Path(raw_path)
        html = path.read_text(encoding="utf-8")
        updated = reorder(html)
        if updated != html:
            path.write_text(updated, encoding="utf-8")
            print(f"reordered projects in {path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
