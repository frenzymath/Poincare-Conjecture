#!/usr/bin/env python3
"""Build the project-local Blueprint map tab from the live hgraph files.

The map is a presentation view, not a second dependency engine.  Blueprint
nodes and ``uses`` edges remain owned by hgraph; this script only groups them
by the chapter/section headings already present in the TeX source, embeds the
resulting JSON in the standalone map template, and places that document in an
iframe so its JavaScript runs when hgraph injects the custom tab.
"""

from __future__ import annotations

import argparse
import html
import json
import re
from collections import defaultdict
from pathlib import Path

import yaml


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_TEMPLATE = ROOT / "blueprint" / "tools" / "blueprint_map_template.html"
DEFAULT_OUTPUT = ROOT / "blueprint" / "blueprint-map-tab.html"


def _header(path: Path) -> dict:
    text = path.read_text(encoding="utf-8")
    if not text.startswith("---"):
        return {}
    front, separator, _ = text[3:].partition("---")
    return yaml.safe_load(front) if separator else {}


def _plain_tex(value: str | None) -> str:
    """Turn a short TeX title/body into readable UI text."""
    text = str(value or "")
    # Keep the first argument of texorpdfstring, which is the visible title.
    text = re.sub(r"\\texorpdfstring\{([^{}]*)\}\{[^{}]*\}", r"\1", text)
    text = re.sub(r"\\(?:ensuremath|text|mathrm|operatorname)\{([^{}]*)\}", r"\1", text)
    text = re.sub(r"\\[A-Za-z]+\*?\s*", " ", text)
    text = text.replace("\\&", "&").replace("\\%", "%").replace("~", " ")
    text = re.sub(r"[{}$]", "", text)
    return re.sub(r"\s+", " ", text).strip()


def _blueprint_macros() -> dict[str, str]:
    """Extract the small macro table needed by KaTeX in statement previews."""
    path = ROOT / "blueprint" / "src" / "macros.tex"
    text = path.read_text(encoding="utf-8") if path.exists() else ""
    macros: dict[str, str] = {"\\mbox": "\\text", "\\hbox": "\\text"}
    command = re.compile(
        r"\\(?:providecommand|newcommand)\s*\{(\\[A-Za-z]+)\}"
        r"(?:\s*\[(\d+)\])?\s*\{([^{}]*)\}"
    )
    for match in command.finditer(text):
        name, arguments, body = match.groups()
        macros[name] = body if not arguments else body
    return macros


def _command_value(text: str, start: int) -> tuple[str, int] | None:
    """Read the balanced argument beginning at ``start`` (the opening brace)."""
    if start >= len(text) or text[start] != "{":
        return None
    depth = 0
    for i in range(start, len(text)):
        if text[i] == "{":
            depth += 1
        elif text[i] == "}":
            depth -= 1
            if depth == 0:
                return text[start + 1 : i], i + 1
    return None


def _heading_context() -> tuple[list[str], dict[str, dict[str, str]]]:
    """Return chapter order and label -> chapter/section source coordinates."""
    content = ROOT / "blueprint" / "src" / "content.tex"
    source = content.read_text(encoding="utf-8")
    includes = re.findall(r"\\input\{([^}]+)\}", source)
    files = []
    for include in includes:
        if include == "macros":
            continue
        path = content.parent / f"{include}.tex"
        if path.exists():
            files.append(path)

    chapters: list[str] = []
    labels: dict[str, dict[str, str]] = {}
    for chapter_number, path in enumerate(files, start=1):
        text = path.read_text(encoding="utf-8")
        chapter = None
        section = "Other results"
        command_re = re.compile(r"\\(chapter|section|subsection)\*?")
        for match in command_re.finditer(text):
            value = _command_value(text, match.end())
            if value is None:
                continue
            title, end = value
            command = match.group(1)
            if command == "chapter":
                chapter = _plain_tex(title)
                if chapter and chapter not in chapters:
                    chapters.append(chapter)
                section = "Other results"
            elif command == "section":
                section = _plain_tex(title) or "Other results"
            elif command == "subsection" and section == "Other results":
                section = _plain_tex(title) or section

        # All theorem-like environments share the chapter-scoped `theorem`
        # counter in macros.tex.  Record the number readers see in the PDF so
        # map cards do not have to expose internal labels or source citations.
        statement_re = re.compile(
            r"\\begin\{(theorem|proposition|lemma|corollary|definition|remark)\}"
        )
        for statement_number, statement in enumerate(statement_re.finditer(text), start=1):
            environment = statement.group(1)
            end = text.find(rf"\end{{{environment}}}", statement.end())
            block = text[statement.end() : end if end >= 0 else len(text)]
            label = re.search(r"\\label\{([^}]+)\}", block)
            if not label:
                continue
            context = labels.setdefault(label.group(1).strip(), {})
            context["number"] = f"{chapter_number}.{statement_number}"
            context["display_kind"] = environment.title()
            dcref = re.search(r"\\dcref\{([^}]+)\}", block)
            if dcref:
                context["dcref"] = dcref.group(1).strip()
        # A label belongs to the latest heading before it in this file.  Walk
        # once more so labels inside nested theorem bodies get that context.
        chapter = None
        section = "Other results"
        events = re.compile(r"\\(chapter|section|subsection)\*?|\\label").finditer(text)
        for match in events:
            if match.group(0) == r"\label":
                value = _command_value(text, match.end())
                if value and value[0].strip():
                    context = labels.setdefault(value[0].strip(), {})
                    context.update({
                        "chapter": chapter or "Other results",
                        "section": section or "Other results",
                    })
                continue
            value = _command_value(text, match.end())
            if value is None:
                continue
            title, _ = value
            command = match.group(1)
            if command == "chapter":
                chapter = _plain_tex(title)
                section = "Other results"
            elif command == "section":
                section = _plain_tex(title) or "Other results"
            elif command == "subsection" and section == "Other results":
                section = _plain_tex(title) or section

    return chapters, labels


def _build_data() -> dict:
    chapters, label_context = _heading_context()
    nodes: dict[str, dict] = {}
    for path in sorted((ROOT / "hgraph" / "nodes").glob("*.md")):
        meta = _header(path)
        if meta.get("generated") != "blueprint" or meta.get("stale"):
            continue
        node_id = path.stem
        label = str(meta.get("label") or node_id)
        context = label_context.get(label, {})
        kind = str(meta.get("content_type") or "statement")
        title = _plain_tex(meta.get("title")) or label
        display_kind = context.get("display_kind") or kind.title()
        display_number = context.get("number")
        display_title = f"{display_kind} {display_number}: {title}" if display_number else f"{display_kind}: {title}"
        chapter = str(meta.get("chapter") or context.get("chapter") or "Other results")
        # Older generated records spell ampersands differently.  They are
        # normally stale, but normalising here keeps hand-authored records in
        # the correct column if one survives a partial sync.
        chapter = _plain_tex(chapter).replace(" and ", " & ")
        raw_body = path.read_text(encoding="utf-8").split("---", 2)[-1].strip()
        nodes[node_id] = {
            "id": node_id,
            "label": label,
            "title": title,
            "display_title": display_title,
            # Keep the source TeX for the preview panel; the browser's KaTeX
            # renderer makes it match the statement body in the blueprint.
            "body": raw_body,
            "chapter": chapter,
            "section": context.get("section") or "Other results",
            "kind": kind,
            "status": str(meta.get("lean_status") or "empty"),
            "order": int(meta.get("order") or 0),
            "ref": _plain_tex(context.get("dcref") or meta.get("ref")),
        }

    # Hgraph stores uses as consumer -> prerequisite.  The visual map reads
    # left-to-right, so expose arrows as prerequisite -> consumer.
    edges: list[dict] = []
    seen: set[tuple[str, str]] = set()
    for path in sorted((ROOT / "hgraph" / "edges").glob("*.md")):
        meta = _header(path)
        if meta.get("type") != "uses":
            continue
        source, target = str(meta.get("source") or ""), str(meta.get("target") or "")
        if source not in nodes or target not in nodes or (target, source) in seen:
            continue
        seen.add((target, source))
        edges.append({"from": target, "to": source})

    chapter_order = []
    for chapter in chapters:
        normalized = _plain_tex(chapter).replace(" and ", " & ")
        if any(n["chapter"] == normalized for n in nodes.values()):
            chapter_order.append(normalized)
    for chapter in sorted({n["chapter"] for n in nodes.values()}):
        if chapter not in chapter_order:
            chapter_order.append(chapter)

    grouped: dict[str, dict[str, list[dict]]] = defaultdict(lambda: defaultdict(list))
    for node in sorted(nodes.values(), key=lambda n: (n["chapter"], n["order"], n["title"])):
        grouped[node["chapter"]][node["section"]].append(node)

    chapter_payload = []
    for chapter in chapter_order:
        sections = []
        for section, section_nodes in grouped.get(chapter, {}).items():
            sections.append({
                "id": re.sub(r"[^a-z0-9]+", "-", section.lower()).strip("-") or "other",
                "title": section,
                "nodes": section_nodes,
            })
        chapter_payload.append({
            "id": re.sub(r"[^a-z0-9]+", "-", chapter.lower()).strip("-") or "chapter",
            "title": chapter,
            "sections": sections,
        })

    return {
        "title": "The Poincare Conjecture",
        "chapters": chapter_payload,
        "nodes": list(nodes.values()),
        "edges": edges,
        "stats": {"nodes": len(nodes), "edges": len(edges), "chapters": len(chapter_payload)},
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--template", type=Path, default=DEFAULT_TEMPLATE)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()

    template = args.template.read_text(encoding="utf-8")
    payload = json.dumps(_build_data(), ensure_ascii=False, separators=(",", ":"))
    macros = json.dumps(_blueprint_macros(), ensure_ascii=False, separators=(",", ":"))
    app = (
        template
        .replace("__BLUEPRINT_MAP_DATA__", payload)
        .replace("__BLUEPRINT_MAP_MACROS__", macros)
    )
    # hgraph renders custom tab content as injected HTML.  Scripts in injected
    # markup are inert, so keep the interactive map self-contained in srcdoc.
    rendered = (
        '<div class="blueprint-map-embed">'
        '<iframe title="Blueprint map" class="blueprint-map-frame" '
        f'srcdoc="{html.escape(app, quote=True)}" loading="eager"></iframe>'
        '</div>'
        '<style>'
        '.blueprint-map-embed{position:fixed;z-index:40;inset:0;width:100vw;'
        'height:100vh;min-height:0;background:#f5f7fa;}'
        '.blueprint-map-frame{display:block;width:100%;height:100%;min-height:0;'
        'border:0;background:#f5f7fa;}'
        '</style>'
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(rendered, encoding="utf-8")
    print(f"wrote {args.output} ({len(payload)} bytes of map data)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
