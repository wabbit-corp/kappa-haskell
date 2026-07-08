#!/usr/bin/env python3
from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass, field
from pathlib import Path
import re


IGNORE_DIR_NAMES = {
    ".git",
    ".idea",
    ".vs",
    ".dotnet",
    ".kappa",
    ".toolchain",
    "__pycache__",
    "anon-workspace",
    "bin",
    "obj",
    "dist",
    "dist-newstyle",
    "dist-source",
}

IGNORE_FILE_NAMES = {
    ".dotnet-install.ps1",
}

TEXT_SUFFIXES = {
    ".c",
    ".cabal",
    ".fs",
    ".fsproj",
    ".h",
    ".hs",
    ".json",
    ".kp",
    ".md",
    ".props",
    ".ps1",
    ".py",
    ".sh",
    ".sln",
    ".targets",
    ".toml",
    ".txt",
    ".xml",
    ".yaml",
    ".yml",
}

FORBIDDEN_CHARS = {
    0x00A0: "NO-BREAK SPACE",
    0x200B: "ZERO WIDTH SPACE",
    0x200C: "ZERO WIDTH NON-JOINER",
    0x200D: "ZERO WIDTH JOINER",
    0xFEFF: "BYTE ORDER MARK",
    0xFFFD: "REPLACEMENT CHARACTER",
}

ALLOWED_LATIN1_SUPPLEMENT = {
    0x00A7,  # section sign
    0x00B7,  # middle dot
}

SECTION_SIGN = "\u00A7"
EN_DASH = "\u2013"
EM_DASH = "\u2014"
APPENDIX_SECTION_TOKEN = r"[A-Z](?:\.\d+)*"
NUMERIC_SECTION_TOKEN = r"\d+(?:\.\d+)*(?:[A-Z])?"
PURE_NUMERIC_SECTION_TOKEN = r"\d+(?:\.\d+)*"
SECTION_TOKEN = rf"(?:{APPENDIX_SECTION_TOKEN}|{NUMERIC_SECTION_TOKEN})"
FENCE_RE = re.compile(r"^(?P<marker>`{3,}|~{3,})(?P<rest>.*)$")
WIKI_REFERENCE_RE = re.compile(rf"\[\[([^\[\]:]+\.md)(?::({SECTION_TOKEN}))?\]\]")
APPENDIX_REFERENCE_RE = re.compile(rf"\bAppendix (?P<section>{APPENDIX_SECTION_TOKEN})\b")
SECTION_ID_FORMAT_RE = re.compile(r"^[a-z][a-z0-9_]*(?:\.[a-z][a-z0-9_]*)*$")
HTML_COMMENT_RE = re.compile(r"^\s*<!--\s*(?P<body>.*?)\s*-->\s*$")

NUMERIC_HEADING_RE = re.compile(
    rf"^(?P<hashes>#{{2,6}})\s+(?P<section>{NUMERIC_SECTION_TOKEN})(?:\.)?\s+(?P<title>\S.*\S|\S)\s*$"
)
APPENDIX_HEADING_RE = re.compile(
    r"^(?P<hashes>##)\s+Appendix\s+(?P<section>[A-Z])\.\s+(?P<title>\S.*\S|\S)\s*$"
)
APPENDIX_SUBHEADING_RE = re.compile(
    r"^(?P<hashes>#{3,6})\s+(?P<section>[A-Z](?:\.\d+)*)(?:\.)?\s+(?P<title>\S.*\S|\S)\s*$"
)
HEADING_RE = re.compile(r"^(?P<hashes>#{1,6})\s+(?P<title>\S.*\S|\S)\s*$")

SECTION_SEPARATOR = rf"(?:-|{EN_DASH}|{EM_DASH}|,(?:\s*(?:and|or))?|and|or)"
SECTION_GROUP_RE = re.compile(
    rf"{SECTION_SIGN}{{1,2}}{SECTION_TOKEN}"
    rf"(?:\s*{SECTION_SEPARATOR}\s*(?:{SECTION_SIGN}{{1,2}})?{SECTION_TOKEN})*"
)
SECTION_REFERENCE_RE = re.compile(rf"(?:{SECTION_SIGN}{{1,2}})?(?P<section>{SECTION_TOKEN})")
INLINE_CODE_RE = re.compile(r"(`+)(.*?)\1")
NUMERIC_SECTION_PART_RE = re.compile(r"^(?P<number>\d+)(?P<suffix>[A-Z]?)$")
PURE_NUMERIC_SECTION_RE = re.compile(rf"^{PURE_NUMERIC_SECTION_TOKEN}$")
RANGE_SEPARATORS = {"-", EN_DASH, EM_DASH}


@dataclass(frozen=True)
class Problem:
    path: Path
    line: int
    message: str


@dataclass(frozen=True)
class Reference:
    path: Path
    line: int
    target: Path
    section: str | None
    raw: str


@dataclass
class ParsedMarkdown:
    path: Path
    sections: set[str] = field(default_factory=set)
    references: list[Reference] = field(default_factory=list)
    problems: list[Problem] = field(default_factory=list)


@dataclass(frozen=True)
class Fence:
    marker_char: str
    marker_length: int


def problem_sort_key(problem: Problem) -> tuple[str, int, str]:
    return (problem.path.as_posix().lower(), problem.line, problem.message)


def repo_root() -> Path:
    return Path(__file__).resolve().parent.parent


def default_paths() -> list[Path]:
    root = repo_root()
    for candidate in (root / "docs" / "Spec.md", root / "Spec.md"):
        if candidate.is_file():
            return [candidate]
    return iter_text_files(root)


def is_ignored_file(path: Path) -> bool:
    return path.name in IGNORE_FILE_NAMES


def is_text_file(path: Path) -> bool:
    return path.suffix.lower() in TEXT_SUFFIXES and path.is_file() and not is_ignored_file(path)


def iter_text_files(root: Path) -> list[Path]:
    results: list[Path] = []
    for child in sorted(root.iterdir(), key=lambda p: (p.is_file(), p.name.lower())):
        if child.is_dir():
            if child.name in IGNORE_DIR_NAMES:
                continue
            results.extend(iter_text_files(child))
            continue
        if is_text_file(child):
            results.append(child)
    return results


def resolve_paths(raw_paths: list[str]) -> list[Path]:
    if not raw_paths:
        return default_paths()

    results: list[Path] = []
    for raw in raw_paths:
        path = Path(raw).resolve()
        if path.is_dir():
            results.extend(iter_text_files(path))
            continue
        if is_text_file(path):
            results.append(path)
            continue
        raise FileNotFoundError(f"not a supported text file or directory: {raw}")

    deduped: list[Path] = []
    seen: set[Path] = set()
    for path in results:
        if path not in seen:
            deduped.append(path)
            seen.add(path)
    return deduped


def decode_utf8(path: Path) -> tuple[str | None, list[Problem]]:
    try:
        raw = path.read_bytes()
    except OSError as exc:
        return None, [Problem(path, 1, f"unable to read file: {exc}")]

    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        return None, [
            Problem(
                path,
                1,
                "file is not valid UTF-8 "
                f"(byte offset {exc.start}, reason: {exc.reason})",
            )
        ]

    return text, []


def validate_unicode_characters(path: Path, text: str) -> list[Problem]:
    problems: list[Problem] = []

    for line_number, line in enumerate(text.splitlines(True), start=1):
        for ch in line.rstrip("\r\n"):
            codepoint = ord(ch)

            if codepoint in FORBIDDEN_CHARS:
                problems.append(
                    Problem(
                        path,
                        line_number,
                        f"contains forbidden character U+{codepoint:04X} "
                        f"({FORBIDDEN_CHARS[codepoint]})",
                    )
                )
            elif 0x0080 <= codepoint <= 0x00FF and codepoint not in ALLOWED_LATIN1_SUPPLEMENT:
                problems.append(
                    Problem(
                        path,
                        line_number,
                        "contains suspicious Latin-1 Supplement character "
                        f"U+{codepoint:04X} ({repr(ch)})",
                    )
                )

    return problems


def strip_inline_code(line: str) -> str:
    stripped = INLINE_CODE_RE.sub(lambda match: " " * len(match.group(0)), line)
    unmatched = stripped.find("`")
    if unmatched == -1:
        return stripped
    return stripped[:unmatched] + (" " * (len(stripped) - unmatched))


def strip_blockquote_prefix(line: str) -> str:
    remaining = line

    while True:
        i = 0
        n = len(remaining)

        while i < n and remaining[i] in " \t":
            i += 1
        if i >= n or remaining[i] != ">":
            return remaining

        remaining = remaining[i + 1 :]
        if remaining.startswith(" "):
            remaining = remaining[1:]


def is_blank_line(line: str) -> bool:
    return not line.strip()


def is_indented_code_line(line: str) -> bool:
    content = strip_blockquote_prefix(line)
    return content.startswith("\t") or content.startswith("    ")


def update_fence_state(line: str, current_fence: Fence | None) -> tuple[Fence | None, bool]:
    match = FENCE_RE.match(strip_blockquote_prefix(line))
    if match is None:
        return current_fence, False

    marker = match.group("marker")
    rest = match.group("rest")

    if current_fence is None:
        return Fence(marker_char=marker[0], marker_length=len(marker)), True

    if (
        marker[0] == current_fence.marker_char
        and len(marker) >= current_fence.marker_length
        and not rest.strip()
    ):
        return None, True

    return current_fence, False


def iter_non_fenced_lines(lines: list[str], strip_inline: bool = False) -> list[tuple[int, str]]:
    items: list[tuple[int, str]] = []
    fence: Fence | None = None
    in_indented_code = False
    previous_blank = True

    for index, line in enumerate(lines, start=1):
        fence, is_fence_line = update_fence_state(line, fence)
        if is_fence_line:
            previous_blank = False
            continue
        if fence is not None:
            previous_blank = False
            continue
        if in_indented_code:
            if is_blank_line(line) or is_indented_code_line(line):
                continue
            in_indented_code = False
        if previous_blank and is_indented_code_line(line):
            in_indented_code = True
            continue
        items.append((index, strip_inline_code(line) if strip_inline else line))
        previous_blank = is_blank_line(line)

    return items


def validate_line_lengths(path: Path, lines: list[str], max_length: int) -> list[Problem]:
    if max_length <= 0:
        return []

    problems: list[Problem] = []
    fence: Fence | None = None
    in_indented_code = False
    previous_blank = True

    for index, line in enumerate(lines, start=1):
        fence, is_fence_line = update_fence_state(line, fence)
        if is_fence_line:
            previous_blank = False
            continue
        if fence is not None:
            previous_blank = False
            continue
        if in_indented_code:
            if is_blank_line(line) or is_indented_code_line(line):
                continue
            in_indented_code = False
        if previous_blank and is_indented_code_line(line):
            in_indented_code = True
            continue
        if len(line) > max_length:
            problems.append(
                Problem(
                    path,
                    index,
                    f"line length {len(line)} exceeds {max_length} characters",
                )
            )
        previous_blank = is_blank_line(line)

    return problems


def parse_numeric_section(section: str) -> tuple[tuple[int, ...], tuple[int, str]]:
    parts = section.split(".")
    final_part = NUMERIC_SECTION_PART_RE.fullmatch(parts[-1])
    if final_part is None:
        raise ValueError(f"invalid numeric section: {section}")

    parent = tuple(int(part) for part in parts[:-1])
    current = (int(final_part.group("number")), final_part.group("suffix"))
    return parent, current


def format_numeric_child(child: tuple[int, str]) -> str:
    return f"{child[0]}{child[1]}"


def is_valid_next_numeric_child(
    previous: tuple[int, str] | None,
    current: tuple[int, str],
    *,
    allow_preface_zero: bool = False,
) -> bool:
    if previous is None:
        return current == (1, "") or (allow_preface_zero and current == (0, ""))

    previous_number, previous_suffix = previous
    current_number, current_suffix = current
    if current_number == previous_number:
        expected_suffix = "A" if not previous_suffix else chr(ord(previous_suffix) + 1)
        return current_suffix == expected_suffix
    return current_number == previous_number + 1 and not current_suffix


def expected_numeric_child(
    previous: tuple[int, str] | None,
    current: tuple[int, str],
) -> str:
    if previous is None:
        return "1"
    if current[0] == previous[0]:
        previous_suffix = previous[1]
        next_suffix = "A" if not previous_suffix else chr(ord(previous_suffix) + 1)
        return f"{previous[0]}{next_suffix}"
    return str(previous[0] + 1)


def validate_numeric_heading(
    path: Path,
    line_number: int,
    section: str,
    seen_numeric_children: dict[tuple[int, ...], tuple[int, str]],
    seen_numeric_sections: set[str],
    sections: set[str],
) -> list[Problem]:
    problems: list[Problem] = []
    parent, current = parse_numeric_section(section)
    parent_section = ".".join(str(part) for part in parent)

    if parent and parent_section not in seen_numeric_sections:
        problems.append(
            Problem(
                path,
                line_number,
                f"section {section} is missing its numbered parent {parent_section}",
            )
        )

    previous = seen_numeric_children.get(parent)
    allow_preface_zero = bool(parent)
    if not is_valid_next_numeric_child(
        previous,
        current,
        allow_preface_zero=allow_preface_zero,
    ):
        expected = expected_numeric_child(previous, current)
        scope = f"within section {parent_section}" if parent else "at the top level"
        problems.append(
            Problem(
                path,
                line_number,
                f"section number {section} is not consecutive {scope}; expected {expected}",
            )
        )
    seen_numeric_children[parent] = current
    seen_numeric_sections.add(section)
    sections.add(section)
    return problems


def validate_appendix_heading(
    path: Path,
    line_number: int,
    section: str,
    seen_appendix_children: dict[tuple[str, ...], int],
    seen_appendices: set[str],
    seen_appendix_sections: set[tuple[str, ...]],
    sections: set[str],
) -> list[Problem]:
    problems: list[Problem] = []
    parts = tuple(section.split("."))

    if len(parts) == 1:
        appendix = parts[0]
        if appendix in seen_appendices:
            problems.append(
                Problem(path, line_number, f"appendix {appendix} is declared more than once")
            )
        seen_appendices.add(appendix)
        seen_appendix_sections.add(parts)
        sections.add(section)
        return problems

    parent = parts[:-1]
    if parent not in seen_appendix_sections:
        problems.append(
            Problem(
                path,
                line_number,
                f"appendix section {section} is missing its numbered parent {'.'.join(parent)}",
            )
        )

    current = int(parts[-1])
    expected = seen_appendix_children.get(parent, 0) + 1
    if current != expected:
        problems.append(
            Problem(
                path,
                line_number,
                f"appendix section {section} is not consecutive within {'.'.join(parent)}; expected {expected}",
            )
        )
    seen_appendix_children[parent] = current
    seen_appendix_sections.add(parts)
    sections.add(section)
    return problems


def format_missing_heading_levels(previous_level: int, current_level: int) -> str:
    missing_levels = [("#" * level) for level in range(previous_level + 1, current_level)]
    if len(missing_levels) == 1:
        return f"{missing_levels[0]} heading"
    return f"{', '.join(missing_levels)} headings"


def validate_section_id(
    path: Path,
    lines: list[str],
    line_number: int,
    seen_section_ids: set[str],
) -> list[Problem]:
    if line_number <= 1:
        return [
            Problem(
                path,
                line_number,
                "heading is missing a preceding section id comment like <!-- modules.files -->",
            )
        ]

    previous_line = lines[line_number - 2]
    comment = HTML_COMMENT_RE.fullmatch(previous_line)
    if comment is None:
        return [
            Problem(
                path,
                line_number,
                "heading is missing a preceding section id comment like <!-- modules.files -->",
            )
        ]

    section_id = comment.group("body")
    if SECTION_ID_FORMAT_RE.fullmatch(section_id) is None:
        return [
            Problem(
                path,
                line_number,
                f"section id {section_id!r} must use lowercase dot-separated identifiers",
            )
        ]

    if section_id in seen_section_ids:
        return [Problem(path, line_number, f"section id {section_id!r} is declared more than once")]

    seen_section_ids.add(section_id)
    return []


def validate_markdown_sections(path: Path, lines: list[str]) -> tuple[list[Problem], set[str]]:
    problems: list[Problem] = []
    sections: set[str] = set()
    seen_numeric_children: dict[tuple[int, ...], tuple[int, str]] = {}
    seen_appendix_children: dict[tuple[str, ...], int] = {}
    seen_numeric_sections: set[str] = set()
    seen_appendix_sections: set[tuple[str, ...]] = set()
    seen_appendices: set[str] = set()
    seen_section_ids: set[str] = set()
    seen_titles: set[str] = set()
    previous_heading_level: int | None = None

    for index, line in iter_non_fenced_lines(lines):
        if not line.startswith("#"):
            continue

        heading_match = HEADING_RE.match(line)
        if heading_match is None:
            problems.append(Problem(path, index, "heading must have a title"))
            continue

        heading_level = len(heading_match.group("hashes"))
        if previous_heading_level is not None and heading_level > previous_heading_level + 1:
            problems.append(
                Problem(
                    path,
                    index,
                    f"heading level jumps from {'#' * previous_heading_level} to {'#' * heading_level}; "
                    f"missing {format_missing_heading_levels(previous_heading_level, heading_level)}",
                )
            )
        previous_heading_level = heading_level
        if heading_level >= 2:
            problems.extend(validate_section_id(path, lines, index, seen_section_ids))

        numeric = NUMERIC_HEADING_RE.match(line)
        if numeric:
            title = numeric.group("title")
            if title in seen_titles:
                problems.append(Problem(path, index, f"heading title '{title}' is declared more than once"))
            seen_titles.add(title)
            problems.extend(
                validate_numeric_heading(
                    path=path,
                    line_number=index,
                    section=numeric.group("section"),
                    seen_numeric_children=seen_numeric_children,
                    seen_numeric_sections=seen_numeric_sections,
                    sections=sections,
                )
            )
            continue

        appendix = APPENDIX_HEADING_RE.match(line)
        if appendix:
            title = appendix.group("title")
            if title in seen_titles:
                problems.append(Problem(path, index, f"heading title '{title}' is declared more than once"))
            seen_titles.add(title)
            problems.extend(
                validate_appendix_heading(
                    path=path,
                    line_number=index,
                    section=appendix.group("section"),
                    seen_appendix_children=seen_appendix_children,
                    seen_appendices=seen_appendices,
                    seen_appendix_sections=seen_appendix_sections,
                    sections=sections,
                )
            )
            continue

        appendix_sub = APPENDIX_SUBHEADING_RE.match(line)
        if appendix_sub:
            title = appendix_sub.group("title")
            if title in seen_titles:
                problems.append(Problem(path, index, f"heading title '{title}' is declared more than once"))
            seen_titles.add(title)
            problems.extend(
                validate_appendix_heading(
                    path=path,
                    line_number=index,
                    section=appendix_sub.group("section"),
                    seen_appendix_children=seen_appendix_children,
                    seen_appendices=seen_appendices,
                    seen_appendix_sections=seen_appendix_sections,
                    sections=sections,
                )
            )
            continue

        title = heading_match.group("title")
        if title in seen_titles:
            problems.append(Problem(path, index, f"heading title '{title}' is declared more than once"))
        seen_titles.add(title)

    return problems, sections


def expand_numeric_range(start: str, end: str) -> list[str] | None:
    if not PURE_NUMERIC_SECTION_RE.fullmatch(start) or not PURE_NUMERIC_SECTION_RE.fullmatch(end):
        return None

    start_parts = tuple(int(part) for part in start.split("."))
    end_parts = tuple(int(part) for part in end.split("."))

    if len(start_parts) != len(end_parts):
        return None
    if start_parts[:-1] != end_parts[:-1]:
        return None
    if start_parts[-1] > end_parts[-1]:
        return None

    prefix = start_parts[:-1]
    return [".".join(str(part) for part in (*prefix, value)) for value in range(start_parts[-1], end_parts[-1] + 1)]


def classify_range_problem(raw: str, start: str, end: str) -> str:
    if start[:1].isalpha() or end[:1].isalpha():
        return f"appendix ranges are not expanded; enumerate sections explicitly: {raw}"
    return f"section ranges are not expanded; enumerate sections explicitly: {raw}"


def is_heading_prefix_match(line: str, match_start: int) -> bool:
    prefix = line[:match_start].strip()
    return bool(prefix) and set(prefix) == {"#"}


def parse_section_group(path: Path, line_number: int, group: str) -> tuple[list[str], list[Problem]]:
    matches = list(SECTION_REFERENCE_RE.finditer(group))
    if not matches:
        return [], []

    sections = [matches[0].group("section")]
    problems: list[Problem] = []
    previous_match = matches[0]
    previous_section = sections[0]

    for match in matches[1:]:
        current_section = match.group("section")
        separator = group[previous_match.end() : match.start()].strip()

        if separator in RANGE_SEPARATORS:
            expanded = expand_numeric_range(previous_section, current_section)
            if expanded is None:
                problems.append(
                    Problem(
                        path,
                        line_number,
                        classify_range_problem(
                            f"{SECTION_SIGN}{previous_section}{separator}{current_section}",
                            previous_section,
                            current_section,
                        ),
                    )
                )
                sections.append(current_section)
            else:
                sections.extend(expanded[1:])
        else:
            sections.append(current_section)

        previous_match = match
        previous_section = current_section

    return sections, problems


def collect_markdown_references(path: Path, lines: list[str]) -> tuple[list[Reference], list[Problem]]:
    references: list[Reference] = []
    problems: list[Problem] = []

    for line_number, line in iter_non_fenced_lines(lines, strip_inline=True):
        for match in WIKI_REFERENCE_RE.finditer(line):
            raw_target = match.group(1)
            references.append(
                Reference(
                    path=path,
                    line=line_number,
                    target=(path.parent / raw_target).resolve(),
                    section=match.group(2),
                    raw=match.group(0),
                )
            )

        for match in APPENDIX_REFERENCE_RE.finditer(line):
            if is_heading_prefix_match(line, match.start()):
                continue
            references.append(
                Reference(
                    path=path,
                    line=line_number,
                    target=path,
                    section=match.group("section"),
                    raw=match.group(0),
                )
            )

        for match in SECTION_GROUP_RE.finditer(line):
            sections, group_problems = parse_section_group(path, line_number, match.group(0))
            problems.extend(group_problems)
            for section in sections:
                references.append(
                    Reference(
                        path=path,
                        line=line_number,
                        target=path,
                        section=section,
                        raw=f"{SECTION_SIGN}{section}",
                    )
                )

    return references, problems


def parse_markdown(path: Path, text: str, max_line_length: int) -> ParsedMarkdown:
    lines = text.splitlines()
    section_problems, sections = validate_markdown_sections(path, lines)
    references, reference_problems = collect_markdown_references(path, lines)
    problems = validate_line_lengths(path, lines, max_line_length) + section_problems + reference_problems
    return ParsedMarkdown(path=path, sections=sections, references=references, problems=problems)


def build_markdown_document(path: Path, text: str, max_line_length: int) -> ParsedMarkdown:
    document = parse_markdown(path, text, max_line_length)
    document.problems = validate_unicode_characters(path, text) + document.problems
    return document


def load_markdown_from_text(
    path: Path,
    text: str,
    documents: dict[Path, ParsedMarkdown],
    max_line_length: int,
) -> ParsedMarkdown:
    existing = documents.get(path)
    if existing is not None:
        return existing

    document = build_markdown_document(path, text, max_line_length)
    documents[path] = document
    return document


def load_markdown(
    path: Path,
    documents: dict[Path, ParsedMarkdown],
    max_line_length: int,
) -> ParsedMarkdown | None:
    existing = documents.get(path)
    if existing is not None:
        return existing

    text, decode_problems = decode_utf8(path)
    if decode_problems or text is None:
        document = ParsedMarkdown(path=path, problems=decode_problems)
        documents[path] = document
        return document

    return load_markdown_from_text(path, text, documents, max_line_length)


def validate_markdown_references(
    documents: dict[Path, ParsedMarkdown],
    max_line_length: int,
) -> list[Problem]:
    problems: list[Problem] = []

    for document in list(documents.values()):
        for reference in document.references:
            target_doc = documents.get(reference.target)

            if target_doc is None:
                if not reference.target.is_file():
                    problems.append(
                        Problem(
                            reference.path,
                            reference.line,
                            f"referenced file does not exist: {reference.raw}",
                        )
                    )
                    continue
                if reference.target.suffix.lower() != ".md":
                    problems.append(
                        Problem(
                            reference.path,
                            reference.line,
                            f"referenced file is not markdown: {reference.raw}",
                        )
                    )
                    continue
                loaded = load_markdown(reference.target, documents, max_line_length)
                if loaded is None:
                    continue
                target_doc = loaded

            if reference.section is not None and reference.section not in target_doc.sections:
                problems.append(
                    Problem(
                        reference.path,
                        reference.line,
                        f"referenced section does not exist: {reference.raw}",
                    )
                )

    return problems


def validate_file(
    path: Path,
    markdown_documents: dict[Path, ParsedMarkdown],
    max_line_length: int,
) -> list[Problem]:
    text, decode_problems = decode_utf8(path)
    if decode_problems or text is None:
        return decode_problems

    if path.suffix.lower() == ".md":
        document = load_markdown_from_text(path, text, markdown_documents, max_line_length)
        return document.problems

    return validate_unicode_characters(path, text)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Validate Kappa spec files for UTF-8 hygiene, mojibake, markdown section "
            "numbering, and section references."
        )
    )
    parser.add_argument(
        "paths",
        nargs="*",
        help=(
            "Files or directories to validate. Defaults to docs/Spec.md when present, "
            "then Spec.md, then the repository root containing this script."
        ),
    )
    parser.add_argument(
        "--max-line-length",
        type=int,
        default=0,
        help=(
            "Optional markdown line-length limit outside fenced code blocks. "
            "Use 0 to disable the check. Recommended future target: 120."
        ),
    )
    args = parser.parse_args(argv)

    try:
        files = resolve_paths(args.paths)
    except FileNotFoundError as exc:
        print(exc, file=sys.stderr)
        return 2

    if not files:
        print("no supported text files found", file=sys.stderr)
        return 2

    all_problems: list[Problem] = []
    initial_files = set(files)
    markdown_documents: dict[Path, ParsedMarkdown] = {}

    for path in files:
        all_problems.extend(validate_file(path, markdown_documents, args.max_line_length))

    all_problems.extend(validate_markdown_references(markdown_documents, args.max_line_length))
    for document in markdown_documents.values():
        if document.path not in initial_files:
            all_problems.extend(document.problems)
    all_problems.sort(key=problem_sort_key)

    if not all_problems:
        print(f"Validation passed: checked {len(files)} file(s).")
        return 0

    for problem in all_problems:
        print(f"{problem.path}:{problem.line}: {problem.message}")
    print(f"Validation failed: {len(all_problems)} problem(s) across {len(files)} file(s).")
    return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
