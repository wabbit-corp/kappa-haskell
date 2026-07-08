from __future__ import annotations

import sys
import textwrap
from pathlib import Path, PureWindowsPath


SCRIPTS_DIR = Path(__file__).resolve().parent / "scripts"
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))

import validate as validate


def write_text(path: Path, content: str) -> Path:
    path.write_text(textwrap.dedent(content).lstrip("\n"), encoding="utf-8")
    return path


def test_strip_inline_code_replaces_matched_code_spans_with_whitespace() -> None:
    line = "Alpha `[[Ignored.md:1]]` and ``§2 `still code` `` omega"

    stripped = validate.strip_inline_code(line)

    assert len(stripped) == len(line)
    assert stripped.startswith("Alpha ")
    assert " and " in stripped
    assert stripped.endswith(" omega")
    assert "[[Ignored.md:1]]" not in stripped
    assert "§2" not in stripped
    assert "still code" not in stripped


def test_strip_inline_code_blanks_rest_of_line_after_unmatched_backtick() -> None:
    line = "Alpha `[[Ignored.md:1]] and §2"

    stripped = validate.strip_inline_code(line)

    assert len(stripped) == len(line)
    assert stripped.startswith("Alpha ")
    assert set(stripped[len("Alpha ") :]) == {" "}


def test_validate_unicode_characters_reports_forbidden_and_suspicious_characters(
    tmp_path: Path,
) -> None:
    path = tmp_path / "sample.md"
    text = f"alpha\u00A0\nbeta{chr(0x00E9)}\nsection {validate.SECTION_SIGN}1"

    problems = validate.validate_unicode_characters(path, text)

    assert [(problem.line, problem.message) for problem in problems] == [
        (1, "contains forbidden character U+00A0 (NO-BREAK SPACE)"),
        (
            2,
            "contains suspicious Latin-1 Supplement character "
            f"U+00E9 ({chr(0x00E9)!r})",
        ),
    ]


def test_parse_markdown_ignores_inline_and_fenced_references(tmp_path: Path) -> None:
    path = write_text(
        tmp_path / "doc.md",
        """
        <!-- intro -->
        ## 1. Intro
        Inline `[[Ignored.md:1]]` and `\u00A71.9` should not count.
        ```
        [[AlsoIgnored.md:2]]
        \u00A72.3
        ```
        See [[Guide.md:2.1]] and \u00A71.
        """,
    )

    document = validate.parse_markdown(
        path,
        path.read_text(encoding="utf-8"),
        max_line_length=0,
    )

    assert document.sections == {"1"}
    assert [
        (reference.raw, reference.target.name, reference.section)
        for reference in document.references
    ] == [
        ("[[Guide.md:2.1]]", "Guide.md", "2.1"),
        (f"{validate.SECTION_SIGN}1", "doc.md", "1"),
    ]


def test_validate_markdown_sections_reports_missing_parent_and_nonconsecutive_numbers(
    tmp_path: Path,
) -> None:
    path = tmp_path / "Guide.md"
    lines = [
        "<!-- child -->",
        "### 1.2 Child",
        "<!-- later -->",
        "## 3. Later",
    ]

    problems, sections = validate.validate_markdown_sections(path, lines)

    assert sections == {"1.2", "3"}
    assert [problem.message for problem in problems] == [
        "section 1.2 is missing its numbered parent 1",
        "section number 1.2 is not consecutive within section 1; expected 1",
        "section number 3 is not consecutive at the top level; expected 1",
    ]


def test_validate_markdown_sections_accepts_consecutive_numeric_headings(tmp_path: Path) -> None:
    path = tmp_path / "Guide.md"
    lines = [
        "<!-- one -->",
        "## 1. One",
        "<!-- one.child_one -->",
        "### 1.1 Child One",
        "<!-- one.child_two -->",
        "### 1.2 Child Two",
        "<!-- two -->",
        "## 2. Two",
    ]

    problems, sections = validate.validate_markdown_sections(path, lines)

    assert problems == []
    assert sections == {"1", "1.1", "1.2", "2"}


def test_validate_markdown_sections_accepts_preface_zero_child_before_one(
    tmp_path: Path,
) -> None:
    path = tmp_path / "Guide.md"
    lines = [
        "<!-- runtime -->",
        "## 1. Runtime",
        "<!-- runtime.preface -->",
        "### 1.1 Runtime model",
        "<!-- runtime.preface.conformance_model -->",
        "#### 1.1.0 Conformance model",
        "<!-- runtime.preface.io -->",
        "#### 1.1.1 IO semantics",
    ]

    problems, sections = validate.validate_markdown_sections(path, lines)

    assert problems == []
    assert sections == {"1", "1.1", "1.1.0", "1.1.1"}


def test_validate_markdown_sections_reports_nonconsecutive_child_heading(tmp_path: Path) -> None:
    path = tmp_path / "Guide.md"
    lines = [
        "<!-- one -->",
        "## 1. One",
        "<!-- one.child_one -->",
        "### 1.1 Child One",
        "<!-- one.child_three -->",
        "### 1.3 Child Three",
    ]

    problems, sections = validate.validate_markdown_sections(path, lines)

    assert sections == {"1", "1.1", "1.3"}
    assert [problem.message for problem in problems] == [
        "section number 1.3 is not consecutive within section 1; expected 2"
    ]


def test_validate_markdown_sections_accepts_letter_suffixed_numeric_sections(
    tmp_path: Path,
) -> None:
    path = tmp_path / "Guide.md"
    lines = [
        "<!-- expressions -->",
        "## 1. Expressions",
        "<!-- expressions.match -->",
        "### 1.1 Match",
        "<!-- expressions.match.base -->",
        "#### 1.1.1 Base",
        "<!-- expressions.match.inserted_a -->",
        "#### 1.1.1A Inserted A",
        "<!-- expressions.match.inserted_b -->",
        "#### 1.1.1B Inserted B",
        "<!-- expressions.match.next -->",
        "#### 1.1.2 Next",
    ]

    problems, sections = validate.validate_markdown_sections(path, lines)

    assert problems == []
    assert sections == {"1", "1.1", "1.1.1", "1.1.1A", "1.1.1B", "1.1.2"}


def test_validate_markdown_sections_accepts_appendix_and_first_child(tmp_path: Path) -> None:
    path = tmp_path / "Guide.md"
    lines = [
        "<!-- appendix.foo -->",
        "## Appendix A. Foo",
        "<!-- appendix.foo.bar -->",
        "### A.1 Bar",
    ]

    problems, sections = validate.validate_markdown_sections(path, lines)

    assert problems == []
    assert sections == {"A", "A.1"}


def test_validate_markdown_sections_accepts_appendix_child_with_trailing_dot(
    tmp_path: Path,
) -> None:
    path = tmp_path / "Guide.md"
    lines = [
        "<!-- appendix.foo -->",
        "## Appendix A. Foo",
        "<!-- appendix.foo.bar -->",
        "### A.1. Bar",
    ]

    problems, sections = validate.validate_markdown_sections(path, lines)

    assert problems == []
    assert sections == {"A", "A.1"}


def test_validate_markdown_sections_reports_heading_level_jump(tmp_path: Path) -> None:
    path = tmp_path / "Guide.md"
    lines = [
        "<!-- parent -->",
        "## Parent",
        "<!-- parent.too_deep -->",
        "#### Too Deep",
    ]

    problems, sections = validate.validate_markdown_sections(path, lines)

    assert sections == set()
    assert [problem.message for problem in problems] == [
        "heading level jumps from ## to ####; missing ### heading"
    ]


def test_validate_markdown_sections_reports_duplicate_appendix(tmp_path: Path) -> None:
    path = tmp_path / "Guide.md"
    lines = [
        "<!-- appendix.foo -->",
        "## Appendix A. Foo",
        "<!-- appendix.bar -->",
        "## Appendix A. Bar",
    ]

    problems, sections = validate.validate_markdown_sections(path, lines)

    assert sections == {"A"}
    assert [problem.message for problem in problems] == [
        "appendix A is declared more than once"
    ]


def test_validate_markdown_sections_reports_duplicate_titles(tmp_path: Path) -> None:
    path = tmp_path / "Guide.md"
    lines = [
        "<!-- one.foo -->",
        "## 1. Foo",
        "<!-- two.foo -->",
        "## 2. Foo",
    ]

    problems, sections = validate.validate_markdown_sections(path, lines)

    assert sections == {"1", "2"}
    assert [problem.message for problem in problems] == [
        "heading title 'Foo' is declared more than once"
    ]


def test_validate_markdown_sections_accepts_unique_section_ids(tmp_path: Path) -> None:
    path = tmp_path / "Spec.md"
    lines = [
        "# Kappa Language Specification",
        "<!-- design -->",
        "## 1. Design",
        "<!-- design.principles -->",
        "### 1.1 Principles",
        "<!-- design.principles.readability_counts -->",
        "#### Readability counts",
    ]

    problems, sections = validate.validate_markdown_sections(path, lines)

    assert problems == []
    assert sections == {"1", "1.1"}


def test_validate_markdown_sections_requires_section_ids_in_any_markdown_file(
    tmp_path: Path,
) -> None:
    path = tmp_path / "Guide.md"
    lines = [
        "## 1. Intro",
        "### 1.1 Details",
    ]

    problems, sections = validate.validate_markdown_sections(path, lines)

    assert [problem.message for problem in problems] == [
        "heading is missing a preceding section id comment like <!-- modules.files -->",
        "heading is missing a preceding section id comment like <!-- modules.files -->",
    ]
    assert sections == {"1", "1.1"}


def test_validate_markdown_sections_requires_section_id_for_every_section_heading(
    tmp_path: Path,
) -> None:
    path = tmp_path / "Guide.md"
    lines = [
        "<!-- modules -->",
        "## 1. Modules",
        "<!-- modules.imports -->",
        "### 1.1 Imports",
        "#### URL module specifiers",
    ]

    problems, sections = validate.validate_markdown_sections(path, lines)

    assert sections == {"1", "1.1"}
    assert [problem.message for problem in problems] == [
        "heading is missing a preceding section id comment like <!-- modules.files -->"
    ]


def test_validate_markdown_sections_reports_invalid_section_id_format(tmp_path: Path) -> None:
    path = tmp_path / "Spec.md"
    lines = [
        "<!-- Modules.Files -->",
        "## 1. Modules and files",
    ]

    problems, sections = validate.validate_markdown_sections(path, lines)

    assert sections == {"1"}
    assert [problem.message for problem in problems] == [
        "section id 'Modules.Files' must use lowercase dot-separated identifiers"
    ]


def test_validate_markdown_sections_reports_duplicate_section_ids(tmp_path: Path) -> None:
    path = tmp_path / "Spec.md"
    lines = [
        "<!-- design -->",
        "## 1. Design",
        "<!-- design -->",
        "### 1.1 Principles",
    ]

    problems, sections = validate.validate_markdown_sections(path, lines)

    assert sections == {"1", "1.1"}
    assert [problem.message for problem in problems] == [
        "section id 'design' is declared more than once"
    ]


def test_problem_sort_key_normalizes_paths_to_lowercase_posix() -> None:
    problem = validate.Problem(
        path=PureWindowsPath(r"Docs\MixedCase.md"),
        line=7,
        message="boom",
    )

    assert validate.problem_sort_key(problem) == ("docs/mixedcase.md", 7, "boom")


def test_main_ignores_fenced_lines_for_max_line_length(tmp_path: Path, capsys) -> None:
    path = write_text(
        tmp_path / "doc.md",
        f"""
        <!-- intro -->
        ## 1. Intro
        ```
        {'x' * 40}
        ```
        See \u00A71.
        """,
    )

    exit_code = validate.main(["--max-line-length", "20", str(path)])
    captured = capsys.readouterr()

    assert exit_code == 0
    assert captured.out.strip() == "Validation passed: checked 1 file(s)."
    assert captured.err == ""


def test_main_reports_cross_file_reference_errors(tmp_path: Path, capsys) -> None:
    write_text(
        tmp_path / "A.md",
        """
        <!-- intro -->
        ## 1. Intro
        See [[B.md:2]] and [[Missing.md:1]].
        """,
    )
    write_text(
        tmp_path / "B.md",
        """
        <!-- present -->
        ## 1. Present
        """,
    )

    exit_code = validate.main([str(tmp_path)])
    captured = capsys.readouterr()

    assert exit_code == 1
    assert "referenced section does not exist: [[B.md:2]]" in captured.out
    assert "referenced file does not exist: [[Missing.md:1]]" in captured.out
    assert "Validation failed: 2 problem(s) across 2 file(s)." in captured.out
    assert captured.err == ""


def test_main_reports_problems_in_referenced_markdown_files(tmp_path: Path, capsys) -> None:
    write_text(
        tmp_path / "A.md",
        """
        <!-- intro -->
        ## 1. Intro
        See [[B.md]].
        """,
    )
    write_text(
        tmp_path / "B.md",
        """
        <!-- child -->
        ### 1.2 Child
        """,
    )

    exit_code = validate.main([str(tmp_path / "A.md")])
    captured = capsys.readouterr()

    assert exit_code == 1
    assert "B.md:2: section 1.2 is missing its numbered parent 1" in captured.out
    assert (
        "B.md:2: section number 1.2 is not consecutive within section 1; expected 1"
        in captured.out
    )
    assert "Validation failed: 2 problem(s) across 1 file(s)." in captured.out
    assert captured.err == ""


def test_main_reports_invalid_utf8(tmp_path: Path, capsys) -> None:
    path = tmp_path / "broken.md"
    path.write_bytes(b"\xff")

    exit_code = validate.main([str(path)])
    captured = capsys.readouterr()

    assert exit_code == 1
    assert "file is not valid UTF-8" in captured.out
    assert "Validation failed: 1 problem(s) across 1 file(s)." in captured.out
    assert captured.err == ""


def test_main_validates_appendix_wiki_link_sections(tmp_path: Path, capsys) -> None:
    write_text(
        tmp_path / "A.md",
        """
        <!-- intro -->
        ## 1. Intro
        See [[B.md:A.2]].
        """,
    )
    write_text(
        tmp_path / "B.md",
        """
        <!-- appendix.notes -->
        ## Appendix A. Notes
        <!-- appendix.notes.details -->
        ### A.1 Details
        """,
    )

    exit_code = validate.main([str(tmp_path)])
    captured = capsys.readouterr()

    assert exit_code == 1
    assert "referenced section does not exist: [[B.md:A.2]]" in captured.out
    assert "Validation failed: 1 problem(s) across 2 file(s)." in captured.out
    assert captured.err == ""


def test_parse_markdown_expands_numeric_section_ranges(tmp_path: Path) -> None:
    path = write_text(
        tmp_path / "doc.md",
        """
        <!-- intro -->
        ## 1. Intro
        See \u00A71-3 and \u00A7\u00A71.1 \u2013 1.3.
        """,
    )

    document = validate.parse_markdown(
        path,
        path.read_text(encoding="utf-8"),
        max_line_length=0,
    )

    assert [reference.section for reference in document.references] == [
        "1",
        "2",
        "3",
        "1.1",
        "1.2",
        "1.3",
    ]
    assert document.problems == []


def test_parse_markdown_collects_section_lists_with_oxford_comma(tmp_path: Path) -> None:
    path = write_text(
        tmp_path / "doc.md",
        """
        <!-- intro -->
        ## 1. Intro
        See \u00A7\u00A72.1, 2.2, 2.3, and 2.3.2.
        """,
    )

    document = validate.parse_markdown(
        path,
        path.read_text(encoding="utf-8"),
        max_line_length=0,
    )

    assert [reference.section for reference in document.references] == [
        "2.1",
        "2.2",
        "2.3",
        "2.3.2",
    ]
    assert document.problems == []


def test_parse_markdown_collects_letter_suffixed_numeric_references(tmp_path: Path) -> None:
    path = write_text(
        tmp_path / "doc.md",
        """
        <!-- expressions -->
        ## 1. Expressions
        <!-- expressions.match -->
        ### 1.1 Match
        <!-- expressions.match.base -->
        #### 1.1.1 Base
        <!-- expressions.match.inserted_a -->
        #### 1.1.1A Inserted A
        See \u00A71.1.1A and \u00A717.4.7A.
        """,
    )

    document = validate.parse_markdown(
        path,
        path.read_text(encoding="utf-8"),
        max_line_length=0,
    )

    assert document.sections == {"1", "1.1", "1.1.1", "1.1.1A"}
    assert [reference.section for reference in document.references] == [
        "1.1.1A",
        "17.4.7A",
    ]
    assert document.problems == []


def test_parse_markdown_collects_plain_appendix_references(tmp_path: Path) -> None:
    path = write_text(
        tmp_path / "doc.md",
        """
        <!-- appendix.pipe_operators -->
        ## Appendix B. Pipe operators
        <!-- appendix.pipe_operators.prelude_provisions -->
        ### B.1 Prelude provisions
        <!-- appendix.pipe_operators.interaction -->
        ### B.2 Interaction
        <!-- appendix.pipe_operators.optional_typed_pipe -->
        ### B.3 Optional typed pipe
        <!-- appendix.applicative_do -->
        ## Appendix G. ApplicativeDo
        See Appendix G and Appendix B.3.
        """,
    )

    document = validate.parse_markdown(
        path,
        path.read_text(encoding="utf-8"),
        max_line_length=0,
    )

    assert document.sections == {"B", "B.1", "B.2", "B.3", "G"}
    assert [reference.section for reference in document.references] == ["G", "B.3"]
    assert document.problems == []


def test_parse_markdown_warns_on_appendix_ranges(tmp_path: Path) -> None:
    path = write_text(
        tmp_path / "doc.md",
        """
        <!-- appendix.notes -->
        ## Appendix A. Notes
        <!-- appendix.notes.one -->
        ### A.1 One
        <!-- appendix.notes.two -->
        ### A.2 Two
        See \u00A7A.1-A.3.
        """,
    )

    document = validate.parse_markdown(
        path,
        path.read_text(encoding="utf-8"),
        max_line_length=0,
    )

    assert [reference.section for reference in document.references] == ["A.1", "A.3"]
    assert [problem.message for problem in document.problems] == [
        "appendix ranges are not expanded; enumerate sections explicitly: \u00A7A.1-A.3"
    ]


def test_validate_line_lengths_requires_matching_fence_length(tmp_path: Path) -> None:
    path = tmp_path / "doc.md"
    lines = [
        "````",
        "x" * 40,
        "```",
        "y" * 40,
        "````",
    ]

    problems = validate.validate_line_lengths(path, lines, max_length=10)

    assert problems == []


def test_parse_markdown_ignores_blockquote_fences(tmp_path: Path) -> None:
    path = write_text(
        tmp_path / "doc.md",
        """
        <!-- intro -->
        ## 1. Intro
        > ```
        > [[Ignored.md:1]]
        > \u00A72
        > ```
        See [[Guide.md:1]] and \u00A71.
        """,
    )

    document = validate.parse_markdown(
        path,
        path.read_text(encoding="utf-8"),
        max_line_length=0,
    )

    assert [(reference.target.name, reference.section) for reference in document.references] == [
        ("Guide.md", "1"),
        ("doc.md", "1"),
    ]


def test_parse_markdown_ignores_references_in_indented_code_blocks(tmp_path: Path) -> None:
    path = write_text(
        tmp_path / "doc.md",
        """
        <!-- intro -->
        ## 1. Intro

            [[Ignored.md:1]]
            \u00A72

        \t[[AlsoIgnored.md:1]]
        \t\u00A73

        See [[Guide.md:1]] and \u00A71.
        """,
    )

    document = validate.parse_markdown(
        path,
        path.read_text(encoding="utf-8"),
        max_line_length=0,
    )

    assert [(reference.target.name, reference.section) for reference in document.references] == [
        ("Guide.md", "1"),
        ("doc.md", "1"),
    ]


def test_validate_line_lengths_ignores_indented_code_blocks(tmp_path: Path) -> None:
    path = tmp_path / "doc.md"
    lines = [
        "## 1. Intro",
        "",
        f"    {'x' * 40}",
        f"\t{'y' * 40}",
        "See §1.",
    ]

    problems = validate.validate_line_lengths(path, lines, max_length=20)

    assert problems == []


def test_validate_unicode_characters_counts_carriage_return_lines(tmp_path: Path) -> None:
    path = tmp_path / "sample.md"
    text = "alpha\rbeta\u00A0\rgamma"

    problems = validate.validate_unicode_characters(path, text)

    assert [(problem.line, problem.message) for problem in problems] == [
        (2, "contains forbidden character U+00A0 (NO-BREAK SPACE)")
    ]


def test_parse_markdown_ignores_references_after_unterminated_inline_code(tmp_path: Path) -> None:
    path = write_text(
        tmp_path / "doc.md",
        """
        <!-- intro -->
        ## 1. Intro
        Unterminated `[[Ignored.md:1]] and \u00A72
        See [[Guide.md:1]] and \u00A71.
        """,
    )

    document = validate.parse_markdown(
        path,
        path.read_text(encoding="utf-8"),
        max_line_length=0,
    )

    assert [(reference.target.name, reference.section) for reference in document.references] == [
        ("Guide.md", "1"),
        ("doc.md", "1"),
    ]
