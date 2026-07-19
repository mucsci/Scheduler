"""Enforce complete documentation for public callables and data fields."""

import ast
import re
from pathlib import Path

import pytest

SOURCE = Path(__file__).resolve().parents[1] / "src" / "scheduler"
REQUIRED_SECTIONS = ("Args:", "Returns:", "Raises:", "Behavior:")


def _public_callables(tree: ast.Module):
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and not node.name.startswith("_"):
            yield node.name, node
        if isinstance(node, ast.ClassDef):
            for child in node.body:
                if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)) and not child.name.startswith("_"):
                    yield f"{node.name}.{child.name}", child


def _documented_inline(class_node: ast.ClassDef, index: int, field: ast.AnnAssign) -> bool:
    if index + 1 < len(class_node.body):
        following = class_node.body[index + 1]
        if isinstance(following, ast.Expr) and isinstance(following.value, ast.Constant):
            if isinstance(following.value.value, str) and following.value.value.strip():
                return True
    if isinstance(field.value, ast.Call):
        return any(
            keyword.arg == "description"
            and isinstance(keyword.value, ast.Constant)
            and isinstance(keyword.value.value, str)
            and keyword.value.value.strip()
            for keyword in field.value.keywords
        )
    return False


def _documented_in_class_docstring(class_node: ast.ClassDef, field_name: str) -> bool:
    docstring = ast.get_docstring(class_node) or ""
    return re.search(rf"(?m)^\s*(?:-\s*)?`?{re.escape(field_name)}`?\s*:", docstring) is not None


def test_all_public_callables_have_complete_docstrings() -> None:
    failures: list[str] = []
    for path in sorted(SOURCE.rglob("*.py")):
        tree = ast.parse(path.read_text(encoding="utf-8"))
        for qualified_name, node in _public_callables(tree):
            docstring = ast.get_docstring(node) or ""
            summary = docstring.split("Args:", maxsplit=1)[0].strip()
            missing = [section for section in REQUIRED_SECTIONS if section not in docstring]
            if len(summary) < 20:
                missing.append("high-level description")
            if missing:
                failures.append(f"{path.relative_to(SOURCE)}:{node.lineno} {qualified_name}: {', '.join(missing)}")
    assert not failures, "\n" + "\n".join(failures)


def test_all_public_data_fields_are_described() -> None:
    failures: list[str] = []
    for path in sorted(SOURCE.rglob("*.py")):
        tree = ast.parse(path.read_text(encoding="utf-8"))
        for class_node in (node for node in tree.body if isinstance(node, ast.ClassDef)):
            for index, field in enumerate(class_node.body):
                if not isinstance(field, ast.AnnAssign) or not isinstance(field.target, ast.Name):
                    continue
                if field.target.id.startswith("_"):
                    continue
                if not _documented_inline(class_node, index, field) and not _documented_in_class_docstring(
                    class_node, field.target.id
                ):
                    failures.append(f"{path.relative_to(SOURCE)}:{field.lineno} {class_node.name}.{field.target.id}")
    assert not failures, "\n" + "\n".join(failures)


@pytest.mark.parametrize("module", ["contracts.py", "problem.py"])
def test_solver_independent_datatype_docs_do_not_require_importing_z3(module: str) -> None:
    """Keep documentation enforcement source-based for the Z3-free contract layers."""
    tree = ast.parse((SOURCE / module).read_text(encoding="utf-8"))
    assert tree.body
