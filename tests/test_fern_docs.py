"""Regression tests for the Fern-native Python library reference configuration."""

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_fern_cli_and_openapi_migration_are_pinned() -> None:
    """Keep the repository compiler pin and OpenAPI compatibility migration aligned."""
    fern_config = json.loads((ROOT / "fern" / "fern.config.json").read_text(encoding="utf-8"))
    generators = (ROOT / "fern" / "generators.yml").read_text(encoding="utf-8")

    assert fern_config["version"] == "5.75.4"
    assert "disambiguate-request-names: false" in generators


def test_python_reference_uses_fern_library_generation() -> None:
    """Ensure Python docs come from local source and generated output stays untracked."""
    docs_config = (ROOT / "fern" / "docs.yml").read_text(encoding="utf-8")
    gitignore = (ROOT / ".gitignore").read_text(encoding="utf-8")

    assert "scheduler-python:" in docs_config
    assert "path: .." in docs_config
    assert "path: ./static/python-reference" in docs_config
    assert "lang: python" in docs_config
    assert "source: /python-api/reference" in docs_config
    assert "destination: /python-api/reference/scheduler" in docs_config
    assert "slug: reference" in docs_config
    assert "/fern/static/python-reference/" in gitignore


def test_legacy_python_reference_generator_is_removed() -> None:
    """Prevent the retired pydoc-markdown pipeline from being reintroduced accidentally."""
    project = (ROOT / "pyproject.toml").read_text(encoding="utf-8")

    assert "pydoc-markdown" not in project
    assert not (ROOT / "scripts" / "gen_python_api_mdx.py").exists()
    assert not (ROOT / "fern" / "docs" / "pages" / "python" / "reference.mdx").exists()


def test_docs_workflow_generates_and_validates_without_publishing_pull_requests() -> None:
    """Lock the native generation command, runtime versions, and publish guard in CI."""
    workflow = (ROOT / ".github" / "workflows" / "docs.yml").read_text(encoding="utf-8")

    assert "pull_request:" in workflow
    assert 'node-version: "22"' in workflow
    assert "npm install -g fern-api@5.75.4" in workflow
    assert "fern docs md generate --local --library scheduler-python" in workflow
    assert "Verify Python library reference coverage" in workflow
    assert "git diff --exit-code -- fern/openapi.json fern/docs/assets/combined-config.schema.json" in workflow
    assert "fern check --warnings" in workflow
    assert "if: github.event_name != 'pull_request'" in workflow


def test_docs_workflow_checks_complete_scheduler_reference_surface() -> None:
    """Require CI coverage for façade methods, helpers, and diagnostic/audit contracts."""
    workflow = (ROOT / ".github" / "workflows" / "docs.yml").read_text(encoding="utf-8")

    required_reference_terms = (
        "Scheduler.diagnose",
        "Scheduler.audit_schedule",
        "validate_combined_config_data",
        "load_config_from_file",
        "ScheduleDiagnosis",
        "ScheduleAudit",
        "ConstraintDiagnostic",
        "CourseInstance",
    )
    for term in required_reference_terms:
        assert term in workflow
