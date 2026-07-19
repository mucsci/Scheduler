"""Source-driven checks keeping narrative documentation aligned with public behavior."""

import inspect
import re
from pathlib import Path

import pytest

from scheduler import CombinedConfig, Scheduler, load_config_from_file
from scheduler import scheduler as facade_module
from scheduler.config import (
    ClassPattern,
    CourseConfig,
    FacultyConfig,
    Meeting,
    SchedulerConfig,
    TimeBlock,
    TimeRange,
    TimeSlotConfig,
)
from scheduler.server import app

ROOT = Path(__file__).resolve().parents[1]
PAGES = ROOT / "fern" / "docs" / "pages"


def _page(relative_path: str) -> str:
    return (PAGES / relative_path).read_text(encoding="utf-8")


@pytest.mark.parametrize(
    ("model", "pages"),
    [
        (TimeBlock, ("configuration/time-slots.mdx",)),
        (TimeRange, ("configuration/faculty.mdx", "configuration/time-slots.mdx")),
        (Meeting, ("configuration/time-slots.mdx",)),
        (ClassPattern, ("configuration/time-slots.mdx",)),
        (TimeSlotConfig, ("configuration/time-slots.mdx",)),
        (CourseConfig, ("configuration/courses.mdx",)),
        (FacultyConfig, ("configuration/faculty.mdx",)),
        (
            SchedulerConfig,
            (
                "configuration/overview.mdx",
                "configuration/rooms-labs.mdx",
                "configuration/courses.mdx",
                "configuration/faculty.mdx",
            ),
        ),
        (
            CombinedConfig,
            (
                "configuration/overview.mdx",
                "configuration/limit.mdx",
                "configuration/optimizer-flags.mdx",
            ),
        ),
    ],
)
def test_every_configuration_field_has_narrative_coverage(model, pages: tuple[str, ...]) -> None:
    """Require each live Pydantic field name in its assigned configuration guide."""
    narrative = "\n".join(_page(page) for page in pages)
    missing = [name for name in model.model_fields if f"`{name}`" not in narrative]
    assert not missing, f"{model.__name__} fields missing from {pages}: {missing}"


def test_every_fastapi_route_has_rest_inventory_coverage() -> None:
    """Require every non-framework application route in the REST integration page."""
    narrative = _page("rest/quickstart.mdx")
    framework_routes = {"/openapi.json", "/docs", "/docs/oauth2-redirect", "/redoc"}
    application_paths = {
        path
        for route in app.routes
        if isinstance((path := getattr(route, "path", None)), str) and path not in framework_routes
    }
    missing = sorted(path for path in application_paths if f"`{path}`" not in narrative)
    assert not missing, f"REST routes missing from endpoint inventory: {missing}"


def test_python_guides_cover_facade_methods_and_compatibility_exports() -> None:
    """Keep documented workflows and legacy public contracts synchronized with the façade."""
    python_guide = _page("python/overview.mdx")
    concepts = _page("concepts/diagnostics-auditing.mdx")
    narrative = python_guide + "\n" + concepts

    public_methods = {
        name for name, value in inspect.getmembers(Scheduler, predicate=inspect.isfunction) if not name.startswith("_")
    }
    missing_methods = sorted(name for name in public_methods if f"`{name}" not in python_guide)
    missing_exports = sorted(name for name in facade_module.__all__ if f"`{name}`" not in narrative)

    assert not missing_methods, f"Scheduler methods missing from Python guide: {missing_methods}"
    assert not missing_exports, f"Compatibility exports missing from Python/concepts guides: {missing_exports}"


def test_every_api_limit_environment_variable_is_documented() -> None:
    """Discover server safeguard variables directly from source and require REST coverage."""
    server_source = (ROOT / "src" / "scheduler" / "server.py").read_text(encoding="utf-8")
    environment_variables = set(re.findall(r"SCHEDULER_API_[A-Z_]+", server_source))
    rest_guide = _page("rest/quickstart.mdx")
    missing = sorted(name for name in environment_variables if f"`{name}`" not in rest_guide)
    assert not missing, f"API limit variables missing from REST guide: {missing}"


def test_canonical_documented_configurations_validate() -> None:
    """Keep every complete configuration linked as canonical executable input."""
    overview = _page("configuration/overview.mdx")
    paths = (ROOT / "tests" / "fixtures" / "minimal_config.json", ROOT / "example.json")
    for path in paths:
        assert path.name in overview
        load_config_from_file(CombinedConfig, path)


@pytest.mark.integration
def test_canonical_minimal_python_workflow_matches_documentation() -> None:
    """Exercise enumeration, diagnosis, and auditing with the documented minimal input."""
    config = load_config_from_file(CombinedConfig, ROOT / "tests" / "fixtures" / "minimal_config.json")
    scheduler = Scheduler(config, solver_timeout_ms=30_000)
    diagnosis = scheduler.diagnose()
    schedule = next(scheduler.get_models())
    audit = scheduler.audit_schedule(schedule)

    assert diagnosis.status == "satisfiable"
    assert audit.is_valid
    assert len(schedule) == len(config.config.courses)


def test_contributor_docs_reject_monolithic_architecture_claims() -> None:
    """Prevent the pre-refactor scheduler ownership model from returning."""
    constraints = _page("dev/constraints.mdx")
    contributing = (ROOT / "CONTRIBUTING.md").read_text(encoding="utf-8")
    agent_guide = (ROOT / "AGENT.md").read_text(encoding="utf-8")

    stale_claims = (
        "Hard scheduling rules are expressed as Z3 boolean formulas in **`src/scheduler/scheduler.py`**",
        "scheduler.py            # Core scheduling logic and Z3 integration",
        "src/scheduler/     # Package: config, scheduler (Z3)",
    )
    corpus = "\n".join((constraints, contributing, agent_guide))
    assert not [claim for claim in stale_claims if claim in corpus]
    assert "`SolverEngine` owns the Z3 context" in constraints
    assert "`Scheduler` is a stable orchestration façade" in constraints
