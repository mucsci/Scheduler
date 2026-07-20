"""Compatibility tests for documented and legacy scheduler imports."""

import inspect

import scheduler
import scheduler.scheduler as legacy_scheduler


def test_scheduler_public_imports_remain_compatible() -> None:
    exported_names = (
        "Scheduler",
        "ScheduleDiagnosis",
        "ConfigurationDiagnostic",
        "ConfigurationValidationResult",
        "DayFeasibilityDiagnostic",
        "CandidateDomainDiagnostic",
        "CapacityDiagnostic",
        "FacultyWorkloadDiagnostic",
        "ResourceUsageDiagnostic",
        "ObjectiveScoreDiagnostic",
        "ProvenanceEdge",
        "ScheduleAudit",
        "RepairSetDiagnostic",
        "ConstraintDiagnostic",
        "RelaxationSuggestion",
        "load_config_from_file",
        "validate_combined_config_data",
    )
    for name in exported_names:
        assert getattr(scheduler, name) is getattr(legacy_scheduler, name)


def test_scheduler_constructor_and_methods_keep_their_signatures() -> None:
    assert (
        str(inspect.signature(scheduler.Scheduler))
        == "(full_config: scheduler.config.CombinedConfig, *, solver_timeout_ms: int | None = None)"
    )
    assert (
        str(inspect.signature(scheduler.Scheduler.get_models))
        == "(self) -> collections.abc.Generator[list[scheduler.models.course.CourseInstance], None, None]"
    )
    assert str(inspect.signature(scheduler.Scheduler.diagnose)) == "(self) -> scheduler.contracts.ScheduleDiagnosis"
    assert (
        str(inspect.signature(scheduler.Scheduler.audit_schedule))
        == "(self, schedule: list['CourseInstance']) -> scheduler.contracts.ScheduleAudit"
    )


def test_legacy_faculty_availability_helper_remains_importable() -> None:
    assert callable(legacy_scheduler.get_faculty_availability)


def test_capacity_resource_config_models_are_exported() -> None:
    assert scheduler.RoomConfig(name="R1", capacity=30).name == "R1"
    assert scheduler.LabConfig(name="L1", capacity=24).capacity == 24
    assert scheduler.CourseModality.HYBRID == "hybrid"
    assert scheduler.DeliveryMode.ONLINE == "online"
