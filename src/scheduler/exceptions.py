class SchedulerError(Exception):
    """Base exception for all scheduler-related errors."""
    pass


class ConfigurationError(SchedulerError):
    """Raised when there are issues with the configuration."""
    pass


class ConstraintViolationError(SchedulerError):
    """Raised when a schedule violates constraints."""
    pass


class TimeSlotError(SchedulerError):
    """Raised when there are issues with time slot configuration."""
    pass


class ResourceError(SchedulerError):
    """Raised when there are issues with resources."""
    pass


class OptimizationError(SchedulerError):
    """Raised when optimization fails."""
    pass


class ExportError(SchedulerError):
    """Raised when schedule export fails."""
    pass 