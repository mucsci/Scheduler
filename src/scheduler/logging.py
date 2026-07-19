import logging
import os

logger = logging.getLogger("Scheduler")


def configure_logging() -> None:
    """
    Configure the process-wide default logging handler for application entry points.

    Args:
        None.

    Returns:
        None.

    Raises:
        None under normal operation; exceptions from the standard library logging
        configuration are allowed to propagate.

    Behavior:
        The root logger is configured with a timestamped text format and the level
        named by ``LOGLEVEL``, defaulting to ``INFO``. The function is called by
        CLI and server startup rather than library import, so embedding applications
        retain control of logging. As with ``logging.basicConfig``, an existing root
        handler normally causes the call to leave the active configuration intact.
    """
    logging.basicConfig(
        level=os.getenv("LOGLEVEL", "INFO").upper(),
        format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
        style="%",
        datefmt="%Y-%m-%d %H:%M:%S",
    )
