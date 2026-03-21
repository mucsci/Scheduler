import logging
import os

logger = logging.getLogger("Scheduler")


def configure_logging() -> None:
    """
    Configure logging for CLI and server entry points.

    Called by the scheduler CLI and scheduler-server at startup. Not invoked
    on library import, so applications that embed the scheduler control their
    own logging configuration.

    **Usage:**
    ```python
    from scheduler.logging import configure_logging
    configure_logging()
    ```
    """
    logging.basicConfig(
        level=os.getenv("LOGLEVEL", "INFO").upper(),
        format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
        style="%",
        datefmt="%Y-%m-%d %H:%M:%S",
    )
