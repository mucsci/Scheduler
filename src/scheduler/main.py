import click

from .config import CombinedConfig, OptimizerFlags
from .logging import logger
from .scheduler import Scheduler, load_config_from_file
from .writers import CSVWriter, JSONWriter


def _get_writer(format: str, output_file: str | None) -> JSONWriter | CSVWriter:
    """
    Get the appropriate writer based on the output format.

    **Args:**
    - format: The output format ("json" or "csv")
    - output_file: The output file path, or None for stdout

    **Returns:**
    The appropriate writer instance (JSONWriter or CSVWriter)
    """
    if format == "json":
        return JSONWriter(output_file)
    else:
        return CSVWriter(output_file)


@click.command()
@click.argument("config", type=click.Path(exists=True), required=True)
@click.option("--limit", "-l", type=int, help="Maximum number of models to generate")
@click.option(
    "--format",
    "-f",
    type=click.Choice(["csv", "json"]),
    default="csv",
    help="Output format",
)
@click.option("--output", "-o", help="Output basename (extension added automatically)")
@click.option(
    "--optimizer-flags",
    "-O",
    type=click.Choice([flag.value for flag in OptimizerFlags]),
    multiple=True,
    help="Optimizer flags",
)
def main(
    config: str,
    limit: int,
    format: str,
    output: str,
    optimizer_flags: list[OptimizerFlags],
):
    """Generate course schedules using constraint satisfaction solving."""

    full_config = load_config_from_file(CombinedConfig, config)
    if limit is not None:
        full_config.limit = limit
    limit = full_config.limit
    if optimizer_flags:
        full_config.optimizer_flags = optimizer_flags

    logger.info(f"Using limit={limit}")

    sched = Scheduler(full_config)
    logger.info("Created all constraints")

    # Determine output filename
    output_file = f"{output}.{format}" if output else None

    # Create appropriate writer
    with _get_writer(format, output_file) as writer:
        for i, m in enumerate(sched.get_models()):
            writer.add_schedule(m)
            # For interactive mode (no output file), prompt user
            if not output and i + 1 < limit and not click.confirm("Generate next model?", default=True):
                break

    if output_file:
        logger.info(f"Output written to {output_file}")


if __name__ == "__main__":
    main()
