import click

from .config import SchedulerConfig, TimeSlotConfig
from .logging import logger
from .scheduler import load_config_from_file, Scheduler
from .writers import JSONWriter, CSVWriter


def _get_writer(format: str, output_file: str) -> JSONWriter | CSVWriter:
    if format == "json":
        return JSONWriter(output_file)
    else:
        return CSVWriter(output_file)


@click.command()
@click.argument("config", type=click.Path(exists=True), required=True)
@click.option(
    "--timeslot-config",
    "-t",
    type=click.Path(exists=True),
    default="time_slots.json",
    help="Path to the time slot configuration file",
)
@click.option("--limit", "-l", default=10, help="Maximum number of models to generate")
@click.option(
    "--format",
    "-f",
    type=click.Choice(["csv", "json"]),
    default="csv",
    help="Output format",
)
@click.option("--output", "-o", help="Output basename (extension added automatically)")
@click.option(
    "--optimize",
    "-O",
    is_flag=True,
    help="Enable optimization of preferences (slower)",
)
def main(
    config: str,
    timeslot_config: str,
    limit: int,
    format: str,
    output: str,
    optimize: bool,
):
    """Generate course schedules using constraint satisfaction solving."""

    logger.info(f"Using limit={limit}, optimize={optimize}")
    config = load_config_from_file(SchedulerConfig, config)
    time_slot_config = load_config_from_file(TimeSlotConfig, timeslot_config)

    sched = Scheduler(config, time_slot_config)
    logger.info("Created all constraints")

    # Determine output filename
    output_file = f"{output}.{format}" if output else None

    # Create appropriate writer
    with _get_writer(format, output_file) as writer:
        for i, m in enumerate(sched.get_models(limit, optimize)):
            writer.add_schedule(sched.courses, m)

            # For interactive mode (no output file), prompt user
            if not output and i + 1 < limit:
                if not click.confirm("Generate next model?", default=True):
                    break
        
    if output_file:
        logger.info(f"Output written to {output_file}")


if __name__ == "__main__":
    main()
