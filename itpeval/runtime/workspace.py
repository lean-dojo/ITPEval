from contextlib import contextmanager
from pathlib import Path
import tempfile


@contextmanager
def attempt_workspace(retain_dir: Path | None):
    if retain_dir is None:
        with tempfile.TemporaryDirectory(prefix="itpeval-attempt-") as directory:
            yield Path(directory)
    else:
        retain_dir.mkdir(parents=True, exist_ok=True)
        yield Path(tempfile.mkdtemp(prefix="attempt-", dir=retain_dir))
