# Document revisions

<span id="manage-document-revisions"></span>

`DocumentSession(task, prepared)` checks source edits across all ten built-in provers. `submit(handle, candidate)` returns a revision handle and evidence. `reset()` starts a new generation and invalidates old handles, `replay(candidates)` resets and checks a sequence of edits, and `finalize(handle)` runs a fresh check. [Native goal sessions](native-interaction.md)

## Fork and save a document

Call `fork(handle)` to try an alternate edit while keeping the original revision. Save `checkpoint(handle)` to resume from another process with the same prepared environment.

```python
import json
from pathlib import Path

from itpeval.backends.projects import build_task
from itpeval.environments import load_project
from itpeval.runtime.sessions import DocumentCheckpoint, DocumentSession

# Open the same task you would give to verify-task.
project = load_project(Path("path/to/lock.json"))
task = build_task(project)
session = DocumentSession(task, project)
original, evidence = session.submit(session.handle, task.allowed_edits[0])

# Try a second candidate without changing the original revision.
branch = session.fork(original)
branch.submit(branch.handle, task.allowed_edits[1])

# A fresh worker can read this JSON and replay the saved revision.
path = Path("proof-checkpoint.json")
path.write_text(json.dumps(session.checkpoint(original).to_dict()), encoding="utf-8")
checkpoint = DocumentCheckpoint.from_dict(json.loads(path.read_bytes()))
restored, replayed = DocumentSession.from_checkpoint(task, project, checkpoint)
print(replayed.task_success)
```

A checkpoint stores the submission, task ID and environment ID. Restoring it checks the saved input again. [Proof task format](../../reference/task-manifests.md)
