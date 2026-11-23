# Isolated continuation setup

The first setup command created this run directory and its metadata, then
failed to read `verification/runs/20261123T201422Z/run-verifier.py` from the
recovery worktree. That source-only remote checkpoint predates the local
runner. The observed error was:

```text
FileNotFoundError: [Errno 2] No such file or directory: 'verification/runs/20261123T201422Z/run-verifier.py'
```

The next command copied the existing local runner from its observed absolute
path and adapted only the new-source snapshot directory. No proof source or
audit gate was changed by this setup error. The original full audit continues
in its original checkout. Both checkouts have separate project build outputs
and share the unchanged pinned dependency checkouts.
