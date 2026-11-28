# Agent instructions

This repository is developed as a submodule of SQLMRLab; the rules for
publishing it (branches `main` and `feature/pipeline-dev`, submodules first)
are in SQLMRLab's `AGENTS.md`. These rules hold here too.

# Language

Everything written into this repository or published from it is in English, with
no Chinese: commit messages, code comments, documentation and READMEs, issue
titles and bodies, pull request and patch descriptions, and comments on GitHub.
This holds from now on and for every change. Commit history already pushed is
not rewritten; files that are still in Chinese are translated into English.

# Branches after a merge

A branch forked for a pull request (for example a `claude/...` branch) lives
only until that pull request is merged into `feature/pipeline-dev` (or another
stable development branch). Right after the merge, delete that branch both
locally and on `origin`, and make sure its pull request is closed: merged, or
closed by hand if it was superseded. Check first that the branch has no commit
the target branch lacks. Fork a new branch from the latest
`feature/pipeline-dev` for the next pull request.

# Remote CI

Every commit published to any of the three repositories must pass that
repository's remote CI (GitHub Actions). Merge a pull request only after all of
its checks are green; when a check fails, find the cause and fix it before the
merge. Never skip, disable or weaken a check to make it pass.
