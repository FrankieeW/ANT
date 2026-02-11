# Git Configuration Guide for This Project

## Overview

This document explains the `.gitignore` and `.gitkeep` setup for this Lean 4 project.

## What Gets Ignored

### Lean 4 Build Artifacts
```
.lake/          # Lake build directory
build/          # Alternative build output
*.olean         # Lean object files
*.ilean         # Lean interface files
*.trace         # Lean trace files
lake-packages/  # Downloaded dependencies
```

### Beads Issue Tracker
```
.beads/db.jsonl       # Local issue database
.beads/.sync-*        # Sync state files
.beads/.repo-id       # Repository fingerprint
```

**Important**: `.beads/config.toml` IS tracked (shared team configuration)

### Editor Files
```
.vscode/.history/     # VS Code local history
*.swp, *.swo          # Vim swap files
*~                    # Backup files
```

### OS Files
```
.DS_Store             # macOS folder metadata
Thumbs.db             # Windows thumbnails
desktop.ini           # Windows folder config
```

## What Gets Preserved with .gitkeep

### `.vscode/.gitkeep`
- Preserves the `.vscode/` directory in git
- Allows you to add shared workspace settings later
- Prevents git from deleting the directory when it's empty

## Best Practices

### Adding New Ignore Rules

Edit `.gitignore` and add patterns:
```bash
# Pattern examples:
*.log              # Ignore all .log files
temp/              # Ignore entire temp directory
!important.log     # Exception: don't ignore this specific file
```

### Adding .gitkeep to Empty Directories

If you have a directory structure you want to preserve:
```bash
mkdir -p docs/diagrams
touch docs/diagrams/.gitkeep
git add docs/diagrams/.gitkeep
```

### Checking What's Ignored

```bash
# See all ignored files
git status --ignored

# Check if specific file is ignored
git check-ignore -v path/to/file

# See what would be added (dry run)
git add --dry-run .
```

### Cleaning Ignored Files

```bash
# Preview what would be deleted
git clean -ndX

# Actually delete ignored files (BE CAREFUL!)
git clean -fdX
```

## Common Scenarios

### "I accidentally committed build artifacts"
```bash
# Remove from git but keep locally
git rm --cached -r .lake/
git commit -m "chore: remove .lake/ from tracking"

# Ensure .gitignore has .lake/
echo ".lake/" >> .gitignore
git add .gitignore
git commit -m "chore: add .lake/ to .gitignore"
```

### "I want to track a specific ignored file"
```bash
# Force add despite .gitignore
git add -f path/to/file

# Or add exception to .gitignore
echo "!path/to/file" >> .gitignore
```

### "Empty directory keeps disappearing"
```bash
# Add .gitkeep to preserve it
touch empty-dir/.gitkeep
git add empty-dir/.gitkeep
```

## This Project's Structure

```
ANT/
├── .gitignore           # Ignore patterns
├── .vscode/
│   └── .gitkeep        # Preserves directory
├── ANT/                # Lean source files (tracked)
├── .beads/
│   ├── config.toml     # Tracked (shared config)
│   ├── db.jsonl        # Ignored (local database)
│   └── .sync-*         # Ignored (sync state)
└── .lake/              # Ignored (build artifacts)
```

## References

- [Git Documentation - .gitignore](https://git-scm.com/docs/gitignore)
- [GitHub gitignore templates](https://github.com/github/gitignore)
- [Lean 4 Manual](https://lean-lang.org/lean4/doc/)
