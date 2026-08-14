# VS Code Extension Manager (`code-extensions`)

A Python script to install, update, list, search, and remove VS Code extensions directly from the VS Code Marketplace or Open VSX Registry. It features an interactive terminal user interface (TUI) for selecting updates, search results, or extensions to remove, along with security controls to mitigate supply-chain attacks.

## Features

- **Subcommands**: Supports `install`, `update`, `list`, `search`, and `remove` commands.
- **Direct VS Code Marketplace API Integration**: Queries extension metadata and package assets directly from the marketplace gallery API.
- **Supply-Chain Security Mitigation**: Holds back releases newer than a specified age (default `24h`) across both `install` and `update` commands to ensure packages have not been compromised or flag-analyzed.
- **Interactive Terminal UI**: Scrollable interactive menus in your terminal to toggle, select, and review updates, search results, or removals.
- **Auto Platform & Architecture Resolution**: Detects and downloads platform-specific `.vsix` packages (e.g. `linux-x64`, `darwin-arm64`, `win32-x64`).
- **VS Code Version Compatibility Checks**: Verifies host VS Code version engine requirements so you never install incompatible extensions.
- **Alternative VS Code Extension Registries & Open VSX**: Query extensions from Open VSX or custom self-hosted VS Code Extension Galleries.
- **Alternative VS Code Forks Supported**: Works with alternative builds or forks (e.g. VSCodium, VS Code Insiders) via `--code-binary`.

---

## Installation

Ensure you have Python 3.9 or newer installed. Make the script executable and run:

```bash
chmod +x code-extensions.py
./code-extensions --help
```

No external Python dependencies are required (uses standard library modules like `urllib`, `subprocess`, and `argparse`). The config file is read with the standard library's `tomllib` on Python 3.11+, falling back to `tomli` or `toml` when either is installed, and to a built-in parser otherwise.

---

## Usage

```bash
code-extensions <command> [options]
```

### Commands

* `install`: Install extension(s) by ID (e.g. `publisher.name` or `publisher.name@version`).
* `update` (or `upgrade`): Check, download, and install updates for installed extensions.
* `list` (or `ls`): List installed extensions with optional filtering and update checks.
* `search`: Search the VS Code Marketplace / Open VSX for extensions.
* `info` (or `show`): Display detailed metadata and local installation status for an extension.
* `clean`: Purge cached API response JSON files and temporary VSIX downloads.
* `config`: View or modify global settings and extension-specific rules in `config.toml`.
* `remove`: Remove installed extension(s) by ID or interactively select extensions to remove.

### 1. `install` Command

```bash
code-extensions install [extension-id...] [options]
```

* Installs specified extension(s). Supports explicit version parameter (e.g., `ms-python.python@2024.1.0`).
* Supports batch importing extensions from a text file using `-f` / `--file`.
* Respects `min-release-age` policy. If the latest release is too fresh, automatically selects the latest age-eligible version, or warns before proceeding.

**Options**:
* `-f`, `--file <path>`: Text file containing extension IDs to install (one per line).
* `-p`, `--include-prerelease`: Allow pre-release versions.
* `-V`, `--no-code-version-check`: Disable VS Code host compatibility check.
* `-d`, `--download-dir <path>`: Directory for downloading `.vsix` files.
* `-y`, `--yes`: Non-interactive mode. A version pinned with `@` is installed even when it is held back by the release-age policy; an unpinned extension whose only release is held back is skipped rather than prompted for.
* `-a`, `--min-release-age <age>`: Minimum release age threshold (e.g. `24h`, `3d`, `0`).
* `--force`: Force re-installation even if the target version is already installed.

### 2. `update` Command

```bash
code-extensions update [extensions...] [options]
```

* Scans installed extensions, queries marketplace for updates, and launches interactive TUI selection (or auto-installs if `-y`).
* Without a terminal (piped output, cron, CI) the available updates are only reported; pass `-y` to install them.
* Optionally limit the check to one or more extensions by passing full IDs (e.g. `ms-python.python`) or partial names (e.g. `python`, resolved against installed extensions like `info`). Without arguments, all installed extensions are checked.

**Options**:
* `-p`, `--include-prerelease`: Include pre-release versions in update check.
* `-n`, `--dry-run`: Perform a dry run (show available updates without downloading or installing).
* `-V`, `--no-code-version-check`: Disable VS Code host compatibility check.
* `-d`, `--download-dir <path>`: Download directory for `.vsix` files.
* `-y`, `--yes`: Non-interactive auto-update.
* `-a`, `--min-release-age <age>`: Minimum release age threshold (e.g. `24h`, `3d`, `0`).

### 3. `list` Command

```bash
code-extensions list [query] [options]
```

* Lists installed extensions, optionally filtering by a search query string.

**Options**:
* `-q`, `--quiet`: Output raw extension IDs only (one per line, ideal for scripting).
* `-u`, `--outdated`: List only extensions that have updates available.
* `-p`, `--include-prerelease`: Count pre-release versions as updates (with `--outdated`).
* `-V`, `--no-code-version-check`: Disable the VS Code version compatibility check (with `--outdated`).
* `-a`, `--min-release-age <age>`: Minimum release age threshold (with `--outdated`).

### 4. `search` Command

```bash
code-extensions search <query> [options]
```

* Searches the VS Code Marketplace or Open VSX Registry for extensions.
* Displays ID, version, display name, and short description. Launches an interactive TUI browser to inspect info or install search results directly.

**Options**:
* `-n`, `--max-results <N>`: Maximum number of search results (default: `15`).
* `-q`, `--quiet`: Output raw extension IDs only (one per line, ideal for piping).
* `-p`, `--include-prerelease`: Include pre-release versions.
* `-V`, `--no-code-version-check`: Disable VS Code host compatibility check.
* `-a`, `--min-release-age <age>`: Minimum release age threshold.

### 5. `info` / `show` Command

```bash
code-extensions info <extension-id>
```

* Displays rich metadata for an extension (publisher, latest version, pricing, repository links, description, eligible version, and local installation status).

### 6. `clean` Command

```bash
code-extensions clean
```

* Purges cached API response JSON files (`~/.cache/code-extensions/`) and removes temporary downloaded `.vsix` files.

### 7. `config` Command

```bash
code-extensions config [list|get|set|unset] [key] [value]
```

* View, set, or unset configuration settings and per-extension rules directly in `config.toml`.

**Examples**:
```bash
code-extensions config list
code-extensions config set min_release_age 3d
code-extensions config set code_binary codium
code-extensions config set charliermarsh.ruff.min_release_age 12h
code-extensions config set ms-python.python.ignore true
code-extensions config get min_release_age
code-extensions config unset charliermarsh.ruff.min_release_age
```

### 8. `completion` Command

```bash
code-extensions completion <shell>
```

* Generates tab completion scripts for **bash**, **fish**, **powershell**, or **zsh**.

**Usage**:
```bash
# Fish shell (add to ~/.config/fish/config.fish)
code-extensions completion fish | source

# Bash shell (add to ~/.bashrc)
eval "$(code-extensions completion bash)"

# Zsh shell (add to ~/.zshrc)
eval "$(code-extensions completion zsh)"

# PowerShell (add to $PROFILE)
code-extensions completion powershell | Out-String | Invoke-Expression
```

### 9. `remove` Command

```bash
code-extensions remove [extension-id...] [options]
```

* Removes specified extension(s). Supports aliases `uninstall` and `rm`.
* If no extension IDs are passed, launches an interactive TUI listing all installed extensions to select which ones to remove.

**Options**:
* `-y`, `--yes`: Skip confirmation prompt.

---

## Configuration File

Set defaults and per-extension rules in `~/.config/code-extensions/config.toml` (or `$XDG_CONFIG_HOME/code-extensions/config.toml` when that variable is set). Set `CODE_EXTENSIONS_CONFIG=/path/to/config.toml` to load a different file; a `config.toml` in the current working directory is *not* picked up automatically, because the file can name the executable to run and the gallery to download from. Because the file can hold an access token, it is written owner-only (`0600`, in a `0700` directory) on Unix-like systems; on Windows it inherits the ACLs of its parent directory instead:

```toml
min-release-age = "12h"        # Default release age buffer (e.g., 24h, 3d, 0)
include-prerelease = false
no-code-version-check = false
code-binary = "code"           # Path to executable or fork (e.g., "codium")
download-dir = "~/Downloads"
yes = false
open-vsx = false

[extensions."ms-python.python"]
ignore = true                  # Ignore during update checks

[extensions."golang.go"]
min-release-age = "3d"         # Require updates/installs for this extension to be at least 3 days old
skip-versions = ["0.39.0"]
```

Settings are resolved in one order everywhere: a flag passed on the command line wins over a per-extension rule, which wins over the global setting, which falls back to the built-in default. So `-a 0` or `-p` always applies, whatever the config file says about that extension.

---

## Examples

```bash
# Search marketplace for extensions
./code-extensions search "python debugger"

# Pipe top search result directly into install
./code-extensions search "ruff" -q -n 1 | xargs ./code-extensions install -y

# Install extensions
./code-extensions install ms-python.python golang.go

# Install specific version respecting 12h release age
./code-extensions install ms-python.python@2024.1.0 -a 12h

# List installed extensions matching "python"
./code-extensions list python

# Export list of installed extension IDs to a file
./code-extensions list -q > extensions.txt

# List extensions that have updates available
./code-extensions list --outdated

# Interactive update check
./code-extensions update

# Auto-upgrade all extensions non-interactively
./code-extensions update -y

# Update a single extension (full ID or partial name)
./code-extensions update ms-python.python
./code-extensions update python -y

# Remove extension directly
./code-extensions remove ms-python.python

# Interactive removal menu
./code-extensions remove
```

---

## License

This project is licensed under the GNU General Public License v3.0 or later (GPL-3.0-or-later) - see the [LICENSE](LICENSE) file for details.
