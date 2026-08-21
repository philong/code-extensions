#!/usr/bin/env python3
#
# Copyright (C) 2026 Phi-Long Do
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <https://www.gnu.org/licenses/>.

import argparse
import contextlib
import datetime
import hashlib
import http.client
import json
import os
import platform
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import time
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
import zlib
from collections import namedtuple
from functools import lru_cache

if sys.version_info < (3, 11):
    # 3.11 is the minimum supported interpreter: it is the release that
    # added both tomllib and the datetime.UTC alias used below. Check it
    # before those uses so an older interpreter exits up front with an
    # actionable message instead of dying with a less useful error.
    sys.exit(
        f"code-extensions requires Python 3.11 or newer; "
        f"this interpreter is {platform.python_version()}."
    )

import tomllib

try:
    import select
    import termios
    import tty

    HAS_TTY = True
except ImportError:
    HAS_TTY = False

# Upper bound on an expanded .vsix, so a hostile or misconfigured gallery cannot
# fill the disk (the largest extensions on the Marketplace are ~200MB).
MAX_VSIX_BYTES = 1024 * 1024 * 1024

# Every way a package download can fail: urllib's URLError/HTTPError and any
# failure writing the .vsix to disk (OSError), a truncated or otherwise
# malformed HTTP response (HTTPException), a corrupt compressed body
# (zlib.error), and the size cap above (ValueError).
DOWNLOAD_ERRORS = (OSError, http.client.HTTPException, zlib.error, ValueError)

ANSI_ESCAPE = re.compile(r"\x1b\[[0-9;]*[a-zA-Z]")

DEFAULT_SERVICE_URL = "https://marketplace.visualstudio.com/_apis/public/gallery"
OPEN_VSX_SERVICE_URL = "https://open-vsx.org/vscode/gallery"
OPEN_VSX_HOST = "open-vsx.org"
# Microsoft's gallery and the CDN hosts it serves packages from. An Open VSX
# token is meaningless to them, so it is never worth the risk of sending it.
MARKETPLACE_HOSTS = ("visualstudio.com", "vsassets.io")


def url_host(url):
    try:
        return (urllib.parse.urlparse(url).hostname or "").lower()
    except ValueError:
        return ""


class _AuthStrippingRedirectHandler(urllib.request.HTTPRedirectHandler):
    """Drop the Authorization header when a redirect crosses hosts.

    urllib copies every header except Content-* onto the redirected request, so
    without this the access token would be handed to whatever CDN host the
    gallery redirects downloads to (*.vsassets.io, blob storage, GitHub, ...).
    """

    def redirect_request(self, req, fp, code, msg, headers, newurl):
        new_req = super().redirect_request(req, fp, code, msg, headers, newurl)
        if new_req is None:
            return None
        if url_host(req.full_url) != url_host(new_req.full_url):
            # Request.add_header() capitalizes header names.
            new_req.headers.pop("Authorization", None)
            new_req.unredirected_hdrs.pop("Authorization", None)
        return new_req


_url_opener = urllib.request.build_opener(_AuthStrippingRedirectHandler)


class _ColorsMeta(type):
    """Resolve public color codes through the class's `_enabled` flag."""

    def __getattribute__(cls, name):
        value = super().__getattribute__(name)
        if (
            not name.startswith("_")
            and isinstance(value, str)
            and not super().__getattribute__("_enabled")
        ):
            return ""
        return value


class Colors(metaclass=_ColorsMeta):
    # The codes below stay intact; whether they render is decided per access
    # by _enabled, so every reader agrees no matter when colors were
    # disabled - and disabling is reversible, which rewriting the attributes
    # was not.
    _enabled = True
    BLUE = "\033[94m"
    CYAN = "\033[96m"
    GREEN = "\033[92m"
    YELLOW = "\033[93m"
    RED = "\033[91m"
    ENDC = "\033[0m"
    BOLD = "\033[1m"


def _disable_colors():
    Colors._enabled = False


def _enable_windows_vt():
    """Enable ANSI escape processing on the Windows console. Returns success."""
    try:
        import ctypes

        kernel32 = ctypes.windll.kernel32
        handle = kernel32.GetStdHandle(-11)  # STD_OUTPUT_HANDLE
        mode = ctypes.c_uint32()
        if not kernel32.GetConsoleMode(handle, ctypes.byref(mode)):
            return False
        ENABLE_VIRTUAL_TERMINAL_PROCESSING = 0x0004
        return bool(
            kernel32.SetConsoleMode(
                handle, mode.value | ENABLE_VIRTUAL_TERMINAL_PROCESSING
            )
        )
    # No windll off Windows (AttributeError), and the console calls raise
    # OSError when stdout is not attached to a real console.
    except (ImportError, AttributeError, OSError):
        return False


class _AnsiStrippingStream:
    """Write-through wrapper that removes escape sequences."""

    def __init__(self, stream):
        self._stream = stream

    def write(self, text):
        return self._stream.write(ANSI_ESCAPE.sub("", text))

    def writelines(self, lines):
        # Must not fall through to __getattr__, which would reach the wrapped
        # stream directly and let escape sequences past the filter.
        for line in lines:
            self.write(line)

    def __getattr__(self, name):
        return getattr(self._stream, name)


def enable_colors():
    if not sys.stdout.isatty():
        _disable_colors()
        return
    if os.name == "nt" and not _enable_windows_vt():
        # Legacy console without VT support would print raw escape codes.
        _disable_colors()
        return
    # Colors are decided by stdout, but warnings and errors go to stderr, which
    # may be redirected on its own (`cmd 2>log`). Strip the codes there.
    if not sys.stderr.isatty():
        sys.stderr = _AnsiStrippingStream(sys.stderr)


def get_local_target_platform():
    system = platform.system().lower()
    machine = platform.machine().lower()

    if system == "linux":
        if "arm" in machine or "aarch64" in machine:
            return "linux-arm64" if "64" in machine else "linux-armhf"
        return "linux-x64"
    elif system == "darwin":
        return (
            "darwin-arm64"
            if ("arm" in machine or "aarch64" in machine)
            else "darwin-x64"
        )
    elif system == "windows":
        return (
            "win32-arm64" if ("arm" in machine or "aarch64" in machine) else "win32-x64"
        )
    return "universal"


def _comparable_version_parts(parts):
    return tuple((0, x) if isinstance(x, int) else (1, str(x)) for x in parts)


@lru_cache(maxsize=4096)
def parse_version(v_str):
    parts = v_str.split("-")
    main_parts = parts[0].split(".")

    parsed_ints = []
    for p in main_parts:
        try:
            parsed_ints.append(int(p))
        except ValueError:
            digits = re.findall(r"\d+", p)
            if digits:
                parsed_ints.append(int("".join(digits)))
            else:
                parsed_ints.append(p)

    while len(parsed_ints) < 3:
        parsed_ints.append(0)

    is_release = len(parts) == 1

    prerelease_parts = ()
    if not is_release:
        raw_pre = parts[1].split(".")
        pre_parsed = []
        for x in raw_pre:
            try:
                pre_parsed.append(int(x))
            except ValueError:
                pre_parsed.append(x)
        prerelease_parts = tuple(pre_parsed)

    return (
        _comparable_version_parts(parsed_ints),
        is_release,
        _comparable_version_parts(prerelease_parts),
    )


def parse_code_binary(code_binary):
    if isinstance(code_binary, (list, tuple)):
        tokens = [str(x) for x in code_binary]
    elif isinstance(code_binary, str):
        try:
            tokens = shlex.split(code_binary)
        except ValueError:
            # Unbalanced quote: fall back to the raw string as a single token.
            tokens = [code_binary]
    elif code_binary:
        tokens = [str(code_binary)]
    else:
        tokens = ["code"]

    if not tokens:
        tokens = ["code"]

    executable = os.path.expanduser(tokens[0])
    resolved_exec = shutil.which(executable) or executable
    return [resolved_exec, *tokens[1:]]


def run_code_cmd(args, retries=3, delay=1.0):
    # On Windows the `code` CLI is a batch script (code.cmd); CreateProcess
    # cannot launch .cmd/.bat directly, so route those through the shell, which
    # CPython wraps as `cmd /c "<quoted args>"`.
    #
    # The CLI can also fail sporadically and succeed on retry (a lock held by
    # another instance, first-launch setup), so keep retrying - but back off
    # exponentially: a fast first retry catches the common flake, and a
    # genuinely broken binary is not hammered at a fixed interval.
    use_shell = os.name == "nt" and str(args[0]).lower().endswith((".cmd", ".bat"))
    for attempt in range(retries + 1):
        try:
            return subprocess.run(
                args, capture_output=True, text=True, check=True, shell=use_shell
            )
        except subprocess.CalledProcessError as e:
            if attempt < retries:
                wait = delay * (2**attempt)
                cmd_str = " ".join(args)
                print(
                    f"{Colors.YELLOW}Warning: Command '{cmd_str}' failed with exit code {e.returncode}. Retrying in {wait:g}s... (attempt {attempt + 1}/{retries}){Colors.ENDC}",
                    file=sys.stderr,
                )
                time.sleep(wait)
                continue
            raise


def query_installed_extensions(code_binary="code"):
    """Return (mapping of extension id to version, error message or None).

    An empty mapping is ambiguous - no extensions installed, or no usable 'code'
    binary - so callers that need to tell those apart get the error text too.
    """
    binary_cmd = parse_code_binary(code_binary)
    full_cmd = [*binary_cmd, "--list-extensions", "--show-versions"]
    try:
        result = run_code_cmd(full_cmd)
        output = result.stdout
    # A missing or unexecutable binary raises OSError; a non-zero exit raises
    # CalledProcessError, which SubprocessError covers.
    except (OSError, subprocess.SubprocessError) as e:
        return {}, f"Error running '{' '.join(full_cmd)}': {e}"

    extensions = {}
    for line in output.strip().splitlines():
        line = line.strip()
        if not line or "@" not in line:
            continue
        ext_id, version = line.rsplit("@", 1)
        extensions[ext_id.lower()] = version

    return extensions, None


def get_installed_extensions(code_binary="code", ignore_errors=False):
    extensions, error = query_installed_extensions(code_binary)
    if error and not ignore_errors:
        print(f"{Colors.RED}{error}{Colors.ENDC}", file=sys.stderr)
        sys.exit(1)
    return extensions


def is_prerelease(version_obj):
    properties = version_obj.get("properties", [])
    for p in properties:
        if (
            p.get("key") == "Microsoft.VisualStudio.Code.PreRelease"
            and p.get("value") == "true"
        ):
            return True
    return False


def get_vscode_version(code_binary="code"):
    binary_cmd = parse_code_binary(code_binary)
    full_cmd = [*binary_cmd, "--version"]
    try:
        result = run_code_cmd(full_cmd)
    except (OSError, subprocess.SubprocessError):
        # The caller treats an unknown version as 'skip the engine check'.
        return None
    lines = result.stdout.strip().splitlines()
    return lines[0].strip() if lines else None


def semver_parts(v_str):
    cleaned = re.sub(r"^[^0-9]+", "", v_str)
    main_part = cleaned.split("-")[0]
    parts = main_part.split(".")
    try:
        major = int(parts[0]) if len(parts) > 0 else 0
        minor = int(parts[1]) if len(parts) > 1 else 0
        patch = int(parts[2]) if len(parts) > 2 else 0
        return major, minor, patch
    except ValueError:
        return 0, 0, 0


def expand_x_range(version_str):
    """Expand a wildcard range into [lower, upper) bounds.

    '1.80.x' -> ('1.80.0', '1.81.0'), '1.x' -> ('1.0.0', '2.0.0'),
    'x' -> ('0.0.0', None) meaning unbounded. Returns None when the version
    carries no wildcard, or when it is too odd to interpret.
    """
    core = version_str.split("-", 1)[0].split("+", 1)[0].strip()
    if not core:
        return None
    components = [c.strip() for c in core.split(".")]
    fixed = []
    for component in components:
        if component in ("x", "X", "*"):
            break
        fixed.append(component)
    if len(fixed) == len(components):
        return None
    try:
        numbers = [int(c) for c in fixed]
    except ValueError:
        return None
    if not numbers:
        return ("0.0.0", None)
    if len(numbers) == 1:
        return (f"{numbers[0]}.0.0", f"{numbers[0] + 1}.0.0")
    if len(numbers) == 2:
        return (f"{numbers[0]}.{numbers[1]}.0", f"{numbers[0]}.{numbers[1] + 1}.0")
    return None


@lru_cache(maxsize=4096)
def is_engine_compatible(vscode_version_str, engine_constraint):
    if not vscode_version_str or not engine_constraint:
        return True
    # VS Code reports Insiders and other pre-release builds as e.g.
    # '1.86.0-insider'. Semver ranks that below the 1.86.0 release, so every
    # extension requiring ^1.86.0 would look incompatible. VS Code itself treats
    # such a build as satisfying the corresponding release constraint.
    vscode_version_str = vscode_version_str.split("-", 1)[0]
    constraint_str = engine_constraint.strip()
    # An operator may be spaced from its version ('>= 1.80.0'). Fold it onto
    # the version so the whitespace split below cannot tear the comparator off
    # and evaluate it as its own token.
    constraint_str = re.sub(r"([><=~^]+)\s+", r"\1", constraint_str)
    if constraint_str == "*" or constraint_str == "":
        return True
    if "||" in constraint_str:
        return any(
            is_engine_compatible(vscode_version_str, g)
            for g in constraint_str.split("||")
        )
    parts = [p.strip() for p in re.split(r"\s+", constraint_str) if p.strip()]
    # Hyphen range: 'A - B' means >=A <=B. Only the spaced spelling is treated as
    # a range, since 'A-B' unspaced is a pre-release version.
    if len(parts) == 3 and parts[1] == "-":
        return is_engine_compatible(
            vscode_version_str, f">={parts[0]}"
        ) and is_engine_compatible(vscode_version_str, f"<={parts[2]}")
    if len(parts) > 1:
        return all(is_engine_compatible(vscode_version_str, p) for p in parts)
    single_constraint = parts[0]
    match = re.match(r"^([>=<~^]+)?(.*)$", single_constraint)
    if not match:
        return True
    op, version_str = match.groups()

    # Wildcard ranges ('1.80.x', '1.*'). Without this the wildcard component
    # parses as a string that sorts above every integer, which inverts the
    # comparison: '1.80.x' rejected 1.80.0 and accepted 1.81.0.
    x_range = expand_x_range(version_str)
    # A bare partial version ('1', '1.26') is an x-range under npm semantics:
    # '1.26' means '>=1.26.0 <1.27.0' and '1' means '>=1.0.0 <2.0.0'. A partial
    # with an operator is zero-filled instead ('>=1.26' is '>=1.26.0'), which
    # parse_version already does, so only the bare form needs expanding - and
    # only when it carries no pre-release or build, which would make it a
    # specific version rather than a range.
    if x_range is None and not op:
        core = version_str.split("-", 1)[0].split("+", 1)[0]
        parts = core.split(".")
        if (
            version_str == core
            and len(parts) in (1, 2)
            and all(p.isdigit() for p in parts)
        ):
            if len(parts) == 1:
                x_range = (f"{parts[0]}.0.0", f"{int(parts[0]) + 1}.0.0")
            else:
                x_range = (
                    f"{parts[0]}.{parts[1]}.0",
                    f"{parts[0]}.{int(parts[1]) + 1}.0",
                )
    if x_range is not None:
        lower, upper = x_range
        if upper is None:
            # A wildcard with nothing fixed in front of it ('x', '*') bounds
            # nothing, whichever comparator precedes it. Semver reads '>x' and
            # '<x' as matching no version at all, but an engine spelled that way
            # is a typo, and discarding every version is the worse guess.
            return True
        if op == "^":
            # A caret widens the wildcard's ceiling to the next major, so
            # '^1.80.x' means '>=1.80.0 <2.0.0' rather than the '<1.81.0' the
            # wildcard alone would give. Below 1.0.0 the caret pins the leading
            # non-zero component, which is the bound the wildcard already
            # carries ('^0.80.x' stays '<0.81.0').
            major = semver_parts(lower)[0]
            if major > 0:
                upper = f"{major + 1}.0.0"
        if op in (None, "", "=", "==", "^", "~"):
            return is_engine_compatible(
                vscode_version_str, f">={lower}"
            ) and is_engine_compatible(vscode_version_str, f"<{upper}")
        # An explicit comparator applies to the range as a whole, so it collapses
        # onto whichever bound it faces: '>=1.80.x' and '<1.80.x' clamp at
        # 1.80.0, while '<=1.80.x' and '>1.80.x' take in the entire 1.80 line.
        if op == "<=":
            return is_engine_compatible(vscode_version_str, f"<{upper}")
        if op == ">":
            return is_engine_compatible(vscode_version_str, f">={upper}")
        version_str = lower

    # A wildcard expand_x_range did not handle (e.g. '1.2.3.x'): parse_version
    # would rank 'x' above every integer and invert the comparison, so apply
    # the fail-open policy for unparseable constraints instead. Only the core
    # version counts: '1.2.3-alpha.x' is a pre-release identifier, not a
    # wildcard, and must fall through to the normal comparison.
    wildcard_core = version_str.split("-", 1)[0].split("+", 1)[0]
    if any(part in ("x", "X", "*") for part in wildcard_core.split(".")):
        return True
    if not op:
        # A bare version ('1.86.0') means exactly that version under semver and
        # npm semantics, not a lower bound, so map it onto the '=' handling.
        op = "="
    parsed_vscode = parse_version(vscode_version_str)
    parsed_constraint = parse_version(version_str)
    if op in ("=", "=="):
        return parsed_vscode[0] == parsed_constraint[0]
    if op == ">=":
        return parsed_vscode >= parsed_constraint
    elif op == ">":
        return parsed_vscode > parsed_constraint
    elif op == "<=":
        return parsed_vscode <= parsed_constraint
    elif op == "<":
        return parsed_vscode < parsed_constraint
    elif op == "~":
        if parsed_vscode < parsed_constraint:
            return False
        major, minor, patch = semver_parts(version_str)
        next_minor_ver = f"{major}.{minor + 1}.0"
        return parsed_vscode < parse_version(next_minor_ver)
    elif op == "^":
        if parsed_vscode < parsed_constraint:
            return False
        major, minor, patch = semver_parts(version_str)
        if major > 0:
            return parsed_vscode < parse_version(f"{major + 1}.0.0")
        elif minor > 0:
            return parsed_vscode < parse_version(f"0.{minor + 1}.0")
        else:
            return parsed_vscode < parse_version(f"0.0.{patch + 1}")
    return True


def filter_versions(
    versions,
    target_platform,
    vscode_version=None,
    include_prerelease=False,
    skip_versions=(),
    required_version=None,
    newer_than=None,
):
    """Select the gallery versions installable on this host, newest first.

    Shared by install, update, search and info so they cannot drift apart on
    which versions they consider. `required_version` pins an exact version,
    `newer_than` drops every version at or below an installed one.

    Candidates are ordered before being filtered, which is what makes stopping at
    the first version below `newer_than` correct: it holds whatever order the
    gallery used, and --service-url accepts any gallery. Both public galleries do
    order by version descending rather than by publication date -- a maintenance
    release for an older line sits at its numeric position, not first -- but
    nothing here depends on that. Sorting up front is not a cost either: it runs
    the version parser in one pass instead of an interpreted loop, and the early
    stop then skips the rest entirely.

    The sort is stable, so several builds of one version (the per-platform
    variants) keep the order the gallery listed them in.
    """
    ordered = sorted(
        (v for v in versions if v.get("version")),
        key=lambda v: parse_version(v["version"]),
        reverse=True,
    )
    parsed_floor = parse_version(newer_than) if newer_than else None

    selected = []
    for ver_obj in ordered:
        version_str = ver_obj["version"]
        if parsed_floor is not None and parse_version(version_str) <= parsed_floor:
            break
        if required_version is not None and version_str != required_version:
            continue
        if version_str in skip_versions:
            continue
        if not include_prerelease and is_prerelease(ver_obj):
            continue
        if vscode_version:
            engine_constraint = get_engine_constraint(ver_obj)
            if engine_constraint and not is_engine_compatible(
                vscode_version, engine_constraint
            ):
                continue
        ver_platform = ver_obj.get("targetPlatform")
        if ver_platform is None or ver_platform.lower() in (
            "universal",
            target_platform.lower(),
        ):
            selected.append(ver_obj)

    return selected


def get_engine_constraint(version_obj):
    properties = version_obj.get("properties", [])
    for p in properties:
        if p.get("key") == "Microsoft.VisualStudio.Code.Engine":
            return p.get("value")
    return None


def parse_age_threshold(age_str):
    if not age_str:
        return datetime.timedelta(0)
    age_str = str(age_str).lower().strip()
    if age_str in ("0", "0h", "0d", "0m"):
        return datetime.timedelta(0)

    match = re.match(r"^(\d+)([hdm])$", age_str)
    if not match:
        raise ValueError(
            f"Invalid age format: '{age_str}'. Expected format like '24h', '1d', '30m'."
        )
    value, unit = match.groups()
    value = int(value)
    if unit == "h":
        return datetime.timedelta(hours=value)
    elif unit == "d":
        return datetime.timedelta(days=value)
    elif unit == "m":
        return datetime.timedelta(minutes=value)
    return datetime.timedelta(0)


def released_long_enough(ver_obj, min_age):
    """Return True if the version passes the minimum-release-age gate.

    A version with no min_age, no lastUpdated, or an unparseable timestamp is
    treated as eligible (True); only a version that is verifiably too recent
    returns False.
    """
    if not min_age or min_age <= datetime.timedelta(0):
        return True
    last_updated = ver_obj.get("lastUpdated")
    if not last_updated:
        return True
    try:
        cleaned_ts = (
            last_updated[:-1] + "+00:00" if last_updated.endswith("Z") else last_updated
        )
        release_dt = datetime.datetime.fromisoformat(cleaned_ts)
        now = datetime.datetime.now(datetime.UTC)
        return now - release_dt >= min_age
    # An unparsable timestamp (ValueError), a non-string one (AttributeError,
    # TypeError), or a naive one compared against an aware now (TypeError) all
    # mean the age is unknown, which the gate treats as old enough.
    except (AttributeError, TypeError, ValueError):
        return True


CACHE_FILE_PREFIX = "vscode_ext_cache_"


def first_eligible_version(versions, min_age):
    """Newest version that satisfies the minimum-release-age gate, if any."""
    for ver_obj in versions:
        if released_long_enough(ver_obj, min_age):
            return ver_obj
    return None


def get_cache_dir():
    """Return the private cache directory, or None if it cannot be secured.

    Falling back to the shared temp directory would put cache files under
    world-writable, fully predictable paths, letting a local attacker pre-create
    one and dictate which download URL the tool trusts. Losing the cache is the
    lesser evil.
    """
    base = os.environ.get("XDG_CACHE_HOME") or os.path.expanduser("~/.cache")
    cache_dir = os.path.join(base, "code-extensions")
    try:
        os.makedirs(cache_dir, mode=0o700, exist_ok=True)
    except OSError:
        return None
    # makedirs ignores mode for an existing directory.
    restrict_to_owner(cache_dir, 0o700)
    return cache_dir


def is_cache_file(filename):
    # .tmp covers a partial write left behind by a killed process; the reader
    # only ever opens the final name, so collecting them is safe.
    return filename.startswith(CACHE_FILE_PREFIX) and filename.endswith(
        (".json", ".tmp")
    )


def is_cache_temp_file(filename):
    """Whether the name is a cache entry mid-write rather than a finished one.

    A .tmp still belonging to a live process must not be removed: its os.replace
    would then fail and that run would lose the entry it just fetched.
    """
    return is_cache_file(filename) and filename.endswith(".tmp")


def write_cache_atomically(cache_file, payload):
    """Write a cache entry via a temporary file and a rename.

    Writing in place leaves a half-written entry behind if the process is
    interrupted, or if two runs cache the same query at once. A reader recovers
    from that by refetching, but it also wastes the entry for a full hour.
    """
    tmp_path = f"{cache_file}.{os.getpid()}.tmp"
    replaced = False
    try:
        with open(tmp_path, "w", encoding="utf-8") as f:
            json.dump(payload, f)
        os.replace(tmp_path, cache_file)
        replaced = True
    except OSError:
        pass
    finally:
        if not replaced:
            with contextlib.suppress(OSError):
                os.remove(tmp_path)


def cleanup_stale_cache():
    cache_dir = get_cache_dir()
    if not cache_dir:
        return
    try:
        now = time.time()
        for filename in os.listdir(cache_dir):
            if is_cache_file(filename):
                filepath = os.path.join(cache_dir, filename)
                try:
                    if now - os.path.getmtime(filepath) > 3600:
                        os.remove(filepath)
                except OSError:
                    pass
    except OSError:
        pass


_TOML_ESCAPES = {
    '"': '"',
    "\\": "\\",
    "/": "/",
    "b": "\b",
    "f": "\f",
    "n": "\n",
    "r": "\r",
    "t": "\t",
}


def unescape_toml_basic(text):
    out = []
    i = 0
    while i < len(text):
        char = text[i]
        if char != "\\" or i + 1 >= len(text):
            out.append(char)
            i += 1
            continue
        following = text[i + 1]
        if following in _TOML_ESCAPES:
            out.append(_TOML_ESCAPES[following])
            i += 2
        elif following in ("u", "U"):
            width = 4 if following == "u" else 8
            digits = text[i + 2 : i + 2 + width]
            # A short slice means the escape was truncated by the end of the
            # string; without the length check '\u12' would decode as '\x12'
            # instead of being kept as written. Lone surrogates are not
            # characters either, and would fail later on encode.
            code_point = None
            if len(digits) == width:
                try:
                    code_point = int(digits, 16)
                except ValueError:
                    code_point = None
            if code_point is None or 0xD800 <= code_point <= 0xDFFF:
                out.append(char)
                i += 1
            else:
                out.append(chr(code_point))
                i += 2 + width
        else:
            out.append(char)
            i += 1
    return "".join(out)


def unquote_toml_value(text):
    """Strip one layer of TOML quoting, honouring escapes in basic strings.

    Basic ("...") strings process escapes; literal ('...') strings do not.
    """
    text = text.strip()
    if len(text) >= 2 and text[0] == text[-1]:
        if text[0] == '"':
            return unescape_toml_basic(text[1:-1])
        if text[0] == "'":
            return text[1:-1]
    return text


def split_comment(line):
    """Split a line into its code and its trailing '#' comment.

    A '#' inside a quoted value is part of the value, not a comment.
    """
    in_quote = None
    escaped = False
    for i, char in enumerate(line):
        if escaped:
            escaped = False
            continue
        # Only basic ("...") strings process escapes; inside a literal string a
        # backslash is just a backslash.
        if char == "\\" and in_quote != "'":
            escaped = True
            continue
        if char in ('"', "'"):
            if in_quote == char:
                in_quote = None
            elif in_quote is None:
                in_quote = char
        elif char == "#" and in_quote is None:
            return line[:i], line[i:]
    return line, ""


def strip_comment(line):
    return split_comment(line)[0].strip()


GLOBAL_CONFIG_SCHEMA = [
    (
        "min_release_age",
        str,
        "Minimum release age threshold (e.g. '24h', '3d', '0')",
        "24h",
    ),
    (
        "code_binary",
        str,
        "VS Code executable path or command (e.g. 'code', 'codium')",
        "code",
    ),
    (
        "include_prerelease",
        bool,
        "Allow pre-release versions by default (true/false)",
        "false",
    ),
    (
        "no_code_version_check",
        bool,
        "Disable engine version check (true/false)",
        "false",
    ),
    (
        "download_dir",
        str,
        "Custom directory path for downloaded .vsix files",
        "system temp",
    ),
    ("open_vsx", bool, "Use Open VSX registry by default (true/false)", "false"),
    (
        "open_vsx_token",
        str,
        "Personal access token for Open VSX Registry authentication",
        "none",
    ),
    (
        "service_url",
        str,
        "Custom Extension Gallery API endpoint URL",
        "Marketplace API",
    ),
    ("yes", bool, "Non-interactive mode by default (true/false)", "false"),
]

EXT_CONFIG_SCHEMA = [
    (
        "min_release_age",
        str,
        "Per-extension minimum release age override (e.g. '6h', '0')",
    ),
    ("ignore", bool, "Exclude extension from automatic updates (true/false)"),
    (
        "include_prerelease",
        bool,
        "Allow pre-release versions for this extension (true/false)",
    ),
    ("skip_versions", list, "List of version strings to skip (e.g. ['1.2.3'])"),
]

CONFIG_OPTION_TYPES = {entry[0]: entry[1] for entry in GLOBAL_CONFIG_SCHEMA}
EXT_OPTION_TYPES = {entry[0]: entry[1] for entry in EXT_CONFIG_SCHEMA}
EXT_OPTION_KEYS = frozenset(EXT_OPTION_TYPES)


def coerce_config_value(val, expected_type):
    if expected_type is bool:
        if isinstance(val, bool):
            return val
        if isinstance(val, str) and val.strip().lower() in ("true", "false"):
            return val.strip().lower() == "true"
        raise ValueError(f"expected true or false, got {val!r}")
    if expected_type is list:
        if isinstance(val, bool):
            raise ValueError(f"expected a list of values, got {val!r}")
        if isinstance(val, list):
            return [str(v) for v in val]
        if isinstance(val, str):
            items = [p for p in re.split(r"[,\s]+", val.strip()) if p]
            if not items:
                raise ValueError("expected a list of values, got an empty value")
            return items
        return [str(val)]
    if isinstance(val, str):
        # An empty string is never a usable setting: as a download-dir it means
        # the working directory, as a code-binary or service-url it means
        # nothing at all. Refuse it here rather than acting on it later.
        if not val.strip():
            raise ValueError("expected a value, got an empty string")
        return val
    if isinstance(val, (int, float)) and not isinstance(val, bool):
        return str(val)
    raise ValueError(f"expected a string, got {val!r}")


def validate_config_value(display_key, norm_key, val, expected_type):
    """Coerce a value being written to the config, refusing to store junk.

    An unusable value used to be accepted here and only rejected on load, which
    left every later command either warning or exiting until the file was fixed
    by hand.
    """
    try:
        coerced = coerce_config_value(val, expected_type)
        if norm_key == "min_release_age":
            parse_age_threshold(coerced)
        return coerced
    except ValueError as e:
        print(
            f"{Colors.RED}Error: Invalid value for '{display_key}': {str(e).rstrip('.')}.{Colors.ENDC}",
            file=sys.stderr,
        )
        sys.exit(1)


def effective_ext_options(
    ext_cfg,
    include_prerelease,
    min_release_age,
    min_release_age_str=None,
    cli_include_prerelease_override=False,
    cli_min_release_age_override=False,
):
    """Merge a per-extension rule with the already-resolved global settings.

    Precedence is the same for every command: an explicitly passed CLI flag wins
    over a per-extension rule, which in turn wins over the global setting. An
    unparsable per-extension age leaves the global one in place; load_config has
    already warned about it.
    """
    ext_cfg = ext_cfg or {}
    eff_include_prerelease = include_prerelease
    if not cli_include_prerelease_override and "include_prerelease" in ext_cfg:
        eff_include_prerelease = ext_cfg["include_prerelease"]

    eff_min_age = min_release_age
    eff_min_age_str = min_release_age_str
    if not cli_min_release_age_override and "min_release_age" in ext_cfg:
        with contextlib.suppress(ValueError):
            eff_min_age = parse_age_threshold(ext_cfg["min_release_age"])
            eff_min_age_str = str(ext_cfg["min_release_age"])

    return eff_include_prerelease, eff_min_age, eff_min_age_str


def resolve_min_release_age(args_val, config):
    """Return (timedelta, source string) for the min-release-age setting."""
    age_str = resolve_option(args_val, config, "min_release_age", "24h")
    try:
        return parse_age_threshold(age_str), age_str
    except ValueError as e:
        print(f"{Colors.RED}Error: {e}{Colors.ENDC}", file=sys.stderr)
        sys.exit(1)


def parse_toml_text(text):
    """Parse TOML text, raising a ValueError on invalid input.

    tomllib ships with Python 3.11, so no fallback is needed. Kept as a
    single indirection so tests can substitute the parser.
    """
    return tomllib.loads(text)


def load_config():
    config_path = get_default_config_path()
    config = {"extensions": {}}
    if not os.path.exists(config_path):
        return config

    try:
        with open(config_path, encoding="utf-8") as f:
            parsed = parse_toml_text(f.read())
    # ValueError covers tomllib's decode errors (TOMLDecodeError derives
    # from it) and UnicodeDecodeError.
    except (OSError, ValueError) as e:
        print(
            f"{Colors.YELLOW}Warning: Failed to parse config file '{config_path}': {e}{Colors.ENDC}",
            file=sys.stderr,
        )
        return config

    ext_sections = {}
    if "extensions" in parsed and isinstance(parsed["extensions"], dict):
        ext_sections.update(parsed["extensions"])
    if "extension" in parsed and isinstance(parsed["extension"], dict):
        ext_sections.update(parsed["extension"])

    for ext_id, ext_data in ext_sections.items():
        if not isinstance(ext_data, dict):
            continue
        ext_id_lower = str(ext_id).strip().lower()
        norm_ext_cfg = {}

        for key, val in ext_data.items():
            norm_key = key.replace("-", "_")
            if norm_key not in EXT_OPTION_TYPES:
                continue
            try:
                norm_ext_cfg[norm_key] = coerce_config_value(
                    val, EXT_OPTION_TYPES[norm_key]
                )
            except ValueError:
                pass

        config["extensions"][ext_id_lower] = norm_ext_cfg

    for key, val in parsed.items():
        if key in ("extensions", "extension"):
            continue
        norm_key = key.replace("-", "_")
        if norm_key not in CONFIG_OPTION_TYPES:
            print(
                f"{Colors.YELLOW}Warning: Unknown option '{key}' in config file '{config_path}'.{Colors.ENDC}",
                file=sys.stderr,
            )
            continue
        try:
            config[norm_key] = coerce_config_value(val, CONFIG_OPTION_TYPES[norm_key])
        except ValueError as e:
            print(
                f"{Colors.YELLOW}Warning: Invalid value for '{key}' in config file '{config_path}': {e}. Ignoring.{Colors.ENDC}",
                file=sys.stderr,
            )

    return config


def resolve_option(args_val, config, key, default):
    if args_val is not None:
        return args_val
    val = config.get(key)
    if val is not None:
        return val
    return default


def resolve_service_url(args, config):
    open_vsx = resolve_option(
        getattr(args, "open_vsx", None), config, "open_vsx", False
    )
    if open_vsx:
        return OPEN_VSX_SERVICE_URL
    url = resolve_option(
        getattr(args, "service_url", None), config, "service_url", DEFAULT_SERVICE_URL
    ).rstrip("/")
    if url.lower().startswith("http://"):
        print(
            f"{Colors.YELLOW}Warning: Service URL '{url}' uses insecure HTTP; extension metadata and downloads could be tampered with in transit.{Colors.ENDC}",
            file=sys.stderr,
        )
    return url


def get_default_config_path():
    # Deliberately NOT ./config.toml: the config can set `code_binary` (which is
    # executed) and `service_url` (where VSIX files are fetched from), so picking
    # one up from the working directory would let any checked-out repository run
    # arbitrary commands. Use CODE_EXTENSIONS_CONFIG for an explicit override.
    override = os.environ.get("CODE_EXTENSIONS_CONFIG")
    if override:
        return os.path.abspath(os.path.expanduser(override))
    base = os.environ.get("XDG_CONFIG_HOME") or os.path.expanduser("~/.config")
    user_config_dir = os.path.join(base, "code-extensions")
    return os.path.join(user_config_dir, "config.toml")


def toml_string(value):
    escaped = (
        str(value)
        .replace("\\", "\\\\")
        .replace('"', '\\"')
        .replace("\n", "\\n")
        .replace("\r", "\\r")
        .replace("\t", "\\t")
    )
    return f'"{escaped}"'


def toml_key(key):
    key = str(key)
    return key if re.fullmatch(r"[A-Za-z0-9_-]+", key) else toml_string(key)


def toml_value(value):
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, (int, float)):
        return str(value)
    if isinstance(value, (list, tuple)):
        return "[" + ", ".join(toml_value(v) for v in value) + "]"
    return toml_string(value)


def dump_toml(data):
    lines = []
    for k in sorted(k for k in data if not isinstance(data[k], dict)):
        lines.append(f"{toml_key(k)} = {toml_value(data[k])}")

    for k in sorted(k for k in data if isinstance(data[k], dict) and data[k]):
        subdict = data[k]
        scalar_keys = sorted(sk for sk in subdict if not isinstance(subdict[sk], dict))
        sub_tables = sorted(sk for sk in subdict if isinstance(subdict[sk], dict))

        # Emit the parent header only when it carries keys of its own, so a
        # config holding nothing but per-extension rules has no empty
        # '[extensions]' table hanging above them.
        if scalar_keys or not sub_tables:
            if lines:
                lines.append("")
            lines.append(f"[{toml_key(k)}]")
            for sk in scalar_keys:
                lines.append(f"  {toml_key(sk)} = {toml_value(subdict[sk])}")

        for sk in sub_tables:
            if not subdict[sk]:
                continue
            if lines:
                lines.append("")
            lines.append(f"[{toml_key(k)}.{toml_key(sk)}]")
            for ik in sorted(subdict[sk]):
                lines.append(f"  {toml_key(ik)} = {toml_value(subdict[sk][ik])}")

    return "\n".join(lines).strip() + "\n"


def restrict_to_owner(path, mode):
    # POSIX modes are meaningless on Windows, where os.chmod only toggles the
    # read-only attribute; skip it there instead of risking a read-only config.
    if os.name == "nt":
        return
    with contextlib.suppress(OSError):
        os.chmod(path, mode)


def write_config_text(content, config_path):
    dir_path = os.path.dirname(config_path)
    if dir_path:
        existed = os.path.isdir(dir_path)
        os.makedirs(dir_path, mode=0o700, exist_ok=True)
        # makedirs ignores mode for a directory that already exists, so tighten
        # explicitly - but only our own config dir, never an arbitrary working
        # directory that happens to hold a config.toml.
        if not existed or os.path.basename(dir_path) == "code-extensions":
            restrict_to_owner(dir_path, 0o700)
    # The config can hold an API token, so restrict an existing file before
    # writing and create a new one already restricted, never widening either.
    restrict_to_owner(config_path, 0o600)
    fd = os.open(config_path, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
    with os.fdopen(fd, "w", encoding="utf-8") as f:
        f.write(content)


def save_config(config, config_path):
    write_config_text(dump_toml(config), config_path)


SECRET_CONFIG_KEYS = frozenset({"open_vsx_token"})


def redact_config_value(key, value):
    """Render a config value for display, masking anything secret.

    'config list' is the one command whose output tends to end up in a bug
    report or a screen share, so the token is shown only when asked for by name
    with 'config get'.
    """
    if key in SECRET_CONFIG_KEYS and value:
        return f"{Colors.YELLOW}<set, hidden>{Colors.ENDC}"
    return repr(value)


def config_table_path(target_type, ext_id):
    """The TOML table an edited key lives in: None for a global setting."""
    return None if target_type == "global" else ("extensions", ext_id.lower())


def normalize_toml_key(key):
    return str(key).strip().replace("-", "_")


def split_toml_table_header(line):
    """Split a '[table.sub]' header into its parts, or return None.

    Only the first dot separates the table from its subtable, matching how the
    config is read back: '[extensions."ms-python.python"]' names one extension,
    not a table nested three deep.
    """
    stripped = strip_comment(line)
    if not stripped.startswith("[") or not stripped.endswith("]"):
        return None
    inner = stripped[1:-1].strip()
    if not inner:
        return None

    parts = []
    current = []
    in_quote = None
    for char in inner:
        if char in ('"', "'"):
            if in_quote == char:
                in_quote = None
            elif in_quote is None:
                in_quote = char
            current.append(char)
        elif char == "." and in_quote is None:
            parts.append("".join(current))
            current = []
        else:
            current.append(char)
    parts.append("".join(current))

    names = [unquote_toml_value(p.strip()) for p in parts]
    top = names[0].strip()
    # load_config accepts both spellings, so an edit has to find either.
    if top == "extension":
        top = "extensions"
    if len(names) == 1:
        return (top,)
    return (top, ".".join(names[1:]).strip().lower())


def toml_line_key(line):
    """The key of a 'key = value' line, normalized, or None for any other line."""
    stripped = strip_comment(line)
    if not stripped or "=" not in stripped or stripped.startswith("["):
        return None
    return normalize_toml_key(unquote_toml_value(stripped.split("=", 1)[0].strip()))


def toml_value_is_complete(text):
    """Whether an array value opened on this text is already closed."""
    depth = 0
    in_quote = None
    escaped = False
    for char in text:
        if escaped:
            escaped = False
            continue
        if char == "\\" and in_quote != "'":
            escaped = True
            continue
        if char in ('"', "'"):
            if in_quote == char:
                in_quote = None
            elif in_quote is None:
                in_quote = char
        elif in_quote is None:
            if char == "[":
                depth += 1
            elif char == "]":
                depth -= 1
    return depth <= 0


def drop_empty_toml_table(lines, table):
    """Drop `table`'s header once an edit has left it without keys.

    Blank padding inside the emptied table goes with it; any comment there is
    kept, since it may say something the header did not.
    """
    result = []
    i = 0
    while i < len(lines):
        if split_toml_table_header(lines[i]) != table:
            result.append(lines[i])
            i += 1
            continue

        end = i + 1
        while end < len(lines) and split_toml_table_header(lines[end]) is None:
            end += 1
        body = lines[i + 1 : end]
        if any(toml_line_key(line) is not None for line in body):
            result.extend(lines[i:end])
        else:
            result.extend(line for line in body if line.strip())
        i = end
    return result


def edit_toml_text(text, table, key, value, delete=False):
    """Return `text` with one key set or removed, leaving every other byte alone.

    Rewriting the file from the parsed config would drop the user's comments,
    their key order, and anything this tool does not model, so an edit rewrites
    only the line it owns.
    """
    target_key = normalize_toml_key(key)
    new_line_body = f"{toml_key(key)} = {toml_value(value)}"

    lines = text.splitlines()
    out = []
    current = None
    insert_after = None  # index in `out` of the last line of the target table
    first_header = None  # index in `out` of the first table header
    key_indent = None  # indentation the target table's existing keys use
    table_key_indent = None  # indentation keys use elsewhere in the file
    found = False
    pending = None  # tail of a multi-line value being dropped
    carry = None  # tail of a multi-line value being kept

    for line in lines:
        if pending is not None:
            pending += " " + strip_comment(line)
            if toml_value_is_complete(pending):
                pending = None
            continue

        if carry is not None:
            # Still inside somebody else's array; a new key must go after its
            # closing bracket, not into the middle of it.
            carry += " " + strip_comment(line)
            out.append(line)
            if current == table:
                insert_after = len(out) - 1
            if toml_value_is_complete(carry):
                carry = None
            continue

        header = split_toml_table_header(line)
        if header is not None:
            current = header
            if first_header is None:
                first_header = len(out)
            out.append(line)
            if current == table:
                insert_after = len(out) - 1
            continue

        if current == table and toml_line_key(line) == target_key:
            found = True
            code, comment = split_comment(line)
            if not toml_value_is_complete(code):
                pending = code
            if not delete:
                # Keep the key exactly as the file spells it, along with its
                # indentation and any note the user left on the line.
                indent = line[: len(line) - len(line.lstrip())]
                written_key = code.split("=", 1)[0].strip()
                gap = code[len(code.rstrip()) :] if comment else ""
                out.append(f"{indent}{written_key} = {toml_value(value)}{gap}{comment}")
                insert_after = len(out) - 1
            continue

        out.append(line)
        code = strip_comment(line)
        if toml_line_key(line) is not None:
            if not toml_value_is_complete(code):
                carry = code
            indent = line[: len(line) - len(line.lstrip())]
            if current is not None:
                table_key_indent = indent
            # Only a real key marks where a new one may follow: appending after
            # a trailing comment would put the key under a heading meant for the
            # next table.
            if current == table:
                insert_after = len(out) - 1
                if key_indent is None:
                    key_indent = indent

    if not found and not delete:
        if insert_after is not None:
            indent = key_indent if key_indent is not None else ""
            out.insert(insert_after + 1, f"{indent}{new_line_body}")
        elif table is None:
            # A global setting has to land above the first table header, or it
            # would be read as a key of that table - and above the comment
            # introducing that header, which is about the table, not the key.
            if first_header is None:
                pos = len(out)
                while pos > 0 and not out[pos - 1].strip():
                    pos -= 1
            else:
                pos = first_header
                while pos > 0 and (
                    not out[pos - 1].strip() or out[pos - 1].lstrip().startswith("#")
                ):
                    pos -= 1
            out.insert(pos, new_line_body)
        else:
            if out and out[-1].strip():
                out.append("")
            out.append("[" + ".".join(toml_key(part) for part in table) + "]")
            # Match how the file's other tables indent their keys.
            out.append(f"{table_key_indent or ''}{new_line_body}")

    if delete and found and table is not None:
        out = drop_empty_toml_table(out, table)

    if not out:
        return ""
    newline = "\r\n" if "\r\n" in text else "\n"
    return newline.join(line.rstrip("\r") for line in out).rstrip("\r\n") + newline


def config_edit_took_effect(text, table, key, value, delete):
    """Whether re-reading the edited text really yields the requested change."""
    try:
        parsed = parse_toml_text(text)
    except ValueError:
        return False
    if not isinstance(parsed, dict):
        return False

    sections = []
    if table is None:
        sections.append(parsed)
    else:
        for top in ("extensions", "extension"):
            entries = parsed.get(top)
            if not isinstance(entries, dict):
                continue
            for name, data in entries.items():
                if str(name).strip().lower() == table[1] and isinstance(data, dict):
                    sections.append(data)

    target_key = normalize_toml_key(key)
    seen = False
    for section in sections:
        for k, v in section.items():
            if normalize_toml_key(k) != target_key:
                continue
            if delete or v != value:
                return False
            seen = True
    return not seen if delete else seen


def update_config_file(config, config_path, table, key, value=None, delete=False):
    """Write one config change, keeping the rest of the file as the user wrote it."""
    try:
        with open(config_path, encoding="utf-8") as f:
            text = f.read()
    except FileNotFoundError:
        text = ""
    except (OSError, ValueError) as e:
        print(
            f"{Colors.RED}Error: Failed to read config file '{config_path}': {e}{Colors.ENDC}",
            file=sys.stderr,
        )
        sys.exit(1)

    edited = edit_toml_text(text, table, key, value, delete=delete)
    if config_edit_took_effect(edited, table, key, value, delete):
        write_config_text(edited, config_path)
        return

    if text:
        try:
            parse_toml_text(text)
        except ValueError as e:
            # The original file did not parse, so the in-memory config is the
            # empty fallback from load_config. A full rewrite from it would
            # destroy the user's existing settings, so abort instead.
            print(
                f"{Colors.RED}Error: Cannot update '{config_path}': {e}{Colors.ENDC}",
                file=sys.stderr,
            )
            sys.exit(1)

    # Nothing in the file was recognizable enough to edit in place. Fall back to
    # a full rewrite, which is correct but drops comments and anything this tool
    # does not model, so say so rather than losing it silently.
    print(
        f"{Colors.YELLOW}Warning: Could not edit '{config_path}' in place; rewriting it. "
        f"Comments and unrecognized entries will be lost.{Colors.ENDC}",
        file=sys.stderr,
    )
    save_config(config, config_path)


EXTENSION_ID_PATTERN = re.compile(r"^[A-Za-z0-9_-]+(\.[A-Za-z0-9_-]+)+$")


def is_valid_extension_id(ext_id):
    """Validate whether an extension identifier conforms to 'publisher.name' format."""
    # Deliberately not stripping: callers key the marketplace response map by the
    # exact string they validated, so accepting ' pub.name ' here while looking up
    # the padded form there would report a real extension as missing.
    if not ext_id or not isinstance(ext_id, str):
        return False
    return bool(EXTENSION_ID_PATTERN.fullmatch(ext_id))


def parse_config_key(key, validate=True):
    # `validate` is off for get/unset so that entries an older release wrote with
    # a malformed id stay reachable; only `set` refuses to create new ones.
    key = str(key).strip()
    key = key.removeprefix("extensions.")

    if "." in key:
        parts = key.rsplit(".", 1)
        ext_id, prop = parts[0].strip().lower(), parts[1].strip().lower()
        if not validate or is_valid_extension_id(ext_id):
            return ("extension", ext_id, prop)
        # No global setting contains a dot, so a dotted key was meant as an
        # extension rule. Reporting it as an unknown global would answer with
        # the global option list instead of the actual problem.
        return ("invalid", ext_id, prop)
    return ("global", key.lower(), None)


def handle_config(args, config):
    config_path = get_default_config_path()
    action = args.action or "list"

    if action == "list" and not args.key:
        print(f"{Colors.BOLD}Configuration file:{Colors.ENDC} {config_path}\n")
        print(f"{Colors.BOLD}Active Global Overrides:{Colors.ENDC}")
        globals_found = False
        for k in sorted(config.keys()):
            if k != "extensions":
                print(
                    f"  {Colors.CYAN}{k:<22}{Colors.ENDC} = {redact_config_value(k, config[k])}"
                )
                globals_found = True
        if not globals_found:
            print("  (no global settings overridden)")

        exts = config.get("extensions", {})
        print(f"\n{Colors.BOLD}Active Extension Rules:{Colors.ENDC}")
        if not exts:
            print("  (no extension-specific rules configured)")
        else:
            for ext_id in sorted(exts.keys()):
                print(f"  {Colors.BOLD}{Colors.CYAN}{ext_id}{Colors.ENDC}:")
                for pk, pv in sorted(exts[ext_id].items()):
                    print(f"    {pk} = {pv!r}")

        print(
            f"\n{Colors.BOLD}Available Global Settings{Colors.ENDC} (use 'code-extensions config set <key> <val>'):"
        )
        for key, _type, desc, default in GLOBAL_CONFIG_SCHEMA:
            print(f"  {Colors.CYAN}{key:<22}{Colors.ENDC} {desc} [Default: {default}]")

        print(
            f"\n{Colors.BOLD}Available Per-Extension Rules{Colors.ENDC} (use 'code-extensions config set <pub.name>.<key> <val>'):"
        )
        for key, _type, desc in EXT_CONFIG_SCHEMA:
            print(f"  {Colors.CYAN}{key:<22}{Colors.ENDC} {desc}")
        print()
        return

    if action == "get":
        if not args.key:
            print(
                f"{Colors.RED}Error: 'config get' requires a setting key.{Colors.ENDC}",
                file=sys.stderr,
            )
            sys.exit(1)

        target_type, ext_id, prop = parse_config_key(args.key, validate=False)
        if target_type == "global":
            val = config.get(ext_id.replace("-", "_"))
            if val is not None:
                print(val)
            else:
                print(
                    f"{Colors.YELLOW}Key '{args.key}' is not set in configuration.{Colors.ENDC}",
                    file=sys.stderr,
                )
                sys.exit(1)
        else:
            exts = config.get("extensions", {})
            val = exts.get(ext_id.lower(), {}).get(prop.replace("-", "_"))
            if val is not None:
                print(val)
            else:
                print(
                    f"{Colors.YELLOW}Key '{args.key}' is not set in configuration.{Colors.ENDC}",
                    file=sys.stderr,
                )
                sys.exit(1)
        return

    if action == "set":
        if not args.key or args.value is None:
            print(
                f"{Colors.RED}Error: 'config set' requires both key and value (e.g. 'code-extensions config set min_release_age 3d').{Colors.ENDC}",
                file=sys.stderr,
            )
            sys.exit(1)

        target_type, ext_id, prop = parse_config_key(args.key)
        if target_type == "invalid":
            print(
                f"{Colors.RED}Error: Invalid extension ID '{ext_id}' in key '{args.key}'. Expected format '<publisher>.<name>.<setting>'.{Colors.ENDC}",
                file=sys.stderr,
            )
            sys.exit(1)

        raw_val = args.value.strip()
        coerced_val = raw_val
        if raw_val.lower() == "true":
            coerced_val = True
        elif raw_val.lower() == "false":
            coerced_val = False

        if target_type == "global":
            norm_key = ext_id.replace("-", "_")
            if norm_key not in CONFIG_OPTION_TYPES:
                print(
                    f"{Colors.RED}Error: Unknown global setting '{args.key}'. Valid keys: {', '.join(sorted(CONFIG_OPTION_TYPES))}.{Colors.ENDC}",
                    file=sys.stderr,
                )
                sys.exit(1)
            stored_val = validate_config_value(
                args.key, norm_key, coerced_val, CONFIG_OPTION_TYPES[norm_key]
            )
            config[norm_key] = stored_val
        else:
            norm_prop = prop.replace("-", "_")
            if norm_prop not in EXT_OPTION_KEYS:
                print(
                    f"{Colors.RED}Error: Unknown per-extension setting '{norm_prop}'. Valid keys: {', '.join(sorted(EXT_OPTION_KEYS))}.{Colors.ENDC}",
                    file=sys.stderr,
                )
                sys.exit(1)
            if "extensions" not in config or not isinstance(config["extensions"], dict):
                config["extensions"] = {}
            norm_ext_id = ext_id.lower()
            if norm_ext_id not in config["extensions"]:
                config["extensions"][norm_ext_id] = {}
            stored_val = validate_config_value(
                args.key, norm_prop, coerced_val, EXT_OPTION_TYPES[norm_prop]
            )
            config["extensions"][norm_ext_id][norm_prop] = stored_val
            norm_key = norm_prop

        update_config_file(
            config,
            config_path,
            config_table_path(target_type, ext_id),
            norm_key,
            stored_val,
        )
        print(
            f"  {Colors.GREEN}✓ Set '{args.key}' = {raw_val!r} in {config_path}{Colors.ENDC}"
        )
        return

    if action in ("unset", "delete"):
        if not args.key:
            print(
                f"{Colors.RED}Error: 'config unset' requires a setting key.{Colors.ENDC}",
                file=sys.stderr,
            )
            sys.exit(1)

        target_type, ext_id, prop = parse_config_key(args.key, validate=False)
        changed = False

        if target_type == "global":
            norm_key = ext_id.replace("-", "_")
            if norm_key in config:
                del config[norm_key]
                changed = True
        else:
            exts = config.get("extensions", {})
            norm_ext_id = ext_id.lower()
            norm_key = prop.replace("-", "_")
            if norm_ext_id in exts and norm_key in exts[norm_ext_id]:
                del exts[norm_ext_id][norm_key]
                if not exts[norm_ext_id]:
                    del exts[norm_ext_id]
                changed = True

        if changed:
            update_config_file(
                config,
                config_path,
                config_table_path(target_type, ext_id),
                norm_key,
                delete=True,
            )
            print(f"  {Colors.GREEN}✓ Unset '{args.key}' in {config_path}{Colors.ENDC}")
        else:
            print(
                f"  {Colors.YELLOW}Key '{args.key}' is not set in configuration.{Colors.ENDC}"
            )
        return


def get_vsix_download_url(
    ver_obj, pub_name, ext_name, version, platform, service_url=DEFAULT_SERVICE_URL
):
    if ver_obj and isinstance(ver_obj, dict):
        for f in ver_obj.get("files") or []:
            asset_type = f.get("assetType", "")
            if asset_type in (
                "Microsoft.VisualStudio.Services.VSIXPackage",
                "Microsoft.VisualStudio.Code.VSIXPackage",
            ) and f.get("source"):
                url = f["source"]
                if (
                    platform
                    and platform != "universal"
                    and "targetPlatform=" not in url
                ):
                    sep = "&" if "?" in url else "?"
                    url += f"{sep}targetPlatform={platform}"
                return url

    base_url = service_url.rstrip("/")
    url = (
        f"{base_url}/publishers/{pub_name}/vsextensions/{ext_name}/{version}/vspackage"
    )
    if platform and platform != "universal":
        url += f"?targetPlatform={platform}"
    return url


def resolve_update_url(update, service_url):
    return update.get("eligible_download_url") or get_vsix_download_url(
        {},
        update["publisher"],
        update["name"],
        update["eligible"],
        update["eligible_platform"],
        service_url,
    )


_UNSAFE_FILENAME_CHARS = re.compile(r"[^A-Za-z0-9._-]+")


def safe_filename_part(value, fallback="unknown"):
    """Reduce a gallery-supplied string to something safe inside a filename.

    Publisher, extension name, version and platform all come from the gallery
    response, so a hostile --service-url could otherwise smuggle path separators
    or '..' into the download path.
    """
    cleaned = _UNSAFE_FILENAME_CHARS.sub("_", str(value or "")).strip("._-")
    return cleaned or fallback


def vsix_filename(pub_name, ext_name, version, platform):
    filename = (
        f"{safe_filename_part(pub_name, 'publisher')}."
        f"{safe_filename_part(ext_name, 'extension')}-"
        f"{safe_filename_part(version, 'version')}"
    )
    if platform and platform != "universal":
        filename += f"-{safe_filename_part(platform, 'platform')}"
    return filename + ".vsix"


def is_open_vsx_url(url):
    """Whether a URL points at Open VSX, matched on host rather than substring.

    A substring test would accept hosts such as 'open-vsx.org.example.com' and
    hand them the access token.
    """
    if not url:
        return False
    host = url_host(url)
    return host == OPEN_VSX_HOST or host.endswith("." + OPEN_VSX_HOST)


def is_marketplace_url(url):
    """Whether a URL points at Microsoft's Marketplace or one of its CDN hosts."""
    if not url:
        return False
    host = url_host(url)
    return any(
        host == known or host.endswith("." + known) for known in MARKETPLACE_HOSTS
    )


def resolve_open_vsx_token(args, config):
    config = config or {}
    token = resolve_option(
        getattr(args, "open_vsx_token", None) if args else None,
        config,
        "open_vsx_token",
        None,
    )
    if token:
        return token
    return os.environ.get("OVSX_PAT")


def resolve_token_for_service(service_url, args=None, config=None):
    config = config or {}
    open_vsx = resolve_option(
        getattr(args, "open_vsx", None) if args else None,
        config,
        "open_vsx",
        False,
    )
    has_cli_token = (
        hasattr(args, "open_vsx_token")
        and getattr(args, "open_vsx_token", None) is not None
    )
    has_cfg_token = bool(config.get("open_vsx_token"))
    if is_open_vsx_url(service_url) or open_vsx:
        return resolve_open_vsx_token(args, config)
    # A configured token also covers self-hosted Open VSX registries, whose URLs
    # this tool cannot recognize - but never Microsoft's Marketplace, which would
    # otherwise be handed the credential simply because one happens to be set.
    if (has_cli_token or has_cfg_token) and not is_marketplace_url(service_url):
        return resolve_open_vsx_token(args, config)
    return None


class ExecutionContext:
    """Resolved runtime options and environment for command execution."""

    def __init__(self, args, config):
        config = config or {}
        self._args = args
        self._config = config
        self.code_binary = parse_code_binary(
            resolve_option(
                getattr(args, "code_binary", None), config, "code_binary", "code"
            )
        )
        self.include_prerelease = resolve_option(
            getattr(args, "include_prerelease", None),
            config,
            "include_prerelease",
            False,
        )
        self.no_code_version_check = resolve_option(
            getattr(args, "no_code_version_check", None),
            config,
            "no_code_version_check",
            False,
        )
        self.yes = resolve_option(getattr(args, "yes", None), config, "yes", False)
        self.target_platform = get_local_target_platform()
        self.extensions_config = config.get("extensions", {})
        self._vscode_version = None
        self._vscode_version_fetched = False
        self._service_url = None
        self._token = None
        self._token_resolved = False
        self._min_release_age = None
        self._min_release_age_str = None
        self._min_release_age_resolved = False

    # Resolved on demand: resolve_service_url warns about insecure HTTP and
    # resolve_min_release_age exits on an unparseable value, neither of which a
    # command that never consults the setting (`list`, `remove`) should trigger.
    @property
    def service_url(self):
        if self._service_url is None:
            self._service_url = resolve_service_url(self._args, self._config)
        return self._service_url

    @property
    def token(self):
        if not self._token_resolved:
            self._token = resolve_token_for_service(
                self.service_url, self._args, self._config
            )
            self._token_resolved = True
        return self._token

    def _resolve_min_release_age(self):
        if not self._min_release_age_resolved:
            self._min_release_age, self._min_release_age_str = resolve_min_release_age(
                getattr(self._args, "min_release_age", None), self._config
            )
            self._min_release_age_resolved = True

    @property
    def min_release_age(self):
        self._resolve_min_release_age()
        return self._min_release_age

    @property
    def min_release_age_str(self):
        self._resolve_min_release_age()
        return self._min_release_age_str

    @property
    def vscode_version(self):
        if not self._vscode_version_fetched:
            self._vscode_version = (
                None
                if self.no_code_version_check
                else get_vscode_version(self.code_binary)
            )
            self._vscode_version_fetched = True
        return self._vscode_version


# Upper bound on a Retry-After delay. The header comes from the remote
# service, so a hostile or misbehaving gallery must not be able to park the
# tool for hours on end.
MAX_RETRY_AFTER_SECONDS = 60.0


def _post_extension_query(payload, service_url, token=None):
    """POST an extensionquery payload, with a 1h on-disk cache and retries.

    Returns the parsed JSON response, or None if the request ultimately failed.
    """
    if not token and is_open_vsx_url(service_url):
        token = os.environ.get("OVSX_PAT")

    req_data = json.dumps(payload).encode("utf-8")
    cache_dir = get_cache_dir()
    cache_file = None
    if cache_dir:
        cache_key_data = {
            "service_url": service_url,
            "payload": payload,
            # An authenticated response can differ from an anonymous one, so keep
            # their cache entries apart without storing the token itself.
            "token": hashlib.sha256(token.encode("utf-8")).hexdigest()
            if token
            else None,
        }
        payload_hash = hashlib.sha256(
            json.dumps(cache_key_data, sort_keys=True).encode("utf-8")
        ).hexdigest()
        cache_file = os.path.join(cache_dir, f"{CACHE_FILE_PREFIX}{payload_hash}.json")

        if os.path.exists(cache_file):
            try:
                if time.time() - os.path.getmtime(cache_file) < 3600:
                    with open(cache_file, encoding="utf-8") as f:
                        return json.load(f)
            except (OSError, ValueError):
                pass

    query_endpoint = f"{service_url.rstrip('/')}/extensionquery"
    if "api-version=" not in query_endpoint:
        query_endpoint += "?api-version=7.2-preview.1"

    headers = {
        "Content-Type": "application/json",
        "Accept": "application/json; api-version=7.2-preview.1",
    }
    if token:
        headers["Authorization"] = f"Bearer {token}"

    req = urllib.request.Request(
        query_endpoint,
        data=req_data,
        headers=headers,
        method="POST",
    )

    max_retries = 3
    backoff = 2.0
    err = None
    for attempt in range(max_retries + 1):
        retry_reason = None
        retry_after = None
        try:
            with _url_opener.open(req, timeout=30) as response:
                resp_data = json.loads(response.read().decode("utf-8"))
            if cache_file:
                write_cache_atomically(cache_file, resp_data)
            return resp_data
        except urllib.error.HTTPError as e:
            err = e
            if 500 <= e.code < 600:
                retry_reason = f"returned HTTP status {e.code}"
            elif e.code == 429:
                retry_reason = "rate limited (HTTP 429)"
                ra = e.headers.get("Retry-After")
                if ra and ra.strip().isdigit():
                    retry_after = min(float(ra.strip()), MAX_RETRY_AFTER_SECONDS)
        except (urllib.error.URLError, TimeoutError) as e:
            err = e
            # urllib wraps any OSError raised while connecting or sending into
            # URLError, so a refused or reset connection arrives here rather
            # than in the ConnectionError clause below, which only ever sees
            # failures raised while reading the response body.
            cause = getattr(e, "reason", None)
            reason = str(cause if cause is not None else e).lower()
            if (
                isinstance(e, TimeoutError)
                or isinstance(cause, TimeoutError)
                or "timed out" in reason
                or "timeout" in reason
            ):
                retry_reason = "request timed out"
            elif isinstance(cause, ConnectionError):
                retry_reason = "connection failed"
        except (
            json.JSONDecodeError,
            UnicodeDecodeError,
            http.client.HTTPException,
            ConnectionError,
        ) as e:
            err = e
            if isinstance(e, (json.JSONDecodeError, UnicodeDecodeError)):
                retry_reason = "returned invalid or truncated JSON response"
            else:
                retry_reason = "connection interrupted or incomplete read"
        # Deliberate last resort: every transient failure is classified above,
        # so anything left is unforeseen and must not abort a bulk update
        # midway. It is reported, without a retry_reason, as a plain failure.
        except Exception as e:  # noqa: BLE001
            err = e

        if retry_reason and attempt < max_retries:
            delay = retry_after if retry_after is not None else backoff
            print(
                f"{Colors.YELLOW}Marketplace API {retry_reason}. Retrying in {delay}s... (attempt {attempt + 1}/{max_retries}){Colors.ENDC}",
                file=sys.stderr,
            )
            time.sleep(delay)
            backoff *= 2.0
        else:
            print(
                f"{Colors.RED}Failed to query marketplace API: {err}{Colors.ENDC}",
                file=sys.stderr,
            )
            break

    return None


# Gallery query flags: IncludeVersions (0x1) | IncludeCategoryAndTags (0x4) |
# IncludeVersionProperties (0x10). Without the category flag the response simply
# omits `categories`, which is what `info` reports.
GALLERY_QUERY_FLAGS = 0x1 | 0x4 | 0x10


def query_marketplace_extensions(ext_ids, service_url=DEFAULT_SERVICE_URL, token=None):
    cleanup_stale_cache()
    if not ext_ids:
        return {}

    batch_size = 50
    extension_map = {}

    for i in range(0, len(ext_ids), batch_size):
        batch = ext_ids[i : i + batch_size]
        criteria = [{"filterType": 8, "value": "Microsoft.VisualStudio.Code"}]
        for ext_id in batch:
            criteria.append({"filterType": 7, "value": ext_id})

        payload = {
            "filters": [
                {
                    "criteria": criteria,
                    "pageNumber": 1,
                    "pageSize": len(batch),
                    "sortBy": 0,
                    "sortOrder": 0,
                }
            ],
            "assetTypes": [],
            "flags": GALLERY_QUERY_FLAGS,
        }

        resp_data = _post_extension_query(payload, service_url, token=token)
        if not resp_data:
            continue

        results = resp_data.get("results", [])
        if not results:
            continue

        extensions = results[0].get("extensions", [])
        for ext in extensions:
            pub_name = ext.get("publisher", {}).get("publisherName", "")
            ext_name = ext.get("extensionName", "")
            full_id = f"{pub_name}.{ext_name}".lower()
            extension_map[full_id] = ext

    return extension_map


def query_marketplace_search(
    query_text,
    max_results=15,
    target_platform=None,
    vscode_version=None,
    include_prerelease=False,
    min_release_age=None,
    extensions_config=None,
    cli_include_prerelease_override=False,
    cli_min_release_age_override=False,
    service_url=DEFAULT_SERVICE_URL,
    token=None,
):
    cleanup_stale_cache()
    if not query_text:
        return []

    if target_platform is None:
        target_platform = get_local_target_platform()

    payload = {
        "filters": [
            {
                "criteria": [
                    {"filterType": 8, "value": "Microsoft.VisualStudio.Code"},
                    {"filterType": 10, "value": query_text},
                ],
                "pageNumber": 1,
                "pageSize": max_results,
                "sortBy": 0,
                "sortOrder": 0,
            }
        ],
        "assetTypes": [],
        "flags": 914,
    }

    resp_data = _post_extension_query(payload, service_url, token=token)
    if not resp_data:
        return []

    results = resp_data.get("results", [])
    if not results:
        return []

    extensions = results[0].get("extensions", [])
    if not extensions:
        return []

    ext_ids = [
        f"{ext.get('publisher', {}).get('publisherName', '')}.{ext.get('extensionName', '')}".lower()
        for ext in extensions
        if ext.get("publisher", {}).get("publisherName") and ext.get("extensionName")
    ]
    ext_details_map = query_marketplace_extensions(
        ext_ids, service_url=service_url, token=token
    )

    search_results = []
    for ext in extensions:
        pub_name = ext.get("publisher", {}).get("publisherName", "")
        ext_name = ext.get("extensionName", "")
        full_id = f"{pub_name}.{ext_name}".lower()
        display_name = ext.get("displayName") or ext_name
        description = ext.get("shortDescription") or ""

        full_ext = ext_details_map.get(full_id, ext)

        ext_cfg = extensions_config.get(full_id, {}) if extensions_config else {}
        skipped_versions = ext_cfg.get("skip_versions", [])
        eff_include_prerelease, eff_min_age, _ = effective_ext_options(
            ext_cfg,
            include_prerelease,
            min_release_age,
            cli_include_prerelease_override=cli_include_prerelease_override,
            cli_min_release_age_override=cli_min_release_age_override,
        )

        compatible_versions = filter_versions(
            full_ext.get("versions", []),
            target_platform,
            vscode_version=vscode_version,
            include_prerelease=eff_include_prerelease,
            skip_versions=skipped_versions,
        )

        latest_version = "unknown"
        eligible_version = "unknown"
        is_held_back = False

        if compatible_versions:
            latest_ver_obj = compatible_versions[0]
            latest_version = latest_ver_obj["version"]

            eligible_ver_obj = first_eligible_version(compatible_versions, eff_min_age)

            if eligible_ver_obj:
                eligible_version = eligible_ver_obj["version"]
                if eligible_ver_obj != latest_ver_obj:
                    is_held_back = True
            else:
                eligible_version = "held back"
                is_held_back = True
        else:
            all_versions = full_ext.get("versions", [])
            if all_versions:
                raw_latest = all_versions[0].get("version", "unknown")
                if not eff_include_prerelease and is_prerelease(all_versions[0]):
                    eligible_version = "pre-release"
                    latest_version = raw_latest
                    is_held_back = True

        search_results.append(
            {
                "id": full_id,
                "publisher": pub_name,
                "name": ext_name,
                "displayName": display_name,
                "description": description,
                "latest": latest_version,
                "eligible": eligible_version,
                "is_held_back": is_held_back,
            }
        )

    return search_results


def resolve_download_target(args, config):
    """Return (directory, is_private_temp) for .vsix downloads.

    Without an explicit --download-dir the files go into a fresh 0700 directory
    rather than straight into the shared temp directory: the filenames are
    predictable, so a local attacker could otherwise pre-plant a symlink or swap
    the package between download and install.
    """
    download_dir = resolve_option(
        getattr(args, "download_dir", None), config, "download_dir", None
    )
    # A blank --download-dir would silently mean the working directory, which
    # then keeps the .vsix files nobody asked it to keep.
    if download_dir is not None and str(download_dir).strip():
        return os.path.expanduser(download_dir), False
    return tempfile.mkdtemp(prefix="code-extensions-"), True


def discard_download_dir(directory, is_private_temp):
    if is_private_temp:
        shutil.rmtree(directory, ignore_errors=True)


def download_and_install(
    code_binary,
    url,
    filepath,
    display_id,
    version,
    platform_name,
    token=None,
    service_url=None,
    force=False,
    cleanup=False,
):
    """Download a .vsix from url and install it with the code CLI.

    Shared by `install` and `update` so the two cannot drift. Returns True
    when the package was installed. A failed download skips the install
    (the partial file is already removed by download_vsix); a failed install
    still removes the file when cleanup is set.
    """
    # Accept a raw string as well as a parsed list, like the other code-CLI
    # helpers, so callers cannot pass "code" and unpack it into characters.
    code_binary = parse_code_binary(code_binary)
    print(
        f"Downloading {Colors.CYAN}{display_id}{Colors.ENDC} v{Colors.GREEN}{version}{Colors.ENDC} ({platform_name})..."
    )
    try:
        download_vsix(url, filepath, token=token, service_url=service_url)
    except DOWNLOAD_ERRORS as e:
        print(f"{Colors.RED}✗ Download failed: {e}{Colors.ENDC}", file=sys.stderr)
        return False

    print(
        f"Installing {Colors.CYAN}{display_id}{Colors.ENDC} v{Colors.GREEN}{version}{Colors.ENDC}..."
    )
    installed = False
    try:
        cmd = [*code_binary, "--install-extension", filepath]
        if force:
            cmd.append("--force")
        run_code_cmd(cmd, retries=0)
        print(f"  {Colors.GREEN}✓{Colors.ENDC} Installed successfully.")
        installed = True
    except subprocess.CalledProcessError as e:
        print(
            f"  {Colors.RED}✗ Installation failed: {e.stderr.strip() or e}{Colors.ENDC}",
            file=sys.stderr,
        )
    # run_code_cmd raises OSError when the binary is missing or unexecutable.
    except OSError as e:
        print(f"  {Colors.RED}✗ Installation failed: {e}{Colors.ENDC}", file=sys.stderr)

    if cleanup and os.path.exists(filepath):
        with contextlib.suppress(OSError):
            os.remove(filepath)
    return installed


def open_for_download(filepath):
    """Open a download target for writing, refusing to follow a symlink."""
    flags = os.O_WRONLY | os.O_CREAT | os.O_TRUNC
    flags |= getattr(os, "O_NOFOLLOW", 0)
    flags |= getattr(os, "O_BINARY", 0)
    return os.open(filepath, flags, 0o600)


def download_vsix(url, filepath, token=None, service_url=None):
    parent = os.path.dirname(filepath)
    if parent:
        os.makedirs(parent, exist_ok=True)
    show_progress = sys.stdout.isatty()

    if not token and (
        is_open_vsx_url(url) or (service_url and is_open_vsx_url(service_url))
    ):
        token = os.environ.get("OVSX_PAT")

    # The download host comes from the gallery response, not from the configured
    # service, so it is only trusted with the token when it is the service itself
    # or Open VSX. Anything else - a CDN, a redirector, a host a compromised
    # response named - is served anonymously. Cross-host redirects are handled by
    # _AuthStrippingRedirectHandler; this covers the first hop.
    download_host = url_host(url)
    if token and not (
        is_open_vsx_url(url)
        or (download_host and download_host == url_host(service_url or ""))
    ):
        token = None

    headers = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36"
    }
    if token:
        headers["Authorization"] = f"Bearer {token}"

    req = urllib.request.Request(
        url,
        headers=headers,
    )

    with _url_opener.open(req, timeout=30) as response:
        content_encoding = response.headers.get("Content-Encoding", "").lower()
        total_size = response.headers.get("Content-Length")
        if total_size:
            try:
                total_size = int(total_size)
            except ValueError:
                total_size = None

        # Marketplace serves /vspackage gzip-encoded; decompress as we go rather
        # than holding both the compressed and expanded package in memory.
        decompressor = None
        if content_encoding == "gzip":
            decompressor = zlib.decompressobj(16 + zlib.MAX_WBITS)
        elif content_encoding == "deflate":
            decompressor = zlib.decompressobj()

        bytes_read = 0
        bytes_written = 0
        chunk_size = 32768
        ok = False

        fd = open_for_download(filepath)
        try:
            with os.fdopen(fd, "wb") as f:

                def emit(data):
                    nonlocal bytes_written
                    if not data:
                        return
                    bytes_written += len(data)
                    if bytes_written > MAX_VSIX_BYTES:
                        raise ValueError(
                            f"package exceeds the {MAX_VSIX_BYTES // (1024 * 1024)}MB limit"
                        )
                    f.write(data)

                while True:
                    chunk = response.read(chunk_size)
                    if not chunk:
                        break
                    bytes_read += len(chunk)
                    emit(decompressor.decompress(chunk) if decompressor else chunk)
                    report_download_progress(show_progress, bytes_read, total_size)

                if decompressor:
                    emit(decompressor.flush())
            ok = True
        finally:
            if not ok:
                # Never leave a truncated package behind for `--install-extension`.
                with contextlib.suppress(OSError):
                    os.remove(filepath)

        if show_progress and (total_size or bytes_read > 0):
            sys.stdout.write("\n")
            sys.stdout.flush()


def report_download_progress(show_progress, bytes_read, total_size):
    if not show_progress:
        return
    read_mb = bytes_read / (1024 * 1024)
    if total_size and total_size > 0:
        # Content-Length can understate the body (a re-encoding proxy), so
        # clamp percent and the bar rather than drawing >100% or a bar wider
        # than its frame.
        percent = min(100, (bytes_read * 100) // total_size)
        bar_len = 30
        filled_len = min(bar_len, round(bar_len * bytes_read / float(total_size)))
        bar = "=" * filled_len + " " * (bar_len - filled_len)
        total_mb = total_size / (1024 * 1024)
        sys.stdout.write(f"\r  [{bar}] {percent}% ({read_mb:.2f}MB / {total_mb:.2f}MB)")
    else:
        sys.stdout.write(f"\r  Downloaded: {read_mb:.2f}MB")
    sys.stdout.flush()


# Final byte of a CSI escape sequence (ESC '[' <byte>) for the arrow keys.
CSI_ARROW_KEYS = {"A": "up", "B": "down", "C": "right", "D": "left"}


def get_key():
    if not HAS_TTY:
        return None
    fd = sys.stdin.fileno()
    old_settings = termios.tcgetattr(fd)
    try:
        tty.setraw(fd)
        rlist, _, _ = select.select([fd], [], [], None)
        if not rlist:
            return None
        b = os.read(fd, 1)
        if not b:
            return None
        # A non-ASCII keystroke arrives as several bytes; decoding only the first
        # one yields "" and silently swallows the key.
        lead = b[0]
        if lead >= 0x80:
            if lead >= 0xF0:
                extra = 3
            elif lead >= 0xE0:
                extra = 2
            elif lead >= 0xC0:
                extra = 1
            else:
                extra = 0
            for _ in range(extra):
                rlist, _, _ = select.select([fd], [], [], 0.05)
                if not rlist:
                    break
                more = os.read(fd, 1)
                if not more:
                    break
                b += more
        ch = b.decode("utf-8", errors="ignore")
        if ch == "\x1b":
            rlist, _, _ = select.select([fd], [], [], 0.05)
            if rlist:
                b2 = os.read(fd, 1)
                ch2 = b2.decode("utf-8", errors="ignore") if b2 else ""
                if ch2 == "[":
                    rlist, _, _ = select.select([fd], [], [], 0.05)
                    if rlist:
                        b3 = os.read(fd, 1)
                        ch3 = b3.decode("utf-8", errors="ignore") if b3 else ""
                        if ch3 in CSI_ARROW_KEYS:
                            return CSI_ARROW_KEYS[ch3]
            return "esc"
        elif ch in ("\r", "\n"):
            return "enter"
        elif ch == " ":
            return "space"
        elif ch == "\x03":
            return "ctrl+c"
        else:
            return ch
    finally:
        termios.tcsetattr(fd, termios.TCSADRAIN, old_settings)


def display_width(text):
    clean_text = ANSI_ESCAPE.sub("", str(text))
    w = 0
    for ch in clean_text:
        if unicodedata.east_asian_width(ch) in ("F", "W"):
            w += 2
        else:
            w += 1
    return w


def truncate(text, width):
    text = str(text)
    if width <= 0:
        return ""
    if display_width(text) <= width:
        return text

    current_w = 0
    chars = []
    for ch in text:
        ch_w = 2 if unicodedata.east_asian_width(ch) in ("F", "W") else 1
        if current_w + ch_w > width:
            while chars and (current_w + 1 > width):
                popped = chars.pop()
                current_w -= (
                    2 if unicodedata.east_asian_width(popped) in ("F", "W") else 1
                )
            chars.append("…")
            break
        chars.append(ch)
        current_w += ch_w
    return "".join(chars)


def fit_column(text, width):
    t = truncate(text, width)
    dw = display_width(t)
    if dw < width:
        return t + " " * (width - dw)
    return t


def format_action_bar(items):
    formatted = []
    for keys_str, action_name, color_code in items:
        formatted.append(
            f"[{color_code}{Colors.BOLD}{keys_str}{Colors.ENDC}] {action_name}"
        )
    return f"{Colors.BOLD}Actions:{Colors.ENDC} " + "   ".join(formatted)


def prompt_yes_no(question, default=False):
    suffix = " [Y/n] " if default else " [y/N] "
    try:
        reply = input(f"{Colors.YELLOW}{question}{suffix}{Colors.ENDC}").strip().lower()
        if not reply:
            return default
        return reply.startswith("y")
    except (KeyboardInterrupt, EOFError):
        print()
        return False


def handle_install(args, config):
    ctx = ExecutionContext(args, config)

    target_specs = list(args.extensions or [])
    file_option = getattr(args, "file", None)
    if file_option:
        file_path = os.path.expanduser(file_option)
        if not os.path.isfile(file_path):
            print(
                f"{Colors.RED}Error: File '{file_option}' not found.{Colors.ENDC}",
                file=sys.stderr,
            )
            sys.exit(1)
        try:
            with open(file_path, encoding="utf-8") as f:
                for line in f:
                    line = line.strip()
                    if line and not line.startswith("#"):
                        target_specs.append(line)
        except (OSError, UnicodeDecodeError) as e:
            print(
                f"{Colors.RED}Error reading file '{file_option}': {e}{Colors.ENDC}",
                file=sys.stderr,
            )
            sys.exit(1)

    if not target_specs:
        print(
            f"{Colors.RED}Error: No extension ID(s) provided. Specify extension ID(s) or pass -f/--file.{Colors.ENDC}",
            file=sys.stderr,
        )
        sys.exit(1)

    parsed_targets = []
    failures = []
    for spec in target_specs:
        spec = spec.strip()
        if "@" in spec:
            ext_id, req_ver = spec.rsplit("@", 1)
            # A trailing '@' pins nothing. filter_versions tests the pin with
            # 'is not None', so leaving it as '' would match no version and turn
            # 'publisher.name@' into 'no compatible version found'.
            req_ver = req_ver.strip() or None
        else:
            ext_id, req_ver = spec, None
        ext_id_lower = ext_id.strip().lower()
        if not is_valid_extension_id(ext_id_lower):
            print(
                f"{Colors.RED}Error: Invalid extension ID '{spec}'. Expected format 'publisher.name' or 'publisher.name@version'.{Colors.ENDC}",
                file=sys.stderr,
            )
            failures.append(ext_id_lower)
            continue
        parsed_targets.append((ext_id_lower, req_ver))

    if not parsed_targets:
        # Every spec was rejected, so exit non-zero: a script that pipes a list
        # of ids in has otherwise no way to tell this from a successful install.
        print("No valid extensions specified for installation.", file=sys.stderr)
        sys.exit(1)

    ext_ids = [t[0] for t in parsed_targets]
    print(f"{Colors.BLUE}Querying extension gallery for installation...{Colors.ENDC}")
    marketplace_data = query_marketplace_extensions(
        ext_ids, service_url=ctx.service_url, token=ctx.token
    )
    installed_exts = get_installed_extensions(ctx.code_binary)

    download_dir_resolved, download_dir_is_temp = resolve_download_target(args, config)

    for ext_id, req_ver in parsed_targets:
        ext_obj = marketplace_data.get(ext_id)
        if not ext_obj:
            print(
                f"{Colors.RED}✗ Extension '{ext_id}' not found on extension gallery.{Colors.ENDC}",
                file=sys.stderr,
            )
            failures.append(ext_id)
            continue

        pub_name = ext_obj.get("publisher", {}).get("publisherName", "")
        ext_name = ext_obj.get("extensionName", "")
        full_id = f"{pub_name}.{ext_name}".lower()

        ext_cfg = ctx.extensions_config.get(full_id, {})
        eff_include_prerelease, eff_min_age, eff_min_age_str = effective_ext_options(
            ext_cfg,
            ctx.include_prerelease,
            ctx.min_release_age,
            ctx.min_release_age_str,
            # bool() rather than `is not None`: programmatic callers (the
            # search TUI, the test suite) pass False to mean "flag not
            # given", which `is not None` would read as an override.
            cli_include_prerelease_override=bool(
                getattr(args, "include_prerelease", None)
            ),
            cli_min_release_age_override=args.min_release_age is not None,
        )

        # An explicitly requested version overrides the config's opinion about
        # pre-releases and skipped versions, the same way it overrides the
        # min-release-age gate below.
        skipped_versions = [] if req_ver else ext_cfg.get("skip_versions", [])

        compatible_versions = filter_versions(
            ext_obj.get("versions", []),
            ctx.target_platform,
            vscode_version=ctx.vscode_version,
            include_prerelease=eff_include_prerelease or bool(req_ver),
            skip_versions=skipped_versions,
            required_version=req_ver,
        )

        if not compatible_versions:
            if req_ver:
                print(
                    f"{Colors.RED}✗ Version '{req_ver}' for '{full_id}' not found or incompatible with host platform/VS Code.{Colors.ENDC}"
                )
            else:
                print(
                    f"{Colors.RED}✗ No compatible version of '{full_id}' found.{Colors.ENDC}"
                )
            failures.append(full_id)
            continue

        latest_ver_obj = compatible_versions[0]
        eligible_ver_obj = first_eligible_version(compatible_versions, eff_min_age)

        selected_ver_obj = None

        if req_ver:
            target_ver_obj = compatible_versions[0]
            is_too_fresh = not released_long_enough(target_ver_obj, eff_min_age)

            if is_too_fresh:
                print(
                    f"{Colors.YELLOW}Warning: Requested version '{req_ver}' of '{full_id}' was released less than {eff_min_age} ago.{Colors.ENDC}"
                )
                if not ctx.yes:
                    if not sys.stdin.isatty():
                        # Nobody to ask, so the age gate stands: that is a
                        # failure for whoever scripted the install.
                        print(f"Skipping installation of '{full_id}@{req_ver}'.")
                        failures.append(full_id)
                        continue
                    if not prompt_yes_no(
                        f"Do you want to install '{full_id}@{req_ver}' despite minimum release age policy?"
                    ):
                        print(f"Skipping installation of '{full_id}@{req_ver}'.")
                        continue
                else:
                    print(
                        f"Installing '{full_id}@{req_ver}' due to explicit version parameter."
                    )
            selected_ver_obj = target_ver_obj
        else:
            if eligible_ver_obj:
                selected_ver_obj = eligible_ver_obj
                if eligible_ver_obj != latest_ver_obj:
                    print(
                        f"{Colors.YELLOW}Notice: Latest version '{latest_ver_obj['version']}' of '{full_id}' is held back by minimum release age policy ({eff_min_age_str}). Installing latest eligible version '{eligible_ver_obj['version']}'.{Colors.ENDC}"
                    )
            else:
                latest_ver_str = latest_ver_obj["version"]
                print(
                    f"{Colors.YELLOW}Warning: Latest version '{latest_ver_str}' of '{full_id}' is held back by minimum release age policy, and no older compatible release was found.{Colors.ENDC}"
                )
                if not ctx.yes and sys.stdin.isatty():
                    if prompt_yes_no(
                        f"Install held-back version '{latest_ver_str}' anyway?"
                    ):
                        selected_ver_obj = latest_ver_obj
                    else:
                        print(f"Skipping '{full_id}'.")
                        continue
                else:
                    print(
                        f"{Colors.RED}Skipping '{full_id}' (held back by release age requirement). Use --min-release-age 0 to override.{Colors.ENDC}"
                    )
                    failures.append(full_id)
                    continue

        target_version = selected_ver_obj["version"]
        installed_ver = installed_exts.get(full_id)
        force = getattr(args, "force", False)

        if installed_ver and not force and not req_ver:
            parsed_installed = parse_version(installed_ver)
            parsed_target = parse_version(target_version)
            if parsed_installed == parsed_target:
                print(
                    f"  {Colors.GREEN}✓ Extension '{full_id}' is already installed at version v{installed_ver} (latest eligible version). Skipping.{Colors.ENDC}"
                )
                continue
            elif parsed_installed > parsed_target:
                print(
                    f"  {Colors.GREEN}✓ Extension '{full_id}' is already installed at newer version v{installed_ver} (eligible version is v{target_version}). Skipping.{Colors.ENDC}"
                )
                continue

        target_plat = selected_ver_obj.get("targetPlatform") or "universal"
        url = get_vsix_download_url(
            selected_ver_obj,
            pub_name,
            ext_name,
            target_version,
            target_plat,
            ctx.service_url,
        )
        filename = vsix_filename(pub_name, ext_name, target_version, target_plat)
        filepath = os.path.join(download_dir_resolved, filename)

        # Downgrading to an older version needs --force, just like a
        # re-install of the same version does.
        installed_ok = download_and_install(
            ctx.code_binary,
            url,
            filepath,
            full_id,
            target_version,
            target_plat,
            token=ctx.token,
            service_url=ctx.service_url,
            force=force
            or bool(
                installed_ver
                and parse_version(installed_ver) > parse_version(target_version)
            ),
            cleanup=download_dir_is_temp,
        )
        if not installed_ok:
            failures.append(full_id)

    discard_download_dir(download_dir_resolved, download_dir_is_temp)

    if failures:
        print(
            f"{Colors.RED}✗ {len(failures)} of the requested extension(s) failed to install.{Colors.ENDC}",
            file=sys.stderr,
        )
        sys.exit(1)


def check_updates(
    installed_exts,
    target_platform,
    vscode_version=None,
    include_prerelease=False,
    min_release_age=None,
    extensions_config=None,
    cli_include_prerelease_override=False,
    cli_min_release_age_override=False,
    service_url=DEFAULT_SERVICE_URL,
    token=None,
):
    ext_ids = list(installed_exts.keys())
    if extensions_config:
        ext_ids = [
            eid
            for eid in ext_ids
            if not extensions_config.get(eid.lower(), {}).get("ignore", False)
        ]

    marketplace_data = query_marketplace_extensions(
        ext_ids, service_url=service_url, token=token
    )
    updates = []

    for full_id, ext in marketplace_data.items():
        pub_name = ext.get("publisher", {}).get("publisherName", "")
        ext_name = ext.get("extensionName", "")
        installed_ver = installed_exts.get(full_id)
        if not installed_ver:
            continue

        ext_cfg = extensions_config.get(full_id, {}) if extensions_config else {}
        skipped_versions = ext_cfg.get("skip_versions", [])
        eff_include_prerelease, eff_min_age, _ = effective_ext_options(
            ext_cfg,
            include_prerelease,
            min_release_age,
            cli_include_prerelease_override=cli_include_prerelease_override,
            cli_min_release_age_override=cli_min_release_age_override,
        )

        compatible_versions = filter_versions(
            ext.get("versions", []),
            target_platform,
            vscode_version=vscode_version,
            include_prerelease=eff_include_prerelease,
            skip_versions=skipped_versions,
            newer_than=installed_ver,
        )

        if not compatible_versions:
            continue

        latest_ver_obj = compatible_versions[0]
        latest_version = latest_ver_obj["version"]

        if parse_version(latest_version) > parse_version(installed_ver):
            eligible_ver_obj = first_eligible_version(compatible_versions, eff_min_age)

            last_updated = latest_ver_obj.get("lastUpdated", "")
            latest_release_date = (
                last_updated[:10] if len(last_updated) >= 10 else last_updated
            )

            eligible_version = None
            eligible_release_date = ""
            eligible_platform = "universal"

            if eligible_ver_obj:
                el_ver = eligible_ver_obj["version"]
                if parse_version(el_ver) > parse_version(installed_ver):
                    eligible_version = el_ver
                    el_updated = eligible_ver_obj.get("lastUpdated", "")
                    eligible_release_date = (
                        el_updated[:10] if len(el_updated) >= 10 else el_updated
                    )
                    eligible_platform = (
                        eligible_ver_obj.get("targetPlatform") or "universal"
                    )

            latest_download_url = get_vsix_download_url(
                latest_ver_obj,
                pub_name,
                ext_name,
                latest_version,
                latest_ver_obj.get("targetPlatform"),
                service_url,
            )
            eligible_download_url = (
                get_vsix_download_url(
                    eligible_ver_obj,
                    pub_name,
                    ext_name,
                    eligible_version,
                    eligible_platform,
                    service_url,
                )
                if eligible_ver_obj
                else None
            )

            updates.append(
                {
                    "id": full_id,
                    "publisher": pub_name,
                    "name": ext_name,
                    "installed": installed_ver,
                    "latest": latest_version,
                    "latest_release_date": latest_release_date,
                    "latest_platform": latest_ver_obj.get("targetPlatform")
                    or "universal",
                    "latest_download_url": latest_download_url,
                    "eligible": eligible_version,
                    "eligible_release_date": eligible_release_date,
                    "eligible_platform": eligible_platform,
                    "eligible_download_url": eligible_download_url,
                }
            )

    updates.sort(key=lambda u: u["id"])
    return updates


def print_updates_table(updates):
    widths = (45, 12, 12, 12, 15, 12)
    print(
        f"{Colors.BOLD}{fit_column('Extension ID', 45)} {fit_column('Installed', 12)} {fit_column('Eligible', 12)} {fit_column('Latest', 12)} {fit_column('Release Date', 15)} {fit_column('Platform', 12)}{Colors.ENDC}"
    )
    print("-" * (sum(widths) + len(widths) - 1))
    for update in updates:
        eligible_str = (
            f"{Colors.GREEN}{fit_column(update['eligible'], 12)}{Colors.ENDC}"
            if update["eligible"]
            else f"{Colors.YELLOW}{fit_column('held back', 12)}{Colors.ENDC}"
        )
        print(
            f"{Colors.CYAN}{fit_column(update['id'], 45)}{Colors.ENDC} "
            f"{Colors.YELLOW}{fit_column(update['installed'], 12)}{Colors.ENDC} "
            f"{eligible_str} "
            f"{Colors.BLUE}{fit_column(update['latest'], 12)}{Colors.ENDC} "
            f"{fit_column(update['latest_release_date'], 15)} "
            f"{fit_column(update['eligible_platform'] or update['latest_platform'], 12)}"
        )


def run_list_picker(
    count,
    layout,
    header,
    row,
    actions,
    unit_label,
    selected=None,
    cursor_idx=0,
    top=0,
    toggle_all=None,
    extra_keys=(),
):
    """Drive a scrollable checkbox list until the user commits or leaves.

    Shared by the update, removal and search screens, which differ only in their
    columns, action bar and what a commit means. layout(cols) returns the column
    widths for the current terminal plus the total row width; header and row
    render with those widths. Returns (action, selected, cursor_idx, top) where
    action is "confirm", "quit", or whichever of extra_keys was pressed, so the
    caller can act and, if it wants, resume with the same selection and the same
    stretch of the list on screen.
    """
    if count <= 0:
        # Nothing to show. The window height is clamped to at least one row, so
        # rendering would index an empty list and the cursor arithmetic would
        # divide by zero.
        return "quit", [], 0, 0

    if selected is None:
        selected = [False] * count
    first_frame = True
    prev_lines = 0

    sys.stdout.write("\033[?25l")
    sys.stdout.flush()
    try:
        while True:
            cols, rows = shutil.get_terminal_size((80, 24))
            widths, row_width = layout(cols)
            lines_per_row = max(1, -(-row_width // cols))
            win = max(1, min(count, (rows - 5) // lines_per_row))

            if cursor_idx < top:
                top = cursor_idx
            elif cursor_idx >= top + win:
                top = cursor_idx - win + 1
            top = max(0, min(top, max(0, count - win)))

            out = [
                format_action_bar(actions),
                header(widths),
                "-" * min(cols, row_width),
            ]
            for i in range(top, top + win):
                out.append(row(i, widths, i == cursor_idx, selected[i]))

            status = (
                f"[{top + 1}-{top + win}/{count}]  (scroll with \u2191/\u2193)"
                if win < count
                else f"[{count} {unit_label}{'s' if count != 1 else ''}]"
            )
            out.append(f"{Colors.BOLD}{status}{Colors.ENDC}")

            if not first_frame:
                if prev_lines > 1:
                    sys.stdout.write(f"\r\033[{prev_lines - 1}A")
                else:
                    sys.stdout.write("\r")
                sys.stdout.write("\033[J")
            else:
                first_frame = False

            prev_lines = sum(max(1, -(-display_width(line) // cols)) for line in out)

            sys.stdout.write("\n".join(out))
            sys.stdout.flush()

            key = get_key()
            if key in extra_keys:
                return key, selected, cursor_idx, top
            # None means stdin gave EOF (terminal went away); treat it as cancel
            # rather than looping on a dead descriptor.
            if key is None or key in ("ctrl+c", "esc", "q", "Q"):
                return "quit", selected, cursor_idx, top
            elif key == "up":
                cursor_idx = (cursor_idx - 1) % count
            elif key == "down":
                cursor_idx = (cursor_idx + 1) % count
            elif key == "space":
                selected[cursor_idx] = not selected[cursor_idx]
            elif key in ("a", "A"):
                if any(selected):
                    selected = [False] * count
                else:
                    selected = toggle_all() if toggle_all else [True] * count
            elif key == "enter":
                return "confirm", selected, cursor_idx, top
    finally:
        sys.stdout.write("\n\033[?25h")
        sys.stdout.flush()


def select_updates(updates, action_label="Install"):
    if not HAS_TTY or not sys.stdin.isatty() or not sys.stdout.isatty():
        return updates

    n = len(updates)
    W_VER, W_DATE, W_PLAT = 12, 12, 12
    OVERHEAD = 6 + 1 + (W_VER + 1) * 3 + (W_DATE + 1) + W_PLAT + 1

    def layout(cols):
        id_w = max(12, cols - OVERHEAD)
        return {"id": id_w}, OVERHEAD + id_w

    def header(widths):
        return (
            f"{Colors.BOLD}{'':6}{fit_column('Extension ID', widths['id'])} {fit_column('Installed', W_VER)} "
            f"{fit_column('Eligible', W_VER)} {fit_column('Latest', W_VER)} {fit_column('Release', W_DATE)} {fit_column('Platform', W_PLAT)}{Colors.ENDC}"
        )

    def row(i, widths, is_cursor, is_selected):
        update = updates[i]
        prefix = ">" if is_cursor else " "
        if update["eligible"]:
            mark = f"{Colors.GREEN}x{Colors.ENDC}" if is_selected else " "
            eligible_str = (
                f"{Colors.GREEN}{fit_column(update['eligible'], W_VER)}{Colors.ENDC}"
            )
        else:
            mark = f"{Colors.YELLOW}!{Colors.ENDC}" if is_selected else " "
            eligible_str = (
                f"{Colors.YELLOW}{fit_column('held back', W_VER)}{Colors.ENDC}"
            )
        return (
            f"{prefix} [{mark}] {Colors.CYAN}{fit_column(update['id'], widths['id'])}{Colors.ENDC} "
            f"{Colors.YELLOW}{fit_column(update['installed'], W_VER)}{Colors.ENDC} "
            f"{eligible_str} "
            f"{Colors.BLUE}{fit_column(update['latest'], W_VER)}{Colors.ENDC} "
            f"{fit_column(update['latest_release_date'], W_DATE)} "
            f"{fit_column(update['eligible_platform'] or update['latest_platform'], W_PLAT)}"
        )

    eligible_mask = [bool(u["eligible"]) for u in updates]
    try:
        action, selected, _cursor, _top = run_list_picker(
            n,
            layout,
            header,
            row,
            [
                ("Space", "Toggle", Colors.CYAN),
                ("a", "Toggle All", Colors.CYAN),
                ("\u2191/\u2193", "Move", Colors.CYAN),
                ("Enter", action_label, Colors.GREEN),
                ("q/Esc", "Exit", Colors.RED),
            ],
            "update",
            selected=list(eligible_mask),
            toggle_all=lambda: list(eligible_mask),
        )
    except KeyboardInterrupt:
        action = "quit"

    if action == "quit":
        print("Selection cancelled.")
        sys.exit(0)

    chosen = []
    for i in range(n):
        if selected[i]:
            update = updates[i]
            if not update["eligible"]:
                update["eligible"] = update["latest"]
                update["eligible_platform"] = update["latest_platform"]
                update["eligible_release_date"] = update["latest_release_date"]
                update["eligible_download_url"] = update.get("latest_download_url")
            chosen.append(update)
    return chosen


def resolve_installed_targets(specs, installed_exts, exact_name=False):
    """Resolve user-supplied specs to a subset of installed extensions.

    Accepts full IDs (``publisher.name``) or partial names (matched as a
    case-insensitive substring against installed IDs, mirroring ``info``).
    With ``exact_name`` a partial must equal the extension name (the part
    after the publisher) rather than merely appear inside the ID, which
    ``remove`` uses since a loose substring hit could delete the wrong
    extension. Returns a dict of the matched installed extensions; unresolved
    or ambiguous specs are reported and skipped.
    """
    resolved = {}
    for spec in specs:
        s = spec.strip().lower()
        if "@" in s:
            s = s.split("@")[0]
        if not s:
            continue
        if s in installed_exts:
            resolved[s] = installed_exts[s]
            continue
        if exact_name:
            matches = sorted(
                eid for eid in installed_exts if eid.split(".", 1)[-1] == s
            )
        else:
            matches = sorted(eid for eid in installed_exts if s in eid)
            # Disambiguate a partial that hits several IDs by preferring one
            # whose extension name (the part after the publisher) matches
            # exactly, e.g. 'python' -> 'ms-python.python' rather than
            # 'ms-python.debugpy'.
            if len(matches) > 1:
                exact_name_hit = [eid for eid in matches if eid.split(".", 1)[-1] == s]
                if len(exact_name_hit) == 1:
                    matches = exact_name_hit
        if len(matches) == 1:
            match = matches[0]
            print(
                f"{Colors.YELLOW}Notice: '{spec}' is not a full extension ID. Resolving to installed match '{match}'.{Colors.ENDC}"
            )
            resolved[match] = installed_exts[match]
        elif len(matches) > 1:
            print(
                f"{Colors.YELLOW}Notice: '{spec}' matches multiple installed extensions; be more specific:{Colors.ENDC}"
            )
            for m in matches:
                print(f"    {m}")
        else:
            print(
                f"{Colors.RED}✗ '{spec}' is not installed; skipping.{Colors.ENDC}",
                file=sys.stderr,
            )
    return resolved


def handle_update(args, config):
    ctx = ExecutionContext(args, config)
    dry_run = bool(getattr(args, "dry_run", None))

    print(f"{Colors.BLUE}Fetching installed VS Code extensions...{Colors.ENDC}")
    installed_exts = get_installed_extensions(ctx.code_binary)
    if not installed_exts:
        print("No extensions found installed.")
        return

    target_specs = list(getattr(args, "extensions", None) or [])
    if target_specs:
        installed_exts = resolve_installed_targets(target_specs, installed_exts)
        if not installed_exts:
            print("No matching installed extensions to update.")
            return
        print(f"Checking {len(installed_exts)} selected extension(s) for updates.")
    else:
        print(f"Found {len(installed_exts)} extensions installed.")
    print(
        f"{Colors.BLUE}Checking updates (including pre-releases: {ctx.include_prerelease})...{Colors.ENDC}"
    )

    cli_min_release_age_override = args.min_release_age is not None
    updates = check_updates(
        installed_exts,
        ctx.target_platform,
        vscode_version=ctx.vscode_version,
        include_prerelease=ctx.include_prerelease,
        min_release_age=ctx.min_release_age,
        extensions_config=ctx.extensions_config,
        cli_include_prerelease_override=bool(getattr(args, "include_prerelease", None)),
        cli_min_release_age_override=cli_min_release_age_override,
        service_url=ctx.service_url,
        token=ctx.token,
    )

    print()
    if not updates:
        print(f"{Colors.GREEN}All extensions are up to date!{Colors.ENDC}")
        return

    if ctx.yes:
        print(f"{Colors.GREEN}{Colors.BOLD}Updates available:{Colors.ENDC}")
        print_updates_table(updates)
        print()
        eligible_updates = [u for u in updates if u["eligible"]]
        if not eligible_updates:
            print(
                f"{Colors.YELLOW}All available updates are held back by minimum release age policy; nothing to install.{Colors.ENDC}"
            )
            return
        selected_updates = eligible_updates
    elif HAS_TTY and sys.stdin.isatty() and sys.stdout.isatty():
        selected_updates = select_updates(
            updates, action_label="Dry Run" if dry_run else "Install"
        )
        if not selected_updates:
            print(
                "No updates selected for dry run."
                if dry_run
                else "No updates selected for installation."
            )
            return
    else:
        print(f"{Colors.GREEN}{Colors.BOLD}Updates available:{Colors.ENDC}")
        print_updates_table(updates)
        selected_updates = [u for u in updates if u["eligible"]]
        # Without a terminal there is nobody to confirm the selection, so stop at
        # the report rather than installing everything unattended. A dry run
        # changes nothing, so it can still list what an install would pick up.
        if not dry_run:
            print(
                f"\n{Colors.YELLOW}Not a terminal: no updates were installed. "
                f"Re-run with -y to install them.{Colors.ENDC}"
            )
            return

    if dry_run:
        print()
        print(
            f"{Colors.YELLOW}{Colors.BOLD}[Dry-run] Would update {len(selected_updates)} extension(s):{Colors.ENDC}"
        )
        for update in selected_updates:
            version = update["eligible"]
            platform = update["eligible_platform"]
            print(
                f"  {Colors.CYAN}{update['id']}{Colors.ENDC}: {Colors.YELLOW}{update['installed']}{Colors.ENDC} -> {Colors.GREEN}{version}{Colors.ENDC} ({platform})"
            )
            print(f"    Download URL: {resolve_update_url(update, ctx.service_url)}")
        print(
            f"\n{Colors.YELLOW}[Dry-run] No extensions were downloaded or installed.{Colors.ENDC}"
        )
        return

    download_dir_resolved, download_dir_is_temp = resolve_download_target(args, config)

    for update in selected_updates:
        pub_name = update["publisher"]
        ext_name = update["name"]
        version = update["eligible"]
        platform = update["eligible_platform"]
        url = resolve_update_url(update, ctx.service_url)
        filepath = os.path.join(
            download_dir_resolved, vsix_filename(pub_name, ext_name, version, platform)
        )

        download_and_install(
            ctx.code_binary,
            url,
            filepath,
            update["id"],
            version,
            platform,
            token=ctx.token,
            service_url=ctx.service_url,
            cleanup=download_dir_is_temp,
        )

    discard_download_dir(download_dir_resolved, download_dir_is_temp)


def select_removals(installed_exts):
    if not HAS_TTY or not sys.stdin.isatty() or not sys.stdout.isatty():
        return []

    ext_list = sorted(installed_exts.items(), key=lambda x: x[0])
    n = len(ext_list)
    if n == 0:
        return []

    W_VER = 15
    OVERHEAD = 6 + 1 + W_VER + 1

    def layout(cols):
        id_w = max(12, cols - OVERHEAD)
        return {"id": id_w}, OVERHEAD + id_w

    def header(widths):
        return (
            f"{Colors.BOLD}{'':6}{fit_column('Extension ID', widths['id'])} "
            f"{fit_column('Version', W_VER)}{Colors.ENDC}"
        )

    def row(i, widths, is_cursor, is_selected):
        ext_id, ver = ext_list[i]
        prefix = ">" if is_cursor else " "
        mark = f"{Colors.RED}x{Colors.ENDC}" if is_selected else " "
        return (
            f"{prefix} [{mark}] {Colors.CYAN}{fit_column(ext_id, widths['id'])}{Colors.ENDC} "
            f"{Colors.YELLOW}{fit_column(ver, W_VER)}{Colors.ENDC}"
        )

    try:
        action, selected, _cursor, _top = run_list_picker(
            n,
            layout,
            header,
            row,
            [
                ("Space", "Toggle", Colors.CYAN),
                ("a", "Toggle All", Colors.CYAN),
                ("\u2191/\u2193", "Move", Colors.CYAN),
                ("Enter", "Uninstall", Colors.RED),
                ("q/Esc", "Exit", Colors.YELLOW),
            ],
            "extension",
        )
    except KeyboardInterrupt:
        action = "quit"

    if action == "quit":
        print("Removal selection cancelled.")
        sys.exit(0)

    return [ext_list[i][0] for i in range(n) if selected[i]]


def handle_remove(args, config):
    ctx = ExecutionContext(args, config)

    installed_exts = get_installed_extensions(ctx.code_binary)
    if not installed_exts:
        print("No extensions found installed.")
        return

    targets = []
    if args.extensions:
        # Resolve partial names to exact extension IDs so 'remove python' can
        # target ms-python.python. Unlike 'update'/'info' the match must equal
        # the extension name, not merely appear inside the ID: removing the
        # wrong extension is not recoverable. Unknown or ambiguous specs are
        # reported as a side effect; a full ID and a partial name that
        # resolves to it collapse onto one dict key.
        targets = list(
            resolve_installed_targets(args.extensions, installed_exts, exact_name=True)
        )
        if not targets:
            print("No matching installed extensions to remove.")
            return
    else:
        if HAS_TTY and sys.stdin.isatty() and sys.stdout.isatty():
            targets = select_removals(installed_exts)
            if not targets:
                print("No extensions selected for removal.")
                return
        else:
            print(
                f"{Colors.RED}Error: Standard input is non-interactive. Please specify extension ID(s) to remove.{Colors.ENDC}",
                file=sys.stderr,
            )
            sys.exit(1)

    print(f"\n{Colors.RED}{Colors.BOLD}Extensions to remove:{Colors.ENDC}")
    for t in targets:
        print(f"  - {t} (v{installed_exts.get(t, 'unknown')})")

    if not ctx.yes and not prompt_yes_no(
        f"Are you sure you want to remove {len(targets)} extension(s)?",
        default=False,
    ):
        print("Removal cancelled.")
        return

    for ext_id in targets:
        print(f"Removing {Colors.CYAN}{ext_id}{Colors.ENDC}...")
        try:
            run_code_cmd([*ctx.code_binary, "--uninstall-extension", ext_id], retries=0)
            print(f"  {Colors.GREEN}✓{Colors.ENDC} Removed successfully.")
        except subprocess.CalledProcessError as e:
            print(
                f"  {Colors.RED}✗ Removal failed: {e.stderr.strip() or e}{Colors.ENDC}",
                file=sys.stderr,
            )
        # run_code_cmd raises OSError when the binary is missing or unexecutable.
        except OSError as e:
            print(f"  {Colors.RED}✗ Removal failed: {e}{Colors.ENDC}", file=sys.stderr)


def handle_list(args, config):
    ctx = ExecutionContext(args, config)
    installed_exts = get_installed_extensions(ctx.code_binary)

    if not installed_exts:
        print("No extensions found installed.")
        return

    ext_items = sorted(installed_exts.items(), key=lambda x: x[0])

    if args.query:
        q = args.query.strip().lower()
        ext_items = [item for item in ext_items if q in item[0]]

    if args.outdated:
        filtered_dict = dict(ext_items)
        updates = check_updates(
            filtered_dict,
            ctx.target_platform,
            vscode_version=ctx.vscode_version,
            include_prerelease=ctx.include_prerelease,
            min_release_age=ctx.min_release_age,
            extensions_config=ctx.extensions_config,
            cli_include_prerelease_override=bool(
                getattr(args, "include_prerelease", None)
            ),
            cli_min_release_age_override=getattr(args, "min_release_age", None)
            is not None,
            service_url=ctx.service_url,
            token=ctx.token,
        )
        update_ids = {u["id"]: u for u in updates}
        ext_items = [item for item in ext_items if item[0] in update_ids]

        if args.quiet:
            for ext_id, _ in ext_items:
                print(ext_id)
            return

        if not ext_items:
            print(f"{Colors.GREEN}All extensions are up to date!{Colors.ENDC}")
            return

        print(
            f"{Colors.BOLD}{fit_column('Extension ID', 45)} {fit_column('Installed', 15)} {fit_column('Latest', 15)}{Colors.ENDC}"
        )
        print("-" * 77)
        for ext_id, installed_ver in ext_items:
            up_info = update_ids[ext_id]
            latest_str = up_info["latest"]
            print(
                f"{Colors.CYAN}{fit_column(ext_id, 45)}{Colors.ENDC} {Colors.YELLOW}{fit_column(installed_ver, 15)}{Colors.ENDC} {Colors.GREEN}{fit_column(latest_str, 15)}{Colors.ENDC}"
            )
        return

    if args.quiet:
        for ext_id, _ in ext_items:
            print(ext_id)
        return

    print(
        f"{Colors.BOLD}{fit_column('Extension ID', 45)} {fit_column('Version', 15)}{Colors.ENDC}"
    )
    print("-" * (45 + 1 + 15))
    for ext_id, ver in ext_items:
        print(
            f"{Colors.CYAN}{fit_column(ext_id, 45)}{Colors.ENDC} {Colors.YELLOW}{fit_column(ver, 15)}{Colors.ENDC}"
        )
    print(f"\nTotal: {len(ext_items)} extension(s)")


def show_search_item_info(item, config, args):
    info_args = argparse.Namespace(
        extension=item["id"],
        code_binary=getattr(args, "code_binary", None),
        service_url=getattr(args, "service_url", None),
        open_vsx=getattr(args, "open_vsx", None),
        open_vsx_token=getattr(args, "open_vsx_token", None),
        min_release_age=getattr(args, "min_release_age", None),
        include_prerelease=getattr(args, "include_prerelease", None),
        no_code_version_check=getattr(args, "no_code_version_check", None),
    )

    sys.stdout.write("\033[2J\033[H")
    sys.stdout.flush()
    handle_info(info_args, config)

    print(
        format_action_bar(
            [
                ("i/Enter", "Install", Colors.GREEN),
                ("b/Esc", "Back to Search Results", Colors.YELLOW),
                ("q", "Exit", Colors.RED),
            ]
        )
    )

    while True:
        key = get_key()
        if key is None or key in ("q", "Q", "ctrl+c"):
            return "exit"
        if key in ("i", "I", "enter"):
            return "install"
        elif key in ("b", "B", "esc", "backspace"):
            sys.stdout.write("\033[2J\033[H")
            sys.stdout.flush()
            return "back"


def install_search_items(ext_ids, config, args):
    print(
        f"\n{Colors.GREEN}{Colors.BOLD}Installing selected extension(s):{Colors.ENDC} {', '.join(ext_ids)}\n"
    )
    install_args = argparse.Namespace(
        extensions=ext_ids,
        file=None,
        include_prerelease=getattr(args, "include_prerelease", False),
        no_code_version_check=getattr(args, "no_code_version_check", False),
        download_dir=getattr(args, "download_dir", None),
        yes=True,
        min_release_age=getattr(args, "min_release_age", None),
        force=False,
        code_binary=getattr(args, "code_binary", None),
        service_url=getattr(args, "service_url", None),
        open_vsx=getattr(args, "open_vsx", None),
        open_vsx_token=getattr(args, "open_vsx_token", None),
    )
    handle_install(install_args, config)


def interactive_search_flow(search_results, config, args, installed_exts=None):
    if not HAS_TTY or not sys.stdin.isatty() or not sys.stdout.isatty():
        return

    n = len(search_results)
    if n == 0:
        return

    if installed_exts is None:
        code_binary = parse_code_binary(
            resolve_option(args.code_binary, config, "code_binary", "code")
        )
        installed_exts = get_installed_extensions(code_binary, ignore_errors=True)

    W_VER = 12
    W_NAME = 25
    OVERHEAD = 6 + 1 + (W_NAME + 1) + (W_VER + 1) + 1
    max_id_len = max((display_width(res["id"]) for res in search_results), default=35)

    def layout(cols):
        avail = max(20, cols - OVERHEAD)
        id_w = max(12, min(max_id_len, max(35, avail // 3)))
        desc_w = max(10, cols - OVERHEAD - id_w)
        return {"id": id_w, "desc": desc_w}, OVERHEAD + id_w + desc_w

    def header(widths):
        return (
            f"{Colors.BOLD}{'':6}{fit_column('Extension ID', widths['id'])} {fit_column('Display Name', W_NAME)} "
            f"{fit_column('Eligible', W_VER)} {fit_column('Description', widths['desc'])}{Colors.ENDC}"
        )

    def row(i, widths, is_cursor, is_selected):
        res = search_results[i]
        prefix = ">" if is_cursor else " "
        mark = f"{Colors.GREEN}x{Colors.ENDC}" if is_selected else " "
        ver_color = Colors.YELLOW if res["is_held_back"] else Colors.GREEN
        is_installed = res["id"].lower() in installed_exts
        id_color = Colors.GREEN if is_installed else Colors.CYAN
        return (
            f"{prefix} [{mark}] {id_color}{fit_column(res['id'], widths['id'])}{Colors.ENDC} "
            f"{Colors.BOLD}{fit_column(res['displayName'], W_NAME)}{Colors.ENDC} "
            f"{ver_color}{fit_column(res['eligible'], W_VER)}{Colors.ENDC} "
            f"{fit_column(res['description'], widths['desc'])}"
        )

    actions = [
        ("Space", "Toggle", Colors.CYAN),
        ("a", "Toggle All", Colors.CYAN),
        ("\u2191/\u2193", "Move", Colors.CYAN),
        ("Enter", "View Info", Colors.GREEN),
        ("i", "Install", Colors.GREEN),
        ("q/Esc", "Exit", Colors.RED),
    ]

    selected = [False] * n
    cursor_idx = 0
    # Carried across the detail view so returning to the list shows the same
    # window rather than scrolling the cursor's row to the bottom.
    top = 0
    try:
        while True:
            action, selected, cursor_idx, top = run_list_picker(
                n,
                layout,
                header,
                row,
                actions,
                "result",
                selected=selected,
                cursor_idx=cursor_idx,
                top=top,
                extra_keys=("enter", "i", "I"),
            )
            if action == "quit":
                return
            if action in ("i", "I"):
                to_install = [
                    search_results[i]["id"] for i in range(n) if selected[i]
                ] or [search_results[cursor_idx]["id"]]
                install_search_items(to_install, config, args)
                return
            # Enter opens the detail view, which can hand back to the list.
            outcome = show_search_item_info(search_results[cursor_idx], config, args)
            if outcome == "exit":
                return
            if outcome == "install":
                install_search_items([search_results[cursor_idx]["id"]], config, args)
                return
    except KeyboardInterrupt:
        return


def handle_search(args, config):
    ctx = ExecutionContext(args, config)

    if not args.quiet:
        print(
            f"{Colors.BLUE}Searching extension gallery for '{args.query}'...{Colors.ENDC}"
        )
    results = query_marketplace_search(
        args.query,
        max_results=args.max_results,
        target_platform=ctx.target_platform,
        vscode_version=ctx.vscode_version,
        include_prerelease=ctx.include_prerelease,
        min_release_age=ctx.min_release_age,
        extensions_config=ctx.extensions_config,
        cli_include_prerelease_override=bool(getattr(args, "include_prerelease", None)),
        cli_min_release_age_override=getattr(args, "min_release_age", None) is not None,
        service_url=ctx.service_url,
        token=ctx.token,
    )

    if not results:
        print(f"No extensions found matching '{args.query}'.")
        return

    # Quiet output is just the ids, so it never reaches VS Code - and it is the
    # form that gets piped into another command, where spawning the editor to
    # answer a question nobody asked is pure latency.
    if args.quiet:
        for r in results:
            print(r["id"])
        return

    installed_exts = get_installed_extensions(ctx.code_binary, ignore_errors=True)

    if HAS_TTY and sys.stdin.isatty() and sys.stdout.isatty():
        interactive_search_flow(results, config, args, installed_exts=installed_exts)
        return

    max_id_len = max((display_width(r["id"]) for r in results), default=35)
    W_NAME = 25
    W_VER = 12
    cols, _ = shutil.get_terminal_size((100, 24))
    avail = max(20, cols - 4 - W_NAME - W_VER)
    W_ID = max(12, min(max_id_len, max(35, avail // 3)))
    W_DESC = max(10, cols - W_ID - W_NAME - W_VER - 4)

    print(
        f"\n{Colors.BOLD}{fit_column('Extension ID', W_ID)} {fit_column('Display Name', W_NAME)} {fit_column('Eligible', W_VER)} {fit_column('Description', W_DESC)}{Colors.ENDC}"
    )
    print("-" * min(cols, W_ID + W_NAME + W_VER + W_DESC + 4))

    for r in results:
        ver_color = Colors.YELLOW if r["is_held_back"] else Colors.GREEN
        is_installed = r["id"].lower() in installed_exts
        id_color = Colors.GREEN if is_installed else Colors.CYAN
        print(
            f"{id_color}{fit_column(r['id'], W_ID)}{Colors.ENDC} "
            f"{Colors.BOLD}{fit_column(r['displayName'], W_NAME)}{Colors.ENDC} "
            f"{ver_color}{fit_column(r['eligible'], W_VER)}{Colors.ENDC} "
            f"{fit_column(r['description'], W_DESC)}"
        )

    print(f"\nFound {len(results)} matching extension(s).")


def handle_info(args, config):
    ctx = ExecutionContext(args, config)

    ext_id = args.extension.strip().lower()
    if "@" in ext_id:
        ext_id = ext_id.split("@")[0].strip()

    # Anything that is not a well-formed id is treated as a search term, so a
    # malformed one falls back to the gallery search rather than being sent
    # straight to a by-id query that can only answer 'not found'.
    if not is_valid_extension_id(ext_id):
        print(
            f"{Colors.BLUE}Searching extension gallery for '{ext_id}'...{Colors.ENDC}"
        )
        search_results = query_marketplace_search(
            ext_id, max_results=5, service_url=ctx.service_url, token=ctx.token
        )
        if not search_results:
            print(
                f"{Colors.RED}✗ Extension '{ext_id}' not found on extension gallery.{Colors.ENDC}",
                file=sys.stderr,
            )
            sys.exit(1)
        best_match = search_results[0]["id"]
        print(
            f"{Colors.YELLOW}Notice: '{args.extension}' is not a full extension ID. Showing info for top match '{best_match}'.{Colors.ENDC}\n"
        )
        ext_id = best_match

    print(f"{Colors.BLUE}Fetching extension metadata for '{ext_id}'...{Colors.ENDC}")
    marketplace_data = query_marketplace_extensions(
        [ext_id], service_url=ctx.service_url, token=ctx.token
    )
    ext_obj = marketplace_data.get(ext_id)

    if not ext_obj:
        print(
            f"{Colors.RED}✗ Extension '{ext_id}' not found on extension gallery.{Colors.ENDC}",
            file=sys.stderr,
        )
        sys.exit(1)

    pub_name = ext_obj.get("publisher", {}).get("publisherName", "")
    pub_disp = ext_obj.get("publisher", {}).get("displayName") or pub_name
    ext_name = ext_obj.get("extensionName", "")
    full_id = f"{pub_name}.{ext_name}".lower()
    display_name = ext_obj.get("displayName") or ext_name
    description = ext_obj.get("shortDescription") or "No description provided."

    versions = ext_obj.get("versions", [])

    ext_cfg = ctx.extensions_config.get(full_id, {})
    skipped_versions = ext_cfg.get("skip_versions", [])
    eff_include_prerelease, eff_min_age, _ = effective_ext_options(
        ext_cfg,
        ctx.include_prerelease,
        ctx.min_release_age,
        cli_include_prerelease_override=bool(getattr(args, "include_prerelease", None)),
        cli_min_release_age_override=getattr(args, "min_release_age", None) is not None,
    )

    # Same eligibility filter as install/search/update, so what `info` reports as
    # eligible is what those commands would actually pick.
    compatible_versions = filter_versions(
        versions,
        ctx.target_platform,
        vscode_version=ctx.vscode_version,
        include_prerelease=eff_include_prerelease,
        skip_versions=skipped_versions,
    )

    latest_ver = "unknown"
    eligible_ver = "unknown"
    is_held_back = False
    latest_ver_obj = None

    if compatible_versions:
        latest_ver_obj = compatible_versions[0]
        latest_ver = latest_ver_obj["version"]
        eligible_ver_obj = first_eligible_version(compatible_versions, eff_min_age)
        if eligible_ver_obj:
            eligible_ver = eligible_ver_obj["version"]
            is_held_back = eligible_ver != latest_ver
        else:
            eligible_ver = "held back"
            is_held_back = True
    elif versions:
        # Nothing compatible with this host; still report the newest published
        # version so the user sees what exists, but flag it as ineligible.
        latest_ver_obj = versions[0]
        latest_ver = latest_ver_obj.get("version", "unknown")
        eligible_ver = "incompatible"
        is_held_back = True

    last_updated = latest_ver_obj.get("lastUpdated", "") if latest_ver_obj else ""
    release_date = last_updated[:10] if len(last_updated) >= 10 else last_updated

    categories = ext_obj.get("categories", [])
    cat_str = ", ".join(categories) if categories else "None"

    # Almost everything reported here is gallery metadata, so a missing or
    # broken 'code' binary costs the installed-version line, not the command.
    installed_exts, installed_error = query_installed_extensions(ctx.code_binary)
    installed_ver = installed_exts.get(full_id)
    if installed_error:
        installed_status = f"{Colors.YELLOW}Unknown (cannot query VS Code){Colors.ENDC}"
    elif installed_ver:
        installed_status = f"{Colors.GREEN}Installed (v{installed_ver}){Colors.ENDC}"
    else:
        installed_status = f"{Colors.YELLOW}Not installed{Colors.ENDC}"

    props = latest_ver_obj.get("properties", []) if latest_ver_obj else []
    repo_url = None
    homepage_url = None
    pricing = "Free"
    for p in props:
        k, v = p.get("key"), p.get("value")
        if k == "Microsoft.VisualStudio.Services.Links.Source":
            repo_url = v
        elif k == "Microsoft.VisualStudio.Services.Links.Getstarted":
            homepage_url = v
        elif k == "Microsoft.VisualStudio.Services.Content.Pricing":
            pricing = v

    print(
        f"\n{Colors.BOLD}{Colors.CYAN}{display_name}{Colors.ENDC} ({Colors.BOLD}{full_id}{Colors.ENDC})"
    )
    print("=" * (len(display_name) + len(full_id) + 5))
    print(f"  {Colors.BOLD}Publisher:{Colors.ENDC}   {pub_disp} ({pub_name})")
    print(f"  {Colors.BOLD}Latest Ver:{Colors.ENDC}  v{latest_ver} ({release_date})")
    if is_held_back:
        if eligible_ver == "incompatible":
            el_str = "none"
            note = "no version compatible with this VS Code/platform"
        elif eligible_ver == "held back":
            el_str = "held back"
            note = "held back by min-release-age policy"
        else:
            el_str = f"v{eligible_ver}"
            note = "held back by min-release-age policy"
        print(
            f"  {Colors.BOLD}Eligible Ver:{Colors.ENDC} {Colors.YELLOW}{el_str}{Colors.ENDC} ({Colors.YELLOW}{note}{Colors.ENDC})"
        )
    else:
        print(
            f"  {Colors.BOLD}Eligible Ver:{Colors.ENDC} {Colors.GREEN}v{eligible_ver}{Colors.ENDC} ({Colors.GREEN}latest{Colors.ENDC})"
        )
    print(f"  {Colors.BOLD}Status:{Colors.ENDC}      {installed_status}")
    print(f"  {Colors.BOLD}Pricing:{Colors.ENDC}     {pricing}")
    print(f"  {Colors.BOLD}Categories:{Colors.ENDC}  {cat_str}")
    if repo_url:
        print(f"  {Colors.BOLD}Repository:{Colors.ENDC}  {repo_url}")
    if homepage_url and homepage_url != repo_url:
        print(f"  {Colors.BOLD}Homepage:{Colors.ENDC}    {homepage_url}")
    print(f"\n  {Colors.BOLD}Description:{Colors.ENDC}")
    print(f"    {description}\n")


def dir_size(path):
    total = 0
    for root, _dirs, files in os.walk(path):
        for name in files:
            with contextlib.suppress(OSError):
                total += os.path.getsize(os.path.join(root, name))
    return total


def handle_clean(args, config):
    cache_dir = get_cache_dir()
    temp_dir = tempfile.gettempdir()

    cleaned_files = 0
    freed_bytes = 0

    print(f"{Colors.BLUE}Cleaning cached data and temporary files...{Colors.ENDC}")

    now = time.time()

    if cache_dir and os.path.exists(cache_dir):
        for f in os.listdir(cache_dir):
            if is_cache_file(f):
                fp = os.path.join(cache_dir, f)
                try:
                    # Same one-hour grace period as the temp directory below: a
                    # young .tmp is probably a concurrent run still writing it.
                    if is_cache_temp_file(f) and now - os.path.getmtime(fp) <= 3600:
                        continue
                    size = os.path.getsize(fp)
                    os.remove(fp)
                    cleaned_files += 1
                    freed_bytes += size
                except OSError:
                    pass

    # Download directories left behind by an interrupted run. Anything younger
    # than an hour may belong to a concurrent invocation, so leave it alone.
    if os.path.exists(temp_dir):
        for f in os.listdir(temp_dir):
            if not f.startswith("code-extensions-"):
                continue
            fp = os.path.join(temp_dir, f)
            if not os.path.isdir(fp) or os.path.islink(fp):
                continue
            try:
                if now - os.path.getmtime(fp) <= 3600:
                    continue
                size = dir_size(fp)
                shutil.rmtree(fp)
                cleaned_files += 1
                freed_bytes += size
            except OSError:
                pass

    freed_kb = freed_bytes / 1024.0
    if freed_kb > 1024:
        freed_str = f"{freed_kb / 1024.0:.2f} MB"
    else:
        freed_str = f"{freed_kb:.1f} KB"

    print(
        f"{Colors.GREEN}✓ Cleaned {cleaned_files} file(s) ({freed_str} freed).{Colors.ENDC}"
    )


# --- CLI surface shared with the shell completion scripts --------------------
#
# The completion scripts repeat the subcommand, alias, config-action and shell
# names that argparse also needs. Both sides are generated from these tables, so
# a name added here reaches the parser and all four scripts at once instead of
# silently going missing from one of them.

CliChoice = namedtuple("CliChoice", "name aliases summary")

SUBCOMMANDS = (
    CliChoice("install", (), "Install VS Code extension(s)"),
    CliChoice("update", ("upgrade",), "Check and install updates"),
    CliChoice("remove", ("uninstall", "rm"), "Remove installed extension(s)"),
    CliChoice("list", ("ls",), "List installed extensions"),
    CliChoice("search", (), "Search the extension gallery"),
    CliChoice("info", ("show",), "Show detailed metadata for an extension"),
    CliChoice("clean", (), "Purge the API cache and temporary files"),
    CliChoice("config", (), "View or modify configuration settings"),
    CliChoice("completion", (), "Generate a shell completion script"),
)

CONFIG_ACTIONS = (
    CliChoice("list", (), "List all configuration settings"),
    CliChoice("get", (), "Get a configuration key value"),
    CliChoice("set", (), "Set a configuration key value"),
    CliChoice("unset", ("delete",), "Unset a configuration key"),
)

COMPLETION_SHELLS = ("bash", "fish", "powershell", "zsh")

CANONICAL_SUBCOMMANDS = tuple(c.name for c in SUBCOMMANDS)
SUBCOMMAND_ALIASES = {c.name: list(c.aliases) for c in SUBCOMMANDS}
CONFIG_ACTION_CHOICES = [n for c in CONFIG_ACTIONS for n in (c.name, *c.aliases)]


def subcommand_names(*names):
    """Canonical subcommand names plus their aliases, in registration order."""
    return [n for name in names for n in (name, *SUBCOMMAND_ALIASES[name])]


# Options, with the argparse help text and the shorter summary the completion
# scripts show. `value` is None for switches, else (label, zsh completer).
CliOption = namedtuple("CliOption", "flags help summary value kwargs")


def _switch(flags, help_text, summary, default=None, **kwargs):
    return CliOption(
        flags,
        help_text,
        summary,
        None,
        {"action": "store_true", "default": default, **kwargs},
    )


def _valued(flags, help_text, summary, value, default=None, **kwargs):
    return CliOption(flags, help_text, summary, value, {"default": default, **kwargs})


# argparse adds -h/--help itself; the completion scripts have to offer it.
HELP_OPTION = _switch(("-h", "--help"), "Show help message", "Show help message")

GLOBAL_OPTIONS = (
    _valued(
        ("-b", "--code-binary"),
        "Path to VS Code binary/executable or its fork (default: code)",
        "VS Code executable binary or fork",
        ("binary", "_files"),
    ),
    _valued(
        ("-s", "--service-url"),
        "VS Code Extension Gallery service API URL",
        "VS Code Extension Gallery service API URL",
        ("url", ""),
    ),
    _switch(
        ("--open-vsx",),
        "Use Open VSX Registry (https://open-vsx.org/vscode/gallery)",
        "Use Open VSX Registry",
    ),
    _valued(
        ("--open-vsx-token",),
        "Access token for Open VSX Registry",
        "Access token for Open VSX Registry",
        ("token", ""),
    ),
)

VERSION_FILTER_OPTIONS = (
    _switch(
        ("-p", "--include-prerelease"),
        "Allow pre-release versions (or include them in update/outdated check)",
        "Allow pre-release versions",
    ),
    _switch(
        ("-V", "--no-code-version-check"),
        "Disable VS Code version compatibility check",
        "Disable VS Code version check",
        dest="no_code_version_check",
    ),
    _valued(
        ("-a", "--min-release-age"),
        "Minimum release age threshold (e.g. 24h, 3d, 0)",
        "Minimum release age threshold",
        ("age", ""),
    ),
)

DOWNLOAD_OPTIONS = (
    _valued(
        ("-d", "--download-dir"),
        "Download directory for .vsix files",
        "Download directory",
        ("dir", "_files -/"),
    ),
)

YES_OPTIONS = (
    _switch(
        ("-y", "--yes"),
        "Non-interactive mode / skip confirmation prompt",
        "Non-interactive mode",
    ),
)

QUIET_OPTIONS = (
    _switch(
        ("-q", "--quiet"),
        "Output raw extension IDs only (one per line, ideal for scripting)",
        "Output raw extension IDs only",
        default=False,
    ),
)

# Options each subcommand adds on top of GLOBAL_OPTIONS, in help-output order.
SUBCOMMAND_OPTIONS = {
    "install": VERSION_FILTER_OPTIONS
    + DOWNLOAD_OPTIONS
    + (
        _valued(
            ("-f", "--file"),
            "File containing extension IDs to install (one per line)",
            "File containing extension IDs",
            ("file", "_files"),
        ),
        _switch(
            ("--force",),
            "Force re-installation even if the target version is already installed",
            "Force re-installation",
            default=False,
        ),
        _switch(
            ("-y", "--yes"),
            "Non-interactive mode (install a pinned version even when held back; "
            "otherwise skip held-back extensions instead of prompting)",
            "Non-interactive mode",
        ),
    ),
    "update": VERSION_FILTER_OPTIONS
    + DOWNLOAD_OPTIONS
    + YES_OPTIONS
    + (
        _switch(
            ("-n", "--dry-run"),
            "Perform a dry run (show available updates without downloading or installing)",
            "Perform dry run without downloading or installing",
        ),
    ),
    "remove": YES_OPTIONS,
    "list": VERSION_FILTER_OPTIONS
    + QUIET_OPTIONS
    + (
        _switch(
            ("-u", "--outdated"),
            "List only extensions that have updates available",
            "List extensions with updates available",
            default=False,
        ),
    ),
    "search": VERSION_FILTER_OPTIONS
    + QUIET_OPTIONS
    + (
        _valued(
            ("-n", "--max-results"),
            "Maximum number of search results to return (default: 15)",
            "Maximum search results",
            ("number", ""),
            default=15,
            type=int,
        ),
    ),
    "info": (),
    "clean": (),
    "config": (),
    "completion": (),
}


def add_options(parser, options):
    for opt in options:
        parser.add_argument(*opt.flags, help=opt.help, **opt.kwargs)
    return parser


def _fish_option(opt, predicate=None):
    parts = ["complete -c code-extensions"]
    if predicate:
        parts.append(f'-n "{predicate}"')
    parts += [
        f"-l {flag[2:]}" if flag.startswith("--") else f"-s {flag[1:]}"
        for flag in opt.flags
    ]
    parts.append(f'-d "{opt.summary}"')
    if opt.value:
        parts.append("-r")
        if "_files" in opt.value[1]:
            parts.append("-F")
    return " ".join(parts)


def _fish_subcommand_options():
    """One completion line per option, listing every subcommand that takes it."""
    grouped = {}
    for name in CANONICAL_SUBCOMMANDS:
        for opt in SUBCOMMAND_OPTIONS[name]:
            grouped.setdefault((opt.flags, opt.summary), (opt, []))[1].append(name)
    return "\n".join(
        _fish_option(
            opt,
            "__fish_seen_subcommand_from " + " ".join(subcommand_names(*names)),
        )
        for opt, names in grouped.values()
    )


def _bash_flags(options):
    return " ".join(flag for opt in options for flag in opt.flags)


def _zsh_option(opt):
    value = f":{opt.value[0]}:{opt.value[1]}" if opt.value else ""
    if len(opt.flags) == 1:
        return f"'{opt.flags[0]}[{opt.summary}]{value}'"
    short, long = opt.flags
    return f"'({short} {long})'{{{short},{long}}}'[{opt.summary}]{value}'"


def _zsh_options(options, indent):
    pad = " " * indent
    return " \\\n".join(pad + _zsh_option(opt) for opt in options)


# @@ALIASES:remove,info@@ expands to those subcommands and their aliases, joined
# the way the target shell spells a set of alternatives; the other markers are
# filled in per script below.
_ALIAS_MARKER_RE = re.compile(r"@@ALIASES:([a-z,]+)@@")
_FLAGS_MARKER_RE = re.compile(r"@@FLAGS:([a-z]+)@@")


def _render_completion(template, join_names, markers, format_flags=None):
    script = _ALIAS_MARKER_RE.sub(
        lambda m: join_names(subcommand_names(*m.group(1).split(","))), template
    )
    if format_flags:
        script = _FLAGS_MARKER_RE.sub(lambda m: format_flags(m.group(1)), script)
    for marker, value in markers.items():
        script = script.replace(f"@@{marker}@@", value)
    if "@@" in script:
        # An unresolved marker would be emitted into the user's shell startup.
        raise RuntimeError(f"unfilled marker in completion script: {script}")
    return script


_FISH_TEMPLATE = """# Fish completion script for code-extensions

complete -c code-extensions -f

@@SUBCOMMANDS@@

@@GLOBAL_OPTIONS@@

complete -c code-extensions -n "__fish_seen_subcommand_from @@ALIASES:config@@" -a "@@CONFIG_ACTIONS@@"
complete -c code-extensions -n "__fish_seen_subcommand_from @@ALIASES:completion@@" -a "@@SHELLS@@"

@@SUBCOMMAND_OPTIONS@@

complete -c code-extensions -n "__fish_seen_subcommand_from @@ALIASES:remove,info,update@@" -a "(code-extensions list -q 2>/dev/null)"
"""

FISH_COMPLETION_SCRIPT = _render_completion(
    _FISH_TEMPLATE,
    " ".join,
    {
        "SUBCOMMANDS": "\n".join(
            f'complete -c code-extensions -n "__fish_use_subcommand"'
            f' -a "{c.name}" -d "{c.summary}"'
            for c in SUBCOMMANDS
        ),
        "CONFIG_ACTIONS": " ".join(c.name for c in CONFIG_ACTIONS),
        "SHELLS": " ".join(COMPLETION_SHELLS),
        "GLOBAL_OPTIONS": "\n".join(
            _fish_option(opt) for opt in (*GLOBAL_OPTIONS, HELP_OPTION)
        ),
        "SUBCOMMAND_OPTIONS": _fish_subcommand_options(),
    },
)

_BASH_TEMPLATE = """# Bash completion script for code-extensions

_code_extensions_completion() {
    local cur prev words cword
    _init_completion -n : 2>/dev/null || {
        cur="${COMP_WORDS[COMP_CWORD]}"
        prev="${COMP_WORDS[COMP_CWORD-1]}"
    }

    local commands="@@COMMANDS@@"
    local config_actions="@@CONFIG_ACTIONS@@"
    local shells="@@SHELLS@@"

    if [[ $COMP_CWORD -eq 1 ]]; then
        COMPREPLY=( $(compgen -W "$commands" -- "$cur") )
        return 0
    fi

    local cmd="${COMP_WORDS[1]}"

    case "$cmd" in
        @@ALIASES:config@@)
            if [[ $COMP_CWORD -eq 2 ]]; then
                COMPREPLY=( $(compgen -W "$config_actions" -- "$cur") )
            fi
            ;;
        @@ALIASES:completion@@)
            if [[ $COMP_CWORD -eq 2 ]]; then
                COMPREPLY=( $(compgen -W "$shells" -- "$cur") )
            fi
            ;;
        @@ALIASES:remove@@)
            if [[ "$cur" == -* ]]; then
                COMPREPLY=( $(compgen -W "@@FLAGS:remove@@" -- "$cur") )
            else
                local installed
                installed=$(code-extensions list -q 2>/dev/null)
                COMPREPLY=( $(compgen -W "$installed" -- "$cur") )
            fi
            ;;
        @@ALIASES:update@@)
            if [[ "$cur" == -* ]]; then
                COMPREPLY=( $(compgen -W "@@FLAGS:update@@" -- "$cur") )
            else
                local installed
                installed=$(code-extensions list -q 2>/dev/null)
                COMPREPLY=( $(compgen -W "$installed" -- "$cur") )
            fi
            ;;
        @@ALIASES:info@@)
            if [[ "$cur" == -* ]]; then
                COMPREPLY=( $(compgen -W "@@FLAGS:info@@" -- "$cur") )
            else
                local installed
                installed=$(code-extensions list -q 2>/dev/null)
                COMPREPLY=( $(compgen -W "$installed" -- "$cur") )
            fi
            ;;
        @@ALIASES:install@@)
            COMPREPLY=( $(compgen -W "@@FLAGS:install@@" -- "$cur") )
            ;;
        @@ALIASES:list@@)
            COMPREPLY=( $(compgen -W "@@FLAGS:list@@" -- "$cur") )
            ;;
        @@ALIASES:search@@)
            COMPREPLY=( $(compgen -W "@@FLAGS:search@@" -- "$cur") )
            ;;
        *)
            COMPREPLY=( $(compgen -W "@@GLOBAL_FLAGS@@" -- "$cur") )
            ;;
    esac
}

complete -F _code_extensions_completion code-extensions
"""

BASH_COMPLETION_SCRIPT = _render_completion(
    _BASH_TEMPLATE,
    "|".join,
    {
        "COMMANDS": " ".join(CANONICAL_SUBCOMMANDS),
        "CONFIG_ACTIONS": " ".join(c.name for c in CONFIG_ACTIONS),
        "SHELLS": " ".join(COMPLETION_SHELLS),
        "GLOBAL_FLAGS": _bash_flags((*GLOBAL_OPTIONS, HELP_OPTION)),
    },
    # bash has no per-subcommand option state, so every branch offers the
    # global options too, exactly like the parser accepts them.
    format_flags=lambda name: _bash_flags(
        (*SUBCOMMAND_OPTIONS[name], *GLOBAL_OPTIONS, HELP_OPTION)
    ),
)

_ZSH_TEMPLATE = """#compdef code-extensions

_code_extensions() {
    local -a commands
    commands=(
@@ZSH_COMMANDS@@
    )

    local -a config_actions
    config_actions=(
@@ZSH_CONFIG_ACTIONS@@
    )

    local -a shells
    shells=(@@ZSH_SHELLS@@)

    _arguments -C \\
@@ZSH_GLOBAL_OPTIONS@@ \\
        '1: :->command' \\
        '*:: :->args'

    case $state in
        command)
            _describe -t commands 'code-extensions command' commands
            ;;
        args)
            case $words[1] in
                @@ALIASES:config@@)
                    _values 'config action' $config_actions
                    ;;
                @@ALIASES:completion@@)
                    _values 'shell' $shells
                    ;;
                @@ALIASES:remove@@)
                    local -a installed
                    installed=($(code-extensions list -q 2>/dev/null))
                    _arguments \\
@@FLAGS:remove@@ \\
                        '*:installed extension:($installed)'
                    ;;
                @@ALIASES:info@@)
                    local -a installed
                    installed=($(code-extensions list -q 2>/dev/null))
                    _values 'installed extensions' $installed
                    ;;
                @@ALIASES:update@@)
                    local -a installed
                    installed=($(code-extensions list -q 2>/dev/null))
                    _arguments \\
@@FLAGS:update@@ \\
                        '*:installed extension:($installed)'
                    ;;
                @@ALIASES:install@@)
                    _arguments \\
@@FLAGS:install@@
                    ;;
                @@ALIASES:list@@)
                    _arguments \\
@@FLAGS:list@@
                    ;;
                @@ALIASES:search@@)
                    _arguments \\
@@FLAGS:search@@
                    ;;
            esac
            ;;
    esac
}

_code_extensions "$@"
"""

ZSH_COMPLETION_SCRIPT = _render_completion(
    _ZSH_TEMPLATE,
    "|".join,
    {
        "ZSH_COMMANDS": "\n".join(
            f"        '{c.name}:{c.summary}'" for c in SUBCOMMANDS
        ),
        "ZSH_CONFIG_ACTIONS": "\n".join(
            f"        '{c.name}:{c.summary}'" for c in CONFIG_ACTIONS
        ),
        "ZSH_SHELLS": " ".join(f"'{sh}'" for sh in COMPLETION_SHELLS),
        "ZSH_GLOBAL_OPTIONS": _zsh_options((*GLOBAL_OPTIONS, HELP_OPTION), 8),
    },
    format_flags=lambda name: _zsh_options(SUBCOMMAND_OPTIONS[name], 24),
)

_POWERSHELL_TEMPLATE = """# PowerShell completion script for code-extensions

Register-ArgumentCompleter -Native -CommandName 'code-extensions' -ScriptBlock {
    param($wordToComplete, $commandAst, $cursorPosition)

    $commandElements = $commandAst.CommandElements
    $command = $commandElements[1].Value

    $subcommands = @@PS_COMMANDS@@
    $configActions = @@PS_CONFIG_ACTIONS@@
    $shells = @@PS_SHELLS@@

    if ($commandElements.Count -eq 2) {
        $subcommands | Where-Object { $_ -like "$wordToComplete*" } | ForEach-Object {
            [System.Management.Automation.CompletionResult]::new($_, $_, 'ParameterValue', $_)
        }
        return
    }

    switch ($command) {
        { $_ -in @@ALIASES:config@@ } {
            if ($commandElements.Count -eq 3) {
                $configActions | Where-Object { $_ -like "$wordToComplete*" } | ForEach-Object {
                    [System.Management.Automation.CompletionResult]::new($_, $_, 'ParameterValue', $_)
                }
            }
        }
        { $_ -in @@ALIASES:completion@@ } {
            if ($commandElements.Count -eq 3) {
                $shells | Where-Object { $_ -like "$wordToComplete*" } | ForEach-Object {
                    [System.Management.Automation.CompletionResult]::new($_, $_, 'ParameterValue', $_)
                }
            }
        }
        { $_ -in @@ALIASES:remove,info,update@@ } {
            $installed = code-extensions list -q 2>$null
            $installed | Where-Object { $_ -like "$wordToComplete*" } | ForEach-Object {
                [System.Management.Automation.CompletionResult]::new($_, $_, 'ParameterValue', $_)
            }
        }
    }
}
"""


def _ps_array(names):
    return "@(" + ", ".join(f"'{n}'" for n in names) + ")"


POWERSHELL_COMPLETION_SCRIPT = _render_completion(
    _POWERSHELL_TEMPLATE,
    _ps_array,
    {
        "PS_COMMANDS": _ps_array(CANONICAL_SUBCOMMANDS),
        "PS_CONFIG_ACTIONS": _ps_array([c.name for c in CONFIG_ACTIONS]),
        "PS_SHELLS": _ps_array(COMPLETION_SHELLS),
    },
)

SHELL_COMPLETION_SCRIPTS = {
    "bash": BASH_COMPLETION_SCRIPT,
    "fish": FISH_COMPLETION_SCRIPT,
    "powershell": POWERSHELL_COMPLETION_SCRIPT,
    "zsh": ZSH_COMPLETION_SCRIPT,
}


def handle_completion(args, config):
    shell = args.shell.lower().strip()
    script = SHELL_COMPLETION_SCRIPTS.get(shell)
    if script is None:
        print(
            f"{Colors.RED}Error: Unsupported shell '{shell}'. "
            f"Supported: {', '.join(COMPLETION_SHELLS)}{Colors.ENDC}",
            file=sys.stderr,
        )
        sys.exit(1)
    sys.stdout.write(script.strip() + "\n")


HANDLERS = {
    "install": handle_install,
    "update": handle_update,
    "remove": handle_remove,
    "list": handle_list,
    "search": handle_search,
    "info": handle_info,
    "clean": handle_clean,
    "config": handle_config,
    "completion": handle_completion,
}
for _name, _aliases in SUBCOMMAND_ALIASES.items():
    for _alias in _aliases:
        HANDLERS[_alias] = HANDLERS[_name]


def main():
    enable_colors()
    config = load_config()

    # Options come from SUBCOMMAND_OPTIONS so the parser and the completion
    # scripts cannot disagree about what a subcommand accepts.
    parent_parser = add_options(argparse.ArgumentParser(add_help=False), GLOBAL_OPTIONS)

    parser = argparse.ArgumentParser(
        prog="code-extensions",
        description="VS Code Extension Manager: Install, update, list, search, and remove extensions with security controls.",
    )
    subparsers = parser.add_subparsers(dest="command", help="Subcommand to execute")

    # Install sub-parser
    parser_install = subparsers.add_parser(
        "install",
        parents=[parent_parser],
        help="Install VS Code extension(s) by ID (e.g. publisher.name or publisher.name@version)",
    )
    add_options(parser_install, SUBCOMMAND_OPTIONS["install"])
    parser_install.add_argument(
        "extensions",
        nargs="*",
        default=[],
        help="Extension ID(s) to install (e.g. ms-python.python or ms-python.python@2024.1.0)",
    )

    # Update sub-parser
    parser_update = subparsers.add_parser(
        "update",
        aliases=SUBCOMMAND_ALIASES["update"],
        parents=[parent_parser],
        help="Check, download, and install updates for installed extensions",
    )
    add_options(parser_update, SUBCOMMAND_OPTIONS["update"])
    parser_update.add_argument(
        "extensions",
        nargs="*",
        help="Extension ID(s) or partial name(s) to update (default: all installed)",
    )

    # Remove sub-parser
    parser_remove = subparsers.add_parser(
        "remove",
        aliases=SUBCOMMAND_ALIASES["remove"],
        parents=[parent_parser],
        help="Remove installed extension(s)",
    )
    add_options(parser_remove, SUBCOMMAND_OPTIONS["remove"])
    parser_remove.add_argument(
        "extensions",
        nargs="*",
        default=[],
        help="Extension ID(s) to remove (if omitted, launches interactive removal TUI)",
    )

    # List sub-parser
    parser_list = subparsers.add_parser(
        "list",
        aliases=SUBCOMMAND_ALIASES["list"],
        parents=[parent_parser],
        help="List installed extension(s)",
    )
    add_options(parser_list, SUBCOMMAND_OPTIONS["list"])
    parser_list.add_argument(
        "query",
        nargs="?",
        default=None,
        help="Optional search query to filter extensions by ID",
    )

    # Search sub-parser
    parser_search = subparsers.add_parser(
        "search",
        parents=[parent_parser],
        help="Search VS Code Marketplace / Open VSX for extensions",
    )
    add_options(parser_search, SUBCOMMAND_OPTIONS["search"])
    parser_search.add_argument(
        "query",
        help="Search query text (e.g. python, rust, gitlens)",
    )

    # Info / Show sub-parser
    parser_info = subparsers.add_parser(
        "info",
        aliases=SUBCOMMAND_ALIASES["info"],
        parents=[parent_parser],
        help="Show detailed metadata for an extension",
    )
    parser_info.add_argument(
        "extension",
        help="Extension ID (e.g. ms-python.python)",
    )

    # Clean sub-parser
    subparsers.add_parser(
        "clean",
        parents=[parent_parser],
        help="Purge cached API response JSON files and temporary VSIX downloads",
    )

    # Config sub-parser
    parser_config = subparsers.add_parser(
        "config",
        parents=[parent_parser],
        help="View or modify configuration settings in config.toml",
    )
    parser_config.add_argument(
        "action",
        nargs="?",
        choices=CONFIG_ACTION_CHOICES,
        default="list",
        help="Action to perform: list, get, set, unset",
    )
    parser_config.add_argument(
        "key",
        nargs="?",
        default=None,
        help="Configuration setting key (e.g. min_release_age or charliermarsh.ruff.min_release_age)",
    )
    parser_config.add_argument(
        "value",
        nargs="?",
        default=None,
        help="Configuration value to set (for 'set' action)",
    )

    # Completion sub-parser
    parser_completion = subparsers.add_parser(
        "completion",
        parents=[parent_parser],
        help=f"Generate shell completion script ({', '.join(COMPLETION_SHELLS)})",
    )
    parser_completion.add_argument(
        "shell",
        choices=COMPLETION_SHELLS,
        help="Target shell environment",
    )

    # Exclude aliases from the usage and positional argument list in help output.
    # Spelled out rather than derived from argparse's private _choices_actions,
    # whose absence would break every invocation, including --help.
    subparsers.metavar = "{" + ",".join(CANONICAL_SUBCOMMANDS) + "}"

    args = parser.parse_args()

    if not args.command:
        parser.print_help(sys.stderr)
        # Exit 2, argparse's usage-error code, so a script can tell a forgotten
        # subcommand from a successful run of one.
        sys.exit(2)

    HANDLERS[args.command](args, config)


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        # Restore the cursor in case we were interrupted inside a TUI.
        if sys.stdout.isatty():
            sys.stdout.write("\033[?25h\n")
            sys.stdout.flush()
        print("Aborted.", file=sys.stderr)
        sys.exit(130)
    except BrokenPipeError:
        # e.g. `code-extensions list -q | head`
        os._exit(0)
    except Exception as e:
        # A terminal that disappears mid-TUI surfaces as termios.error (not an
        # OSError subclass) from the raw-mode restore. There is nowhere left to
        # print a traceback to, so exit like an interrupted run -- but say so on
        # stderr, because the same error also comes from a tcgetattr that fails
        # on a descriptor isatty() nonetheless called a terminal, and vanishing
        # with no output at all leaves nothing to debug.
        if HAS_TTY and isinstance(e, termios.error):
            with contextlib.suppress(OSError):
                print(f"Terminal error: {e}", file=sys.stderr)
            sys.exit(130)
        raise
