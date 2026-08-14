#!/usr/bin/env python3

import argparse
import contextlib
import datetime
import email
import http.client
import importlib.util
import io
import json
import os
import random
import tempfile
import time
import unittest
import urllib.request
import zlib
from unittest.mock import MagicMock, patch

# Dynamically import code-extensions.py module (since filename contains a hyphen)
CODE_EXTENSIONS_PATH = os.path.join(os.path.dirname(__file__), "code-extensions.py")
SPEC = importlib.util.spec_from_file_location("code_extensions", CODE_EXTENSIONS_PATH)
ce = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ce)


# =====================================================================
# Engine Compatibility & Semver Tests
# =====================================================================
class TestSemverAndEngineCompatibility(unittest.TestCase):
    def test_parse_version_standard(self):
        v = ce.parse_version("1.2.3")
        self.assertTrue(v[1])  # is_release
        self.assertEqual(v[0], ((0, 1), (0, 2), (0, 3)))

    def test_parse_version_prerelease(self):
        v = ce.parse_version("1.2.3-beta.1")
        self.assertFalse(v[1])  # is_release
        self.assertEqual(v[2], ((1, "beta"), (0, 1)))

    def test_is_engine_compatible_cases(self):
        test_cases = [
            ("1.85.0", "^1.80.0", True),
            ("1.79.0", "^1.80.0", False),
            ("2.0.0", "^1.80.0", False),
            ("1.80.5", "~1.80.0", True),
            ("1.81.0", "~1.80.0", False),
            ("1.86.0-insider", "^1.86.0", True),  # Insider build handling
            ("1.80.5", "1.80.x", True),  # Wildcard range expansion
            ("1.81.0", "1.80.x", False),
            # A caret over a wildcard reaches to the next major.
            ("1.85.0", "^1.80.x", True),
            ("1.79.0", "^1.80.x", False),
            ("2.0.0", "^1.80.x", False),
            ("1.85.0", "^1.x", True),
            ("0.81.0", "^0.80.x", False),  # Caret below 1.0.0 pins the minor
            ("0.80.5", "^0.80.x", True),
            ("1.81.0", "~1.80.x", False),  # Tilde keeps the wildcard's ceiling
            # A comparator applies to the wildcard range as a whole.
            ("1.80.5", ">1.80.x", False),
            ("1.81.0", ">1.80.x", True),
            ("1.80.0", ">=1.80.x", True),
            ("1.80.0", "<1.80.x", False),
            ("1.80.5", "<=1.80.x", True),
            ("1.81.0", "<=1.80.x", False),
            # An unbounded wildcard constrains nothing, comparator or not.
            ("1.85.0", "x", True),
            ("1.85.0", "<=x", True),
            ("1.85.0", ">x", True),
            ("1.85.0", ">=1.80.0 <1.90.0", True),
            ("1.91.0", ">=1.80.0 <1.90.0", False),
            ("1.50.0", "1.0.0 - 2.0.0", True),
            ("2.5.0", "1.0.0 - 2.0.0", False),
            ("1.85.0", "^1.80.0 || ^1.85.0", True),
            ("1.70.0", "^1.80.0 || ^1.85.0", False),
            ("1.85.0", "*", True),
            ("1.85.0", "", True),
        ]
        for vs_ver, constraint, expected in test_cases:
            with self.subTest(vs_ver=vs_ver, constraint=constraint):
                self.assertEqual(
                    ce.is_engine_compatible(vs_ver, constraint),
                    expected,
                    f"Failed for vs_ver={vs_ver}, constraint={constraint}",
                )

    def test_expand_x_range(self):
        self.assertEqual(ce.expand_x_range("1.80.x"), ("1.80.0", "1.81.0"))
        self.assertEqual(ce.expand_x_range("1.x"), ("1.0.0", "2.0.0"))
        self.assertEqual(ce.expand_x_range("x"), ("0.0.0", None))
        self.assertIsNone(ce.expand_x_range("1.80.0"))

    def test_filter_versions(self):
        versions = [
            {"version": "2.0.0", "targetPlatform": "linux-x64"},
            {"version": "1.9.0", "targetPlatform": "universal"},
            {
                "version": "1.8.0-pre",
                "properties": [
                    {
                        "key": "Microsoft.VisualStudio.Code.PreRelease",
                        "value": "true",
                    }
                ],
            },
            {"version": "1.7.0", "targetPlatform": "win32-x64"},
        ]

        # Standard filtering for linux-x64
        selected = ce.filter_versions(
            versions, target_platform="linux-x64", include_prerelease=False
        )
        version_strings = [v["version"] for v in selected]
        self.assertEqual(version_strings, ["2.0.0", "1.9.0"])

        # Include prerelease
        selected_pre = ce.filter_versions(
            versions, target_platform="linux-x64", include_prerelease=True
        )
        self.assertIn("1.8.0-pre", [v["version"] for v in selected_pre])

        # Newer than filter
        selected_newer = ce.filter_versions(
            versions, target_platform="linux-x64", newer_than="1.9.0"
        )
        self.assertEqual([v["version"] for v in selected_newer], ["2.0.0"])

    def test_filter_versions_ignores_input_order(self):
        """The early stop must not depend on the order the gallery used."""
        versions = [{"version": v} for v in ("2.0.0", "1.9.0", "1.8.0", "1.7.0")]
        expected = ["2.0.0", "1.9.0"]

        rng = random.Random(0)
        for _ in range(8):
            shuffled = versions[:]
            rng.shuffle(shuffled)
            selected = ce.filter_versions(
                shuffled, target_platform="linux-x64", newer_than="1.8.0"
            )
            self.assertEqual([v["version"] for v in selected], expected)

    def test_filter_versions_skip_and_pinned_versions(self):
        versions = [{"version": v} for v in ("2.0.0", "1.9.0", "1.8.0")]

        skipped = ce.filter_versions(
            versions, target_platform="linux-x64", skip_versions=["2.0.0"]
        )
        self.assertEqual([v["version"] for v in skipped], ["1.9.0", "1.8.0"])

        pinned = ce.filter_versions(
            versions, target_platform="linux-x64", required_version="1.9.0"
        )
        self.assertEqual([v["version"] for v in pinned], ["1.9.0"])

    def test_filter_versions_keeps_platform_variant_order(self):
        """Equal versions must stay in gallery order so [0] picks the same build."""
        versions = [
            {"version": "1.0.0", "targetPlatform": "linux-x64"},
            {"version": "1.0.0", "targetPlatform": "universal"},
        ]
        selected = ce.filter_versions(versions, target_platform="linux-x64")
        self.assertEqual(
            [v["targetPlatform"] for v in selected], ["linux-x64", "universal"]
        )


# =====================================================================
# TOML Parser & Config Engine
# =====================================================================
class TestTOMLParserAndConfig(unittest.TestCase):
    def test_strip_comment_with_hash_in_quotes(self):
        line = 'key = "value # with hash" # real comment'
        stripped = ce.strip_comment(line)
        self.assertEqual(stripped, 'key = "value # with hash"')

    def test_strip_comment_with_escaped_quote(self):
        """An escaped quote must not close the string and expose a later '#'."""
        self.assertEqual(ce.strip_comment(r'token = "a\"b#c"'), r'token = "a\"b#c"')
        self.assertEqual(
            ce.strip_comment(r'key = "foo \" # bar"'), r'key = "foo \" # bar"'
        )
        # A literal string does not process escapes, so it ends at the quote.
        self.assertEqual(ce.strip_comment(r"lit = 'a\' # b"), r"lit = 'a\'")

    def test_unquote_toml_value(self):
        self.assertEqual(ce.unquote_toml_value('"hello"'), "hello")
        self.assertEqual(ce.unquote_toml_value("'hello'"), "hello")
        self.assertEqual(ce.unquote_toml_value(r'"hello\nworld"'), "hello\nworld")
        # Literal strings keep backslashes verbatim.
        self.assertEqual(ce.unquote_toml_value(r"'a\nb'"), r"a\nb")

    def test_unescape_toml_basic(self):
        escaped = r"Hello\nWorld\t\"Test\""
        self.assertEqual(ce.unescape_toml_basic(escaped), 'Hello\nWorld\t"Test"')
        self.assertEqual(ce.unescape_toml_basic(r"\u0041\u00e9"), "Aé")
        self.assertEqual(ce.unescape_toml_basic(r"\U0001F600"), "\U0001f600")

    def test_unescape_toml_basic_keeps_bad_escapes_literal(self):
        for text in (r"\u12", r"\U000", r"\uZZZZ", r"\ud800", r"\q", "\\"):
            with self.subTest(text=text):
                self.assertEqual(ce.unescape_toml_basic(text), text)

    def test_config_value_round_trip_through_fallback(self):
        """dump_toml output must read back identically on the no-tomllib path."""
        import tomllib

        cases = [
            {"open_vsx_token": 'a"b#c'},
            {"open_vsx_token": 'to"ken'},
            {"code_binary": r"C:\Program Files\VS Code\code.cmd"},
            {"service_url": "https://example.com/gallery#frag"},
            {
                "min_release_age": "3d",
                "extensions": {"golang.go": {"skip_versions": ["0.39.0"]}},
            },
        ]
        for cfg in cases:
            with self.subTest(cfg=cfg):
                text = ce.dump_toml(cfg)
                self.assertEqual(tomllib.loads(text), cfg)
                self.assertEqual(ce.parse_toml_fallback(text), cfg)

    def test_parse_toml_fallback_structures(self):
        toml_content = """
        # Comment line
        global_key = "value"

        [charliermarsh.ruff]
        min_release_age = "24h"
        include_prerelease = true
        max_results = 10

        [sec.sub]
        foo = "bar"
        """
        parsed = ce.parse_toml_fallback(toml_content)
        self.assertEqual(parsed["global_key"], "value")
        self.assertEqual(parsed["charliermarsh"]["ruff"]["min_release_age"], "24h")
        self.assertTrue(parsed["charliermarsh"]["ruff"]["include_prerelease"])
        self.assertEqual(parsed["sec"]["sub"]["foo"], "bar")

    def test_coerce_config_value(self):
        self.assertTrue(ce.coerce_config_value("true", bool))
        self.assertFalse(ce.coerce_config_value("FALSE", bool))
        self.assertEqual(ce.coerce_config_value(42, str), "42")
        self.assertEqual(ce.coerce_config_value("hello", str), "hello")

    def test_load_and_save_config(self):
        with tempfile.TemporaryDirectory() as tmp_dir:
            config_path = os.path.join(tmp_dir, "config.toml")
            initial_cfg = {
                "min_release_age": "24h",
                "open_vsx": True,
                "extensions": {"charliermarsh.ruff": {"min_release_age": "1d"}},
            }
            ce.save_config(initial_cfg, config_path)

            with patch.object(ce, "get_default_config_path", return_value=config_path):
                loaded_cfg = ce.load_config()
                self.assertEqual(loaded_cfg.get("min_release_age"), "24h")
                self.assertTrue(loaded_cfg.get("open_vsx"))
                # The per-extension table, whose key needs quoting, round-trips.
                self.assertEqual(
                    loaded_cfg["extensions"]["charliermarsh.ruff"]["min_release_age"],
                    "1d",
                )

            if os.name != "nt":
                # The file can hold an access token, so it must not be readable
                # by anyone else.
                self.assertEqual(os.stat(config_path).st_mode & 0o777, 0o600)

    def test_get_default_config_path_ignores_the_working_directory(self):
        """A config.toml in the CWD must not be picked up: it names the binary
        to execute and the gallery to download from."""
        with tempfile.TemporaryDirectory() as tmp_dir:
            with open(os.path.join(tmp_dir, "config.toml"), "w") as f:
                f.write('code_binary = "/tmp/evil.sh"\n')
            cwd = os.getcwd()
            os.chdir(tmp_dir)
            try:
                with patch.dict(os.environ, {}, clear=False):
                    os.environ.pop("CODE_EXTENSIONS_CONFIG", None)
                    resolved = ce.get_default_config_path()
            finally:
                os.chdir(cwd)
            self.assertNotEqual(
                os.path.realpath(resolved),
                os.path.realpath(os.path.join(tmp_dir, "config.toml")),
            )

    def test_get_default_config_path_honors_explicit_override(self):
        with patch.dict(os.environ, {"CODE_EXTENSIONS_CONFIG": "/tmp/mine.toml"}):
            self.assertEqual(ce.get_default_config_path(), "/tmp/mine.toml")


# =====================================================================
# Release Age Gating Tests
# =====================================================================
class TestReleaseAgeGating(unittest.TestCase):
    def test_parse_age_threshold_valid(self):
        cases = [
            ("24h", datetime.timedelta(hours=24)),
            ("2d", datetime.timedelta(days=2)),
            ("30m", datetime.timedelta(minutes=30)),
            ("0", datetime.timedelta(0)),
            ("0h", datetime.timedelta(0)),
        ]
        for age_str, expected_td in cases:
            with self.subTest(age_str=age_str):
                self.assertEqual(ce.parse_age_threshold(age_str), expected_td)

    def test_parse_age_threshold_invalid(self):
        with self.assertRaises(ValueError):
            ce.parse_age_threshold("invalid_age")

    def test_released_long_enough(self):
        now = datetime.datetime.now(datetime.timezone.utc)
        recent_ts = (now - datetime.timedelta(hours=5)).isoformat()
        old_ts = (now - datetime.timedelta(hours=48)).isoformat()

        min_age = datetime.timedelta(hours=24)

        self.assertTrue(ce.released_long_enough({"lastUpdated": old_ts}, min_age))
        self.assertFalse(ce.released_long_enough({"lastUpdated": recent_ts}, min_age))
        self.assertTrue(ce.released_long_enough({}, min_age))  # missing timestamp

    def test_first_eligible_version(self):
        now = datetime.datetime.now(datetime.timezone.utc)
        v1_ts = (now - datetime.timedelta(hours=5)).isoformat()  # Too recent
        v2_ts = (now - datetime.timedelta(hours=30)).isoformat()  # Pass
        v3_ts = (now - datetime.timedelta(hours=60)).isoformat()  # Pass

        versions = [
            {"version": "2.0.0", "lastUpdated": v1_ts},
            {"version": "1.9.0", "lastUpdated": v2_ts},
            {"version": "1.8.0", "lastUpdated": v3_ts},
        ]
        min_age = datetime.timedelta(hours=24)
        eligible = ce.first_eligible_version(versions, min_age)
        self.assertEqual(eligible["version"], "1.9.0")


# =====================================================================
# Security & Host Validation Tests
# =====================================================================
class TestSecurityAndHostValidation(unittest.TestCase):
    def test_is_open_vsx_url(self):
        cases = [
            ("https://open-vsx.org/vscode/gallery", True),
            ("https://sub.open-vsx.org/gallery", True),
            ("https://open-vsx.org.attacker.com/vscode/gallery", False),
            ("https://marketplace.visualstudio.com", False),
            ("", False),
        ]
        for url, expected in cases:
            with self.subTest(url=url):
                self.assertEqual(ce.is_open_vsx_url(url), expected)

    def test_is_marketplace_url(self):
        cases = [
            ("https://marketplace.visualstudio.com/_apis/public/gallery", True),
            ("https://ms-python.gallerycdn.vsassets.io/file.vsix", True),
            ("https://marketplace.visualstudio.com.attacker.com/gallery", False),
            ("https://open-vsx.org/vscode/gallery", False),
            ("https://vsx.internal.example.com/gallery", False),
            ("", False),
        ]
        for url, expected in cases:
            with self.subTest(url=url):
                self.assertEqual(ce.is_marketplace_url(url), expected)

    def test_resolve_token_for_service_withholds_from_the_marketplace(self):
        args = argparse.Namespace(open_vsx_token="secret_pat", open_vsx=None)
        config = {"open_vsx_token": "secret_pat"}

        # A token set for some other registry must not reach Microsoft's.
        self.assertIsNone(
            ce.resolve_token_for_service(ce.DEFAULT_SERVICE_URL, args, config)
        )
        self.assertIsNone(
            ce.resolve_token_for_service(
                ce.DEFAULT_SERVICE_URL, argparse.Namespace(open_vsx=None), config
            )
        )

        # Open VSX itself, an explicit --open-vsx, and a self-hosted registry all
        # still get it.
        self.assertEqual(
            ce.resolve_token_for_service(ce.OPEN_VSX_SERVICE_URL, args, config),
            "secret_pat",
        )
        self.assertEqual(
            ce.resolve_token_for_service(
                "https://vsx.internal.example.com/gallery", args, config
            ),
            "secret_pat",
        )
        self.assertEqual(
            ce.resolve_token_for_service(
                ce.DEFAULT_SERVICE_URL,
                argparse.Namespace(open_vsx=True),
                {"open_vsx_token": "secret_pat"},
            ),
            "secret_pat",
        )

    def test_resolve_token_for_service_without_a_token_configured(self):
        args = argparse.Namespace(open_vsx=None)
        with patch.dict(os.environ, {}, clear=True):
            self.assertIsNone(
                ce.resolve_token_for_service(ce.DEFAULT_SERVICE_URL, args, {})
            )
            self.assertIsNone(
                ce.resolve_token_for_service(ce.OPEN_VSX_SERVICE_URL, args, {})
            )

    def test_auth_stripping_redirect_handler_cross_host(self):
        handler = ce._AuthStrippingRedirectHandler()

        orig_req = urllib.request.Request(
            "https://marketplace.visualstudio.com/download",
            headers={"Authorization": "Bearer secret_token"},
        )
        new_req = urllib.request.Request("https://cdn.vsassets.io/file.vsix")

        result = handler.redirect_request(
            orig_req,
            None,
            302,
            "Found",
            email.message_from_string(""),
            new_req.full_url,
        )

        self.assertNotIn("Authorization", result.headers)
        self.assertNotIn("Authorization", result.unredirected_hdrs)

    def test_auth_stripping_redirect_handler_same_host(self):
        handler = ce._AuthStrippingRedirectHandler()

        orig_req = urllib.request.Request(
            "https://marketplace.visualstudio.com/download",
            headers={"Authorization": "Bearer secret_token"},
        )
        new_req = urllib.request.Request(
            "https://marketplace.visualstudio.com/final_download"
        )

        result = handler.redirect_request(
            orig_req,
            None,
            302,
            "Found",
            email.message_from_string(""),
            new_req.full_url,
        )

        self.assertEqual(result.headers.get("Authorization"), "Bearer secret_token")

    def test_safe_filename_part(self):
        self.assertEqual(ce.safe_filename_part("ms-python.python"), "ms-python.python")
        self.assertEqual(ce.safe_filename_part("../../../etc/passwd"), "etc_passwd")
        self.assertEqual(ce.safe_filename_part(".."), "unknown")
        self.assertEqual(ce.safe_filename_part("", "publisher"), "publisher")

    def test_vsix_filename_is_a_single_path_component(self):
        name = ce.vsix_filename("../../etc", "pa/ss", "1.0.0", "linux-x64")
        self.assertNotIn("/", name)
        self.assertNotIn("\\", name)
        self.assertTrue(name.endswith(".vsix"))

    def test_ansi_stripping_stream_filters_every_write_path(self):
        sink = io.StringIO()
        stream = ce._AnsiStrippingStream(sink)
        stream.write("\033[91mred\033[0m\n")
        # writelines must not reach the wrapped stream directly.
        stream.writelines(["\033[92mgreen\033[0m\n", "plain\n"])
        self.assertEqual(sink.getvalue(), "red\ngreen\nplain\n")
        # Everything else still delegates.
        self.assertFalse(stream.isatty())


# =====================================================================
# Atomic Cache & File Security Tests
# =====================================================================
class TestAtomicCacheAndFileSecurity(unittest.TestCase):
    def test_write_cache_atomically(self):
        with tempfile.TemporaryDirectory() as tmp_dir:
            cache_file = os.path.join(tmp_dir, "test_cache.json")
            payload = {"data": "test_value"}

            ce.write_cache_atomically(cache_file, payload)

            self.assertTrue(os.path.exists(cache_file))
            with open(cache_file) as f:
                self.assertEqual(json.load(f), payload)
            # No half-written temporary file may survive a successful write.
            self.assertEqual(os.listdir(tmp_dir), ["test_cache.json"])

    def test_write_cache_atomically_leaves_nothing_behind_on_failure(self):
        with tempfile.TemporaryDirectory() as tmp_dir:
            cache_file = os.path.join(tmp_dir, "test_cache.json")
            ce.write_cache_atomically(cache_file, {"good": 1})

            with self.assertRaises(TypeError):
                ce.write_cache_atomically(cache_file, {"bad": object()})

            # The previous entry survives and no .tmp is left over.
            self.assertEqual(os.listdir(tmp_dir), ["test_cache.json"])
            with open(cache_file) as f:
                self.assertEqual(json.load(f), {"good": 1})

    def test_write_cache_atomically_ignores_unwritable_directory(self):
        if os.name == "nt":
            self.skipTest("POSIX permissions only")
        with tempfile.TemporaryDirectory() as tmp_dir:
            os.chmod(tmp_dir, 0o500)
            try:
                # Caching is best-effort; an unwritable cache dir must not raise.
                ce.write_cache_atomically(os.path.join(tmp_dir, "c.json"), {"a": 1})
            finally:
                os.chmod(tmp_dir, 0o700)

    def test_is_cache_file(self):
        self.assertTrue(ce.is_cache_file("vscode_ext_cache_12345.json"))
        self.assertTrue(ce.is_cache_file("vscode_ext_cache_12345.tmp"))
        self.assertFalse(ce.is_cache_file("other_file.json"))

    def test_clean_spares_a_temp_file_a_concurrent_run_may_own(self):
        with (
            tempfile.TemporaryDirectory() as cache_dir,
            tempfile.TemporaryDirectory() as temp_dir,
        ):
            fresh = os.path.join(cache_dir, "vscode_ext_cache_a.json.999.tmp")
            stale = os.path.join(cache_dir, "vscode_ext_cache_b.json.998.tmp")
            entry = os.path.join(cache_dir, "vscode_ext_cache_c.json")
            for path in (fresh, stale, entry):
                with open(path, "w") as f:
                    f.write("{}")
            old = time.time() - 7200
            os.utime(stale, (old, old))

            with (
                patch.object(ce, "get_cache_dir", return_value=cache_dir),
                patch.object(ce.tempfile, "gettempdir", return_value=temp_dir),
                contextlib.redirect_stdout(io.StringIO()),
            ):
                ce.handle_clean(MagicMock(), {})

            # A .tmp younger than an hour belongs to a run still writing it;
            # removing it would make its os.replace fail.
            self.assertEqual(
                sorted(os.listdir(cache_dir)), ["vscode_ext_cache_a.json.999.tmp"]
            )


# =====================================================================
# CLI Command & Binary Logic Tests
# =====================================================================
class TestCLIAndBinaryParsing(unittest.TestCase):
    def test_parse_code_binary_string(self):
        res = ce.parse_code_binary("code")
        self.assertEqual(len(res), 1)
        self.assertTrue(os.path.basename(res[0]).startswith("code"))

    def test_parse_code_binary_list(self):
        cmd = ce.parse_code_binary(["code-insiders", "--user-data-dir", "/tmp/dir"])
        self.assertEqual(cmd[1:], ["--user-data-dir", "/tmp/dir"])

    def test_run_list_picker_handles_an_empty_list(self):
        """The window height clamps to one row, so an empty list would index [0]
        and the cursor arithmetic would divide by zero."""

        def boom(*args, **kwargs):  # pragma: no cover - must not be reached
            raise AssertionError("nothing should be rendered for an empty list")

        action, selected, cursor, top = ce.run_list_picker(
            0,
            layout=boom,
            header=boom,
            row=boom,
            actions=[],
            unit_label="thing",
        )
        self.assertEqual((action, selected, cursor, top), ("quit", [], 0, 0))

    def test_run_list_picker_hands_back_the_scroll_offset(self):
        """The caller resumes with it, so leaving the list must not reset the
        window to wherever the cursor happens to sit."""
        with (
            patch.object(ce, "get_key", return_value="q"),
            patch.object(
                ce.shutil, "get_terminal_size", return_value=os.terminal_size((80, 9))
            ),
            contextlib.redirect_stdout(io.StringIO()),
        ):
            action, _selected, cursor, top = ce.run_list_picker(
                100,
                layout=lambda cols: ({}, 40),
                header=lambda widths: "header",
                row=lambda i, widths, is_cursor, is_selected: f"row {i}",
                actions=[],
                unit_label="thing",
                cursor_idx=50,
                top=48,
            )
        self.assertEqual((action, cursor, top), ("quit", 50, 48))

    @patch("subprocess.run")
    def test_get_installed_extensions(self, mock_run):
        mock_run.return_value = MagicMock(
            stdout="ms-python.python@2023.1.0\ncharliermarsh.ruff@0.0.1\n",
            returncode=0,
        )
        installed = ce.get_installed_extensions("code")
        self.assertEqual(
            installed,
            {
                "ms-python.python": "2023.1.0",
                "charliermarsh.ruff": "0.0.1",
            },
        )


# Helper to construct mock gallery extension data
def make_mock_gallery_extension(
    pub_name="ms-python",
    ext_name="python",
    version="2024.2.0",
    last_updated=None,
    properties=None,
    categories=None,
    target_platform="universal",
    versions_list=None,
):
    if last_updated is None:
        last_updated = (
            datetime.datetime.now(datetime.timezone.utc) - datetime.timedelta(days=7)
        ).isoformat()
    if versions_list is None:
        versions_list = [
            {
                "version": version,
                "lastUpdated": last_updated,
                "targetPlatform": target_platform,
                "properties": properties
                or [
                    {"key": "Microsoft.VisualStudio.Code.Engine", "value": "^1.80.0"},
                    {
                        "key": "Microsoft.VisualStudio.Services.Links.Source",
                        "value": "https://github.com/example/repo",
                    },
                    {
                        "key": "Microsoft.VisualStudio.Services.Links.Getstarted",
                        "value": "https://example.com/docs",
                    },
                    {
                        "key": "Microsoft.VisualStudio.Services.Content.Pricing",
                        "value": "Free",
                    },
                ],
                "files": [
                    {
                        "assetType": "Microsoft.VisualStudio.Services.VSIXPackage",
                        "source": f"https://marketplace.visualstudio.com/download/{pub_name}.{ext_name}/{version}",
                    }
                ],
            }
        ]
    return {
        "publisher": {"publisherName": pub_name, "displayName": pub_name.capitalize()},
        "extensionName": ext_name,
        "displayName": f"{pub_name}.{ext_name}",
        "shortDescription": f"Test description for {pub_name}.{ext_name}",
        "categories": categories or ["Programming Languages"],
        "versions": versions_list,
    }


# Helper to construct a check_updates() entry
def make_mock_update(
    pub_name="ms-python",
    ext_name="python",
    installed="2024.1.0",
    latest="2024.2.0",
    eligible="2024.2.0",
):
    url = f"https://example.com/{ext_name}.vsix"
    return {
        "id": f"{pub_name}.{ext_name}",
        "publisher": pub_name,
        "name": ext_name,
        "installed": installed,
        "latest": latest,
        "eligible": eligible,
        "eligible_platform": "universal",
        "latest_platform": "universal",
        "latest_release_date": "2024-01-01",
        "eligible_release_date": "2024-01-01",
        "latest_download_url": url,
        "eligible_download_url": url,
    }


# =====================================================================
# Network Retry & Extension ID Validation Tests
# =====================================================================
class TestNetworkRetryAndIDValidation(unittest.TestCase):
    def test_is_valid_extension_id(self):
        valid_ids = [
            "ms-python.python",
            "charliermarsh.ruff",
            "golang.go",
            "pub.name-with-hyphens",
            "pub_name.ext_name",
            "pub.ext.sub",
            "A.B",
            "a1.b2",
        ]
        for vid in valid_ids:
            with self.subTest(vid=vid):
                self.assertTrue(ce.is_valid_extension_id(vid))

        invalid_ids = [
            "python",  # no dot
            "ms-python.python&calc",
            "ms-python.python|dir",
            "ms-python.python;ls",
            "../../etc/passwd",
            "foo..bar",
            "",
            None,
            123,
            " . ",
            # Padding is rejected rather than stripped, so what is validated is
            # exactly what the caller goes on to use as a lookup key.
            "ms-python.python ",
            " ms-python.python",
        ]
        for iid in invalid_ids:
            with self.subTest(iid=iid):
                self.assertFalse(ce.is_valid_extension_id(iid))

    @patch.object(ce, "get_cache_dir", return_value=None)
    @patch.object(ce.time, "sleep")
    def test_post_extension_query_retries_on_json_decode_error(
        self, mock_sleep, mock_cache
    ):
        resp_bad = MagicMock()
        resp_bad.read.return_value = b"<!DOCTYPE html><html>Gateway Error</html>"
        resp_bad.__enter__.return_value = resp_bad
        resp_bad.__exit__.return_value = None

        resp_good = MagicMock()
        resp_good.read.return_value = b'{"results": [{"extensions": []}]}'
        resp_good.__enter__.return_value = resp_good
        resp_good.__exit__.return_value = None

        with (
            patch.object(ce._url_opener, "open", side_effect=[resp_bad, resp_good]),
            contextlib.redirect_stderr(io.StringIO()),
        ):
            result = ce._post_extension_query(
                {"dummy": True}, "https://example.com/gallery"
            )
        self.assertEqual(result, {"results": [{"extensions": []}]})
        mock_sleep.assert_called_once()

    @patch.object(ce, "get_cache_dir", return_value=None)
    @patch.object(ce.time, "sleep")
    def test_post_extension_query_retries_on_incomplete_read(
        self, mock_sleep, mock_cache
    ):
        resp_good = MagicMock()
        resp_good.read.return_value = b'{"results": []}'
        resp_good.__enter__.return_value = resp_good
        resp_good.__exit__.return_value = None

        with (
            patch.object(
                ce._url_opener,
                "open",
                side_effect=[http.client.IncompleteRead(b"partial"), resp_good],
            ),
            contextlib.redirect_stderr(io.StringIO()),
        ):
            result = ce._post_extension_query(
                {"dummy": True}, "https://example.com/gallery"
            )
        self.assertEqual(result, {"results": []})
        mock_sleep.assert_called_once()

    @patch.object(ce, "get_cache_dir", return_value=None)
    @patch.object(ce.time, "sleep")
    def test_post_extension_query_retries_a_refused_connection(
        self, mock_sleep, mock_cache
    ):
        # urllib wraps a connect-phase OSError into URLError, so this never
        # reaches the ConnectionError clause; the URLError arm has to recognize
        # the wrapped cause or a refused connection fails on the first attempt.
        refused = urllib.error.URLError(
            ConnectionRefusedError(111, "Connection refused")
        )

        resp_good = MagicMock()
        resp_good.read.return_value = b'{"results": []}'
        resp_good.__enter__.return_value = resp_good
        resp_good.__exit__.return_value = None

        with (
            patch.object(ce._url_opener, "open", side_effect=[refused, resp_good]),
            contextlib.redirect_stderr(io.StringIO()) as err,
        ):
            result = ce._post_extension_query(
                {"dummy": True}, "https://example.com/gallery"
            )
        self.assertEqual(result, {"results": []})
        mock_sleep.assert_called_once()
        self.assertIn("connection failed", err.getvalue())

    @patch.object(ce, "get_cache_dir", return_value=None)
    @patch.object(ce.time, "sleep")
    def test_post_extension_query_exhausts_retries_on_persistent_bad_json(
        self, mock_sleep, mock_cache
    ):
        resp_bad = MagicMock()
        resp_bad.read.return_value = b"garbage"
        resp_bad.__enter__.return_value = resp_bad
        resp_bad.__exit__.return_value = None

        with (
            patch.object(ce._url_opener, "open", return_value=resp_bad),
            contextlib.redirect_stderr(io.StringIO()),
        ):
            result = ce._post_extension_query(
                {"dummy": True}, "https://example.com/gallery"
            )
        self.assertIsNone(result)
        self.assertEqual(mock_sleep.call_count, 3)


# =====================================================================
# Package Download Tests
# =====================================================================
class FakeDownloadResponse:
    """Minimal stand-in for the object _url_opener.open() hands back."""

    def __init__(self, body, headers=None):
        self._body = body
        self._pos = 0
        self.headers = email.message_from_string("")
        for key, value in (headers or {}).items():
            self.headers[key] = value

    def read(self, size):
        chunk = self._body[self._pos : self._pos + size]
        self._pos += len(chunk)
        return chunk

    def __enter__(self):
        return self

    def __exit__(self, *exc_info):
        return False


class TestDownloadVsix(unittest.TestCase):
    def setUp(self):
        self.tmpdir = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmpdir.cleanup)
        self.filepath = os.path.join(self.tmpdir.name, "ext.vsix")

    def download(self, response, url, **kwargs):
        """Run download_vsix against a canned response, returning the Request."""
        captured = {}

        def fake_open(req, timeout=None):
            captured["req"] = req
            return response

        # download_vsix draws a progress line when stdout is a terminal, which it
        # is when this file is run directly rather than through a pipe.
        with (
            patch.object(ce._url_opener, "open", side_effect=fake_open),
            contextlib.redirect_stdout(io.StringIO()),
        ):
            ce.download_vsix(url, self.filepath, **kwargs)
        return captured["req"]

    def test_download_writes_the_package(self):
        req = self.download(
            FakeDownloadResponse(b"PK\x03\x04payload"),
            "https://open-vsx.org/api/pub/ext/file.vsix",
        )
        self.assertNotIn("Authorization", req.headers)
        with open(self.filepath, "rb") as f:
            self.assertEqual(f.read(), b"PK\x03\x04payload")

    def test_download_sends_the_token_to_open_vsx(self):
        req = self.download(
            FakeDownloadResponse(b"payload"),
            "https://open-vsx.org/api/pub/ext/file.vsix",
            token="secret_pat",
        )
        self.assertEqual(req.headers.get("Authorization"), "Bearer secret_pat")

    def test_download_sends_the_token_to_the_configured_service(self):
        req = self.download(
            FakeDownloadResponse(b"payload"),
            "https://vsx.internal.example.com/files/ext.vsix",
            token="secret_pat",
            service_url="https://vsx.internal.example.com/gallery",
        )
        self.assertEqual(req.headers.get("Authorization"), "Bearer secret_pat")

    def test_download_withholds_the_token_from_any_other_host(self):
        # The download URL comes out of the gallery response, so a host that is
        # neither the configured service nor Open VSX is served anonymously -
        # Microsoft's CDN, a redirector, or a host a compromised response named.
        cases = [
            (
                "https://marketplace.visualstudio.com/_apis/public/gallery/vspackage",
                None,
            ),
            ("https://ms-python.gallerycdn.vsassets.io/file.vsix", None),
            (
                "https://cdn.example.net/file.vsix",
                "https://vsx.internal.example.com/gallery",
            ),
            ("https://open-vsx.org.attacker.com/file.vsix", ce.OPEN_VSX_SERVICE_URL),
        ]
        for url, service_url in cases:
            with self.subTest(url=url):
                req = self.download(
                    FakeDownloadResponse(b"payload"),
                    url,
                    token="secret_pat",
                    service_url=service_url,
                )
                self.assertNotIn("Authorization", req.headers)

    def test_download_refuses_an_oversized_package(self):
        with (
            patch.object(ce, "MAX_VSIX_BYTES", 8),
            self.assertRaises(ce.DOWNLOAD_ERRORS),
        ):
            self.download(
                FakeDownloadResponse(b"x" * 64),
                "https://open-vsx.org/api/pub/ext/file.vsix",
            )
        # A truncated package must never be left behind for --install-extension.
        self.assertFalse(os.path.exists(self.filepath))

    def test_download_refuses_a_corrupt_compressed_package(self):
        with self.assertRaises(ce.DOWNLOAD_ERRORS):
            self.download(
                FakeDownloadResponse(b"not actually gzip", {"Content-Encoding": "gzip"}),
                "https://open-vsx.org/api/pub/ext/file.vsix",
            )
        self.assertFalse(os.path.exists(self.filepath))

    def test_download_decompresses_a_gzip_encoded_package(self):
        compressor = zlib.compressobj(wbits=16 + zlib.MAX_WBITS)
        body = compressor.compress(b"PK\x03\x04payload") + compressor.flush()

        self.download(
            FakeDownloadResponse(body, {"Content-Encoding": "gzip"}),
            "https://open-vsx.org/api/pub/ext/file.vsix",
        )
        with open(self.filepath, "rb") as f:
            self.assertEqual(f.read(), b"PK\x03\x04payload")


# =====================================================================
# CLI Integration Tests: handle_install
# =====================================================================
class TestHandleInstallIntegration(unittest.TestCase):
    def setUp(self):
        self.config = {"extensions": {}}

    @patch.object(ce, "run_code_cmd")
    @patch.object(ce, "download_vsix")
    @patch.object(ce, "get_installed_extensions", return_value={})
    @patch.object(ce, "get_vscode_version", return_value="1.85.0")
    @patch.object(ce, "query_marketplace_extensions")
    def test_handle_install_success(
        self, mock_query, mock_vsver, mock_installed, mock_download, mock_run
    ):
        mock_query.return_value = {
            "ms-python.python": make_mock_gallery_extension(
                "ms-python", "python", "2024.2.0"
            )
        }
        args = argparse.Namespace(
            code_binary="code",
            service_url=None,
            open_vsx=False,
            open_vsx_token=None,
            extensions=["ms-python.python"],
            file=None,
            include_prerelease=False,
            no_code_version_check=False,
            yes=True,
            min_release_age="0",
            download_dir=None,
            force=False,
        )
        with contextlib.redirect_stdout(io.StringIO()):
            ce.handle_install(args, self.config)

        mock_download.assert_called_once()
        mock_run.assert_called_once()
        self.assertIn("--install-extension", mock_run.call_args[0][0])

    @patch.object(ce, "run_code_cmd")
    @patch.object(ce, "download_vsix")
    @patch.object(ce, "get_installed_extensions", return_value={})
    @patch.object(ce, "get_vscode_version", return_value="1.85.0")
    @patch.object(ce, "query_marketplace_extensions")
    def test_handle_install_pinned_version(
        self, mock_query, mock_vsver, mock_installed, mock_download, mock_run
    ):
        ext_data = make_mock_gallery_extension(
            "ms-python",
            "python",
            versions_list=[
                {
                    "version": "2024.2.0",
                    "targetPlatform": "universal",
                    "properties": [
                        {
                            "key": "Microsoft.VisualStudio.Code.Engine",
                            "value": "^1.80.0",
                        }
                    ],
                    "files": [
                        {
                            "assetType": "Microsoft.VisualStudio.Services.VSIXPackage",
                            "source": "https://marketplace.visualstudio.com/download/2024.2.0",
                        }
                    ],
                },
                {
                    "version": "2024.1.0",
                    "targetPlatform": "universal",
                    "properties": [
                        {
                            "key": "Microsoft.VisualStudio.Code.Engine",
                            "value": "^1.80.0",
                        }
                    ],
                    "files": [
                        {
                            "assetType": "Microsoft.VisualStudio.Services.VSIXPackage",
                            "source": "https://marketplace.visualstudio.com/download/2024.1.0",
                        }
                    ],
                },
            ],
        )
        mock_query.return_value = {"ms-python.python": ext_data}
        args = argparse.Namespace(
            code_binary="code",
            service_url=None,
            open_vsx=False,
            open_vsx_token=None,
            extensions=["ms-python.python@2024.1.0"],
            file=None,
            include_prerelease=False,
            no_code_version_check=False,
            yes=True,
            min_release_age="0",
            download_dir=None,
            force=False,
        )
        with contextlib.redirect_stdout(io.StringIO()):
            ce.handle_install(args, self.config)

        call_url = mock_download.call_args[0][0]
        self.assertIn("2024.1.0", call_url)
        self.assertIn("2024.1.0", mock_download.call_args[0][1])

    @patch.object(ce, "run_code_cmd")
    @patch.object(ce, "download_vsix")
    @patch.object(ce, "get_installed_extensions", return_value={})
    @patch.object(ce, "get_vscode_version", return_value="1.85.0")
    @patch.object(ce, "query_marketplace_extensions")
    def test_handle_install_from_file(
        self, mock_query, mock_vsver, mock_installed, mock_download, mock_run
    ):
        mock_query.return_value = {
            "ms-python.python": make_mock_gallery_extension(
                "ms-python", "python", "2024.2.0"
            ),
            "charliermarsh.ruff": make_mock_gallery_extension(
                "charliermarsh", "ruff", "0.1.0"
            ),
        }
        with tempfile.NamedTemporaryFile("w", delete=False) as tf:
            tf.write("# Extension list\nms-python.python\n\ncharliermarsh.ruff\n")
            temp_path = tf.name

        try:
            args = argparse.Namespace(
                code_binary="code",
                service_url=None,
                open_vsx=False,
                open_vsx_token=None,
                extensions=[],
                file=temp_path,
                include_prerelease=False,
                no_code_version_check=False,
                yes=True,
                min_release_age="0",
                download_dir=None,
                force=False,
            )
            with contextlib.redirect_stdout(io.StringIO()):
                ce.handle_install(args, self.config)

            self.assertEqual(mock_download.call_count, 2)
            self.assertEqual(mock_run.call_count, 2)
        finally:
            os.remove(temp_path)

    @patch.object(ce, "run_code_cmd")
    @patch.object(ce, "download_vsix")
    @patch.object(
        ce,
        "get_installed_extensions",
        return_value={"ms-python.python": "2024.2.0"},
    )
    @patch.object(ce, "get_vscode_version", return_value="1.85.0")
    @patch.object(ce, "query_marketplace_extensions")
    def test_handle_install_already_installed_skips(
        self, mock_query, mock_vsver, mock_installed, mock_download, mock_run
    ):
        mock_query.return_value = {
            "ms-python.python": make_mock_gallery_extension(
                "ms-python", "python", "2024.2.0"
            )
        }
        args = argparse.Namespace(
            code_binary="code",
            service_url=None,
            open_vsx=False,
            open_vsx_token=None,
            extensions=["ms-python.python"],
            file=None,
            include_prerelease=False,
            no_code_version_check=False,
            yes=True,
            min_release_age="0",
            download_dir=None,
            force=False,
        )
        with contextlib.redirect_stdout(io.StringIO()) as out:
            ce.handle_install(args, self.config)

        mock_download.assert_not_called()
        mock_run.assert_not_called()
        self.assertIn("already installed", out.getvalue())

    @patch.object(ce, "run_code_cmd")
    @patch.object(ce, "download_vsix")
    @patch.object(
        ce,
        "get_installed_extensions",
        return_value={"ms-python.python": "2024.2.0"},
    )
    @patch.object(ce, "get_vscode_version", return_value="1.85.0")
    @patch.object(ce, "query_marketplace_extensions")
    def test_handle_install_force_reinstalls(
        self, mock_query, mock_vsver, mock_installed, mock_download, mock_run
    ):
        mock_query.return_value = {
            "ms-python.python": make_mock_gallery_extension(
                "ms-python", "python", "2024.2.0"
            )
        }
        args = argparse.Namespace(
            code_binary="code",
            service_url=None,
            open_vsx=False,
            open_vsx_token=None,
            extensions=["ms-python.python"],
            file=None,
            include_prerelease=False,
            no_code_version_check=False,
            yes=True,
            min_release_age="0",
            download_dir=None,
            force=True,
        )
        with contextlib.redirect_stdout(io.StringIO()):
            ce.handle_install(args, self.config)

        mock_download.assert_called_once()
        mock_run.assert_called_once()
        self.assertIn("--force", mock_run.call_args[0][0])

    @patch.object(ce, "run_code_cmd")
    @patch.object(ce, "download_vsix")
    @patch.object(ce, "get_installed_extensions", return_value={})
    @patch.object(ce, "get_vscode_version", return_value="1.85.0")
    @patch.object(ce, "query_marketplace_extensions")
    def test_handle_install_held_back_by_release_age_installs_older(
        self, mock_query, mock_vsver, mock_installed, mock_download, mock_run
    ):
        now = datetime.datetime.now(datetime.timezone.utc)
        ext_data = make_mock_gallery_extension(
            "ms-python",
            "python",
            versions_list=[
                {
                    "version": "2024.2.0",
                    "lastUpdated": (now - datetime.timedelta(hours=2)).isoformat(),
                    "targetPlatform": "universal",
                    "properties": [
                        {
                            "key": "Microsoft.VisualStudio.Code.Engine",
                            "value": "^1.80.0",
                        }
                    ],
                    "files": [
                        {
                            "assetType": "Microsoft.VisualStudio.Services.VSIXPackage",
                            "source": "https://marketplace.visualstudio.com/download/2024.2.0",
                        }
                    ],
                },
                {
                    "version": "2024.1.0",
                    "lastUpdated": (now - datetime.timedelta(hours=48)).isoformat(),
                    "targetPlatform": "universal",
                    "properties": [
                        {
                            "key": "Microsoft.VisualStudio.Code.Engine",
                            "value": "^1.80.0",
                        }
                    ],
                    "files": [
                        {
                            "assetType": "Microsoft.VisualStudio.Services.VSIXPackage",
                            "source": "https://marketplace.visualstudio.com/download/2024.1.0",
                        }
                    ],
                },
            ],
        )
        mock_query.return_value = {"ms-python.python": ext_data}
        args = argparse.Namespace(
            code_binary="code",
            service_url=None,
            open_vsx=False,
            open_vsx_token=None,
            extensions=["ms-python.python"],
            file=None,
            include_prerelease=False,
            no_code_version_check=False,
            yes=True,
            min_release_age="24h",
            download_dir=None,
            force=False,
        )
        with contextlib.redirect_stdout(io.StringIO()):
            ce.handle_install(args, self.config)

        call_url = mock_download.call_args[0][0]
        self.assertIn("2024.1.0", call_url)

    @patch.object(ce, "run_code_cmd")
    @patch.object(
        ce,
        "download_vsix",
        side_effect=ValueError("package exceeds the 1024MB limit"),
    )
    @patch.object(ce, "get_installed_extensions", return_value={})
    @patch.object(ce, "get_vscode_version", return_value="1.85.0")
    @patch.object(ce, "query_marketplace_extensions")
    def test_handle_install_reports_an_oversized_package(
        self, mock_query, mock_vsver, mock_installed, mock_download, mock_run
    ):
        mock_query.return_value = {
            "ms-python.python": make_mock_gallery_extension(
                "ms-python", "python", "2024.2.0"
            )
        }
        args = argparse.Namespace(
            code_binary="code",
            service_url=None,
            open_vsx=False,
            open_vsx_token=None,
            extensions=["ms-python.python"],
            file=None,
            include_prerelease=False,
            no_code_version_check=False,
            yes=True,
            min_release_age="0",
            download_dir=None,
            force=False,
        )
        with (
            contextlib.redirect_stdout(io.StringIO()),
            contextlib.redirect_stderr(io.StringIO()) as err,
        ):
            ce.handle_install(args, self.config)

        # A rejected package is a reported failure, not a traceback.
        self.assertIn("Download failed", err.getvalue())
        mock_run.assert_not_called()

    @patch.object(ce, "download_vsix")
    @patch.object(ce, "get_installed_extensions", return_value={})
    @patch.object(ce, "get_vscode_version", return_value="1.85.0")
    def test_handle_install_invalid_id_rejected(
        self, mock_vsver, mock_installed, mock_download
    ):
        args = argparse.Namespace(
            code_binary="code",
            service_url=None,
            open_vsx=False,
            open_vsx_token=None,
            extensions=["invalid_id_no_dot", "ms-python.python&calc"],
            file=None,
            include_prerelease=False,
            no_code_version_check=False,
            yes=True,
            min_release_age="0",
            download_dir=None,
            force=False,
        )
        with (
            contextlib.redirect_stdout(io.StringIO()),
            contextlib.redirect_stderr(io.StringIO()) as err,
            self.assertRaises(SystemExit) as exit_ctx,
        ):
            ce.handle_install(args, self.config)

        # Rejecting every spec has to be distinguishable from installing them.
        self.assertEqual(exit_ctx.exception.code, 1)
        mock_download.assert_not_called()
        self.assertIn("Invalid extension ID", err.getvalue())

    @patch.object(ce, "run_code_cmd")
    @patch.object(ce, "download_vsix")
    @patch.object(ce, "get_installed_extensions", return_value={})
    @patch.object(ce, "get_vscode_version", return_value="1.85.0")
    @patch.object(ce, "query_marketplace_extensions")
    def test_handle_install_tolerates_a_space_before_the_version_pin(
        self, mock_query, mock_vsver, mock_installed, mock_download, mock_run
    ):
        # 'pub.name @1.2.3' leaves a trailing space on the id after the rsplit.
        # The gallery response is keyed by the canonical id, so the padded form
        # has to be normalized before the query or the lookup misses and a real
        # extension is reported as not found.
        mock_query.return_value = {
            "ms-python.python": make_mock_gallery_extension(
                "ms-python", "python", "2024.2.0"
            )
        }
        args = argparse.Namespace(
            code_binary="code",
            service_url=None,
            open_vsx=False,
            open_vsx_token=None,
            extensions=["ms-python.python @2024.2.0"],
            file=None,
            include_prerelease=False,
            no_code_version_check=False,
            yes=True,
            min_release_age="0",
            download_dir=None,
            force=False,
        )
        with (
            contextlib.redirect_stdout(io.StringIO()),
            contextlib.redirect_stderr(io.StringIO()) as err,
        ):
            ce.handle_install(args, self.config)

        self.assertEqual(mock_query.call_args[0][0], ["ms-python.python"])
        self.assertNotIn("not found", err.getvalue())
        mock_download.assert_called_once()
        mock_run.assert_called_once()


# =====================================================================
# CLI Integration Tests: handle_update
# =====================================================================
class TestHandleUpdateIntegration(unittest.TestCase):
    def setUp(self):
        self.config = {"extensions": {}}

    def update_args(self, **overrides):
        defaults = dict(
            code_binary="code",
            service_url=None,
            open_vsx=False,
            open_vsx_token=None,
            extensions=[],
            include_prerelease=False,
            no_code_version_check=False,
            dry_run=False,
            download_dir=None,
            yes=True,
            min_release_age="24h",
        )
        defaults.update(overrides)
        return argparse.Namespace(**defaults)

    @patch.object(ce, "get_vscode_version", return_value="1.85.0")
    @patch.object(ce, "check_updates", return_value=[])
    @patch.object(
        ce,
        "get_installed_extensions",
        return_value={"ms-python.python": "2024.2.0"},
    )
    def test_handle_update_all_up_to_date(
        self, mock_installed, mock_updates, mock_vsver
    ):
        args = argparse.Namespace(
            code_binary="code",
            service_url=None,
            open_vsx=False,
            open_vsx_token=None,
            extensions=[],
            include_prerelease=False,
            no_code_version_check=False,
            dry_run=False,
            download_dir=None,
            yes=True,
            min_release_age="24h",
        )
        with contextlib.redirect_stdout(io.StringIO()) as out:
            ce.handle_update(args, self.config)

        self.assertIn("All extensions are up to date", out.getvalue())

    @patch.object(ce, "run_code_cmd")
    @patch.object(ce, "download_vsix")
    @patch.object(ce, "get_vscode_version", return_value="1.85.0")
    @patch.object(
        ce,
        "get_installed_extensions",
        return_value={"ms-python.python": "2024.1.0"},
    )
    @patch.object(ce, "check_updates")
    def test_handle_update_yes_installs_eligible(
        self, mock_check, mock_installed, mock_vsver, mock_download, mock_run
    ):
        mock_check.return_value = [
            {
                "id": "ms-python.python",
                "publisher": "ms-python",
                "name": "python",
                "installed": "2024.1.0",
                "latest": "2024.2.0",
                "eligible": "2024.2.0",
                "eligible_platform": "universal",
                "latest_platform": "universal",
                "latest_release_date": "2024-01-01",
                "eligible_release_date": "2024-01-01",
                "latest_download_url": "https://example.com/python.vsix",
                "eligible_download_url": "https://example.com/python.vsix",
            }
        ]
        args = argparse.Namespace(
            code_binary="code",
            service_url=None,
            open_vsx=False,
            open_vsx_token=None,
            extensions=[],
            include_prerelease=False,
            no_code_version_check=False,
            dry_run=False,
            download_dir=None,
            yes=True,
            min_release_age="24h",
        )
        with contextlib.redirect_stdout(io.StringIO()):
            ce.handle_update(args, self.config)

        mock_download.assert_called_once()
        mock_run.assert_called_once()
        self.assertIn("--install-extension", mock_run.call_args[0][0])

    @patch.object(ce, "run_code_cmd")
    @patch.object(ce, "download_vsix")
    @patch.object(ce, "get_vscode_version", return_value="1.85.0")
    @patch.object(
        ce,
        "get_installed_extensions",
        return_value={"ms-python.python": "2024.1.0"},
    )
    @patch.object(ce, "check_updates")
    def test_handle_update_without_a_terminal_reports_but_installs_nothing(
        self, mock_check, mock_installed, mock_vsver, mock_download, mock_run
    ):
        mock_check.return_value = [make_mock_update()]
        args = self.update_args(yes=None)

        # redirect_stdout hands handle_update a non-tty stream, which is what the
        # piped/cron case looks like.
        with contextlib.redirect_stdout(io.StringIO()) as out:
            ce.handle_update(args, self.config)

        mock_download.assert_not_called()
        mock_run.assert_not_called()
        output = out.getvalue()
        self.assertIn("Updates available", output)
        self.assertIn("Re-run with -y", output)

    @patch.object(ce, "run_code_cmd")
    @patch.object(ce, "download_vsix")
    @patch.object(ce, "get_vscode_version", return_value="1.85.0")
    @patch.object(
        ce,
        "get_installed_extensions",
        return_value={"ms-python.python": "2024.1.0"},
    )
    @patch.object(ce, "check_updates")
    def test_handle_update_dry_run_still_reports_without_a_terminal(
        self, mock_check, mock_installed, mock_vsver, mock_download, mock_run
    ):
        mock_check.return_value = [make_mock_update()]
        args = self.update_args(yes=None, dry_run=True)

        with contextlib.redirect_stdout(io.StringIO()) as out:
            ce.handle_update(args, self.config)

        mock_download.assert_not_called()
        mock_run.assert_not_called()
        self.assertIn("Would update 1 extension(s)", out.getvalue())

    @patch.object(ce, "run_code_cmd")
    @patch.object(ce, "download_vsix")
    @patch.object(ce, "get_vscode_version", return_value="1.85.0")
    @patch.object(
        ce,
        "get_installed_extensions",
        return_value={"ms-python.python": "2024.1.0"},
    )
    @patch.object(ce, "check_updates")
    def test_handle_update_dry_run(
        self, mock_check, mock_installed, mock_vsver, mock_download, mock_run
    ):
        mock_check.return_value = [
            {
                "id": "ms-python.python",
                "publisher": "ms-python",
                "name": "python",
                "installed": "2024.1.0",
                "latest": "2024.2.0",
                "eligible": "2024.2.0",
                "eligible_platform": "universal",
                "latest_platform": "universal",
                "latest_release_date": "2024-01-01",
                "eligible_release_date": "2024-01-01",
                "latest_download_url": "https://example.com/python.vsix",
                "eligible_download_url": "https://example.com/python.vsix",
            }
        ]
        args = argparse.Namespace(
            code_binary="code",
            service_url=None,
            open_vsx=False,
            open_vsx_token=None,
            extensions=[],
            include_prerelease=False,
            no_code_version_check=False,
            dry_run=True,
            download_dir=None,
            yes=True,
            min_release_age="24h",
        )
        with contextlib.redirect_stdout(io.StringIO()) as out:
            ce.handle_update(args, self.config)

        mock_download.assert_not_called()
        mock_run.assert_not_called()
        self.assertIn("[Dry-run]", out.getvalue())

    @patch.object(ce, "run_code_cmd")
    @patch.object(ce, "download_vsix")
    @patch.object(ce, "get_vscode_version", return_value="1.85.0")
    @patch.object(
        ce,
        "get_installed_extensions",
        return_value={
            "ms-python.python": "2024.1.0",
            "charliermarsh.ruff": "0.1.0",
        },
    )
    @patch.object(ce, "check_updates")
    def test_handle_update_targeted_extension(
        self, mock_check, mock_installed, mock_vsver, mock_download, mock_run
    ):
        mock_check.return_value = []
        args = argparse.Namespace(
            code_binary="code",
            service_url=None,
            open_vsx=False,
            open_vsx_token=None,
            extensions=["python"],
            include_prerelease=False,
            no_code_version_check=False,
            dry_run=False,
            download_dir=None,
            yes=True,
            min_release_age="24h",
        )
        with contextlib.redirect_stdout(io.StringIO()):
            ce.handle_update(args, self.config)

        passed_exts = mock_check.call_args[0][0]
        self.assertEqual(list(passed_exts.keys()), ["ms-python.python"])


# =====================================================================
# CLI Integration Tests: handle_remove
# =====================================================================
class TestHandleRemoveIntegration(unittest.TestCase):
    @patch.object(ce, "run_code_cmd")
    @patch.object(
        ce,
        "get_installed_extensions",
        return_value={"ms-python.python": "2024.2.0"},
    )
    def test_handle_remove_explicit_with_yes(self, mock_installed, mock_run):
        args = argparse.Namespace(
            code_binary="code",
            yes=True,
            extensions=["ms-python.python"],
        )
        with contextlib.redirect_stdout(io.StringIO()):
            ce.handle_remove(args, {})

        mock_run.assert_called_once()
        self.assertEqual(
            mock_run.call_args[0][0][1:],
            ["--uninstall-extension", "ms-python.python"],
        )

    @patch.object(ce, "run_code_cmd")
    @patch.object(
        ce,
        "get_installed_extensions",
        return_value={"ms-python.python": "2024.2.0"},
    )
    def test_handle_remove_nonexistent(self, mock_installed, mock_run):
        args = argparse.Namespace(
            code_binary="code",
            yes=True,
            extensions=["other.nonexistent"],
        )
        with (
            contextlib.redirect_stdout(io.StringIO()) as out,
            contextlib.redirect_stderr(io.StringIO()),
        ):
            ce.handle_remove(args, {})

        mock_run.assert_not_called()
        self.assertIn("No matching installed extensions to remove", out.getvalue())


# =====================================================================
# CLI Integration Tests: handle_list
# =====================================================================
class TestHandleListIntegration(unittest.TestCase):
    @patch.object(
        ce,
        "get_installed_extensions",
        return_value={
            "ms-python.python": "2024.2.0",
            "charliermarsh.ruff": "0.1.0",
        },
    )
    def test_handle_list_standard(self, mock_installed):
        args = argparse.Namespace(
            code_binary="code",
            query=None,
            quiet=False,
            outdated=False,
        )
        with contextlib.redirect_stdout(io.StringIO()) as out:
            ce.handle_list(args, {})

        output = out.getvalue()
        self.assertIn("ms-python.python", output)
        self.assertIn("charliermarsh.ruff", output)
        self.assertIn("Total: 2 extension(s)", output)

    @patch.object(
        ce,
        "get_installed_extensions",
        return_value={
            "ms-python.python": "2024.2.0",
            "charliermarsh.ruff": "0.1.0",
        },
    )
    def test_handle_list_quiet(self, mock_installed):
        args = argparse.Namespace(
            code_binary="code",
            query=None,
            quiet=True,
            outdated=False,
        )
        with contextlib.redirect_stdout(io.StringIO()) as out:
            ce.handle_list(args, {})

        output = out.getvalue().strip().splitlines()
        self.assertEqual(output, ["charliermarsh.ruff", "ms-python.python"])

    @patch.object(
        ce,
        "get_installed_extensions",
        return_value={
            "ms-python.python": "2024.2.0",
            "charliermarsh.ruff": "0.1.0",
        },
    )
    def test_handle_list_query_filter(self, mock_installed):
        args = argparse.Namespace(
            code_binary="code",
            query="ruff",
            quiet=True,
            outdated=False,
        )
        with contextlib.redirect_stdout(io.StringIO()) as out:
            ce.handle_list(args, {})

        self.assertEqual(out.getvalue().strip(), "charliermarsh.ruff")

    @patch.object(ce, "get_vscode_version", return_value="1.85.0")
    @patch.object(ce, "check_updates")
    @patch.object(
        ce,
        "get_installed_extensions",
        return_value={
            "ms-python.python": "2024.1.0",
            "charliermarsh.ruff": "0.1.0",
        },
    )
    def test_handle_list_outdated(self, mock_installed, mock_updates, mock_vsver):
        mock_updates.return_value = [
            {
                "id": "ms-python.python",
                "installed": "2024.1.0",
                "latest": "2024.2.0",
            }
        ]
        args = argparse.Namespace(
            code_binary="code",
            query=None,
            quiet=False,
            outdated=True,
            include_prerelease=False,
            no_code_version_check=False,
            min_release_age="24h",
            service_url=None,
            open_vsx=False,
            open_vsx_token=None,
        )
        with contextlib.redirect_stdout(io.StringIO()) as out:
            ce.handle_list(args, {})

        output = out.getvalue()
        self.assertIn("ms-python.python", output)
        self.assertNotIn("charliermarsh.ruff", output)


# =====================================================================
# CLI Integration Tests: handle_search
# =====================================================================
class TestHandleSearchIntegration(unittest.TestCase):
    @patch.object(ce, "get_vscode_version", return_value="1.85.0")
    @patch.object(ce, "query_marketplace_search")
    def test_handle_search_quiet(self, mock_search, mock_vsver):
        mock_search.return_value = [
            {
                "id": "ms-python.python",
                "displayName": "Python",
                "eligible": "2024.2.0",
                "description": "Python language support",
                "is_held_back": False,
            }
        ]
        args = argparse.Namespace(
            code_binary="code",
            query="python",
            max_results=10,
            quiet=True,
            include_prerelease=False,
            no_code_version_check=False,
            min_release_age="24h",
            service_url=None,
            open_vsx=False,
            open_vsx_token=None,
        )
        with contextlib.redirect_stdout(io.StringIO()) as out:
            ce.handle_search(args, {})

        self.assertEqual(out.getvalue().strip(), "ms-python.python")

    @patch.object(ce, "get_installed_extensions", return_value={})
    @patch.object(ce, "get_vscode_version", return_value="1.85.0")
    @patch.object(ce, "query_marketplace_search")
    def test_handle_search_table_output_non_tty(
        self, mock_search, mock_vsver, mock_installed
    ):
        mock_search.return_value = [
            {
                "id": "ms-python.python",
                "displayName": "Python",
                "eligible": "2024.2.0",
                "description": "Python language support",
                "is_held_back": False,
            }
        ]
        args = argparse.Namespace(
            code_binary="code",
            query="python",
            max_results=10,
            quiet=False,
            include_prerelease=False,
            no_code_version_check=False,
            min_release_age="24h",
            service_url=None,
            open_vsx=False,
            open_vsx_token=None,
        )
        with (
            patch("sys.stdin.isatty", return_value=False),
            contextlib.redirect_stdout(io.StringIO()) as out,
        ):
            ce.handle_search(args, {})

        output = out.getvalue()
        self.assertIn("ms-python.python", output)
        self.assertIn("Python", output)
        self.assertIn("Found 1 matching extension(s)", output)


# =====================================================================
# CLI Integration Tests: handle_info
# =====================================================================
class TestHandleInfoIntegration(unittest.TestCase):
    @patch.object(ce, "get_vscode_version", return_value="1.85.0")
    @patch.object(
        ce,
        "get_installed_extensions",
        return_value={"ms-python.python": "2024.1.0"},
    )
    @patch.object(ce, "query_marketplace_extensions")
    def test_handle_info_found(self, mock_query, mock_installed, mock_vsver):
        mock_query.return_value = {
            "ms-python.python": make_mock_gallery_extension(
                "ms-python", "python", "2024.2.0"
            )
        }
        args = argparse.Namespace(
            extension="ms-python.python",
            code_binary="code",
            service_url=None,
            open_vsx=False,
            open_vsx_token=None,
            include_prerelease=False,
            no_code_version_check=False,
            min_release_age="24h",
        )
        with contextlib.redirect_stdout(io.StringIO()) as out:
            ce.handle_info(args, {})

        output = out.getvalue()
        self.assertIn("ms-python.python", output)
        self.assertIn("Publisher:", output)
        self.assertIn("Latest Ver:", output)
        self.assertIn("Installed (v2024.1.0)", output)
        self.assertIn("Repository:", output)

    @patch.object(ce, "get_vscode_version", return_value="1.85.0")
    @patch.object(ce, "get_installed_extensions", return_value={})
    @patch.object(ce, "query_marketplace_search")
    @patch.object(ce, "query_marketplace_extensions")
    def test_handle_info_partial_name_fallback(
        self, mock_exts, mock_search, mock_installed, mock_vsver
    ):
        mock_search.return_value = [{"id": "ms-python.python"}]
        mock_exts.return_value = {
            "ms-python.python": make_mock_gallery_extension(
                "ms-python", "python", "2024.2.0"
            )
        }
        args = argparse.Namespace(
            extension="python",
            code_binary="code",
            service_url=None,
            open_vsx=False,
            open_vsx_token=None,
            include_prerelease=False,
            no_code_version_check=False,
            min_release_age="24h",
        )
        with contextlib.redirect_stdout(io.StringIO()) as out:
            ce.handle_info(args, {})

        output = out.getvalue()
        self.assertIn("Showing info for top match 'ms-python.python'", output)
        self.assertIn("ms-python.python", output)

    @patch.object(ce, "get_vscode_version", return_value="1.85.0")
    @patch.object(ce, "get_installed_extensions", return_value={})
    @patch.object(ce, "query_marketplace_search")
    @patch.object(ce, "query_marketplace_extensions")
    def test_handle_info_searches_rather_than_querying_a_malformed_id(
        self, mock_exts, mock_search, mock_installed, mock_vsver
    ):
        # A dot alone used to route straight to a by-id query, which can only
        # answer 'not found' for something that is not a well-formed id.
        mock_search.return_value = [{"id": "ms-python.python"}]
        mock_exts.return_value = {
            "ms-python.python": make_mock_gallery_extension(
                "ms-python", "python", "2024.2.0"
            )
        }
        args = argparse.Namespace(
            extension="ms-python.python&calc",
            code_binary="code",
            service_url=None,
            open_vsx=False,
            open_vsx_token=None,
            include_prerelease=False,
            no_code_version_check=False,
            min_release_age="24h",
        )
        with contextlib.redirect_stdout(io.StringIO()) as out:
            ce.handle_info(args, {})

        mock_search.assert_called_once()
        self.assertEqual(mock_search.call_args[0][0], "ms-python.python&calc")
        self.assertIn("Showing info for top match 'ms-python.python'", out.getvalue())


# =====================================================================
# CLI Integration Tests: handle_clean
# =====================================================================
class TestHandleCleanIntegration(unittest.TestCase):
    def test_handle_clean_purges_cache_and_old_temp_dirs(self):
        with (
            tempfile.TemporaryDirectory() as cache_dir,
            tempfile.TemporaryDirectory() as temp_dir,
        ):
            # Create a stale cache file
            cache_file = os.path.join(cache_dir, "vscode_ext_cache_test.json")
            with open(cache_file, "w") as f:
                f.write('{"data": 123}')

            # Create an old code-extensions temp dir
            ext_temp_dir = os.path.join(temp_dir, "code-extensions-old")
            os.makedirs(ext_temp_dir, exist_ok=True)
            dummy_vsix = os.path.join(ext_temp_dir, "test.vsix")
            with open(dummy_vsix, "w") as f:
                f.write("mock vsix payload")
            old_time = time.time() - 7200
            os.utime(ext_temp_dir, (old_time, old_time))

            args = argparse.Namespace()
            with (
                patch.object(ce, "get_cache_dir", return_value=cache_dir),
                patch.object(ce.tempfile, "gettempdir", return_value=temp_dir),
                contextlib.redirect_stdout(io.StringIO()) as out,
            ):
                ce.handle_clean(args, {})

            self.assertFalse(os.path.exists(cache_file))
            self.assertFalse(os.path.exists(ext_temp_dir))
            self.assertIn("Cleaned", out.getvalue())


# =====================================================================
# CLI Integration Tests: handle_config
# =====================================================================
class TestHandleConfigIntegration(unittest.TestCase):
    def test_handle_config_lifecycle(self):
        with tempfile.TemporaryDirectory() as tmp_dir:
            config_path = os.path.join(tmp_dir, "config.toml")
            with (
                patch.object(ce, "get_default_config_path", return_value=config_path),
                contextlib.redirect_stdout(io.StringIO()),
            ):
                config = ce.load_config()

                # 1. Config set global
                set_args = argparse.Namespace(
                    action="set", key="min_release_age", value="3d"
                )
                ce.handle_config(set_args, config)

                # 2. Config set per-extension
                set_ext_args = argparse.Namespace(
                    action="set",
                    key="charliermarsh.ruff.min_release_age",
                    value="12h",
                )
                ce.handle_config(set_ext_args, config)

                # Reload config from disk
                reloaded = ce.load_config()
                self.assertEqual(reloaded.get("min_release_age"), "3d")
                self.assertEqual(
                    reloaded.get("extensions", {})
                    .get("charliermarsh.ruff", {})
                    .get("min_release_age"),
                    "12h",
                )

                # 3. Config get
                get_args = argparse.Namespace(
                    action="get", key="min_release_age", value=None
                )
                with contextlib.redirect_stdout(io.StringIO()) as get_out:
                    ce.handle_config(get_args, reloaded)
                self.assertEqual(get_out.getvalue().strip(), "3d")

                # 4. Config unset
                unset_args = argparse.Namespace(
                    action="unset", key="min_release_age", value=None
                )
                ce.handle_config(unset_args, reloaded)
                after_unset = ce.load_config()
                self.assertNotIn("min_release_age", after_unset)

    def test_handle_config_still_reaches_a_legacy_malformed_extension_entry(self):
        # Releases before id validation accepted 'foo.ignore' and wrote an
        # [extensions.foo] section. 'set' now refuses to create one, but 'get'
        # and 'unset' must keep reaching the existing section, or it could only
        # be removed by hand-editing the TOML.
        with tempfile.TemporaryDirectory() as tmp_dir:
            config_path = os.path.join(tmp_dir, "config.toml")
            with open(config_path, "w", encoding="utf-8") as f:
                f.write("[extensions.foo]\nignore = true\n")

            with (
                patch.object(ce, "get_default_config_path", return_value=config_path),
                contextlib.redirect_stderr(io.StringIO()) as err,
            ):
                get_args = argparse.Namespace(
                    action="get", key="foo.ignore", value=None
                )
                with contextlib.redirect_stdout(io.StringIO()) as get_out:
                    ce.handle_config(get_args, ce.load_config())
                self.assertEqual(get_out.getvalue().strip(), "True")

                set_args = argparse.Namespace(
                    action="set", key="foo.ignore", value="false"
                )
                with (
                    contextlib.redirect_stdout(io.StringIO()),
                    self.assertRaises(SystemExit),
                ):
                    ce.handle_config(set_args, ce.load_config())
                # The refusal names the malformed id, not the global key list.
                self.assertIn("Invalid extension ID", err.getvalue())
                self.assertNotIn("Unknown global setting", err.getvalue())

                unset_args = argparse.Namespace(
                    action="unset", key="foo.ignore", value=None
                )
                with contextlib.redirect_stdout(io.StringIO()):
                    ce.handle_config(unset_args, ce.load_config())
                self.assertNotIn("foo", ce.load_config().get("extensions", {}))

    def test_parse_config_key_validates_only_when_asked(self):
        # A dotted key is always an extension rule, so a malformed one comes
        # back as 'invalid' rather than being retried as a global setting.
        self.assertEqual(
            ce.parse_config_key("foo.ignore"), ("invalid", "foo", "ignore")
        )
        self.assertEqual(
            ce.parse_config_key("extensions.foo.ignore"), ("invalid", "foo", "ignore")
        )
        self.assertEqual(
            ce.parse_config_key("foo.ignore", validate=False),
            ("extension", "foo", "ignore"),
        )
        self.assertEqual(
            ce.parse_config_key("charliermarsh.ruff.ignore"),
            ("extension", "charliermarsh.ruff", "ignore"),
        )
        self.assertEqual(
            ce.parse_config_key("extensions.charliermarsh.ruff.ignore"),
            ("extension", "charliermarsh.ruff", "ignore"),
        )
        self.assertEqual(
            ce.parse_config_key("min_release_age"), ("global", "min_release_age", None)
        )


# =====================================================================
# CLI Integration Tests: handle_completion
# =====================================================================
class TestHandleCompletionIntegration(unittest.TestCase):
    def test_handle_completion_all_shells(self):
        shells = ["bash", "zsh", "fish", "powershell"]
        for sh in shells:
            with self.subTest(shell=sh):
                args = argparse.Namespace(shell=sh)
                with contextlib.redirect_stdout(io.StringIO()) as out:
                    ce.handle_completion(args, {})
                output = out.getvalue()
                self.assertIn("code-extensions", output)
                self.assertIn("install", output)
                self.assertIn("update", output)


if __name__ == "__main__":
    unittest.main()
