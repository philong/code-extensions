#!/usr/bin/env python3

import datetime
import email
import importlib.util
import io
import json
import os
import random
import tempfile
import unittest
import urllib.request
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
            with open(cache_file, "r") as f:
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
            with open(cache_file, "r") as f:
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

        action, selected, cursor = ce.run_list_picker(
            0,
            layout=boom,
            header=boom,
            row=boom,
            actions=[],
            unit_label="thing",
        )
        self.assertEqual((action, selected, cursor), ("quit", [], 0))

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


if __name__ == "__main__":
    unittest.main()
