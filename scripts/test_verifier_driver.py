#!/usr/bin/env python3
"""Static/fixture controls only: never run Comparator, Landrun, or a Linux proof replay."""
from __future__ import annotations

import contextlib
import io
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock

SCRIPT = Path(__file__).resolve().with_name("verify-comparator.py")
spec = importlib.util.spec_from_file_location("verifier_driver", SCRIPT)
driver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(driver)


def good_config():
    return {"challenge_module": "Challenge", "solution_module": "Solution",
            "theorem_names": list(driver.THEOREMS), "definition_names": [],
            "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"], "enable_nanoda": True}


class ConfigControls(unittest.TestCase):
    def test_complete_twenty_and_reordering(self):
        config = good_config()
        driver.validate_config(config)
        config["theorem_names"].reverse()
        driver.validate_config(config)

    def test_missing_extra_duplicate_and_unexpected_names(self):
        for replacement in (list(driver.THEOREMS[:-1]), list(driver.THEOREMS) + ["extra"],
                            list(driver.THEOREMS[:-1]) + [driver.THEOREMS[0]],
                            list(driver.THEOREMS[:-1]) + ["unproved"]):
            with self.subTest(names=replacement):
                config = good_config()
                config["theorem_names"] = replacement
                with self.assertRaises(driver.VerificationError):
                    driver.validate_config(config)

    def test_exact_fields_modules_axioms_and_nanoda(self):
        for key, value in (("solution_module", "Challenge"), ("challenge_module", "Spoofed"),
                           ("enable_nanoda", False), ("enable_nanoda", 1),
                           ("definition_names", ["hole"]), ("external_kernels", {}),
                           ("permitted_axioms", ["propext", "Quot.sound", "sorryAx"]),
                           ("permitted_axioms", ["propext", "propext", "Quot.sound"])):
            with self.subTest(field=key, value=value):
                config = good_config()
                config[key] = value
                with self.assertRaises(driver.VerificationError):
                    driver.validate_config(config)

    def test_missing_field_and_malformed_names(self):
        for config in ({k: v for k, v in good_config().items() if k != "enable_nanoda"},
                       dict(good_config(), theorem_names=[{}] * 20), None):
            with self.assertRaises(driver.VerificationError):
                driver.validate_config(config)

    def test_duplicate_json_keys(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "duplicate.json"
            path.write_text('{"enable_nanoda": true, "enable_nanoda": false}')
            with self.assertRaises(driver.VerificationError):
                driver.read_json(path)


class CommandControls(unittest.TestCase):
    def test_argv_isolation_and_space_safety(self):
        project, tools = Path("/candidate path; no shell"), Path("/tool cache")
        with mock.patch.object(driver.shutil, "which", side_effect=lambda name: "/usr/bin/" + name):
            command = driver.comparator_command(project, tools, tools / "config.json", "/runtime path:/usr/bin")
        self.assertEqual(command[:5], ["/usr/bin/systemd-run", "--user", "--quiet", "--collect", "--pipe"])
        self.assertIn("--property=RestrictAddressFamilies=~AF_UNIX", command)
        self.assertEqual(command[command.index("--working-directory") + 1], str(project))
        self.assertIn("--setenv=PATH=/runtime path:/usr/bin", command)
        self.assertIn("PALOMAR_LANDRUN_REAL=/tool cache/bin/landrun", command)
        self.assertIn("COMPARATOR_LANDRUN=/tool cache/pipeline/scripts/landrun_passthrough.py", command)
        self.assertIn("COMPARATOR_LEAN4EXPORT=/tool cache/lean4export/.lake/build/bin/lean4export", command)
        self.assertIn("COMPARATOR_NANODA=/tool cache/nanoda/target/release/nanoda_bin", command)
        self.assertEqual(command[command.index("--") + 1:command.index("--") + 4],
                         ["env", "-u", "PALOMAR_PROTECTED_CHALLENGE_MODULE"])
        self.assertEqual(command[-4:], ["lake", "env", "/tool cache/comparator/.lake/build/bin/comparator", "/tool cache/config.json"])
        self.assertNotIn("bash", command)
        self.assertNotIn("--unrestricted-filesystem", command)

    def test_environment_cannot_override_tools_or_skip_challenge(self):
        overrides = {k: "malicious" for k in ("ELAN_TOOLCHAIN", "LEAN_PATH", "LEAN_SRC_PATH",
                     "PALOMAR_PROTECTED_CHALLENGE_MODULE", "COMPARATOR_LANDRUN", "COMPARATOR_NANODA",
                     "COMPARATOR_LEAN4EXPORT", "PALOMAR_LANDRUN_REAL")}
        with mock.patch.dict(os.environ, overrides):
            env = driver.clean_environment()
        for key in overrides:
            self.assertNotIn(key, env)

    def test_both_kernel_lines_and_exit_zero(self):
        driver.require_acceptance(0, set(driver.ACCEPTANCE))
        for code, lines in ((1, set(driver.ACCEPTANCE)), (-15, set(driver.ACCEPTANCE)),
                            (0, set()), (0, {driver.ACCEPTANCE[0]}), (0, {driver.ACCEPTANCE[1]}),
                            (0, {"prefix " + x for x in driver.ACCEPTANCE})):
            with self.subTest(code=code, lines=lines):
                with self.assertRaises(driver.VerificationError):
                    driver.require_acceptance(code, lines)

    def test_signal_normalization(self):
        self.assertEqual(driver.normalized_exit(-15), 143)
        self.assertEqual(driver.normalized_exit(-9), 137)
        self.assertEqual(driver.normalized_exit(7), 7)
        with self.assertRaises(driver.VerificationError) as caught:
            driver.require_acceptance(-15, set(driver.ACCEPTANCE))
        self.assertEqual(caught.exception.exit_code, 143)

    def test_disjoint_tools_in_both_directions(self):
        driver.validate_layout(Path("/candidate"), Path("/tools"))
        for project, tools in (("/candidate", "/candidate/tools"), ("/tools/candidate", "/tools"),
                               ("/same", "/same")):
            with self.assertRaises(driver.VerificationError):
                driver.validate_layout(Path(project), Path(tools))

    def test_shell_syntax_and_help(self):
        shell = SCRIPT.with_suffix(".sh")
        subprocess.run(["bash", "-n", str(shell)], check=True)
        result = subprocess.run(["bash", str(shell), "--help"], text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("--prepare-only", result.stdout)
        self.assertIn("--verify-only", result.stdout)

    def test_mac_and_root_fail_before_any_tools(self):
        with mock.patch.object(driver.platform, "system", return_value="Darwin"), \
             mock.patch.object(driver, "prepare") as prepare:
            with self.assertRaisesRegex(driver.VerificationError, "Requires Linux"):
                driver.main(["--prepare-only"])
            prepare.assert_not_called()
        with mock.patch.object(driver.platform, "system", return_value="Linux"), \
             mock.patch.object(driver.os, "geteuid", return_value=0):
            with self.assertRaisesRegex(driver.VerificationError, "nonprivileged"):
                driver.main(["--prepare-only"])

    def test_platform_and_missing_executable_clear_stale_acceptance(self):
        with tempfile.TemporaryDirectory() as directory:
            project, tools = Path(directory) / "project", Path(directory) / "tools"
            receipt = project / ".verification/independent-verifier/component-replay-result.json"
            receipt.parent.mkdir(parents=True)
            args = ["--verify-only", "--project", str(project), "--tools", str(tools)]
            for platform_name in ("Darwin", "Linux"):
                receipt.write_text('{"status":"accepted", "old":true}')
                with mock.patch.object(driver.platform, "system", return_value=platform_name), \
                     mock.patch.object(driver.os, "geteuid", return_value=1000), \
                     mock.patch.object(driver.os, "getuid", return_value=1000), \
                     mock.patch.object(driver.os, "getgid", return_value=1000), \
                     mock.patch.object(driver.os, "getegid", return_value=1000), \
                     mock.patch.object(driver.shutil, "which", return_value=None):
                    with self.assertRaises(driver.VerificationError):
                        driver.main(args)
                self.assertFalse(receipt.exists())


class CacheControls(unittest.TestCase):
    def test_actual_artifact_hashes_and_adapter_boundary(self):
        with tempfile.TemporaryDirectory() as directory:
            tools = Path(directory).resolve()
            for artifact in driver.ARTIFACTS:
                path = tools / artifact
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("fixture executable; never invoked\n" + artifact)
                path.chmod(0o700)
            (tools / "comparator/lean-toolchain").write_text(driver.COMPARATOR_TOOLCHAIN)
            (tools / "lean4export/lean-toolchain").write_text(driver.PROJECT_TOOLCHAIN)
            (tools / "comparator/lake-manifest.json").write_text(json.dumps(
                {"packages": [{"name": "lean4export", "rev": driver.COMPARATOR_EXPORTER}]}))
            # The fixture adapter pin is deliberate; production pins the official bytes.
            with mock.patch.object(driver, "check_checkout") as check, \
                 mock.patch.object(driver, "ADAPTER_SHA256", driver.digest(tools / driver.ARTIFACTS[-1])):
                metadata = driver.tool_metadata(tools)
                self.assertEqual(len(metadata["artifacts"]), 5)
                self.assertEqual(check.call_count, 5)  # four tools plus Comparator's exporter dependency
                (tools / "prepared-tools.json").write_text(json.dumps(metadata))
                (tools / driver.ARTIFACTS[0]).write_text("mutated binary")
                with self.assertRaisesRegex(driver.VerificationError, "cache changed"):
                    driver.verify_cache(tools)
                (tools / driver.ARTIFACTS[-1]).write_text("mutated adapter")
                with self.assertRaisesRegex(driver.VerificationError, "adapter bytes"):
                    driver.tool_metadata(tools)

    def test_missing_or_changed_cache_receipt(self):
        with tempfile.TemporaryDirectory() as directory:
            tools = Path(directory)
            with self.assertRaises(FileNotFoundError):
                driver.verify_cache(tools)
            (tools / "prepared-tools.json").write_text('{"artifacts": {"binary": "original"}}')
            with mock.patch.object(driver, "tool_metadata", return_value={"artifacts": {"binary": "changed"}}):
                with self.assertRaisesRegex(driver.VerificationError, "changed"):
                    driver.verify_cache(tools)
            with mock.patch.object(driver, "tool_metadata", return_value={"artifacts": {"binary": "original"}}):
                self.assertEqual(driver.verify_cache(tools)["artifacts"]["binary"], "original")

    def test_exact_checkout_head_origin_and_cleanliness(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            (path / ".git").mkdir()
            for answers in (["remote", "revision", ""], ["wrong", "revision", ""],
                            ["remote", "wrong", ""], ["remote", "revision", " M Main.lean"]):
                with mock.patch.object(driver, "git", side_effect=answers):
                    if answers == ["remote", "revision", ""]:
                        driver.check_checkout(path, "remote", "revision")
                    else:
                        with self.assertRaises(driver.VerificationError):
                            driver.check_checkout(path, "remote", "revision")

    def test_existing_cache_does_not_fetch_or_checkout(self):
        with tempfile.TemporaryDirectory() as directory, \
             mock.patch.object(driver, "check_checkout") as check, \
             mock.patch.object(driver, "run") as run:
            driver.checkout(Path(directory), "remote", "revision")
            check.assert_called_once()
            run.assert_not_called()

    def test_prepare_toolchains_and_no_candidate_build(self):
        with tempfile.TemporaryDirectory() as directory:
            tools = Path(directory)
            for name, toolchain in (("comparator", driver.COMPARATOR_TOOLCHAIN), ("lean4export", driver.PROJECT_TOOLCHAIN)):
                (tools / name).mkdir()
                (tools / name / "lean-toolchain").write_text(toolchain)
            with mock.patch.object(driver, "checkout"), mock.patch.object(driver, "build") as build, \
                 mock.patch.object(driver, "tool_metadata", return_value={"checked": True}), \
                 mock.patch.dict(os.environ, {"ELAN_TOOLCHAIN": "wrong"}):
                driver.prepare(tools)
            calls = build.call_args_list
            self.assertEqual(len(calls), 4)
            self.assertEqual(calls[0].args[0], ["lake", "build", "comparator"])
            self.assertNotIn("ELAN_TOOLCHAIN", calls[0].kwargs["env"])
            self.assertEqual(calls[1].kwargs["env"]["ELAN_TOOLCHAIN"], driver.PROJECT_TOOLCHAIN)
            self.assertIn("--locked", calls[2].args[0])
            self.assertEqual(calls[3].args[0][-1].split("@")[1], driver.LANDRUN)
            self.assertEqual(driver.read_json(tools / "prepared-tools.json"), {"checked": True})

    def test_prepare_wrong_toolchain_never_builds(self):
        with tempfile.TemporaryDirectory() as directory:
            tools = Path(directory)
            (tools / "comparator").mkdir()
            (tools / "comparator/lean-toolchain").write_text(driver.PROJECT_TOOLCHAIN)
            with mock.patch.object(driver, "checkout"), mock.patch.object(driver, "build") as build:
                with self.assertRaises(driver.VerificationError):
                    driver.prepare(tools)
                build.assert_not_called()
            self.assertFalse((tools / "prepared-tools.json").exists())

    def test_prepare_only_and_verify_only_modes(self):
        with tempfile.TemporaryDirectory() as directory:
            project, tools = Path(directory).resolve() / "project", Path(directory).resolve() / "tools"
            with mock.patch.object(driver.platform, "system", return_value="Linux"), \
                 mock.patch.object(driver.os, "geteuid", return_value=1000), \
                 mock.patch.object(driver.os, "getuid", return_value=1000), \
                 mock.patch.object(driver.os, "getgid", return_value=1000), \
                 mock.patch.object(driver.os, "getegid", return_value=1000), \
                 mock.patch.object(driver.shutil, "which", return_value="available"), \
                 mock.patch.object(driver, "select_manager", return_value="user"), \
                 mock.patch.object(driver, "project_state") as state, \
                 mock.patch.object(driver, "prepare") as prepare, \
                 mock.patch.object(driver, "verify") as verify:
                base = ["--project", str(project), "--tools", str(tools)]
                driver.main(base + ["--prepare-only"])
                prepare.assert_called_once_with(tools)
                state.assert_not_called()
                verify.assert_not_called()
                prepare.reset_mock()
                driver.main(base + ["--verify-only", "--expected-commit", "a" * 40])
                prepare.assert_not_called()
                verify.assert_called_once_with(project, tools, "a" * 40, "user")


class ProjectControls(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.project = Path(self.temp.name)
        for name, text in {"lean-toolchain": driver.PROJECT_TOOLCHAIN, "Challenge.lean": "statement",
                           "Solution.lean": "proof", "comparator.json": json.dumps(good_config()),
                           "lake-manifest.json": json.dumps({"packages": [{"name": "mathlib", "rev": driver.MATHLIB}]}),
                           ".lake/build/lib/lean/Challenge.olean": "compiled statement",
                           ".lake/build/lib/lean/Solution.olean": "compiled proof"}.items():
            path = self.project / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)

    def state(self, sha="a" * 40, answers=None):
        with mock.patch.object(driver, "git", side_effect=answers or ["a" * 40, "", "tracked"]):
            return driver.project_state(self.project, sha)

    def test_built_exact_project_fingerprint(self):
        state, config = self.state()
        self.assertEqual(state["commit"], "a" * 40)
        self.assertEqual(len(state["inputs"]), 7)
        self.assertEqual(len(config["theorem_names"]), 20)

    def test_wrong_sha_dirty_tree_and_short_sha(self):
        for sha, answers in (("b" * 40, None), ("a" * 40, ["a" * 40, " M Solution.lean"]), ("a" * 12, None)):
            with self.subTest(sha=sha, answers=answers):
                with self.assertRaises(driver.VerificationError):
                    self.state(sha, answers)

    def test_missing_build_is_error_not_rebuild(self):
        (self.project / ".lake/build/lib/lean/Solution.olean").unlink()
        with self.assertRaisesRegex(driver.VerificationError, "completely built"):
            self.state()

    def test_wrong_project_toolchain_or_mathlib(self):
        (self.project / "lean-toolchain").write_text(driver.COMPARATOR_TOOLCHAIN)
        with self.assertRaisesRegex(driver.VerificationError, "toolchain"):
            self.state()
        (self.project / "lean-toolchain").write_text(driver.PROJECT_TOOLCHAIN)
        (self.project / "lake-manifest.json").write_text('{"packages": [{"name": "mathlib", "rev": "wrong"}]}')
        with self.assertRaisesRegex(driver.VerificationError, "Mathlib"):
            self.state()


class StreamingControls(unittest.TestCase):
    def exercise(self, *, code=0, output=None, changed_project=False, manager_failure=False,
                 changed_tools=False, interrupt=False, mutate_config=False):
        with tempfile.TemporaryDirectory() as directory:
            project, tools = Path(directory) / "candidate", Path(directory) / "tools"
            project.mkdir()
            tools.mkdir()
            result = project / ".verification/independent-verifier/component-replay-result.json"
            result.parent.mkdir(parents=True)
            result.write_text('{"status":"accepted", "old":true}')
            config, before = good_config(), {"commit": "a" * 40, "inputs": {"source": "original"}}
            after = {"commit": "a" * 40, "inputs": {"source": "changed"}} if changed_project else before
            fake = mock.Mock()
            fake.stdout = iter((output if output is not None else list(driver.ACCEPTANCE)))
            def wait(**_kwargs):
                if interrupt:
                    raise KeyboardInterrupt
                if mutate_config:
                    (tools / "replay-config.json").write_text('{}')
                return code
            fake.wait.side_effect = wait
            metadata = {"artifacts": {"tool": "original"}}
            end_metadata = {"artifacts": {"tool": "changed"}} if changed_tools else metadata
            manager = driver.VerificationError("Neither systemd manager works") if manager_failure else "user"
            with mock.patch.object(driver, "verify_cache", side_effect=[metadata, end_metadata]), \
                 mock.patch.object(driver, "project_state", side_effect=[(before, config), (after, config)]), \
                 mock.patch.object(driver, "select_manager", side_effect=manager if manager_failure else None,
                                   return_value="user"), \
                 mock.patch.object(driver.shutil, "which", side_effect=lambda name: "/usr/bin/" + name), \
                 mock.patch.object(driver.subprocess, "Popen", return_value=fake) as popen, \
                 mock.patch.object(driver.subprocess, "run") as cleanup, \
                 contextlib.redirect_stdout(io.StringIO()):
                failure = None
                try:
                    driver.verify(project, tools, "a" * 40)
                except (driver.VerificationError, subprocess.CalledProcessError, KeyboardInterrupt) as error:
                    failure = error
                if manager_failure:
                    popen.assert_not_called()
                elif interrupt:
                    fake.terminate.assert_called_once()
                    stop = cleanup.call_args.args[0]
                    self.assertEqual(stop[:3], ["systemctl", "--user", "stop"])
                    self.assertRegex(stop[3], r"^dr-comparator-[0-9a-f]{32}\.service$")
                else:
                    command = popen.call_args.args[0]
                    self.assertIn("--property=RestrictAddressFamilies=~AF_UNIX", command)
                    self.assertEqual(popen.call_args.kwargs["stderr"], subprocess.STDOUT)
                receipt = driver.read_json(result) if result.exists() else None
            return failure, receipt

    def test_streamed_success_receipt_is_component_scoped(self):
        failure, receipt = self.exercise()
        self.assertIsNone(failure)
        self.assertEqual(receipt["status"], "accepted")
        self.assertIn("not official intake", receipt["scope"])
        self.assertEqual(receipt["acceptance_lines"], list(driver.ACCEPTANCE))
        self.assertEqual(receipt["exit_code"], 0)

    def test_nonzero_and_missing_acceptance_never_leave_old_success(self):
        for kwargs in ({"code": -15}, {"code": 8}, {"output": []}, {"output": [driver.ACCEPTANCE[0]]}):
            with self.subTest(kwargs=kwargs):
                failure, receipt = self.exercise(**kwargs)
                self.assertIsInstance(failure, driver.VerificationError)
                self.assertIsNone(receipt)

    def test_changed_inputs_tools_and_replay_config_reject(self):
        for kwargs in ({"changed_project": True}, {"changed_tools": True}, {"mutate_config": True}):
            with self.subTest(kwargs=kwargs):
                failure, receipt = self.exercise(**kwargs)
                self.assertIsInstance(failure, driver.VerificationError)
                self.assertIsNone(receipt)

    def test_missing_user_manager_has_no_sandbox_fallback(self):
        failure, receipt = self.exercise(manager_failure=True)
        self.assertIsInstance(failure, driver.VerificationError)
        self.assertIsNone(receipt)

    def test_interrupt_stops_only_owned_unit_and_clears_receipt(self):
        failure, receipt = self.exercise(interrupt=True)
        self.assertIsInstance(failure, KeyboardInterrupt)
        self.assertIsNone(receipt)


class ManagerControls(unittest.TestCase):
    def choose(self, results, sudo=True):
        def which(name):
            return None if name == "sudo" and not sudo else "/usr/bin/" + name
        with mock.patch.object(driver.shutil, "which", side_effect=which), \
             mock.patch.object(driver.os, "getuid", return_value=1001), \
             mock.patch.object(driver.os, "getgid", return_value=1002), \
             mock.patch.object(driver.subprocess, "run", side_effect=results) as run, \
             mock.patch.object(driver, "stop_unit") as stop:
            error = None
            manager = None
            try:
                manager = driver.select_manager(Path("/candidate"))
            except driver.VerificationError as caught:
                error = caught
            return manager, error, run.call_args_list, stop.call_args_list

    def test_system_first_runs_nonroot_with_all_real_properties(self):
        manager, error, calls, _ = self.choose([mock.Mock(returncode=0)])
        self.assertIsNone(error)
        self.assertEqual(manager, "system")
        command = calls[0].args[0]
        self.assertEqual(command[:3], ["/usr/bin/sudo", "-n", "/usr/bin/systemd-run"])
        self.assertIn("--uid=1001", command)
        self.assertIn("--gid=1002", command)
        for value in driver.SYSTEMD_PROPERTIES:
            self.assertIn("--property=" + value, command)
        self.assertIn("--property=PrivateNetwork=yes", command)
        self.assertIn("--property=RuntimeMaxSec=30s", command)
        self.assertEqual(command[-2:], ["--", "/usr/bin/true"])
        self.assertEqual(calls[0].kwargs["timeout"], 30)
        self.assertFalse(calls[0].kwargs["check"])

    def test_system_rejection_falls_back_only_to_equally_confined_user(self):
        manager, error, calls, _ = self.choose([mock.Mock(returncode=1), mock.Mock(returncode=0)])
        self.assertIsNone(error)
        self.assertEqual(manager, "user")
        self.assertEqual(len(calls), 2)
        command = calls[1].args[0]
        self.assertEqual(command[:2], ["/usr/bin/systemd-run", "--user"])
        for value in driver.SYSTEMD_PROPERTIES:
            self.assertIn("--property=" + value, command)
        self.assertFalse(any(x.startswith("--uid=") for x in command))

    def test_no_sudo_probes_user_directly_and_both_rejected_fail(self):
        manager, error, calls, _ = self.choose([mock.Mock(returncode=0)], sudo=False)
        self.assertEqual(manager, "user")
        self.assertIsNone(error)
        self.assertEqual(len(calls), 1)
        manager, error, calls, _ = self.choose([mock.Mock(returncode=1), mock.Mock(returncode=1)])
        self.assertIsNone(manager)
        self.assertIsInstance(error, driver.VerificationError)
        self.assertEqual(len(calls), 2)

    def test_probe_timeout_stops_matching_system_unit_before_fallback(self):
        manager, error, calls, stops = self.choose([
            subprocess.TimeoutExpired(["probe"], 30), mock.Mock(returncode=0)])
        self.assertEqual(manager, "user")
        self.assertIsNone(error)
        self.assertEqual(stops[0].args[0], "system")
        unit = next(x.split("=", 1)[1] for x in calls[0].args[0] if x.startswith("--unit="))
        self.assertEqual(stops[0].args[1], unit)

    def test_system_cleanup_and_actual_run_keep_nonroot_manager(self):
        with mock.patch.object(driver.shutil, "which", side_effect=lambda name: "/usr/bin/" + name), \
             mock.patch.object(driver.os, "getuid", return_value=1001), \
             mock.patch.object(driver.os, "getgid", return_value=1002), \
             mock.patch.object(driver.subprocess, "run") as cleanup:
            driver.stop_unit("system", "dr-comparator-test.service")
            self.assertEqual(cleanup.call_args.args[0], ["/usr/bin/sudo", "-n", "systemctl", "stop", "dr-comparator-test.service"])
            command = driver.comparator_command(Path("/candidate"), Path("/tools"), Path("/tools/config"), "/bin", "system")
            self.assertIn("--uid=1001", command)
            self.assertIn("--gid=1002", command)
            self.assertIn("--property=RestrictAddressFamilies=~AF_UNIX", command)
            self.assertNotIn("--user", command)

    def test_root_runtime_uid_or_gid_and_unknown_manager_rejected(self):
        for uid, gid, manager in ((0, 1002, "system"), (1001, 0, "system"), (1001, 1002, "unconfined")):
            with mock.patch.object(driver.shutil, "which", side_effect=lambda name: "/usr/bin/" + name), \
                 mock.patch.object(driver.os, "getuid", return_value=uid), \
                 mock.patch.object(driver.os, "getgid", return_value=gid):
                with self.assertRaises(driver.VerificationError):
                    driver.systemd_command(manager, Path("/candidate"), "owned.service")


if __name__ == "__main__":
    print("Fixture/static controls only; no Linux, Landrun, Comparator, or NanoDa replay.")
    unittest.main(verbosity=2)
