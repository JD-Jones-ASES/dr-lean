#!/usr/bin/env python3
"""Pinned Linux component replay; not Palomar intake or protected provenance replay."""
from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import signal
import subprocess
import sys
import uuid

PROJECT_TOOLCHAIN = "leanprover/lean4:v4.33.0"
COMPARATOR_TOOLCHAIN = "leanprover/lean4:v4.34.0-rc1"
COMPARATOR_EXPORTER = "b18d673bd29b476466a51a3be1012df2ed322b10"
MATHLIB = "db584cd6d46c92f209a44c0f1c829460d327499d"
LANDRUN = "811cfff51ceaf3d9843708aa6d22e9b84ccac8b4"
ADAPTER_SHA256 = "b38456d5597e67587c11d37eeeb647db387b0d2556a1db662709c583e527c266"
TOOLS = {
    "comparator": ("https://github.com/leanprover/comparator.git", "575674928e239f5bc452aab72d1dd7b0f1326494"),
    "lean4export": ("https://github.com/leanprover/lean4export.git", "15f6055e299ad5b89345e533cc2192f4cc00f659"),
    "nanoda": ("https://github.com/robsimmons/nanoda_lib.git", "68d5ca9db226849b41a6fff59d796ff19d0a8840"),
    "pipeline": ("https://github.com/PalomarRegistry/PalomarSubmission.git", "ef2fa1eadcb246c2346ddba39b52eaa53d4bb763"),
}
ARTIFACTS = (
    "comparator/.lake/build/bin/comparator",
    "lean4export/.lake/build/bin/lean4export",
    "nanoda/target/release/nanoda_bin",
    "bin/landrun",
    "pipeline/scripts/landrun_passthrough.py",
)
THEOREMS = tuple("DittertRybinRelease." + name for name in (
    "dittert_unique_maximum", "uniform_maximum_order_two", "uniform_maximum_order_three",
    "uniform_maximum_four_rows", "uniform_maximum_five_by_five_order_four",
    "uniform_maximum_twenty_by_twenty_order_four", "uniform_maximum_large_boards",
    "uniform_maximum_large_boards_power", "uniform_maximum_large_endpoints",
    "uniform_maximum_quadratic_endpoint_strip", "uniform_maximum_quartic_endpoint_strip",
    "uniform_maximum_combined_endpoint_strip", "uniform_maximum_consecutive_endpoint",
    "uniform_maximum_short_endpoint", "uniform_maximum_square_near_endpoint",
    "uniform_maximum_arithmetic_endpoint", "uniform_maximum_double_endpoint",
    "uniform_maximum_lll_endpoint", "uniform_maximum_small_side", "uniform_maximum_five_by_five",
))
ACCEPTANCE = ("Lean default kernel accepts the solution", "nanoda kernel accepts the solution")
SYSTEMD_PROPERTIES = (
    "RestrictAddressFamilies=~AF_UNIX", "LimitNOFILE=524288", "NoNewPrivileges=yes",
    "RestrictSUIDSGID=yes", "LockPersonality=yes", "PrivateDevices=yes", "PrivateTmp=yes",
    "ProtectProc=invisible", "ProcSubset=pid", "PrivateNetwork=yes",
)


class VerificationError(RuntimeError):
    def __init__(self, message, exit_code=2):
        super().__init__(message)
        self.exit_code = exit_code


def require(condition, message):
    if not condition:
        raise VerificationError(message)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=unique_object)


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def run(args, *, cwd=None, env=None):
    return subprocess.run(args, cwd=cwd, env=env, check=True, text=True,
                          stdout=subprocess.PIPE, stderr=None).stdout.strip()


def build(args, *, cwd=None, env=None):
    subprocess.run(args, cwd=cwd, env=env, check=True)


def git(path, *args):
    return run(["git", "-C", str(path), *args])


def clean_environment():
    env = os.environ.copy()
    for key in ("ELAN_TOOLCHAIN", "LEAN_PATH", "LEAN_SRC_PATH", "PALOMAR_PROTECTED_CHALLENGE_MODULE",
                "COMPARATOR_LANDRUN", "COMPARATOR_LEAN4EXPORT", "COMPARATOR_NANODA", "PALOMAR_LANDRUN_REAL"):
        env.pop(key, None)
    return env


def validate_config(config):
    keys = {"challenge_module", "solution_module", "theorem_names", "definition_names",
            "permitted_axioms", "enable_nanoda"}
    require(isinstance(config, dict) and set(config) == keys, "Unexpected/missing comparator config fields")
    require(config["challenge_module"] == "Challenge" and config["solution_module"] == "Solution",
            "Expected distinct canonical Challenge and Solution modules")
    names = config["theorem_names"]
    require(isinstance(names, list) and all(isinstance(x, str) for x in names)
            and len(names) == 20 and set(names) == set(THEOREMS), "Expected all 20 unique release declarations")
    axioms = config["permitted_axioms"]
    require(isinstance(axioms, list) and all(isinstance(x, str) for x in axioms)
            and len(axioms) == 3 and set(axioms) == {"propext", "Classical.choice", "Quot.sound"},
            "Expected exactly the three standard permitted axioms")
    require(config["definition_names"] == [], "Definition holes are not permitted in this package")
    require(config["enable_nanoda"] is True, "Mandatory NanoDa must explicitly be enabled")


def validate_layout(project, tools):
    require(project.is_absolute() and tools.is_absolute(), "Paths must be absolute after resolution")
    require(not tools.is_relative_to(project) and not project.is_relative_to(tools),
            "Verifier tools and candidate must be disjoint directories")


def check_checkout(path, remote, revision):
    require((path / ".git").is_dir(), f"Not a standalone Git tool checkout: {path}")
    require(git(path, "remote", "get-url", "origin") == remote, f"Unexpected origin: {path}")
    require(git(path, "rev-parse", "HEAD") == revision, f"Unexpected tool revision: {path}")
    require(not git(path, "status", "--porcelain", "--untracked-files=all"), f"Dirty tool checkout: {path}")


def checkout(path, remote, revision):
    if path.exists():
        # Existing caches must already be exact; never discard local work or switch revisions.
        check_checkout(path, remote, revision)
        return
    run(["git", "clone", "--filter=blob:none", "--no-checkout", remote, str(path)])
    run(["git", "-C", str(path), "fetch", "--depth", "1", "origin", revision])
    run(["git", "-C", str(path), "checkout", "--detach", revision])
    check_checkout(path, remote, revision)


def tool_metadata(tools):
    for name, (remote, revision) in TOOLS.items():
        check_checkout(tools / name, remote, revision)
    require((tools / "comparator/lean-toolchain").read_text().strip() == COMPARATOR_TOOLCHAIN,
            "Comparator must retain its distinct 4.34.0-rc1 toolchain")
    require((tools / "lean4export/lean-toolchain").read_text().strip() == PROJECT_TOOLCHAIN,
            "Exporter must use the project 4.33.0 toolchain")
    packages = read_json(tools / "comparator/lake-manifest.json")["packages"]
    exporters = [p for p in packages if p.get("name") == "lean4export"]
    require(len(exporters) == 1 and exporters[0].get("rev") == COMPARATOR_EXPORTER,
            "Comparator's own exporter dependency was altered")
    check_checkout(tools / "comparator/.lake/packages/lean4export",
                   "https://github.com/leanprover/lean4export", COMPARATOR_EXPORTER)
    hashes = {}
    for relative in ARTIFACTS:
        path = (tools / relative).resolve(strict=True)
        require(path.is_relative_to(tools) and path.is_file() and os.access(path, os.X_OK),
                f"Missing, external or non-executable tool artifact: {relative}")
        hashes[relative] = digest(path)
    require(hashes[ARTIFACTS[-1]] == ADAPTER_SHA256, "Official Landrun adapter bytes differ from the pinned source")
    return {"format": 1, "source_pins": {k: v[1] for k, v in TOOLS.items()},
            "landrun_pin": LANDRUN, "project_toolchain": PROJECT_TOOLCHAIN,
            "comparator_toolchain": COMPARATOR_TOOLCHAIN, "artifacts": hashes}


def prepare(tools):
    receipt = tools / "prepared-tools.json"
    receipt.unlink(missing_ok=True)
    env = clean_environment()
    for name, (remote, revision) in TOOLS.items():
        checkout(tools / name, remote, revision)
    require((tools / "comparator/lean-toolchain").read_text().strip() == COMPARATOR_TOOLCHAIN,
            "Incorrect Comparator toolchain before build")
    require((tools / "lean4export/lean-toolchain").read_text().strip() == PROJECT_TOOLCHAIN,
            "Incorrect project exporter toolchain before build")
    build(["lake", "build", "comparator"], cwd=tools / "comparator", env=env)
    exporter_env = dict(env, ELAN_TOOLCHAIN=PROJECT_TOOLCHAIN)
    build(["lake", "build", "lean4export"], cwd=tools / "lean4export", env=exporter_env)
    build(["cargo", "build", "--release", "--locked", "--manifest-path", str(tools / "nanoda/Cargo.toml")], env=env)
    (tools / "bin").mkdir(exist_ok=True)
    go_env = dict(env, CGO_ENABLED="0", GOBIN=str(tools / "bin"), GOWORK="off")
    build(["go", "install", f"github.com/zouuup/landrun/cmd/landrun@{LANDRUN}"], env=go_env)
    receipt.write_text(json.dumps(tool_metadata(tools), indent=2) + "\n")


def verify_cache(tools):
    expected = read_json(tools / "prepared-tools.json")
    actual = tool_metadata(tools)
    require(expected == actual, "Prepared cache changed; use --prepare-only on a trusted exact cache")
    return actual


def project_state(project, expected_commit):
    require(re.fullmatch(r"[0-9a-f]{40}", expected_commit or "") is not None,
            "Verification requires --expected-commit with the full lowercase 40-character SHA")
    require(git(project, "rev-parse", "HEAD") == expected_commit, "Candidate is not the requested commit")
    require(not git(project, "status", "--porcelain", "--untracked-files=no"), "Tracked candidate files are modified")
    sources = ("comparator.json", "Challenge.lean", "Solution.lean", "lean-toolchain", "lake-manifest.json")
    git(project, "ls-files", "--error-unmatch", *sources)
    require((project / "lean-toolchain").read_text().strip() == PROJECT_TOOLCHAIN, "Unexpected candidate toolchain")
    packages = read_json(project / "lake-manifest.json")["packages"]
    mathlibs = [p for p in packages if p.get("name") == "mathlib"]
    require(len(mathlibs) == 1 and mathlibs[0].get("rev") == MATHLIB, "Unexpected candidate Mathlib pin")
    config = read_json(project / "comparator.json")
    validate_config(config)
    inputs = list(sources) + [".lake/build/lib/lean/Challenge.olean", ".lake/build/lib/lean/Solution.olean"]
    hashes = {}
    for relative in inputs:
        path = project / relative
        require(path.is_file(), f"Caller must supply the completely built candidate: missing {relative}")
        hashes[relative] = digest(path)
    return {"commit": expected_commit, "inputs": hashes}, config


def systemd_command(manager, project, unit, runtime=19800):
    runner = shutil.which("systemd-run")
    require(runner is not None, "systemd-run is required for confinement")
    common = ["--quiet", "--collect", "--pipe", "--wait", f"--unit={unit}",
              *(f"--property={value}" for value in SYSTEMD_PROPERTIES),
              f"--property=RuntimeMaxSec={runtime}s", "--working-directory", str(project)]
    if manager == "system":
        sudo = shutil.which("sudo")
        require(sudo is not None, "Passwordless sudo disappeared after the system-manager probe")
        require(os.getuid() != 0 and os.getgid() != 0, "The system service must run with nonroot UID and GID")
        return [sudo, "-n", runner, *common, f"--uid={os.getuid()}", f"--gid={os.getgid()}"]
    require(manager == "user", "Unknown systemd manager")
    return [runner, "--user", *common]


def stop_unit(manager, unit):
    if manager == "system":
        sudo = shutil.which("sudo")
        require(sudo is not None, "Passwordless sudo disappeared during system-service cleanup")
        command = [sudo, "-n", "systemctl", "stop", unit]
    else:
        command = ["systemctl", "--user", "stop", unit]
    try:
        subprocess.run(command, check=False, stdout=subprocess.DEVNULL,
                       stderr=subprocess.DEVNULL, timeout=15)
    except (OSError, subprocess.TimeoutExpired):
        pass


def select_manager(project):
    """Probe the exact property set, system-first, as in the pinned official runner."""
    true = shutil.which("true")
    require(true is not None, "true is required to probe systemd confinement")
    candidates = ["system", "user"] if shutil.which("sudo") else ["user"]
    for manager in candidates:
        unit = f"dr-comparator-probe-{uuid.uuid4().hex}.service"
        command = [*systemd_command(manager, project, unit, runtime=30), "--", true]
        try:
            probe = subprocess.run(command, cwd=project, env=clean_environment(), timeout=30,
                                   text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
        except subprocess.TimeoutExpired:
            stop_unit(manager, unit)
            continue
        if probe.returncode == 0:
            return manager
    raise VerificationError("Neither passwordless systemd nor a user manager can apply the required confinement properties")


def comparator_command(project, tools, config_path, path_value, manager="user"):
    unit = f"dr-comparator-{uuid.uuid4().hex}.service"
    return [*systemd_command(manager, project, unit),
            f"--setenv=PATH={path_value}", "--", "env", "-u", "PALOMAR_PROTECTED_CHALLENGE_MODULE",
            "-u", "LEAN_PATH", "-u", "LEAN_SRC_PATH", f"ELAN_TOOLCHAIN={PROJECT_TOOLCHAIN}",
            f"PALOMAR_LANDRUN_REAL={tools / 'bin/landrun'}",
            f"COMPARATOR_LANDRUN={tools / 'pipeline/scripts/landrun_passthrough.py'}",
            f"COMPARATOR_LEAN4EXPORT={tools / 'lean4export/.lake/build/bin/lean4export'}",
            f"COMPARATOR_NANODA={tools / 'nanoda/target/release/nanoda_bin'}",
            "lake", "env", str(tools / "comparator/.lake/build/bin/comparator"), str(config_path)]


def normalized_exit(code):
    return 128 - code if code < 0 else code


def require_acceptance(code, lines):
    if code != 0:
        raise VerificationError(f"Comparator/systemd failed with exit {normalized_exit(code)}", normalized_exit(code))
    missing = [line for line in ACCEPTANCE if line not in lines]
    require(not missing, "Missing mandatory acceptance line(s): " + ", ".join(missing))


def invalidate_result(project):
    (project / ".verification/independent-verifier/component-replay-result.json").unlink(missing_ok=True)


def verify(project, tools, expected_commit, manager=None):
    invalidate_result(project)
    metadata = verify_cache(tools)
    before, config = project_state(project, expected_commit)
    manager = manager or select_manager(project)
    config_path = tools / "replay-config.json"
    config_path.write_text(json.dumps(config, indent=2) + "\n")
    output = project / ".verification/independent-verifier"
    output.mkdir(parents=True, exist_ok=True)
    log_path = output / "component-replay.log"
    result_path = output / "component-replay-result.json"
    result_path.unlink(missing_ok=True)
    command = comparator_command(project, tools, config_path, os.environ.get("PATH", ""), manager)
    lines = set()
    with log_path.open("w", encoding="utf-8") as log:
        process = subprocess.Popen(command, env=clean_environment(), text=True,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        unit = next(arg.split("=", 1)[1] for arg in command if arg.startswith("--unit="))
        def interrupted(_signum, _frame):
            raise VerificationError("Verification interrupted; no acceptance receipt", 143)
        previous_term = signal.signal(signal.SIGTERM, interrupted)
        try:
            for line in process.stdout:
                sys.stdout.write(line)
                sys.stdout.flush()
                log.write(line)
                log.flush()
                lines.add(line.strip())
            code = process.wait()
        except BaseException:
            process.terminate()
            # Stop only our uniquely named service; never leave a kernel job orphaned.
            stop_unit(manager, unit)
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()
            raise
        finally:
            signal.signal(signal.SIGTERM, previous_term)
    require_acceptance(code, lines)
    after, after_config = project_state(project, expected_commit)
    require(after == before and after_config == config, "Candidate inputs changed during verification")
    require(verify_cache(tools) == metadata, "Verifier tools changed during verification")
    require(read_json(config_path) == config, "Replay config changed during verification")
    result = {"scope": "direct Comparator + real Landrun + NanoDa component replay; not official intake",
              "status": "accepted", "project": before, "tools": metadata, "command": command,
              "systemd_manager": manager, "runtime_uid": os.getuid(), "runtime_gid": os.getgid(),
              "log_sha256": digest(log_path), "acceptance_lines": list(ACCEPTANCE), "exit_code": code}
    result_path.write_text(json.dumps(result, indent=2) + "\n")
    print(f"Both kernels accepted all 20 declarations. Component receipt: {result_path}")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--prepare-only", action="store_true", help="Build pinned tools early; do not inspect/rebuild candidate")
    mode.add_argument("--verify-only", action="store_true", help="Replay cached exact tools; no tool setup/network")
    parser.add_argument("--project", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--tools", type=Path, default=Path(os.environ.get("PALOMAR_COMPARATOR_CACHE",
                        str(Path.home() / ".cache/dr-lean-verifier"))))
    parser.add_argument("--expected-commit", help="Required for verification; full exact candidate commit")
    args = parser.parse_args(argv)
    project, tools = args.project.resolve(), args.tools.resolve()
    if not args.prepare_only:
        # A failed new verification must not masquerade as an older success.
        invalidate_result(project)
    require(platform.system() == "Linux", "Requires Linux with real Landrun and systemd AF_UNIX isolation; no macOS replay")
    require(os.geteuid() != 0 and os.getuid() != 0 and os.getegid() != 0 and os.getgid() != 0,
            "Comparator must run with a nonprivileged UID and GID")
    validate_layout(project, tools)
    commands = ["git", "lake", "python3", "systemctl", "systemd-run", "true"]
    commands += [] if args.verify_only else ["go", "cargo"]
    for command in commands:
        require(shutil.which(command) is not None, f"Required executable is unavailable: {command}")
    if not args.prepare_only:
        project_state(project, args.expected_commit)
    manager = select_manager(project)
    tools.mkdir(parents=True, exist_ok=True, mode=0o700)
    with (tools / ".verifier.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        if not args.verify_only:
            prepare(tools)
        if args.prepare_only:
            print(f"Exact tools prepared: {tools}; no proof verification performed")
        else:
            verify(project, tools, args.expected_commit, manager)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except subprocess.CalledProcessError as error:
        print(f"Verifier command failed: {error.cmd}; exit {normalized_exit(error.returncode)}", file=sys.stderr)
        raise SystemExit(normalized_exit(error.returncode))
    except KeyboardInterrupt:
        print("Verification interrupted; no acceptance receipt", file=sys.stderr)
        raise SystemExit(130)
    except (VerificationError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"Comparator verifier: {error}", file=sys.stderr)
        raise SystemExit(getattr(error, "exit_code", 2))
