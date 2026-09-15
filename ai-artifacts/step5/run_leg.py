#!/usr/bin/env python3
r"""STEP 5 harness (GUARD_CACHE_QUICK_MODE_PLAN.md section 10 step 5, section 37 item 12).

One leg = one fresh Isa-REPL server on the Phi_System_Base heap loading a list of
theories from source, timed by this script's wall clock.  The guard_decision
records the load writes (under ML_debugger) land in <leg dir>/event_log,
because ISABELLE_EVENT_LOG_DIR is set for the server.

    run_leg.py [--ml-debugger] <leg name> <port> <threads> <theory>...

--ml-debugger passes `-o ML_debugger=true` to the server's `isabelle build`:
ML_debugger is an Isabelle system option, and an option-backed config reads the
process's default options when no context sets it, so every theory the server
then loads from source compiles under the debugger and writes its records.  The
guard cache's own switch (\<phi>guard_cache) is a context attribute, not a system
option: a cache-off leg still needs `declare [[\<phi>guard_cache = false]]` in
PLPR.thy (a TEMPORARY edit, reverted afterwards); result.txt records the diff.
"""

import argparse
import asyncio
import hashlib
import os
import signal
import subprocess
import sys
import time
from pathlib import Path

MLML = Path('/home/qiyuan/Current/MLML')
sys.path.insert(0, str(MLML / 'contrib/Isa-REPL'))
from IsaREPL import Client, REPLFail  # noqa: E402

STEP5 = MLML / 'contrib/phi-system/ai-artifacts/step5'
PHI = MLML / 'contrib/phi-system'
PLPR = PHI / 'Phi_Logic_Programming_Reasoner/PLPR.thy'
FUTURE_ML = MLML / 'contrib/Isabelle2025-2/src/Pure/Concurrent/future.ML'


def git(*args):
    return subprocess.run(['git', '-C', str(PHI), *args], capture_output=True, text=True).stdout


def provenance(server_options):
    """What this leg ran under, so its directory describes itself."""
    return (f'phi_system_head={git("rev-parse", "HEAD").strip()}\n'
            f'server_options={" ".join(server_options)}\n'
            f'future_ml_sha256={hashlib.sha256(FUTURE_ML.read_bytes()).hexdigest()}\n'
            f'plpr_thy_diff={repr(git("diff", "HEAD", "--", str(PLPR)))}\n')  # staged edits too


async def wait_server(server, addr, log_path, deadline_s=1800):
    t0 = time.time()
    while time.time() - t0 < deadline_s:
        if server.poll() is not None:  # the build died: say so now, not after the deadline
            raise RuntimeError(f'server exited with {server.returncode}; see {log_path}')
        try:
            await Client.test_server(addr, timeout=10)  # returns None; raises until the server answers
            return time.time() - t0
        except Exception:
            pass
        await asyncio.sleep(5)
    raise RuntimeError(f'server not up after {deadline_s}s; see {log_path}')


async def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--ml-debugger', action='store_true')
    ap.add_argument('leg')
    ap.add_argument('port', type=int)
    ap.add_argument('threads', type=int)
    ap.add_argument('theories', nargs='+')
    a = ap.parse_args()
    addr = f'127.0.0.1:{a.port}'
    leg_dir = STEP5 / a.leg
    if leg_dir.exists() and any(leg_dir.iterdir()):  # one leg, one directory: never mix two runs
        raise RuntimeError(f'{leg_dir} is not empty; use a new leg name or remove it')
    leg_dir.mkdir(parents=True, exist_ok=True)
    try:  # a fresh leg needs a fresh server: refuse a port something already answers on
        await Client.test_server(addr, timeout=5)
        raise RuntimeError(f'port {a.port} already has a REPL server; kill it first')
    except (ConnectionRefusedError, OSError):
        pass
    server_options = ['-o', f'threads={a.threads}', '-d', str(MLML)]
    if a.ml_debugger:
        server_options += ['-o', 'ML_debugger=true']
    (leg_dir / 'result.txt').write_text(provenance(server_options))
    env = dict(os.environ)
    env['ISABELLE_EVENT_LOG_DIR'] = str(leg_dir / 'event_log')
    env['PATH'] = str(MLML / 'contrib/Isabelle2025-2/bin') + ':' + env['PATH']
    server_log = open(leg_dir / 'server.log', 'w')
    server = subprocess.Popen(
        ['bash', str(MLML / 'contrib/Isa-REPL/repl_server.sh'), addr, 'Phi_System_Base',
         str(leg_dir / 'repl_out'), *server_options],
        cwd=str(MLML), env=env, stdout=server_log, stderr=subprocess.STDOUT,
        start_new_session=True)
    try:
        startup = await wait_server(server, addr, leg_dir / 'server.log')
        print(f'[{a.leg}] server up after {startup:.0f}s', flush=True)
        async with Client(addr, 'Phi_Test', timeout=None) as c:
            await c.set_trace(False)
            t0 = time.time()
            errors = None
            try:
                loaded = await c.load_theory(a.theories)
            except REPLFail as e:
                loaded, errors = None, str(e)
            elapsed = time.time() - t0
        print(f'[{a.leg}] load_theory {a.theories}: {elapsed:.1f}s wall; loaded={loaded}', flush=True)
        if errors:
            print(f'[{a.leg}] ERRORS:\n{errors[:6000]}', flush=True)
        with open(leg_dir / 'result.txt', 'a') as f:
            f.write(f'leg={a.leg}\ntheories={a.theories}\nthreads={a.threads}\nstartup_s={startup:.0f}\n'
                    f'wall_s={elapsed:.1f}\nloaded={loaded}\nerrors={"yes" if errors else "no"}\n')
    finally:
        os.killpg(os.getpgid(server.pid), signal.SIGTERM)
        try:
            server.wait(60)
        except subprocess.TimeoutExpired:
            os.killpg(os.getpgid(server.pid), signal.SIGKILL)
        # the poly process of `isabelle build` outlives its process group: kill the
        # listener on the port too, so the next leg cannot reuse a loaded server
        subprocess.run(['fuser', '-k', '-TERM', f'{a.port}/tcp'], capture_output=True)
        time.sleep(3)
        subprocess.run(['fuser', '-k', '-KILL', f'{a.port}/tcp'], capture_output=True)
        server_log.close()
    print(f'[{a.leg}] done', flush=True)


asyncio.run(main())
