#!/usr/bin/env python3
"""STEP 5 harness (GUARD_CACHE_QUICK_MODE_PLAN.md section 10 step 5, section 37 item 12).

One leg = one fresh Isa-REPL server on the Phi_System_Base heap loading a list of
theories from source, timed by this script's wall clock.  The guard_decision
records the load writes (under ML_debugger, when PLPR.thy declares it) land in
<leg dir>/event_log, because ISABELLE_EVENT_LOG_DIR is set for the server.

    run_leg.py <leg name> <port> <threads> <theory>...

The leg's configuration (cache on/off, ML_debugger) is whatever PLPR.thy declares
at the time -- the caller edits PLPR.thy between legs and reverts it at the end.
"""

import asyncio
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


async def wait_server(addr, log_path, deadline_s=1800):
    t0 = time.time()
    while time.time() - t0 < deadline_s:
        try:
            await Client.test_server(addr, timeout=10)  # returns None; raises until the server answers
            return time.time() - t0
        except Exception:
            pass
        await asyncio.sleep(5)
    raise RuntimeError(f'server not up after {deadline_s}s; see {log_path}')


async def main():
    leg, port, threads, *theories = sys.argv[1:]
    addr = f'127.0.0.1:{port}'
    leg_dir = STEP5 / leg
    leg_dir.mkdir(parents=True, exist_ok=True)
    try:  # a fresh leg needs a fresh server: refuse a port something already answers on
        await Client.test_server(addr, timeout=5)
        raise RuntimeError(f'port {port} already has a REPL server; kill it first')
    except (ConnectionRefusedError, OSError):
        pass
    env = dict(os.environ)
    env['ISABELLE_EVENT_LOG_DIR'] = str(leg_dir / 'event_log')
    env['PATH'] = str(MLML / 'contrib/Isabelle2025-2/bin') + ':' + env['PATH']
    server_log = open(leg_dir / 'server.log', 'w')
    server = subprocess.Popen(
        ['bash', str(MLML / 'contrib/Isa-REPL/repl_server.sh'), addr, 'Phi_System_Base',
         str(leg_dir / 'repl_out'), '-o', f'threads={threads}', '-d', str(MLML)],
        cwd=str(MLML), env=env, stdout=server_log, stderr=subprocess.STDOUT,
        start_new_session=True)
    try:
        startup = await wait_server(addr, leg_dir / 'server.log')
        print(f'[{leg}] server up after {startup:.0f}s', flush=True)
        async with Client(addr, 'Phi_Test', timeout=None) as c:
            await c.set_trace(False)
            t0 = time.time()
            errors = None
            try:
                loaded = await c.load_theory(theories)
            except REPLFail as e:
                loaded, errors = None, str(e)
            elapsed = time.time() - t0
        print(f'[{leg}] load_theory {theories}: {elapsed:.1f}s wall; loaded={loaded}', flush=True)
        if errors:
            print(f'[{leg}] ERRORS:\n{errors[:6000]}', flush=True)
        (leg_dir / 'result.txt').write_text(
            f'leg={leg}\ntheories={theories}\nthreads={threads}\nstartup_s={startup:.0f}\n'
            f'wall_s={elapsed:.1f}\nloaded={loaded}\nerrors={"yes" if errors else "no"}\n')
    finally:
        os.killpg(os.getpgid(server.pid), signal.SIGTERM)
        try:
            server.wait(60)
        except subprocess.TimeoutExpired:
            os.killpg(os.getpgid(server.pid), signal.SIGKILL)
        # the poly process of `isabelle build` outlives its process group: kill the
        # listener on the port too, so the next leg cannot reuse a loaded server
        subprocess.run(['fuser', '-k', '-TERM', f'{port}/tcp'], capture_output=True)
        time.sleep(3)
        subprocess.run(['fuser', '-k', '-KILL', f'{port}/tcp'], capture_output=True)
        server_log.close()
    print(f'[{leg}] done', flush=True)


asyncio.run(main())
