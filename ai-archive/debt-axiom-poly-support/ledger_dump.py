import asyncio, sys, time
sys.path.insert(0, "/home/xero/Current/MLML/contrib/Isa-REPL")
from IsaREPL import Client, REPLFail

TARGET = "/home/xero/debt_dump_20260902/Ledger_Dump.thy"

async def main():
    async with Client("127.0.0.1:6669", "Phi_Examples", timeout=None) as c:
        await c.set_register_thy(False)   # avoid `duplicate exports`
        await c.set_trace(False)
        t0 = time.time()
        try:
            errs = await c.file(TARGET, timeout=None)
            print("ERRORS RETURNED:", errs, flush=True)
        except REPLFail as e:
            print("REPLFail:", str(e)[:8000], flush=True)
        except Exception as e:
            print("EXC %s: %s" % (type(e).__name__, str(e)[:3000]), flush=True)
        print("ELAPSED %.1f s" % (time.time() - t0), flush=True)

asyncio.run(main())
