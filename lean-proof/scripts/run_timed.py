#!/usr/bin/env python3
"""Run a command, preserve its exit code, and record resource use."""
import resource,subprocess,sys,time
start=time.monotonic()
try:
    result=subprocess.run(sys.argv[1:])
except KeyboardInterrupt:
    print('Interrupted by operator.', flush=True)
    raise SystemExit(130)
used=resource.getrusage(resource.RUSAGE_CHILDREN)
print(f'Exit: {result.returncode}; elapsed seconds: {time.monotonic()-start:.3f}; child CPU user/system seconds: {used.ru_utime:.3f}/{used.ru_stime:.3f}; peak child RSS KiB: {used.ru_maxrss}', flush=True)
raise SystemExit(result.returncode)
