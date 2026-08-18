#!/bin/sh
# Run test_word_clipboard.bsh in the same BeanShell interpreter jEdit uses.
#
# Starting jEdit is not needed and would be far slower; the interpreter comes out of
# jedit.jar in the Isabelle distribution.  Point ISABELLE_HOME elsewhere to use another.
#
# A display is needed even though nothing is shown: the script under test installs the
# clipboard hooks, which touches org.gjt.sp.jedit.Registers, whose static initialiser
# calls getSystemClipboard().  Headless that throws.  Xvfb rather than the real display,
# so the test can never disturb what the user has selected or copied.
#
# The interpreter reports a script error on STDOUT and then exits 0, so its exit code
# says nothing: an unbound name or a mistyped method -- the errors only loading the whole
# script can catch -- would otherwise "pass" silently.  Two checks below, because neither
# is enough alone: the test has to say PASS: itself, which catches an error anywhere
# before the summary line, and the output must carry no interpreter error, which catches
# one after it.
set -e
here=$(cd "$(dirname "$0")" && pwd)
component=$(dirname "$here")
isabelle=${ISABELLE_HOME:-$(dirname "$component")/Isabelle2025-2}

jar=$(ls "$isabelle"/contrib/jedit-*/jedit*/jedit.jar 2>/dev/null | head -1)
java=$(ls "$isabelle"/contrib/jdk-*/*/bin/java 2>/dev/null | head -1)
[ -n "$jar" ] || { echo "jedit.jar not found under $isabelle/contrib" >&2; exit 2; }
[ -n "$java" ] || { echo "java not found under $isabelle/contrib" >&2; exit 2; }
command -v xvfb-run >/dev/null 2>&1 || { echo "xvfb-run not found; install xvfb" >&2; exit 2; }

err=$(mktemp)
trap 'rm -f "$err"' EXIT

set +e
out=$(PHI_SYSTEM_HOME=$component xvfb-run -a "$java" -Dfile.encoding=UTF-8 -cp "$jar" \
          org.gjt.sp.jedit.bsh.Interpreter "$here/test_word_clipboard.bsh" 2>"$err")
rc=$?
set -e

printf '%s\n' "$out"
[ -s "$err" ] && cat "$err" >&2

if [ "$rc" -ne 0 ]; then
  echo "FAILED: interpreter exited $rc" >&2
  exit 1
fi
if [ -s "$err" ]; then
  echo "FAILED: output on stderr" >&2
  exit 1
fi
case "$out" in
  *"PASS:"*) ;;
  *) echo "FAILED: the test did not report PASS:" >&2; exit 1 ;;
esac
case "$out" in
  *"Evaluation Error"*|*"Script threw exception"*|*"InterpreterError"*)
    echo "FAILED: the interpreter reported an error" >&2; exit 1 ;;
esac
