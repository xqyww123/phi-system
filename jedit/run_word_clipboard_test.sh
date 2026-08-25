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
# Three ways this reports a failure, and each exists because the other two miss a case:
#
#   the exit code   only catches what the test itself calls System.exit on, and the
#                   interpreter reports a script error and then exits 0;
#   no PASS: line   catches an error anywhere before the summary, but not after it;
#   an error string catches one after it, and script errors go to stdout, not stderr.
#
# A timeout too: a test that loops instead of failing would otherwise wedge for good,
# and a bug of exactly that shape once produced 135 MB of identical FAIL lines in 30 s.
set -e
here=$(cd "$(dirname "$0")" && pwd)
component=$(dirname "$here")
isabelle=${ISABELLE_HOME:-$(dirname "$component")/Isabelle2025-2}
limit=${PHI_TEST_TIMEOUT:-300}

jar=$(ls "$isabelle"/contrib/jedit-*/jedit*/jedit.jar 2>/dev/null | head -1)
java=$(ls "$isabelle"/contrib/jdk-*/*/bin/java 2>/dev/null | head -1)
# A real JEditTextArea is built in the test -- that is how a drop is driven through jEdit's
# own importText instead of only through the script's helpers -- and its constructor reaches
# FlatLaf.  Without this jar it fails with NoClassDefFoundError before anything is checked.
flatlaf=$(ls "$isabelle"/contrib/flatlaf-*/lib/flatlaf-*-no-natives.jar 2>/dev/null | head -1)
[ -n "$jar" ] || { echo "jedit.jar not found under $isabelle/contrib" >&2; exit 2; }
[ -n "$java" ] || { echo "java not found under $isabelle/contrib" >&2; exit 2; }
[ -n "$flatlaf" ] || { echo "flatlaf jar not found under $isabelle/contrib" >&2; exit 2; }
command -v xvfb-run >/dev/null 2>&1 || { echo "xvfb-run not found; install xvfb" >&2; exit 2; }

log=$(mktemp)
trap 'rm -f "$log"' EXIT

set +e
PHI_SYSTEM_HOME=$component timeout "$limit" xvfb-run -a "$java" -Dfile.encoding=UTF-8 \
    -cp "$jar:$flatlaf" org.gjt.sp.jedit.bsh.Interpreter "$here/test_word_clipboard.bsh" \
    > "$log" 2>&1
rc=$?
set -e

# print it all, unless a runaway test made that useless
if [ "$(wc -c < "$log")" -gt 200000 ]; then
  head -20 "$log"
  echo "... $(wc -l < "$log") lines, $(wc -c < "$log") bytes -- truncated ..."
  tail -20 "$log"
else
  cat "$log"
fi

if [ "$rc" -eq 124 ]; then
  echo "FAILED: the test did not finish within ${limit}s" >&2
  exit 1
fi
if [ "$rc" -ne 0 ]; then
  echo "FAILED: interpreter exited $rc" >&2
  exit 1
fi
if ! grep -q "PASS:" "$log"; then
  echo "FAILED: the test did not report PASS:" >&2
  exit 1
fi
if grep -qE "Evaluation Error|Script threw exception|InterpreterError" "$log"; then
  echo "FAILED: the interpreter reported an error" >&2
  exit 1
fi
