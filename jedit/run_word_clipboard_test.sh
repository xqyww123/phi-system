#!/bin/sh
# Run test_word_clipboard.bsh in the same BeanShell interpreter jEdit uses.
#
# Starting jEdit is not needed and would be far slower; the interpreter comes out of
# jedit.jar in the Isabelle distribution.  Point ISABELLE_HOME elsewhere to use another.
set -e
here=$(cd "$(dirname "$0")" && pwd)
component=$(dirname "$here")
isabelle=${ISABELLE_HOME:-$(dirname "$component")/Isabelle2025-2}

jar=$(ls "$isabelle"/contrib/jedit-*/jedit*/jedit.jar 2>/dev/null | head -1)
java=$(ls "$isabelle"/contrib/jdk-*/*/bin/java 2>/dev/null | head -1)
[ -n "$jar" ] || { echo "jedit.jar not found under $isabelle/contrib" >&2; exit 2; }
[ -n "$java" ] || { echo "java not found under $isabelle/contrib" >&2; exit 2; }

PHI_SYSTEM_HOME=$component "$java" -Dfile.encoding=UTF-8 -cp "$jar" \
    org.gjt.sp.jedit.bsh.Interpreter "$here/test_word_clipboard.bsh"
