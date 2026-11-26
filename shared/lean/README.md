# Shared Lean project

Lean and mathlib are pinned by [the toolchain](lean-toolchain) and [the Lake configuration](lakefile.toml). Topic-specific theorem sources live under the relevant topic's own `lean/` directory. Run these commands in `shared/lean` with elan available.

~~~sh
lake update
awk '/^import Mathlib[.]/ {print $2}' OpenMathResearch/*.lean ../../topics/*/lean/*.lean | sort -u | xargs lake exe cache get
lake build
~~~

If the compiled cache utility fails to start on macOS, collect the imported module names first and invoke the same cache utility through Lean's interpreter.

~~~sh
modules=$(awk '/^import Mathlib[.]/ {print $2}' OpenMathResearch/*.lean ../../topics/*/lean/*.lean | sort -u)
(cd .lake/packages/mathlib && lake build Cache.Main && echo "$modules" | xargs lake env lean --run Cache/Main.lean get)
lake build
~~~
