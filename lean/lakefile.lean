import Lake
open Lake DSL

-- Pinned to the Aeneas commit used to generate `DoubleAndAdd.lean`.
require aeneas from git
  "https://github.com/AeneasVerif/aeneas.git" @ "ad05a717f8238ad51e13d10216dba39e42e48737" / "backends/lean"

package «double_and_add» {}

@[default_target] lean_lib DoubleAndAdd
@[default_target] lean_lib DoubleAndAddSpec
