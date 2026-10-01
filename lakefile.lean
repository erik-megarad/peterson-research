import Lake
open Lake DSL

package «peterson-algorithm» where
  fixedToolchain := true

require cslib from git
  "https://github.com/leanprover/cslib" @
  "33e7370a94646c19176dc847f7514559bc5e06fb"

lean_lib Peterson where
  globs := #[.submodules `Peterson]
