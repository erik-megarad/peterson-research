import Lake
open Lake DSL

package «peterson-algorithm» where
  fixedToolchain := true

require cslib from git
  "https://github.com/leanprover/cslib" @
  "9a99cbb320aa7742ecbbcecb8df6b404a9b587a3"

@[default_target]
lean_lib Peterson where
  globs := #[.submodules `Peterson]

@[default_target]
lean_lib CircularElection where
  globs := #[.submodules `CircularElection]

@[default_target]
lean_lib ConcurrentReading where
  globs := #[.submodules `ConcurrentReading]

@[default_target]
lean_lib MultiReaderAtomic where
  globs := #[.submodules `MultiReaderAtomic]
