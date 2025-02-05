import Lake
open Lake DSL

package "lean_minicourse" where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require "leanprover-community" / "mathlib"
require reaper_tac from git "https://github.com/slashbade/reaper_tac.git"

@[default_target]
lean_lib «LeanMinicourse» where
  -- add any library configuration options here
