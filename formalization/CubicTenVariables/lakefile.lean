import Lake
open Lake DSL
package CubicTenVariables where
  leanOptions := #[⟨`autoImplicit, false⟩]
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.26.0"
require HessianTheorem11 from "../HessianTheorem11"
require TranslatedDepthSeven from "../TranslatedDepthSeven"
@[default_target]
lean_lib CubicTenVariables where
  -- The checked public root and its transitive imports. New modules are
  -- added to the root only after their individual proof checks succeed.
  globs := #[.one `CubicTenVariables]
