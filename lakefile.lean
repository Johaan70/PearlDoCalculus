import Lake
open Lake DSL

package «pearldocalculus» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «PearlDoCalculus» where
  -- The library is the root module `PearlDoCalculus` and everything it imports, so a
  -- new file is built only once `PearlDoCalculus.lean` (or a module it imports) imports it.
