import Lake

open Lake DSL

-- Verso Blueprint v4.32 needs its Lean-facing dependencies overridden to their
-- Lean v4.33.0-rc1 releases until an official Blueprint v4.33 tag is published.
require verso from git "https://github.com/leanprover/verso" @
  "6af30619664960f9c816b27157dff3ceb1500dcf"
require «verso-slides» from git "https://github.com/leanprover/verso-slides" @
  "e65ed1fcbe0bfa8ee94b4a267a01075f41983343"
require proofwidgets from git "https://github.com/leanprover-community/ProofWidgets4" @
  "b1436dc749e722c9920036b52cdc43b3451d0b69"
require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint" @
  "51ebcae4b3133f407807e581178d2dcc705ac683"

package MazurBlueprint where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib MazurBlueprint where
