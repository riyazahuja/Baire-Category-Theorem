import Lake
open Lake DSL

package «CMU-Project-1» where
  -- add any package configuration options here

require Paperproof from git "https://github.com/Paper-Proof/paperproof.git"@"main"/"lean"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «CMUProject1» where
  -- add any library configuration options here
