import Lake
open Lake DSL

package pilesort where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib PileSort where
  srcDir := "."
