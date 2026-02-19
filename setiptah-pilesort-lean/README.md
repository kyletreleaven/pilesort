# PileSort — Lean 4 Formalization

Machine-checked proofs for pile shuffle sort computational complexity gadgets.

## Prerequisites

Install [elan](https://github.com/leanprover/elan) (the Lean version manager):

```sh
curl https://elan.lean-lang.org/install.sh -sSf | sh
```

This project uses Lean 4.16.0, which elan will install automatically on first build.

## Building

```sh
cd setiptah-pilesort-lean
~/.elan/bin/lake build
```

A successful build verifies all proofs (any remaining `sorry` will produce warnings).
