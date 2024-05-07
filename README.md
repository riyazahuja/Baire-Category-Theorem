# Baire Category Theorem Formalization

This repository contains a Lean 4 formalization of the Baire Category Theorem (BCT) in complete metric spaces. The formalization leverages Lean's Mathlib library and establishes key properties and lemmas necessary for the proof. 

## The Formalization

### Core Definitions

1. **Cauchy and Convergent Sequences:**
   - `def cauchy (a: ℕ → X) : Prop`
   - `def convergent (a: ℕ → X) : Prop`

2. **Key Concepts:**
   - `NowhereDense`: A set is nowhere dense if the interior of its closure is empty.
   - `limit_point`, `isolated_point`: i.e. accumulation points and non-accumulation points.
   - `meager`, `nonmeager`, `residual`: Characteristics of sets and their "size" defined in terms of \(nowhere\) density.
   - `BaireSpace`: Defines the properties of a Baire Space.

### Important Lemmas

1. **Basic Properties:**
   - `subset_nowhere_dense`
   - `union_of_nowhere_dense`
   - `closure_nowhere_dense`

2. **Applications:**
   - `no_isolated_imp_finite_nowhere_dense`
   - `subset_meager`
   - `union_meager`

3. **Characterization of Baire Spaces:**
   - `BaireSpace_comp_meager_dense`
   - `BaireSpace_dense_intersection`

### Key Theorem: Baire Category Theorem

`theorem Baire_Category_Theorem : Complete X → BaireSpace X`

This theorem states that any complete metric space is a Baire space. The proof uses a combination of lemmas and carefully constructed sequences to show that the intersection of dense open sets is itself dense.

### How to Use

1. Install [Lean](https://leanprover.github.io/) and [Mathlib](https://leanprover.github.io/mathlib4/).
2. Clone this repository.
3. Explore the theorem formalization by reading the `BaireCategoryTheorem.lean` file and the lemmas leading up to it.
4. Test your understanding by experimenting with Lean's interactive features and verifying individual lemmas.

### References

- [Lean Prover Documentation](https://leanprover.github.io/)
- [Mathlib4 Library Documentation](https://leanprover.github.io/mathlib4_docs/)

### Acknowledgements
This formalization is created by Riyaz Ahuja. Special thanks to Patrick Massot for the guidance and inspiration behind this project.
