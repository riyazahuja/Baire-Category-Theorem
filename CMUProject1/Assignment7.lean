import Mathlib.GroupTheory.Subgroup.Basic
import MIL.Common

set_option pp.proofs.withType false

-- In whole file, `G` will be a group.
variable {G : Type*} [Group G]

/-
We first define the conjuguate of a subgroup by an element.
Recall you can use `dsimp` to clean a messy tactic state, as
in the proof of `one_mem'` below.
-/

def conjugate (x : G) (H : Subgroup G) : Subgroup G where
  carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}
  one_mem' := by
    use 1
    constructor
    {
      exact Subgroup.one_mem H
    }
    {
      rw [@eq_mul_inv_iff_mul_eq]
      rw [@one_mul]
      rw [@mul_one]
    }
  inv_mem' := by

    intro x_1
    dsimp
    intro hx_1
    rcases hx_1 with ⟨h,hh,hhA⟩
    use h⁻¹
    constructor
    {
      exact Subgroup.inv_mem H hh
    }
    {
      apply inv_eq_iff_mul_eq_one.2
      rw [hhA]
      rw [@conj_mul]
      rw [@mul_inv_self]
      rw [@mul_inv_eq_one]
      rw [@mul_right_eq_self]
    }



  mul_mem' := by
    dsimp
    intro a b ha hb
    rcases ha with ⟨hA,hhA,hAA⟩
    rcases hb with ⟨hB,hhB,hBB⟩
    use hA*hB
    constructor
    {
      exact Subgroup.mul_mem H hhA hhB
    }
    {
      rw [hAA, hBB]
      exact conj_mul
    }


open Subgroup

lemma conjugate_one (H : Subgroup G) : conjugate 1 H = H := by
  ext x
  simp [conjugate]

instance : MulAction G (Subgroup G) where
  smul := conjugate
  one_smul := by
    intro b
    apply conjugate_one
  mul_smul := by
    intro x y b
    ext z
    constructor
    {
      intro hz
      rcases hz with ⟨h,hh1,hh2⟩
      rw [@mul_inv_rev] at hh2
      use (y * h * y⁻¹)
      constructor
      {
        use h
      }
      {
        rw [hh2]
        rw [← @mul_assoc]
        rw [← @mul_assoc]
        rw [← @mul_assoc]
      }
    }
    {
      intro hz
      rcases hz with ⟨h,hh1,hh2⟩
      rcases hh1 with ⟨k,hk,hkA⟩
      use k
      constructor
      {
        exact hk
      }
      {
        rw [hh2, hkA]
        rw [@mul_inv_rev]
        rw [← @mul_assoc]
        rw [← @mul_assoc]
        rw [← @mul_assoc]
      }
    }




-- Until the end of this file, `H` will denote another group.
variable {H : Type*} [Group H]

#check mem_map
#check mem_comap

example (φ : G →* H) (S T : Subgroup H) (hST : S ≤ T) : comap φ S ≤ comap φ T :=by
  intro g hg
  have temp := mem_comap.1 hg
  apply mem_comap.2
  exact hST temp

example (φ : G →* H) (S T : Subgroup G) (hST : S ≤ T) : map φ S ≤ map φ T :=by
  intro g hg
  have temp := mem_map.1 hg
  apply mem_map.2
  rcases temp with ⟨x,hx,hxA⟩
  use x
  constructor
  {
    exact hST hx
  }
  {
    exact hxA
  }



variable {K : Type*} [Group K]

-- Remember you can use the `ext` tactic to prove an equality of subgroups.

example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) :
  comap (ψ.comp φ) U = comap φ (comap ψ U) := by
  ext g
  constructor
  {
    intro hg
    apply mem_comap.2
    have temp := mem_comap.1 hg

    apply mem_comap.2
    exact temp

  }
  {
    intro hg
    apply mem_comap.2
    have temp := mem_comap.1 hg
    exact mem_comap.1 temp
  }

example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) :
  map (ψ.comp φ) S = map ψ (S.map φ) := by
  ext k
  constructor
  {
    intro hk
    rcases (mem_map.1 hk) with ⟨g,hgS,h_eq⟩
    apply mem_map.2
    use (φ g)
    constructor
    {
      apply mem_map.2
      use g
    }
    {
      exact h_eq
    }
  }
  {
    intro hk
    rcases (mem_map.1 hk) with ⟨h,hhS,h_eq⟩
    rcases (mem_map.1 hhS) with ⟨g,hgS,g_eq⟩
    apply mem_map.2
    use g
    constructor
    {exact hgS}
    {
      rw [MonoidHom.comp_apply,g_eq]
      exact h_eq
    }
  }
