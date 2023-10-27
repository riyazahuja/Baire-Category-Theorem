import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.Set.Basic


universe u
variable {X: Type u} [MetricSpace X]


def cauchy (a: ℕ → X) : Prop := ∀ε>0, ∃N: ℕ, ∀n m : ℕ, (m≥ N ∧ n ≥ N) → dist (a n) (a m) < ε

def convergent (a: ℕ → X) : Prop := ∃L:X, ∀ ε>0, ∃N: ℕ, ∀n:ℕ, n≥ N → dist (a n) L < ε


def complete [MetricSpace X] : Prop := ∀a:ℕ→ X, cauchy a → convergent a




def NowhereDense (A: Set X) : Prop :=
  interior (closure (A)) = ∅



def limit_point {A: Set X} (x: A) : Prop :=
∀ ε > 0, ∃ y ∈ A, y ≠ x ∧ dist y x < ε

def isolated_point {A: Set X} (x:A) : Prop := ¬(limit_point x)


lemma subset_nowhere_dense {A B:Set X} (hA: NowhereDense A) (h: B⊆A ) : NowhereDense B := by
    unfold NowhereDense at *
    have h1 : interior (closure B) ⊆ interior (closure A) := by
      exact interior_mono (closure_mono h)

    rw [hA] at h1
    exact Iff.mp Set.subset_empty_iff h1


lemma union_of_nowhere_dense {P Q : Set X} (hP: NowhereDense P) (hQ: NowhereDense Q) : NowhereDense (P ∪ Q) := by
  unfold NowhereDense at *
  rw [closure_union]
  have closure_closed : IsClosed (closure P) := by
    exact isClosed_closure
  have temp:= interior_union_isClosed_of_interior_empty (closure_closed) (hQ)
  rw [hP] at temp
  exact temp


lemma finite_union_of_nowhere_dense {n:ℕ} {A: ℕ  → Set X} (hA : ∀i < n, NowhereDense (A i) ):
  NowhereDense (⋃ i<n, A i) :=  by
    sorry
    /-INDUCTION-/






lemma closure_nowhere_dense {A: Set X} (hA: NowhereDense A) : NowhereDense (closure A) :=
  by
    unfold NowhereDense at *
    rw [closure_closure]
    exact hA


lemma no_isolated_imp_finite_nowhere_dense (h: (∀x : X, ¬isolated_point x)) : ∀ A:Set X, Set.Finite A → NowhereDense A := by
  sorry



def meager (A : Set X) : Prop := ∃ (U : ℕ → Set X), (∀ i, NowhereDense (U i)) ∧ A = ⋃ i, U i
def nonmeager (A : Set X) : Prop := ¬meager A
def residual (A: Set X) : Prop := meager Aᶜ



lemma subset_meager {A B: Set X} (hA: meager A) (h: B⊆ A) : meager B := by
  unfold meager at *
  rcases hA with ⟨U, hA⟩

  use fun i:ℕ ↦ B ∩ (U i)
  constructor
  {
    intro i
    have temp : (B ∩ (U i)) ⊆ U i := by
      exact Set.inter_subset_right B (U i)
    have temp2 := hA.1 i
    exact subset_nowhere_dense temp2 temp
  }
  {
    have temp : ⋃ (i : ℕ), B ∩ U i = B ∩ (⋃ (i : ℕ), U i) := by
      exact Eq.symm (Set.inter_iUnion B fun i ↦ U i)
    rw [temp]
    rw [← hA.2]
    have final := Set.inter_eq_left_iff_subset.2 h

    rw [final]

  }

lemma union_meager {P Q : Set X} (hP: meager P) (hQ: meager Q) : meager (P ∪ Q) := by
  unfold meager at *
  rcases hP with ⟨R,hP⟩
  rcases hQ with ⟨S,hQ⟩
  rcases hP with ⟨hPA,hPB⟩
  rcases hQ with ⟨hQA,hQB⟩
  use (fun i ↦ (R i) ∪ (S i))
  constructor
  {
    intro i

    specialize hPA i
    specialize hQA i

    exact union_of_nowhere_dense hPA hQA

  }
  {
    rw [hPB, hQB]
    exact Eq.symm (Set.iUnion_union_distrib (fun i ↦ R i) fun i ↦ S i)

    }


lemma countable_union_meager {A: ℕ → Set X} (hA: ∀i: ℕ, meager (A i)): meager (⋃ i, A i) := by
  sorry





lemma no_isolated_imp_countable_meager (h: ∀x:X, ¬(isolated_point x)) : ∀A:Set X, Set.Countable A → meager A := by
  sorry






def BaireSpace [MetricSpace X] : Prop := ∀A:Set X, meager A → interior A = ∅

lemma BaireSpace_dense_intersection [MetricSpace X]: BaireSpace X ↔ (∀ A: ℕ → Set X, (∀ i:ℕ, Dense X (A i) ∧ IsOpen (A i)) → Dense X (⋂ i, A i)) := by
  sorry

lemma BaireSpace_empty_union [MetricSpace X]: BaireSpace X ↔ (∀ A: ℕ → Set X, (∀ i:ℕ, Dense X (A i) ∧ IsClosed (A i)) → Dense X (⋂ i, A i)) := by
  sorry

lemma BaireSpace_residual_dense [MetricSpace X]: BaireSpace X ↔ (∀ A:Set X, residual A → Dense X A) := by
  sorry





theorem Baire_Category_Theorem (hX: complete X) : BaireSpace X := by
  sorry


/-If I have time, do some cool cantor corollaries and -/
