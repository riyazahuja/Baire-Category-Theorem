import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite


universe u
variable {X: Type u} [MetricSpace X]


def cauchy (a: ℕ → X) : Prop := ∀ε>0, ∃N: ℕ, ∀n m : ℕ, ((m≥ N ∧ n ≥ N) → dist (a n) (a m) < ε)

def convergent (a: ℕ → X) : Prop := ∃L:X, ∀ ε>0, ∃N: ℕ, ∀n:ℕ, n≥ N → dist (a n) L < ε




def NowhereDense (A: Set X) : Prop :=
  interior (closure (A)) = ∅



def limit_point (x: X) : Prop :=
∀ ε > 0, ∃ y : X, y ≠ x ∧ dist y x < ε


def isolated_point (x : X) : Prop := ¬(limit_point x)


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

    induction' n with m ih
    {
      rw [Nat.zero_eq] at *
      unfold NowhereDense
      simp
    }
    {
      rw [← Nat.add_one] at *
      have hA' :  ∀ (i : ℕ), i < m → NowhereDense (A i) := by
        intro i hi
        have duh : i < m+1 := by linarith
        specialize hA i duh
        exact hA

      have h_union_nd : NowhereDense (⋃ i < m, A i) := ih hA'

      have last_nd : NowhereDense (A m) := by
        have fin := hA m
        have duh : m < m+1 := by linarith
        exact fin duh

      /-FINISH!!!!!!!!-/

    }






lemma closure_nowhere_dense {A: Set X} (hA: NowhereDense A) : NowhereDense (closure A) :=
  by
    unfold NowhereDense at *
    rw [closure_closure]
    exact hA


lemma no_isolated_imp_finite_nowhere_dense (h: (∀x : X, ¬isolated_point x)) : ∀ A:Set X, Set.Finite A → NowhereDense A := by
  intro A hA
  /-We know A is union of singletons-/
  have temp : ∀ x: X, IsOpen {x} ↔ isolated_point x := by
    intro x
    rw [@Metric.isOpen_singleton_iff]
    constructor
    {
      intro definition
      rcases definition with ⟨ε,hx⟩
      unfold isolated_point
      unfold limit_point
      push_neg
      use ε
      constructor
      exact hx.1
      intro y
      have hx' := hx.2 y
      contrapose!
      exact hx'
    }
    {
      intro definition
      unfold isolated_point at *
      unfold limit_point at *
      push_neg at definition
      rcases definition with ⟨ε,hx⟩
      use ε
      rcases hx with ⟨temp,hx⟩
      constructor
      exact temp
      clear temp
      intro y
      specialize hx y
      contrapose!
      exact hx
    }



  have list_A := (Set.Finite.toFinset hA).toList

  have sizeA := List.length list_A

  have finite_is_singleton_union : N := by
    use fun i:Fin (List.length list_A)  ↦ {list_A.get i}















def meager (A : Set X) : Prop := ∃ (U : ℕ → Set X), (∀ i, NowhereDense (U i)) ∧ A = ⋃ i, U i
def nonmeager (A : Set X) : Prop := ¬meager A
def residual (A: Set X) : Prop := meager Aᶜ


lemma NowhereDense_imp_meager (A: Set X) (hA: NowhereDense A) : meager A := by
  unfold meager
  use fun i ↦ A
  constructor
  {
    intro hm
    exact hA
  }
  {
    exact Eq.symm (Set.iUnion_const A)
  }



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
  unfold meager at *

  choose F hF using hA

  have compose : ⋃i:ℕ, A i = ⋃i:ℕ , ⋃ j:ℕ, F i j := by
    refine Eq.symm (Set.iUnion_congr ?h)
    intro i
    specialize hF i
    rw [hF.2]

  have hG : ∃G:ℕ → Set X, (∀k:ℕ, NowhereDense (G k)) ∧ (⋃i:ℕ , ⋃ j:ℕ, F i j = ⋃ k:ℕ, G k):= by
    use fun k ↦ F (Nat.unpair k).1 (Nat.unpair k).2
    constructor
    {
      intro k
      specialize hF (Nat.unpair k).1
      have final := hF.1 (Nat.unpair k).2
      exact final
    }
    {
      exact Eq.symm (Set.iUnion_unpair F)
    }

  rcases hG with ⟨G,hG⟩
  use G
  constructor
  {
    exact hG.1
  }
  {
    rw [compose]
    exact hG.2
  }



















variable (X)
def BaireSpace  : Prop := ∀A:Set X, meager A → interior A = ∅

lemma BaireSpace_comp_meager_dense: BaireSpace X ↔ (∀ A:Set X, meager (Aᶜ) → Dense A ):= by
  constructor
  {
    intro hBS
    intro A
    intro hAc
    unfold BaireSpace at *
    specialize hBS Aᶜ hAc

    have fact := interior_eq_empty_iff_dense_compl.1 hBS
    rw [@compl_compl] at fact
    exact fact
  }
  {
    intro h
    intro A hA
    specialize h Aᶜ
    rw  [@compl_compl] at h
    specialize h hA
    have fact := interior_eq_empty_iff_dense_compl.2 h
    exact fact
  }





lemma BaireSpace_dense_intersection : BaireSpace X ↔ (∀ A: ℕ → Set X, (∀ i:ℕ, Dense (A i) ∧ IsOpen (A i)) → Dense (⋂ i, A i)) := by

  constructor

  {
    intro hX
    intro A hDO


    unfold BaireSpace at *

    have nowhereDenseCompl : ∀ i:ℕ, NowhereDense (A i)ᶜ := by
      intro i
      specialize hDO i
      have closed : IsClosed (A i)ᶜ := by
        exact isClosed_compl_iff.2 hDO.right
      have empty_interior : interior (A i)ᶜ = ∅ := by
        have rewritten : Dense ((A i)ᶜ)ᶜ := by
          rw  [@compl_compl]
          exact hDO.left
        exact interior_eq_empty_iff_dense_compl.2 rewritten
      unfold NowhereDense
      have fact := closure_eq_iff_isClosed.2 closed
      rw [fact]
      exact empty_interior

    have meagerCompl : ∀i:ℕ , meager (A i)ᶜ := by
      intro i
      specialize nowhereDenseCompl i
      apply NowhereDense_imp_meager
      exact nowhereDenseCompl

    have union_meagerCompl : meager (⋃ i:ℕ, (A i)ᶜ) := by
      exact countable_union_meager meagerCompl

    have Compl_fact : ⋃ (i : ℕ), (A i)ᶜ = (⋂ (i : ℕ), A i)ᶜ := by
      exact Eq.symm (Set.compl_iInter fun i ↦ A i)

    rw [Compl_fact] at union_meagerCompl

    exact (BaireSpace_comp_meager_dense X).1 hX (⋂ (i : ℕ), A i) union_meagerCompl

  }
  {
    intro hX
    unfold BaireSpace
    intro S hS
    unfold meager at *
    rcases hS with ⟨F,hF_nd,hF_u⟩
    unfold NowhereDense at *

    have Dense_closure_compl : ∀ i:ℕ, Dense (closure (F i))ᶜ := by
      intro i
      specialize hF_nd i
      exact Iff.mp interior_eq_empty_iff_dense_compl hF_nd

    have Open_closure_compl : ∀ i:ℕ,IsOpen (closure (F i))ᶜ := by
      intro i
      simp

    have Dense_inter : Dense (⋂ (i : ℕ), (closure (F i))ᶜ ) := by
      apply hX
      intro i
      constructor
      {
        exact Dense_closure_compl i
      }
      {
        exact Open_closure_compl i
      }

    have rwCompl : ⋂ i, (closure (F i))ᶜ = (⋃ i, closure (F i))ᶜ := by
      exact Eq.symm (Set.compl_iUnion fun i ↦ closure (F i))
    rw [rwCompl] at Dense_inter

    have Emp_interior_union : interior (⋃ (i : ℕ), closure (F i)) = ∅ := by
      exact Iff.mpr interior_eq_empty_iff_dense_compl Dense_inter

    rw [hF_u]

    have fact : ⋃ (i : ℕ), F i ⊆ ⋃ (i : ℕ), closure (F i) := by
      intro x hx
      have temp := Set.mem_iUnion.1 hx
      rcases temp with ⟨i,hi⟩

      have hi' : x ∈ closure (F i) := by
        exact subset_closure hi
      exact Set.mem_iUnion_of_mem i hi'

    have fact2 := interior_mono fact
    rw [Emp_interior_union] at fact2
    exact Iff.mp Set.subset_empty_iff fact2
  }






def Complete : Prop := ∀a:ℕ→ X, cauchy a → convergent a


lemma shrinking_closed_set_property (hX: Complete X) (F: ℕ→ Set X)
                                    (hF_chain: ∀a b:ℕ, a ≤ b → F b ⊆ F a)
                                    (hF_bounded : ∀i:ℕ, Metric.Bounded (F i))
                                    (hF_closed: ∀ i: ℕ, IsClosed (F i))
                                    (hF_nonempty: ∀i:ℕ, F i ≠ ∅)
                                    (h_diam_conv: ∀ε>0, ∃N:ℕ, ∀n≥ N, Metric.diam (F n) < ε)
: ∃ x:X, ⋂ i:ℕ, F i = {x} := by

  have get_xi : ∀i:ℕ, ∃x:X, x ∈ (F i) := by
    intro i
    specialize hF_nonempty i
    by_contra opp
    push_neg at opp
    have con : F i = ∅ := by
      exact Iff.mp Set.subset_empty_iff opp
    exact hF_nonempty con

  choose x hx using get_xi

  have cauchy_x : cauchy x := by
    unfold cauchy
    intro ε hε
    specialize h_diam_conv ε hε
    rcases h_diam_conv with ⟨N,hN⟩

    use N

    intro n' m' h_ge_N

    have dist_bnd : dist (x n') (x m') ≤ Metric.diam (F N) := by
      have temp' := ge_iff_le.1 h_ge_N.1
      have temp'' := hF_chain N m' temp'
      have temp1' := ge_iff_le.1 h_ge_N.2
      have temp1'' := hF_chain N n' temp1'

      have wow:= temp1'' (hx n')
      have wow2:= temp'' (hx m')
      have bound := hF_bounded N
      exact Metric.dist_le_diam_of_mem bound wow wow2

    specialize hN N (le_refl N)
    exact gt_of_gt_of_ge hN dist_bnd

  have conv_x := hX x cauchy_x
  rcases conv_x with ⟨L,hL⟩


  have L_everywhere : ∀N:ℕ, L ∈ (F N) := by
    intro N
    have x_N_in_F_N : ∀n≥ N, (x n) ∈ (F N) := by
      intro n hn
      exact hF_chain N n hn (hx n)

    refine Iff.mpr (Metric.mem_of_closed' (hF_closed N)) ?_
    intro ε hε
    specialize hL ε hε
    rcases hL with ⟨M, hL⟩
    specialize hL (max M N) (Nat.le_max_left M N)

    use (x (max M N))
    constructor
    {
      specialize x_N_in_F_N (max M N)  (Nat.le_max_right M N)
      exact x_N_in_F_N
    }
    {
      exact Iff.mp Metric.mem_ball' hL
    }

  use L
  refine Set.ext ?h.h
  intro l
  constructor
  {
    by_contra opp
    push_neg at opp
    rcases opp with ⟨l_inter, l_not⟩
    have duh: l≠ L:= l_not
    clear l_not
    have duh2: dist l L > 0 := by exact Iff.mpr dist_pos duh
    let k : ℝ := dist l L

    specialize h_diam_conv (k/2) (half_pos duh2)
    rcases h_diam_conv with ⟨N,hN⟩
    specialize hN N (le_refl N)
    specialize L_everywhere N
    have hmmm := Set.mem_sInter.1 l_inter (F N) (Set.mem_range_self N)


    have contra1 := Metric.dist_le_diam_of_mem (hF_bounded N) hmmm L_everywhere
    linarith

  }
  {
    intro hl
    have duh : l = L := by exact hl
    rw [duh]
    exact Iff.mpr Set.mem_iInter L_everywhere
  }











theorem Baire_Category_Theorem :  Complete X → BaireSpace X := by
  rw [BaireSpace_dense_intersection]
  intro hX A hA
  have htemp : (∀ (i : ℕ), Dense (A i)) ∧ (∀ (i : ℕ), IsOpen (A i)) := by
    constructor
    intro i
    specialize hA i
    exact hA.1

    intro i
    specialize hA i
    exact hA.2
  rcases htemp with ⟨hAd,hAo⟩
  clear hA

  rw [dense_iff_inter_open]
  intro U hU_open hU_nonempty
  let a:ℕ → ℝ:= fun n ↦ 1/n
  have ha_conv : ∀ ε>0, ∃N:ℕ, ∀n≥ N, a n < ε := by


    intro ε hε
    rcases exists_nat_gt (1/ε) with ⟨N, hN⟩
    use N
    intro n hn

    have fact : ↑N ≤ ↑n := hn
    have fact2 : 1/ε< ↑n := by
      exact_mod_cast lt_of_lt_of_le hN fact
    /-HELP!!!!!!!-/

    dsimp
    have fact3 : 0 < 1/ε:= by
      exact Iff.mpr one_div_pos hε
    refine Iff.mpr (one_div_lt ?h.ha hε) fact2
    exact lt_trans fact3 fact2


  have ha_pos : ∀n:ℕ, n> 0 → a n > 0 := by
    intro n
    intro hn
    simp
    exact hn










  have construction : ∀ n : ℕ, ∀x_old:X, ∀ r_old:ℝ, 0 < r_old → ∃ x:X, ∃ r:ℝ, 0 < r ∧ r ≤ a (n + 1) ∧ (Metric.closedBall x r) ⊆ (Metric.closedBall x_old r_old) ∩ (A n) := by
    intro n x_old r_old h_r_old

    have subset_final : (Metric.ball x_old r_old) ∩ (A n) ⊆ (Metric.closedBall x_old r_old) ∩ (A n) := by
      have duh: (Metric.ball x_old r_old) ⊆ (Metric.closedBall x_old r_old) := by
        exact Metric.ball_subset_closedBall
      exact Set.inter_subset_inter_left (A n) duh

    have subset_interesting : ∀ S : Set X, (S≠ ∅ ∧ IsOpen S) → (∃x:X, ∃r:ℝ, 0< r ∧ r≤ a (n+1) ∧ Metric.closedBall x r ⊆ S):= by
      intro S hS
      rcases hS with ⟨hS_nonempty, hS_open⟩
      have duh : ∃ x : X, x∈ S := by
        by_contra opp
        push_neg at opp
        have :S=∅ := by
          exact Iff.mp Set.subset_empty_iff opp
        exact hS_nonempty this
      rcases duh with ⟨x,hx⟩

      have wow:= Metric.isOpen_iff.1 hS_open x hx
      rcases wow with ⟨ε, hε⟩
      use x
      use ( min (ε/2) (a (n+1)) )
      rcases hε with ⟨hε, wow ⟩

      have woww : Metric.closedBall x ( min (ε/2) (a (n+1)) ) ⊆ Metric.ball x ε := by
        have duh : ( min (ε/2) (a (n+1)) ) ≤ ε /2 := by exact min_le_left (ε / 2) (a (n + 1))

        have this: Metric.closedBall x ( min (ε/2) (a (n+1)) ) ⊆ Metric.closedBall x (ε/2) := Metric.closedBall_subset_closedBall duh

        have this2: Metric.closedBall x (ε/2) ⊆ Metric.ball x ε := Metric.closedBall_subset_ball (half_lt_self hε)

        exact subset_trans this this2



      constructor
      {
        have hm := ha_pos (n+1) (Nat.succ_pos n)
        have hε2 : ε/2 >0 := half_pos hε

        exact lt_min hε2 (ha_pos (n + 1) (Nat.succ_pos n))
      }
      {
        constructor
        {
          exact min_le_right (ε / 2) (a (n + 1))
        }
        {
          exact subset_trans woww wow
        }
      }

    let S:Set X := Metric.ball x_old r_old ∩ A n

    have fact : S≠ ∅ ∧ IsOpen S := by
      constructor
      {
        have fact := Metric.dense_iff.1 (hAd n) x_old r_old h_r_old
        rcases fact with ⟨x,hx⟩

        by_contra opp
        have duh : ∀ x:X, x∉ S := by exact fun x ↦ not_of_eq_false (congrArg (Membership.mem x) opp)
        specialize duh x
        have duhh : x∈ S:= hx
        exact duh hx

      }
      {
        apply IsOpen.inter
        exact Metric.isOpen_ball
        exact hAo n
      }


    /-YAY-/
    specialize subset_interesting S fact
    rcases subset_interesting with ⟨x, r, hr0,hr1,h⟩
    use x
    use r
    constructor
    {
      exact hr0
    }
    {
      constructor
      {
        exact hr1
      }
      {
        exact subset_trans h subset_final
      }
    }

  choose! center radius Hpos Ha Hball using construction
  /- center(n)(old_x)(old_r) = x
     radius(n)(old_x)(old_r) = r -/

  /-Now, want to show that there exists x:ℕ → X and r: ℕ → ℝ such that 0 < r n ≤ a (n+1)
    and closedBall(x (i+1), r (i+1)) ⊆ closedBall(x i,r i) for all i:ℕ,
    and as diam closedBall(x i, r i) = r i ≤ a (n+1), diam converges to 0,
    so ⋂ i, closedBall(x i, r i) = {L}.

    Now, want to show that for all i:ℕ,
    closedBall(x i, r i) ⊆ closedBall(x (i-1), r (i-1)) ∩ A i ⊆ ... ⊆ closedBall(x 0, r 0) ∩ V i ⊆ U ∩ A i
    Thus, L ∈ U ∩ A i for all i:ℕ, and thus L ∈ ⋂ i, (U ∩ A i)
  -/

  /- Want to show that there exists x₀ r₀ such that closedBall(x₀,r₀) ⊆ U -/
  have initialize_process : ∃ x: X, ∃ r : ℝ, 0<r ∧ r≤ (a 1) ∧ Metric.closedBall x r ⊆ U := by
    rcases hU_nonempty with ⟨x,hx⟩
    have :=  Metric.isOpen_iff.1 hU_open x hx
    rcases this with ⟨ε,hε,h ⟩
    use x
    use min (ε/2) (a 1)
    constructor
    {
      have hm := ha_pos 1 ((Nat.succ_pos 0))
      have hε2 : ε/2 >0 := half_pos hε

      exact lt_min hε2 (ha_pos (1) (Nat.succ_pos 0))
    }
    {
      constructor
      {
        exact min_le_right (ε / 2) (a 1)
      }
      {

        have fact:Metric.closedBall x (min (ε / 2) (a 1)) ⊆ Metric.closedBall x (ε / 2) := by
          have fact2 := min_le_left (ε / 2) (a 1)
          exact Metric.closedBall_subset_closedBall fact2
        have fact2 : Metric.closedBall x (ε / 2) ⊆ Metric.ball x ε := by
          have fact3 : ε/2 < ε := by exact half_lt_self hε
          exact Metric.closedBall_subset_ball fact3
        exact subset_trans fact (subset_trans fact2 h)
      }
    }

  rcases initialize_process with ⟨x₀, r₀ ,hr₀_pos, hr₀_am, h₀⟩



  def f : (ℕ × (X × ℝ)) → X × ℝ
  | (0,(x₀,r₀))     => (x₀,r₀)
  | (n+1,(x₀,r₀)) => (center (n+1) (f n).1 (f n).2, radius (n+1) (f n).1 (f n).2)





























/-If I have time, do some cool cantor corollaries and -/
