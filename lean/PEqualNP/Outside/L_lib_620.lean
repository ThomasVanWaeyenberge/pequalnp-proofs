import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_lib_620

theorem large_rectangle {n m : Nat} (positive : 0 < m) (G : Fin n → Fin n → Bool)
    (R C : Finset (Fin n)) (rh : m*4^m ≤ R.card) (ch : m*4^m ≤ C.card) :
    ∃ A ⊆ R, ∃ B ⊆ C, A.card = m ∧ B.card = m ∧
      ∃ b, ∀ a ∈ A, ∀ c ∈ B, G a c = b := by
  classical
  have m1 : 1 ≤ m := by omega
  have bound : 2 ≤ 4^m :=
    le_trans (by decide : 2 ≤ 4^1) (Nat.pow_le_pow_right (by decide) m1)
  have chooseRows : 2*m ≤ R.card :=
    le_trans (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left m bound) rh
  obtain ⟨D,DR,dSize⟩ := Finset.exists_subset_card_eq chooseRows
  let pattern (col : Fin n) (row : D) := G row.val col
  have pCard : (Finset.univ : Finset (D → Bool)).card = 4^m := by
    rw [Finset.card_univ,Fintype.card_fun,Fintype.card_coe,dSize,Fintype.card_bool,pow_mul]
    rfl
  obtain ⟨p,_,fiberSize⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s := C) (t := (Finset.univ : Finset (D → Bool))) (f := pattern) (n := m)
    (fun _ _ => Finset.mem_univ _) ⟨fun _ => false,Finset.mem_univ _⟩
    (by rw [pCard,Nat.mul_comm]; exact ch)
  obtain ⟨B,BC,bSize⟩ := Finset.exists_subset_card_eq fiberSize
  have two : (Finset.univ : Finset Bool).card * m ≤ (Finset.univ : Finset D).card := by
    simp [dSize]
  obtain ⟨color,_,many⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s := (Finset.univ : Finset D)) (t := (Finset.univ : Finset Bool)) (f := p) (n := m)
    (fun _ _ => Finset.mem_univ _) ⟨false,Finset.mem_univ _⟩ two
  obtain ⟨rows,subset,aSize⟩ := Finset.exists_subset_card_eq many
  let A := rows.map (Function.Embedding.subtype fun r => r ∈ D)
  refine ⟨A,?_,B,fun col hc => (Finset.mem_filter.mp (BC hc)).1,
    by simpa [A] using aSize,bSize,color,?_⟩
  · intro a ha
    obtain ⟨r,_,rfl⟩ := Finset.mem_map.mp ha
    exact DR r.property
  · intro a ha col hc
    obtain ⟨r,hr,rfl⟩ := Finset.mem_map.mp ha
    have eq := (Finset.mem_filter.mp (BC hc)).2
    exact (congrFun eq r).trans (Finset.mem_filter.mp (subset hr)).2

def sameColor {n g : Nat} (G : Fin n → Fin n → Bool) (R C : Finset (Fin n))
    (p : R ≃ C) (color : R → Fin g) : Prop :=
  ∀ x y z w : R, color x = color y → color x = color z → color x = color w →
    G x.val (p y).val = G z.val (p w).val

noncomputable def splitRows {n : Nat} {A R : Finset (Fin n)} (sub : A ⊆ R) :
    A ⊕ (R \ A : Finset (Fin n)) ≃ R := by
  classical
  let f : A ⊕ (R \ A : Finset (Fin n)) → R :=
    Sum.elim (fun a => ⟨a.val,sub a.property⟩) (fun b => ⟨b.val,(Finset.mem_sdiff.mp b.property).1⟩)
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro x y eq
    cases x with
    | inl a =>
      cases y with
      | inl b =>
        have same0 := congrArg Subtype.val eq
        exact congrArg Sum.inl (Subtype.ext same0)
      | inr b =>
        have same0 := congrArg Subtype.val eq
        have same : a.val = b.val := same0
        exact ((Finset.mem_sdiff.mp b.property).2 (same ▸ a.property)).elim
    | inr a =>
      cases y with
      | inl b =>
        have same0 := congrArg Subtype.val eq
        have same : a.val = b.val := same0
        exact ((Finset.mem_sdiff.mp a.property).2 (same.symm ▸ b.property)).elim
      | inr b =>
        have same0 := congrArg Subtype.val eq
        exact congrArg Sum.inr (Subtype.ext same0)
  · intro r
    by_cases e : r.val ∈ A
    · exact ⟨Sum.inl ⟨r.val,e⟩,rfl⟩
    · exact ⟨Sum.inr ⟨r.val,Finset.mem_sdiff.mpr ⟨r.property,e⟩⟩,rfl⟩

theorem split_left {n : Nat} {A R : Finset (Fin n)} (sub : A ⊆ R) (a : A) :
    (splitRows sub (Sum.inl a)).val = a.val := rfl

theorem split_right {n : Nat} {A R : Finset (Fin n)} (sub : A ⊆ R) (a : (R \ A : Finset (Fin n))) :
    (splitRows sub (Sum.inr a)).val = a.val := rfl

theorem add_block {n g : Nat} (G : Fin n → Fin n → Bool) {A R B C : Finset (Fin n)}
    (ar : A ⊆ R) (bc : B ⊆ C) (eq : A.card = B.card)
    (fill : ∃ bit, ∀ a ∈ A, ∀ b ∈ B, G a b = bit)
    (matchRest : ∃ p : (R \ A : Finset (Fin n)) ≃ (C \ B : Finset (Fin n)), ∃ color : _ → Fin g,
      sameColor G (R \ A) (C \ B) p color) :
    ∃ p : R ≃ C, ∃ color : R → Fin (g+1), sameColor G R C p color := by
  classical
  obtain ⟨pr,cr,valid⟩ := matchRest
  obtain ⟨bit,fiber⟩ := fill
  let piece : A ≃ B := Fintype.equivOfCardEq (by simpa using eq)
  let combined : A ⊕ (R \ A : Finset (Fin n)) ≃ B ⊕ (C \ B : Finset (Fin n)) :=
    Equiv.sumCongr piece pr
  let p := (splitRows ar).symm.trans (combined.trans (splitRows bc))
  let color : A ⊕ (R \ A : Finset (Fin n)) → Fin (g+1) :=
    Sum.elim (fun _ => 0) (fun t => (cr t).succ)
  have mapping (t : A ⊕ (R \ A : Finset (Fin n))) : p (splitRows ar t) = splitRows bc (combined t) := by simp [p]
  have core (x y z w : A ⊕ (R \ A : Finset (Fin n)))
      (xy : color x = color y) (xz : color x = color z) (xw : color x = color w) :
      G (splitRows ar x).val (splitRows bc (combined y)).val =
        G (splitRows ar z).val (splitRows bc (combined w)).val := by
    have zs : ∀ i : Fin g, (0 : Fin (g+1)) ≠ i.succ := fun i h => Fin.succ_ne_zero i h.symm
    rcases x with x | x <;> rcases y with y | y <;> rcases z with z | z <;> rcases w with w | w <;>
      simp only [color, Sum.elim_inl, Sum.elim_inr, Fin.succ_inj] at xy xz xw
    all_goals try first
      | exact absurd xy (zs _) | exact absurd xy.symm (zs _)
      | exact absurd xz (zs _) | exact absurd xz.symm (zs _)
      | exact absurd xw (zs _) | exact absurd xw.symm (zs _)
    · show G x.val (piece y).val = G z.val (piece w).val
      rw [fiber _ x.property _ (piece y).property, fiber _ z.property _ (piece w).property]
    · show G x.val (pr y).val = G z.val (pr w).val
      exact valid x y z w xy xz xw
  refine ⟨p,fun x => color ((splitRows ar).symm x),?_⟩
  intro x y z w xy xz xw
  simpa only [← mapping,Equiv.apply_symm_apply] using
    core ((splitRows ar).symm x) ((splitRows ar).symm y) ((splitRows ar).symm z)
      ((splitRows ar).symm w) xy xz xw

theorem pack_groups {n m : Nat} (positive : 0 < m) (G : Fin n → Fin n → Bool) (R C : Finset (Fin n))
    (same : R.card = C.card) :
    ∃ k ≤ R.card/m + m*4^m, ∃ p : R ≃ C, ∃ color : R → Fin k, sameColor G R C p color := by
  classical
  generalize nk : R.card = N
  induction N using Nat.strong_induction_on generalizing R C with
  | ind N ih =>
    by_cases small : R.card < m*4^m
    · let p : R ≃ C := Fintype.equivOfCardEq (by simpa using same)
      let color := R.equivFin
      have room := Nat.le_add_left (m*4^m) (N/m)
      refine ⟨R.card,by omega,p,color,?_⟩
      intro x y z w xy xz xw
      have e1 := color.injective xy
      have e2 := color.injective xz
      have e3 := color.injective xw
      subst e1 e2 e3
      rfl
    · obtain ⟨A,ar,B,bc,asize,bsize,fill⟩ := large_rectangle positive G R C (by omega) (by omega)
      have diffR : (R \ A).card = R.card-m := by rw [Finset.card_sdiff_of_subset ar, asize]
      have diffC : (C \ B).card = C.card-m := by rw [Finset.card_sdiff_of_subset bc, bsize]
      have enough : m ≤ R.card := by
        simpa [asize] using Finset.card_le_card ar
      have less : (R \ A).card < N := by omega
      have eq : (R \ A).card = (C \ B).card := by rw [diffR,diffC,same]
      obtain ⟨k,budget,rest⟩ := ih _ less _ _ eq rfl
      have quota : (R.card-m)/m + 1 = R.card/m := by
        have step := Nat.add_div_right (R.card - m) positive
        rw [Nat.sub_add_cancel enough] at step
        exact step.symm
      refine ⟨k+1,?_ ,add_block G ar bc (asize.trans bsize.symm) fill rest⟩
      rw [diffR] at budget
      rw [← nk]
      omega

theorem finish {n m : Nat} (positive : 0 < m) (hn : m^2*4^m ≤ n)
    (G : Fin n → Fin n → Bool) :
    ∃ (π : Equiv.Perm (Fin n)) (group : Fin n → Fin (2*(n/m))),
      ∀ (x y z w : Fin n), group x = group y → group x = group z → group x = group w →
        G x (π y) = G z (π w) := by
  classical
  let U : Finset (Fin n) := Finset.univ
  obtain ⟨k, hk, p, color, clear⟩ := pack_groups positive G U U rfl
  have h : m*4^m ≤ n/m := (Nat.le_div_iff_mul_le positive).mpr (by nlinarith [hn])
  have nk : k ≤ 2*(n/m) := by
    have cardU : U.card = n := by simp [U]
    rw [cardU] at hk
    omega
  let asU : Fin n ≃ U :=
    ⟨fun i => ⟨i,Finset.mem_univ _⟩,Subtype.val,fun _ => rfl,fun _ => rfl⟩
  refine ⟨asU.trans (p.trans asU.symm),fun x => Fin.castLE nk (color (asU x)),?_⟩
  intro x y z w xy xz xw
  exact clear _ _ _ _ (Fin.castLE_injective nk xy) (Fin.castLE_injective nk xz) (Fin.castLE_injective nk xw)

end PEqualNP.Outside.L_lib_620

theorem PEqualNP.Outside.L_lib_620 : (∀ (n m : ℕ), 0 < m → m^2*4^m ≤ n →
  ∀ G : Fin n → Fin n → Bool,
    ∃ (π : Equiv.Perm (Fin n)) (group : Fin n → Fin (2*(n/m))),
      ∀ (x y z w : Fin n), group x = group y → group x = group z → group x = group w →
        G x (π y) = G z (π w)) := by
  intro n m positive large G
  exact PEqualNP.Outside.L_lib_620.finish positive large G
