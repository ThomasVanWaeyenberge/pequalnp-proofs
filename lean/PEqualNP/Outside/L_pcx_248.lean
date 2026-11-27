import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_248

abbrev Bits (n : Nat) := Fin n → ZMod 2

def sound {n : Nat} {k : Fin 3 → Nat} (code : Bits n → (i : Fin 3) → Bits (k i)) : Prop :=
  ∀ word : Fin 3 → Bits n, (∀ i : Fin 3, code (word i) i = code (word (i+1)) i) →
    ∀ p : Fin 3, word p = word 0

def independentKernels {n : Nat} {k : Fin 3 → Nat}
    (a : (i : Fin 3) → Bits n →ₗ[ZMod 2] Bits (k i)) : Prop :=
  ∀ u : Fin 3 → Bits n, (∀ e, a e (u e) = 0) → (∑ e, u e) = 0 → ∀ e, u e = 0

theorem sound_iff {n : Nat} {k : Fin 3 → Nat}
    (a : (i : Fin 3) → Bits n →ₗ[ZMod 2] Bits (k i)) (b : (i : Fin 3) → Bits (k i)) :
    sound (fun word slot => a slot word + b slot) ↔ independentKernels a := by
  constructor
  · intro hs u hu total
    let words : Fin 3 → Bits n := ![0, u 0, u 0 + u 1]
    have steps (p : Fin 3) : words (p+1) - words p = u p := by
      fin_cases p
      · change u 0 - 0 = u 0
        simp
      · change u 0 + u 1 - u 0 = u 1
        abel
      · change 0 - (u 0 + u 1) = u 2
        rw [Fin.sum_univ_three] at total
        calc
          _ = (u 0 + u 1 + u 2) - (u 0 + u 1) := congrArg (fun h => h - (u 0 + u 1)) total.symm
          _ = u 2 := by abel
    have constant := hs words (fun e => by
      have loc := hu e
      rw [← steps e, map_sub] at loc
      exact congrArg (fun val => val + b e) (sub_eq_zero.mp loc).symm)
    intro p
    rw [← steps p, constant (p+1), constant p, sub_self]
  · intro hs words adjacent
    let u : Fin 3 → Bits n := fun e => words (e+1) - words e
    have zeros (e : Fin 3) : a e (u e) = 0 := by
      have h : a e (words e) = a e (words (e+1)) := add_right_cancel (adjacent e)
      simp [u,h]
    have sum0 : ∑ e, u e = 0 := by
      rw [Fin.sum_univ_three]
      change (words 1-words 0)+(words 2-words 1)+(words 0-words 2) = 0
      abel
    have gaps := hs u zeros sum0
    have w1 : words 1 = words 0 := sub_eq_zero.mp (gaps 0)
    have w2 : words 2 = words 1 := sub_eq_zero.mp (gaps 1)
    intro p
    fin_cases p
    · rfl
    · exact w1
    · exact w2.trans w1

theorem lower {n : Nat} {k : Fin 3 → Nat}
    (a : (i : Fin 3) → Bits n →ₗ[ZMod 2] Bits (k i)) (hs : independentKernels a) :
    2*n ≤ ∑ j : Fin 3, min n (k j) := by
  let S : (∀ i : Fin 3, LinearMap.ker (a i)) →ₗ[ZMod 2] Bits n :=
    { toFun := fun p => ∑ i, (p i).val
      map_add' := fun p q => by
        change (∑ i, ((p i).val + (q i).val)) = _
        exact Finset.sum_add_distrib
      map_smul' := fun r p => by
        change (∑ i, r • (p i).val) = r • ∑ i, (p i).val
        rw [Finset.smul_sum] }
  have injective : Function.Injective S := by
    apply (injective_iff_map_eq_zero S).mpr
    intro x hx
    have h := hs (fun i => (x i).val) (fun e => (x e).property) hx
    funext e
    exact Subtype.ext (h e)
  have budget := LinearMap.finrank_le_finrank_of_injective injective
  rw [Module.finrank_pi_fintype,Module.finrank_pi,Fintype.card_fin,Fin.sum_univ_three] at budget
  have each (e : Fin 3) :
      n - min n (k e) ≤ Module.finrank (ZMod 2) (LinearMap.ker (a e)) := by
    have rank := LinearMap.finrank_range_add_finrank_ker (a e)
    have src := LinearMap.finrank_range_le (a e)
    have dst := Submodule.finrank_le (LinearMap.range (a e))
    have sourceRank : Module.finrank (ZMod 2) (Bits n) = n := by
      exact (Module.finrank_pi _).trans (Fintype.card_fin _)
    have targetRank : Module.finrank (ZMod 2) (Bits (k e)) = k e := by
      exact (Module.finrank_pi _).trans (Fintype.card_fin _)
    rw [sourceRank] at rank src
    rw [targetRank] at dst
    have bound := le_min src dst
    calc
      _ ≤ n - Module.finrank (ZMod 2) (LinearMap.range (a e)) := Nat.sub_le_sub_left bound n
      _ = (Module.finrank (ZMod 2) (LinearMap.range (a e)) +
          Module.finrank (ZMod 2) (LinearMap.ker (a e))) -
          Module.finrank (ZMod 2) (LinearMap.range (a e)) :=
        congrArg (fun q => q - Module.finrank (ZMod 2) (LinearMap.range (a e))) rank.symm
      _ = _ := Nat.add_sub_cancel_left _ _
  rw [Fin.sum_univ_three]
  have h0 := each 0
  have h1 := each 1
  have h2 := each 2
  omega

def omitted (n : Nat) (k : Fin 3 → Nat) (e : Fin 3) : Nat := n - min n (k e)

def start (n : Nat) (k : Fin 3 → Nat) : Fin 3 → Nat :=
  ![0, omitted n k 0, omitted n k 0 + omitted n k 1]

theorem segments (n : Nat) (k : Fin 3 → Nat)
    (budget : 2*n ≤ ∑ j : Fin 3, min n (k j)) :
    (∀ e, start n k e + omitted n k e ≤ n) ∧
      (∀ e j : Fin 3, e < j → start n k e + omitted n k e ≤ start n k j) := by
  rw [Fin.sum_univ_three] at budget
  have total : omitted n k 0 + omitted n k 1 + omitted n k 2 ≤ n := by
    simp only [omitted]
    omega
  constructor
  · intro e
    fin_cases e <;> dsimp [start] <;> omega
  · intro e j h
    fin_cases e <;> fin_cases j <;> simp_all [start]

def selection (n slots lo lost : Nat) : Bits n →ₗ[ZMod 2] Bits slots where
  toFun x j :=
    if h : j.val < n-lost then
      x ⟨if j.val < lo then j.val else j.val+lost, by split_ifs <;> omega⟩
    else 0
  map_add' x y := by
    funext j
    simp only [Pi.add_apply]
    by_cases h : j.val < n-lost <;> simp [h]
  map_smul' c x := by
    funext j
    simp only [Pi.smul_apply,RingHom.id_apply]
    by_cases h : j.val < n-lost <;> simp [h]

theorem observed {n slots lo lost : Nat} (enough : n-lost ≤ slots) (end_le : lo + lost ≤ n)
    (x : Bits n)
    (kernel : selection n slots lo lost x = 0)
    (p : Fin n) (outside : p.val < lo ∨ lo+lost ≤ p.val) :
    x p = 0 := by
  rcases outside with before | after
  · have hl : p.val < n-lost := by omega
    let j : Fin slots := ⟨p.val,lt_of_lt_of_le hl enough⟩
    have same := congrFun kernel j
    have h : j.val < n-lost := hl
    have hl' : j.val < lo := before
    simpa [selection,h,hl',j] using same
  · let j : Fin slots := ⟨p.val-lost,by omega⟩
    have hv : j.val < n-lost := by dsimp [j]; omega
    have low : ¬ j.val < lo := by dsimp [j]; omega
    have same := congrFun kernel j
    have eq : (⟨j.val+lost,by dsimp [j]; omega⟩ : Fin n) = p := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa only [selection,dite_eq_left hv,ite_eq_right low,eq,LinearMap.coe_mk,AddHom.coe_mk,Pi.zero_apply] using same

theorem upper {n : Nat} {k : Fin 3 → Nat} (budget : 2*n ≤ ∑ j : Fin 3, min n (k j)) :
    ∃ a : (i : Fin 3) → Bits n →ₗ[ZMod 2] Bits (k i), independentKernels a := by
  let s := start n k
  let d := omitted n k
  have ⟨stop,pairwise⟩ := segments n k budget
  let a (e : Fin 3) := selection n (k e) (s e) (d e)
  refine ⟨a,?_⟩
  intro u hu hsum e
  funext p
  change u e p = 0
  have known (i : Fin 3) (h : p.val < s i ∨ s i+d i ≤ p.val) : u i p = 0 := by
    apply observed (lo := s i) (lost := d i) (slots := k i) _ (stop i) (u i) (hu i) p h
    dsimp [d,omitted]
    omega
  by_cases lies : s e ≤ p.val ∧ p.val < s e+d e
  · have other (j : Fin 3) (ne : j ≠ e) : u j p = 0 := by
      apply known j
      rcases lt_or_gt_of_ne ne with jl | jr
      · exact Or.inr ((pairwise j e jl).trans lies.1)
      · exact Or.inl (lt_of_lt_of_le lies.2 (pairwise e j jr))
    have sumAt : ∑ i : Fin 3, u i p = 0 := by
      simpa only [Finset.sum_apply,Pi.zero_apply] using congrFun hsum p
    have single : ∑ i : Fin 3, u i p = u e p :=
      Finset.sum_eq_single e (fun i _ h => other i h) (fun h => (h (Finset.mem_univ _)).elim)
    exact single.symm.trans sumAt
  · apply known e
    omega

end PEqualNP.Outside.L_pcx_248

theorem PEqualNP.Outside.L_pcx_248 : (∀ (n : ℕ) (k : Fin 3 → ℕ),
  let X := Fin n → ZMod 2
  let Y := fun i : Fin 3 => Fin (k i) → ZMod 2
  let sound := fun code : X → (index : Fin 3) → Y index =>
    ∀ word : Fin 3 → X, (∀ i : Fin 3, code (word i) i = code (word (i+1)) i) →
      ∀ p : Fin 3, word p = word 0
  (∀ (A : (i : Fin 3) → X →ₗ[ZMod 2] Y i) (b : (i : Fin 3) → Y i),
    sound (fun input slot => A slot input + b slot) ↔
      ∀ u : Fin 3 → X, (∀ e, A e (u e) = 0) → (∑ e, u e) = 0 → ∀ e, u e = 0) ∧
  ((∃ (maps : (i : Fin 3) → X →ₗ[ZMod 2] Y i) (offset : (i : Fin 3) → Y i),
      sound (fun z edge => maps edge z + offset edge)) ↔
    2*n ≤ ∑ j : Fin 3, min n (k j))) := by
  intro n k
  dsimp only
  refine ⟨fun A b => PEqualNP.Outside.L_pcx_248.sound_iff A b, ?_⟩
  constructor
  · rintro ⟨a,b,valid⟩
    exact PEqualNP.Outside.L_pcx_248.lower a ((PEqualNP.Outside.L_pcx_248.sound_iff a b).mp valid)
  · intro budget
    obtain ⟨a,h⟩ := PEqualNP.Outside.L_pcx_248.upper budget
    exact ⟨a,fun _ => 0,(PEqualNP.Outside.L_pcx_248.sound_iff a (fun _ => 0)).mpr h⟩
