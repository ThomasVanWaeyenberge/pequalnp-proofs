import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_25716

abbrev Word (k : Nat) := ZMod k → ZMod 2

def rot {k : Nat} (s : Nat) (w : Word k) (i : ZMod k) : ZMod 2 := w (i-(s : ZMod k))

def mix {k : Nat} (d : Nat) (w : Word k) (i : ZMod k) : ZMod 2 :=
  w (i-(d : ZMod k))+w i+w (i+(d : ZMod k))

def out {k : Nat} (d u v : Nat) (name c x : Word k) (j : ZMod k) : ZMod 2 :=
  let y := mix d (rot u x + name)
  y j + (1+y (j+1))*y (j+2) + rot v x j + c j

def test {k : Nat} (d u v : Nat) (z : Word k) (j : ZMod k) : Prop :=
  let a := mix d (rot u z)
  a j = rot v z j ∧ ((k = 1 ∨ k = 3) ∨ (a (j+1) = 0 ∧ a (j+2) = 0))

theorem shift_mix {k : Nat} (d u : Nat) (x z name : Word k) :
    mix d (rot u (x+z) + name) = mix d (rot u x + name) + mix d (rot u z) := by
  funext i
  simp only [mix,rot,Pi.add_apply]
  abel

theorem shift_rot {k : Nat} (u : Nat) (x z : Word k) (j : ZMod k) :
    rot u (x+z) j = rot u x j + rot u z j := rfl

theorem change_out {k : Nat} (d u v : Nat) (x z name c : Word k) (j : ZMod k) :
    let y := mix d (rot u x + name)
    let a := mix d (rot u z)
    out d u v name c (x+z) j = out d u v name c x j ↔
      a j + rot v z j + (1+y (j+1))*a (j+2) + a (j+1)*y (j+2) + a (j+1)*a (j+2) = 0 := by
  dsimp only [out]
  rw [shift_mix,shift_rot]
  simp only [Pi.add_apply]
  constructor <;> intro h <;> linear_combination h

theorem two_cases :
    (∀ a : ZMod 2, (1+a)*a = 0) ∧ (∀ a b : ZMod 2, a+b = 0 ↔ a = b) := by
  decide +kernel

theorem small_width {k : Nat} (d : Nat) (hd : d = 1 ∨ d = 2) (hk : k = 1 ∨ k = 3)
    (w : Word k) (j : ZMod k) : mix d w (j+1) = mix d w (j+2) := by
  rcases hk with rfl | rfl
  · exact congrArg (mix d w) (Subsingleton.elim _ _)
  · rcases hd with rfl | rfl
    · exact (by decide +kernel : ∀ (p : Word 3) i, mix 1 p (i+1) = mix 1 p (i+2)) w j
    · exact (by decide +kernel : ∀ (p : Word 3) i, mix 2 p (i+1) = mix 2 p (i+2)) w j

theorem cast_nonzero {k n : Nat} (hp : 0 < n) (hl : n < k) : (n : ZMod k) ≠ 0 := by
  intro h
  exact (not_le.mpr hl) (Nat.le_of_dvd hp ((ZMod.natCast_eq_zero_iff n k).mp h))

def spike {k : Nat} (p i : ZMod k) : ZMod 2 := if i = p then 1 else 0

theorem two_wide {k : Nat} (wide : 4 ≤ k) (r : ZMod k) (d : Nat) (hd : d = 1 ∨ d = 2) :
    ∃ a b : Word k, mix d a r = 1 ∧ mix d a (r+1) = 0 ∧
      mix d b r = 0 ∧ mix d b (r+1) = 1 := by
  have c1 : (1 : ZMod k) ≠ 0 := by
    simpa only [Nat.cast_one] using (cast_nonzero (k:=k) (n:=1) (by decide) (by omega))
  have c2 : (2 : ZMod k) ≠ 0 := cast_nonzero (k:=k) (n:=2) (by decide) (by omega)
  have c3 : (3 : ZMod k) ≠ 0 := cast_nonzero (k:=k) (n:=3) (by decide) (by omega)
  have ne (x y z : ZMod k) (h : x-y = z) (nz : z ≠ 0) : x ≠ y := by
    intro eq
    exact nz (h.symm.trans (sub_eq_zero.mpr eq))
  rcases hd with rfl | rfl
  · have h01 : r ≠ r-1 := ne _ _ 1 (by ring) c1
    have h11 : r+1 ≠ r-1 := ne _ _ 2 (by ring) c2
    have h21 : r+1+1 ≠ r-1 := ne _ _ 3 (by ring) c3
    have h12 : r+1 ≠ r+1+1 := (ne (r+1+1) (r+1) 1 (by ring) c1).symm
    have h02 : r ≠ r+1+1 := (ne (r+1+1) r 2 (by ring) c2).symm
    have hm2 : r-1 ≠ r+1+1 := h21.symm
    refine ⟨spike (r-1),spike (r+1+1),?_⟩
    simp [mix,spike,h01,h11,h21,h12,h02,hm2]
  · have m2 : r-2 ≠ r := (ne r (r-2) 2 (by ring) c2).symm
    have p2 : r+2 ≠ r := ne _ _ 2 (by ring) c2
    have mm : r+1-2 ≠ r := (ne r (r+1-2) 1 (by ring) c1).symm
    have p1 : r+1 ≠ r := ne _ _ 1 (by ring) c1
    have p3 : r+1+2 ≠ r := ne _ _ 3 (by ring) c3
    have b1 : r-2 ≠ r+1 := (ne (r+1) (r-2) 3 (by ring) c3).symm
    have b3 : r+2 ≠ r+1 := ne _ _ 1 (by ring) c1
    have b4 : r+1-2 ≠ r+1 := (ne (r+1) (r+1-2) 2 (by ring) c2).symm
    have b5 : r+1+2 ≠ r+1 := ne _ _ 2 (by ring) c2
    refine ⟨spike r,spike (r+1),?_⟩
    simp [mix,spike,m2,p2,mm,p1,p3,b1,p1.symm,b3,b4,b5]

theorem width_two_table :
    ∀ j : ZMod 2, ∀ d : Fin 3,
      ∃ a b : Word 2, mix d.val a j = 1 ∧ mix d.val a (j+1) = 0 ∧
        mix d.val b j = 0 ∧ mix d.val b (j+1) = 1 := by
  decide +kernel

theorem two_points {k : Nat} [NeZero k] (nondeg : ¬ (k = 1 ∨ k = 3))
    (r : ZMod k) (d : Nat) (hd : d = 1 ∨ d = 2) :
    ∃ a b : Word k, mix d a r = 1 ∧ mix d a (r+1) = 0 ∧
      mix d b r = 0 ∧ mix d b (r+1) = 1 := by
  by_cases h : k = 2
  · subst k
    rcases hd with rfl | rfl
    · exact width_two_table r 1
    · exact width_two_table r 2
  · have positive := NeZero.pos k
    exact two_wide (by omega) r d hd

theorem rotate_onto {k : Nat} (u : Nat) (w : Word k) :
    rot u (fun j => w (j+(u : ZMod k))) = w := by
  funext j
  simp [rot,sub_add_cancel]

def equation (a b c r x y : ZMod 2) : Prop :=
  a + r + (1+x)*c + b*y + b*c = 0

theorem few_values :
    ∀ a b c r x y : ZMod 2,
      equation a b c r x y → equation a b c r (x+1) y →
      equation a b c r x (y+1) → a = r ∧ b = 0 ∧ c = 0 := by
  unfold equation
  decide +kernel

theorem test_here {k : Nat} [NeZero k] (d u v : Nat) (hd : d = 1 ∨ d = 2)
    (name c z : Word k) (j : ZMod k) :
    (∀ x : Word k, out d u v name c (x+z) j = out d u v name c x j) ↔
      test d u v z j := by
  let a := mix d (rot u z)
  let p := rot v z j
  change _ ↔ a j = p ∧ ((k = 1 ∨ k = 3) ∨ (a (j+1) = 0 ∧ a (j+2) = 0))
  by_cases deg : k = 1 ∨ k = 3
  · have simplify (x : Word k) :
        out d u v name c (x+z) j = out d u v name c x j ↔ a j = p := by
      have nonlinear (w : Word k) : (1+mix d w (j+1)) * mix d w (j+2) = 0 := by
        rw [small_width d hd deg w j]
        exact two_cases.1 _
      simp only [out,nonlinear,add_zero]
      rw [shift_mix,shift_rot]
      simp only [Pi.add_apply]
      rw [← sub_eq_zero]
      have delta :
          mix d (rot u x + name) j + a j + (rot v x j + p) + c j -
            (mix d (rot u x + name) j + rot v x j + c j) = a j + p := by ring
      change _ = 0 ↔ _
      rw [delta]
      exact two_cases.2 _ _
    constructor
    · intro h
      exact ⟨(simplify 0).mp (h 0),Or.inl deg⟩
    · intro h x
      exact (simplify x).mpr h.1
  · let y := mix d name
    have equations (x : Word k) :
        out d u v name c (x+z) j = out d u v name c x j ↔
        equation (a j) (a (j+1)) (a (j+2)) p
          (mix d (rot u x + name) (j+1)) (mix d (rot u x + name) (j+2)) :=
      change_out d u v x z name c j
    constructor
    · intro all
      obtain ⟨sp1,sp2,ha,hb,hc,he⟩ := two_points deg (j+1) d hd
      have plus : j+1+1 = j+2 := by ring
      rw [plus] at hb he
      have base : equation (a j) (a (j+1)) (a (j+2)) p (y (j+1)) (y (j+2)) := by
        have e := (equations 0).mp (all 0)
        have hz : rot u (0 : Word k) = 0 := rfl
        simpa [hz,y] using e
      have shift (sp : Word k) :
          mix d (rot u (fun j => sp (j+(u : ZMod k))) + name) = mix d sp + y := by
        rw [rotate_onto]
        funext i
        simp only [mix,Pi.add_apply,y]
        abel
      have e1 := (equations (fun j => sp1 (j+(u : ZMod k)))).mp (all _)
      have e2 := (equations (fun j => sp2 (j+(u : ZMod k)))).mp (all _)
      rw [shift] at e1 e2
      simp only [Pi.add_apply,ha,hb,hc,he,zero_add,add_comm (1 : ZMod 2)] at e1 e2
      obtain ⟨f,g,h⟩ := few_values _ _ _ _ _ _ base e1 e2
      exact ⟨f,Or.inr ⟨g,h⟩⟩
    · rintro ⟨first,deg' | ⟨s,t⟩⟩ x
      · exact (deg deg').elim
      · apply (equations x).mpr
        simp [equation,s,t,two_cases.2 _ _,first]

end PEqualNP.Outside.L_meta_25716

theorem PEqualNP.Outside.L_meta_25716 : (∀ (k : ℕ) [NeZero k],
  let I := ZMod k
  let B := ZMod 2
  let V := I → B
  let rot := fun (s : ℕ) (w : V) (i : I) => w (i-(s : I))
  let mix := fun (d : ℕ) (w : V) (i : I) => w (i-(d : I))+w i+w (i+(d : I))
  let out := fun (d u v : ℕ) (name c x : V) (j : I) =>
    let y := mix d (rot u x + name)
    y j + (1+y (j+1))*y (j+2) + rot v x j + c j
  let test := fun (d u v : ℕ) (z : V) (j : I) =>
    let a := mix d (rot u z)
    a j = rot v z j ∧ ((k = 1 ∨ k = 3) ∨ (a (j+1) = 0 ∧ a (j+2) = 0))
  ∀ (row col cr cc z : V) (S T : Finset I),
    (∀ x : V,
      (∀ j ∈ S, out 1 1 0 row cr (x+z) j = out 1 1 0 row cr x j) ∧
      (∀ i ∈ T, out 2 3 4 col cc (x+z) i = out 2 3 4 col cc x i)) ↔
    (∀ j ∈ S, test 1 1 0 z j) ∧ (∀ i ∈ T, test 2 3 4 z i)) := by
  intro k nonzero
  dsimp only
  intro row col cr cc z S T
  constructor
  · intro h
    exact ⟨fun j hj => (PEqualNP.Outside.L_meta_25716.test_here 1 1 0 (Or.inl rfl) row cr z j).mp
      (fun x => (h x).1 j hj),
      fun i hi => (PEqualNP.Outside.L_meta_25716.test_here 2 3 4 (Or.inr rfl) col cc z i).mp
      (fun x => (h x).2 i hi)⟩
  · rintro ⟨a,b⟩ x
    exact ⟨fun j hj => (PEqualNP.Outside.L_meta_25716.test_here 1 1 0 (Or.inl rfl) row cr z j).mpr (a j hj) x,
      fun i hi => (PEqualNP.Outside.L_meta_25716.test_here 2 3 4 (Or.inr rfl) col cc z i).mpr (b i hi) x⟩
