import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_25574

def mix (x : Int → Bool) (z : Int) : Bool :=
  xor (xor (x (z-1)) (x z)) (x (z+1))

def core (x : Int → Bool) (z : Int) : Bool :=
  xor (mix x z) (!(mix x (z+1)) && mix x (z+2))

def update (x inj : Int → Bool) (z : Int) : Bool := xor (core x z) (inj z)

def fits (m : Nat) (u v left right : Bool) : Prop :=
  if m = 1 then ¬ (left = !u ∧ right = !v)
  else if m = 2 then right = v
  else if m = 3 then xor left right = !(xor u v)
  else True

def fitB (m : Nat) (u v left right : Bool) : Bool :=
  if m = 1 then !((left == !u) && (right == !v))
  else if m = 2 then right == v
  else if m = 3 then xor left right == !(xor u v)
  else true

theorem fitB_iff (m : Nat) (u v l r : Bool) :
    fitB m u v l r = true ↔ fits m u v l r := by
  by_cases h1 : m = 1 <;> by_cases h2 : m = 2 <;> by_cases h3 : m = 3 <;>
    cases u <;> cases v <;> cases l <;> cases r <;> simp [fitB, fits, h1, h2, h3]

def near (x : Int → Bool) (b : Int) (u v : Bool) : Bool := x b == !(xor u v)
def far (x : Int → Bool) (b : Int) (v : Bool) : Bool := x (b-1) == v
def hit (x : Int → Bool) (b : Int) : Bool := mix x (b-1)

def aligned (x : Int → Bool) (b : Int) (m : Nat) (u v : Bool) : Bool :=
  ((m == 1) && near x b u v && far x b v) || ((m == 2) && far x b v) ||
    ((m == 3) && near x b u v)

def diagonal (retain : Bool) (x : Int → Bool) (b : Int) (m : Nat) (u v : Bool) : Bool :=
  if retain then
    (m == 3) || (!hit x b && (((m == 1) && !near x b u v && !far x b v) || (m == 2)))
  else
    !hit x b && (((m == 1) && !near x b u v && !far x b v) || (m == 2) || (m == 3))

def edge (x : Int → Bool) (b : Int) (m : Nat) (u v : Bool) : Int :=
  b-3+(hit x b).toNat+((aligned x b m u v && hit x b).toNat : Int)

def mode (retain : Bool) (x : Int → Bool) (b : Int) (m : Nat) (u v : Bool) : Nat :=
  if aligned x b m u v then (if hit x b then 0 else 2) else
    if diagonal retain x b m u v then 3 else 1

def front (x : Int → Bool) : BitVec 4 := BitVec.ofBoolListLE [x (-3), x (-2), x (-1), x 0]
def back2 (x : Int → Bool) : BitVec 2 := BitVec.ofBoolListLE [x 1, x 2]
def back4 (x : Int → Bool) : BitVec 4 := BitVec.ofBoolListLE [x 1, x 2, x 3, x 4]

def join {n : Nat} (p : BitVec 4) (q : BitVec n) (z : Int) : Bool :=
  if z ≤ 0 then p.getLsbD (z+3).toNat else q.getLsbD (z-1).toNat

def extend {n : Nat} (x : Int → Bool) (q : BitVec n) (z : Int) : Bool :=
  if z ≤ 0 then x z else q.getLsbD (z-1).toNat

theorem join2_bit (x : Int → Bool) (z : Int) (lo : -3 ≤ z) (hi : z ≤ 2) :
    join (front x) (back2 x) z = x z := by
  interval_cases z <;> simp only [join, front, back2, BitVec.getLsbD_ofBoolListLE] <;> norm_num

theorem join4_bit (x : Int → Bool) (z : Int) (lo : -3 ≤ z) (hi : z ≤ 4) :
    join (front x) (back4 x) z = x z := by
  interval_cases z <;> simp only [join, front, back4, BitVec.getLsbD_ofBoolListLE] <;> norm_num

theorem extend_join {n : Nat} (x : Int → Bool) (t : BitVec n) (z : Int) (lo : -3 ≤ z) :
    join (front x) t z = extend x t z := by
  by_cases h : z ≤ 0
  · interval_cases z <;> simp only [join, front, extend, BitVec.getLsbD_ofBoolListLE] <;> norm_num
  · simp [join, extend, h]

theorem mix_agree {x y : Int → Bool} {z : Int}
    (h : ∀ t, z-1 ≤ t → t ≤ z+1 → x t = y t) : mix x z = mix y z := by
  simp [mix, h (z-1) (by omega) (by omega), h z (by omega) (by omega),
    h (z+1) (by omega) (by omega)]

theorem core_agree {x y : Int → Bool} {z : Int}
    (h : ∀ t, z-1 ≤ t → t ≤ z+3 → x t = y t) : core x z = core y z := by
  unfold core
  rw [mix_agree (fun t lo hi => h t (by omega) (by omega)),
    mix_agree (fun t lo hi => h t (by omega) (by omega)),
    mix_agree (fun t lo hi => h t (by omega) (by omega))]

theorem edge_bounds (x : Int → Bool) (b : Int) (m : Nat) (u v : Bool) :
    b-3 ≤ edge x b m u v ∧ edge x b m u v ≤ b-1 := by
  cases h : hit x b <;> cases a : aligned x b m u v <;> simp [edge,h,a] <;> omega

theorem edge_nonzero (retain : Bool) (x : Int → Bool) (b : Int) (m : Nat) (u v : Bool)
    (nonzero : mode retain x b m u v ≠ 0) : edge x b m u v ≤ b-2 := by
  cases h : hit x b <;> cases a : aligned x b m u v <;> simp_all [edge,mode] <;> omega

theorem parameters_eq {x y : Int → Bool} {b : Int} (m : Nat) (u v : Bool) (retain : Bool)
    (same : ∀ t, b-2 ≤ t → t ≤ b → x t = y t) :
    edge x b m u v = edge y b m u v ∧ mode retain x b m u v = mode retain y b m u v := by
  have e0 := same b (by omega) (by omega)
  have e1 := same (b-1) (by omega) (by omega)
  have e2 := same (b-1-1) (by omega) (by omega)
  simp [edge, mode, diagonal, aligned, near, far, hit, mix, e0, e1, e2]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
theorem finite_stable :
    ∀ (p : BitVec 4) (a b : BitVec 2) (m : Fin 4) (u v : Bool),
      fitB m.val u v (a.getLsbD 0) (a.getLsbD 1) = true →
      fitB m.val u v (b.getLsbD 0) (b.getLsbD 1) = true →
      ∀ s : Fin 2, let z := (s.val : Int)-2
        z ≤ edge (join p a) 0 m.val u v → core (join p a) z = core (join p b) z := by
  decide +kernel

theorem fronts_eq {x y : Int → Bool} (left : ∀ z ≤ 0, y z = x z) : front x = front y := by
  unfold front
  rw [left (-3) (by norm_num), left (-2) (by norm_num), left (-1) (by norm_num), left 0 (by norm_num)]

theorem tail2_fits {x : Int → Bool} {m : Fin 4} {u v : Bool}
    (hx : fits m.val u v (x 1) (x 2)) : fitB m.val u v ((back2 x).getLsbD 0) ((back2 x).getLsbD 1) = true := by
  simpa only [back2, BitVec.getLsbD_ofBoolListLE, List.getD_cons_zero, List.getD_cons_succ] using
    (fitB_iff _ _ _ _ _).mpr hx

theorem tail4_fits {x : Int → Bool} {m : Fin 4} {u v : Bool}
    (hx : fits m.val u v (x 1) (x 2)) : fitB m.val u v ((back4 x).getLsbD 0) ((back4 x).getLsbD 1) = true := by
  simpa only [back4, BitVec.getLsbD_ofBoolListLE, List.getD_cons_zero, List.getD_cons_succ] using
    (fitB_iff _ _ _ _ _).mpr hx

theorem core_stable_zero {x y : Int → Bool} {m : Fin 4} {u v : Bool}
    (left : ∀ z ≤ 0, y z = x z)
    (hx : fits m.val u v (x 1) (x 2))
    (hy : fits m.val u v (y 1) (y 2)) {z : Int}
    (hz : z ≤ edge x 0 m.val u v) : core y z = core x z := by
  by_cases low : z ≤ -3
  · exact core_agree (fun t _ ht => left t (by omega))
  · have zb : z ≤ -1 := le_trans hz (edge_bounds x 0 m.val u v).2
    let idx : Fin 2 := ⟨(z+2).toNat, by omega⟩
    have idx_eq : (idx.val : Int)-2 = z := by dsimp [idx]; omega
    have sameEdge := (parameters_eq m.val u v true
      (x := join (front x) (back2 x)) (y := x) (b := 0)
      (fun t lo hi => join2_bit x t (by omega) (by omega))).1
    have chk := finite_stable (front x) (back2 x) (back2 y) m u v
      (tail2_fits hx) (tail2_fits hy) idx
    dsimp only at chk
    rw [idx_eq, sameEdge] at chk
    have xa : core (join (front x) (back2 x)) z = core x z :=
      core_agree (fun t lo hi => join2_bit x t (by omega) (by omega))
    have ya : core (join (front x) (back2 y)) z = core y z := by
      rw [fronts_eq left]
      exact core_agree (fun t lo hi => join2_bit y t (by omega) (by omega))
    exact ya.symm.trans ((chk hz).symm.trans xa)

def complete (x y : Int → Bool) (b : Int) (m : Nat) (u v : Bool) : Prop :=
  (∀ z ≤ b, y z = x z) ∧ fits m u v (y (b+1)) (y (b+2))

def slide (b : Int) (x : Int → Bool) (z : Int) : Bool := x (b+z)

theorem mix_slide (b z : Int) (x : Int → Bool) : mix (slide b x) z = mix x (b+z) := by
  simp [mix, slide, add_sub_assoc, add_assoc]

theorem update_slide (b z : Int) (x inj : Int → Bool) :
    update (slide b x) (slide b inj) z = update x inj (b+z) := by
  simp [update, core, mix_slide, slide, add_assoc]

theorem aligned_slide (b : Int) (x : Int → Bool) (m : Nat) (u v : Bool) :
    aligned (slide b x) 0 m u v = aligned x b m u v := by
  simp [aligned, near, far, slide, sub_eq_add_neg]

theorem hit_slide (b : Int) (x : Int → Bool) : hit (slide b x) 0 = hit x b := by
  simp [hit, mix_slide, sub_eq_add_neg]

theorem edge_slide (b : Int) (x : Int → Bool) (m : Nat) (u v : Bool) :
    b + edge (slide b x) 0 m u v = edge x b m u v := by
  simp only [edge, hit_slide, aligned_slide]
  omega

theorem mode_slide (retain : Bool) (b : Int) (x : Int → Bool) (m : Nat) (u v : Bool) :
    mode retain (slide b x) 0 m u v = mode retain x b m u v := by
  simp [mode, diagonal, near, far, hit_slide, aligned_slide, slide, sub_eq_add_neg]

theorem complete_slide (b : Int) (x y : Int → Bool) (m : Nat) (u v : Bool) :
    complete (slide b x) (slide b y) 0 m u v ↔ complete x y b m u v := by
  change ((∀ z ≤ 0, y (b+z) = x (b+z)) ∧ fits m u v (y (b+1)) (y (b+2))) ↔ _
  constructor
  · rintro ⟨left, fit⟩
    refine ⟨fun z hz => ?_, fit⟩
    simpa only [show b + (z-b) = z by omega] using left (z-b) (by omega)
  · rintro ⟨left, fit⟩
    exact ⟨fun z hz => left (b+z) (by omega), fit⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
theorem finite_contains :
    ∀ (p t : BitVec 4) (m : Fin 4) (u v injL injR : Bool),
      let base := join p (0 : BitVec 4)
      let f := edge base 0 m.val u v
      let next := mode false base 0 m.val u v
      fitB m.val u v (t.getLsbD 0) (t.getLsbD 1) = true →
      fitB next (xor (mix base (f+1)) injL) injR
        (xor (core (join p t) (f+1)) injL)
        (xor (core (join p t) (f+2)) injR) = true := by
  decide +kernel

theorem fits_after_zero (x inj : Int → Bool) (m : Fin 4) (u v : Bool)
    (xfit : fits m.val u v (x 1) (x 2)) :
    let f := edge x 0 m.val u v
    let next := mode false x 0 m.val u v
    fits next (xor (mix x (f+1)) (inj (f+1))) (inj (f+2))
      (update x inj (f+1)) (update x inj (f+2)) := by
  let f := edge x 0 m.val u v
  let next := mode false x 0 m.val u v
  let base := join (front x) (0 : BitVec 4)
  have bounds : -3 ≤ f ∧ f ≤ -1 := edge_bounds x 0 m.val u v
  have same (t : Int) (lo : -3 ≤ t) (hi : t ≤ 0) : base t = x t := by
    unfold base
    rw [extend_join x _ t lo]
    simp [extend, hi]
  have par := parameters_eq m.val u v false (x := base) (y := x) (b := 0)
    (fun t lo hi => same t (by omega) hi)
  have tbl := finite_contains (front x) (back4 x) m u v (inj (f+1)) (inj (f+2)) (tail4_fits xfit)
  change fitB (mode false base 0 m.val u v)
    (xor (mix base (edge base 0 m.val u v+1)) (inj (f+1))) (inj (f+2))
    (xor (core (join (front x) (back4 x)) (edge base 0 m.val u v+1)) (inj (f+1)))
    (xor (core (join (front x) (back4 x)) (edge base 0 m.val u v+2)) (inj (f+2))) = true at tbl
  have left : core (join (front x) (back4 x)) (f+1) = core x (f+1) :=
    core_agree (fun t lo hi => join4_bit x t (by omega) (by omega))
  have right : core (join (front x) (back4 x)) (f+2) = core x (f+2) :=
    core_agree (fun t lo hi => join4_bit x t (by omega) (by omega))
  rw [par.1, par.2, left, right] at tbl
  change fits next (xor (mix x (f+1)) (inj (f+1))) (inj (f+2))
    (update x inj (f+1)) (update x inj (f+2))
  by_cases zero : next = 0
  · simp [zero, fits]
  · have close := edge_nonzero false x 0 m.val u v zero
    change f ≤ -2 at close
    have mixEq : mix base (f+1) = mix x (f+1) :=
      mix_agree (fun t lo hi => same t (by omega) (by omega))
    rw [mixEq] at tbl
    exact (fitB_iff _ _ _ _ _).mp tbl

theorem fits_after (x inj : Int → Bool) (b : Int) (m : Fin 4) (u v : Bool)
    (xfit : fits m.val u v (x (b+1)) (x (b+2))) :
    let f := edge x b m.val u v
    let next := mode false x b m.val u v
    fits next (xor (mix x (f+1)) (inj (f+1))) (inj (f+2))
      (update x inj (f+1)) (update x inj (f+2)) := by
  let f0 := edge (slide b x) 0 m.val u v
  have sum : b + f0 = edge x b m.val u v := edge_slide b x m.val u v
  have h := fits_after_zero (slide b x) (slide b inj) m u v xfit
  change fits (mode false (slide b x) 0 m.val u v)
    (xor (mix (slide b x) (f0+1)) (slide b inj (f0+1))) (slide b inj (f0+2))
    (update (slide b x) (slide b inj) (f0+1))
    (update (slide b x) (slide b inj) (f0+2)) at h
  simpa only [mode_slide, mix_slide, update_slide, slide, ← add_assoc, sum] using h

theorem core_stable {x y : Int → Bool} {b : Int} {m : Fin 4} {u v : Bool}
    (left : ∀ z ≤ b, y z = x z)
    (hx : fits m.val u v (x (b+1)) (x (b+2)))
    (hy : fits m.val u v (y (b+1)) (y (b+2))) {z : Int}
    (hz : z ≤ edge x b m.val u v) : core y z = core x z := by
  have translated : z-b ≤ edge (slide b x) 0 m.val u v := by
    have := edge_slide b x m.val u v
    omega
  have h := core_stable_zero (x := slide b x) (y := slide b y)
    (fun t ht => left (b+t) (by omega)) hx hy translated
  have shift (w : Int → Bool) : core (slide b w) (z-b) = core w z := by
    unfold core
    simp only [mix_slide, ← add_assoc, show b + (z-b) = z by omega]
  rwa [shift y, shift x] at h

abbrev State := (Int → Bool) × Int × Nat × Bool × Bool

def oneStep (inj : Int → Bool) (st : State) : State :=
  let f := edge st.1 st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2
  (update st.1 inj, f, mode false st.1 st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2,
    xor (mix st.1 (f+1)) (inj (f+1)), inj (f+2))

def run (x : Int → Bool) (i : Nat → Int → Bool) (origin : Int) (n : Nat) : State :=
  (List.range n).foldl (fun st tick => oneStep (i tick) st) (x,origin,0,false,false)

def invariant (origin : Int) (a b : State) : Prop :=
  a.2.1 = b.2.1 ∧ a.2.2.1 = b.2.2.1 ∧ a.2.1 ≤ origin ∧ a.2.2.1 < 4 ∧
    (∀ z ≤ a.2.1, b.1 z = a.1 z) ∧
    (a.2.2.1 ≠ 0 → a.2.2.2.1 = b.2.2.2.1 ∧ a.2.2.2.2 = b.2.2.2.2) ∧
    fits a.2.2.1 a.2.2.2.1 a.2.2.2.2 (a.1 (a.2.1+1)) (a.1 (a.2.1+2)) ∧
    fits b.2.2.1 b.2.2.2.1 b.2.2.2.2 (b.1 (b.2.1+1)) (b.1 (b.2.1+2))

theorem step_mode_zero (x inj : Int → Bool) (b : Int) (u v u' v' : Bool) :
    oneStep inj (x,b,0,u,v) = oneStep inj (x,b,0,u',v') := by
  simp [oneStep, mode, edge, aligned, diagonal]

theorem step_shared (origin b : Int) (x y i j : Int → Bool) (m : Fin 4) (u v : Bool)
    (frontier : b ≤ origin) (left : ∀ z ≤ b, y z = x z)
    (inject : ∀ z ≤ origin+1, i z = j z)
    (hx : fits m.val u v (x (b+1)) (x (b+2)))
    (hy : fits m.val u v (y (b+1)) (y (b+2))) :
    invariant origin (oneStep i (x,b,m.val,u,v)) (oneStep j (y,b,m.val,u,v)) := by
  let f := edge x b m.val u v
  let next := mode false x b m.val u v
  have par := parameters_eq m.val u v false (x := x) (y := y) (b := b)
    (fun t _ hi => (left t hi).symm)
  have bounds : b-3 ≤ f ∧ f ≤ b-1 := edge_bounds x b m.val u v
  have modeBound : next < 4 := by
    unfold next mode
    split_ifs <;> decide
  have leftNext (z : Int) (hz : z ≤ f) : update y j z = update x i z := by
    unfold update
    rw [core_stable left hx hy hz, inject z (by omega)]
  have bits (nonzero : next ≠ 0) :
      xor (mix x (f+1)) (i (f+1)) = xor (mix y (f+1)) (j (f+1)) ∧ i (f+2) = j (f+2) := by
    have close : f ≤ b-2 := edge_nonzero false x b m.val u v nonzero
    have mixes : mix x (f+1) = mix y (f+1) :=
      mix_agree (fun t _ hi => (left t (by omega)).symm)
    rw [mixes, inject (f+1) (by omega), inject (f+2) (by omega)]
    exact ⟨rfl, rfl⟩
  have fx := fits_after x i b m u v hx
  have fy := fits_after y j b m u v hy
  unfold invariant oneStep
  dsimp only
  rw [← par.1, ← par.2]
  rw [← par.1, ← par.2] at fy
  exact ⟨rfl, rfl, by change f ≤ origin; omega, modeBound, leftNext, bits, fx, fy⟩

theorem step_invariant (origin : Int) (a b : State) (i j : Int → Bool)
    (inject : ∀ z ≤ origin+1, i z = j z) (h : invariant origin a b) :
    invariant origin (oneStep i a) (oneStep j b) := by
  rcases a with ⟨x,frontier,m,u,v⟩
  rcases b with ⟨y,other,k,u',v'⟩
  rcases h with ⟨sameFrontier,sameMode,leOrigin,modeBound,left,bits,hx,hy⟩
  change frontier = other at sameFrontier
  change m = k at sameMode
  subst other
  subst k
  let mFin : Fin 4 := ⟨m, modeBound⟩
  by_cases zero : m = 0
  · have rhs : oneStep j (y,frontier,m,u',v') = oneStep j (y,frontier,m,u,v) := by
      rw [zero, step_mode_zero]
    rw [rhs]
    exact step_shared origin frontier x y i j mFin u v leOrigin left inject hx
      (by change fits m u v _ _; simp [zero, fits])
  · rcases bits zero with ⟨hu,hv⟩
    change u = u' at hu
    change v = v' at hv
    subst u'
    subst v'
    exact step_shared origin frontier x y i j mFin u v leOrigin left inject hx hy

theorem run_invariant (n : Nat) (origin : Int) (x y : Int → Bool) (i j : Nat → Int → Bool)
    (left : ∀ z ≤ origin, x z = y z)
    (inject : ∀ t < n, ∀ z ≤ origin+1, i t z = j t z) :
    invariant origin (run x i origin n) (run y j origin n) := by
  induction n with
  | zero =>
    refine ⟨rfl, rfl, le_rfl, by change 0 < (4 : Nat); decide, fun z hz => (left z hz).symm, ?_, ?_, ?_⟩
    · simp [run]
    · simp [run, fits]
    · simp [run, fits]
  | succ n ih =>
    have prev := ih (fun t ht => inject t (by omega))
    simpa only [run, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] using
      step_invariant origin (run x i origin n) (run y j origin n) (i n) (j n)
        (inject n (by omega)) prev

end PEqualNP.Outside.L_meta_25574

theorem PEqualNP.Outside.L_meta_25574 : (let mix := fun (x : Int → Bool) (z : Int) => xor (xor (x (z-1)) (x z)) (x (z+1))
let evolve := fun (x injection : Int → Bool) (z : Int) =>
  xor (xor (mix x z) (!(mix x (z+1)) && mix x (z+2))) (injection z)
let run := fun (initial : Int → Bool) (inject : Nat → Int → Bool) (origin : Int) (n : Nat) =>
  (List.range n).foldl (fun (st : (Int → Bool) × Int × Nat × Bool × Bool) tick =>
    let x := st.1
    let b := st.2.1
    let mode := st.2.2.1
    let u := st.2.2.2.1
    let v := st.2.2.2.2
    let near := x b == !(xor u v)
    let far := x (b-1) == v
    let hit := mix x (b-1)
    let aligned := ((mode == 1) && near && far) || ((mode == 2) && far) ||
      ((mode == 3) && near)
    let diagonal := !hit && (((mode == 1) && !near && !far) ||
      (mode == 2) || (mode == 3))
    let nextMode : Nat := if aligned then (if hit then 0 else 2) else if diagonal then 3 else 1
    let f := b-3+(hit.toNat : Int)+((aligned && hit).toNat : Int)
    (evolve x (inject tick), f, nextMode,
      xor (mix x (f+1)) (inject tick (f+1)), inject tick (f+2)))
    (initial, origin, 0, false, false)
∀ (n : Nat) (origin : Int) (x y : Int → Bool) (i j : Nat → Int → Bool),
  (∀ z ≤ origin, x z = y z) →
  (∀ t < n, ∀ z ≤ origin+1, i t z = j t z) →
  let a := run x i origin n
  let b := run y j origin n
  let edge := a.2.1
  let mode := a.2.2.1
  let u := a.2.2.2.1
  let v := a.2.2.2.2
  edge = b.2.1 ∧ mode = b.2.2.1 ∧ (∀ z ≤ edge, a.1 z = b.1 z) ∧
    (mode ≠ 0 → u = b.2.2.2.1 ∧ v = b.2.2.2.2) ∧
    (mode = 1 → ¬ (a.1 (edge+1) = !u ∧ a.1 (edge+2) = !v)) ∧
    (mode = 2 → a.1 (edge+2) = v) ∧
    (mode = 3 → xor (a.1 (edge+1)) (a.1 (edge+2)) = !(xor u v))) := by
  dsimp only
  intro n origin x y i j left inject
  let a := PEqualNP.Outside.L_meta_25574.run x i origin n
  let b := PEqualNP.Outside.L_meta_25574.run y j origin n
  change a.2.1 = b.2.1 ∧ a.2.2.1 = b.2.2.1 ∧ (∀ z ≤ a.2.1, a.1 z = b.1 z) ∧
    (a.2.2.1 ≠ 0 → a.2.2.2.1 = b.2.2.2.1 ∧ a.2.2.2.2 = b.2.2.2.2) ∧
    (a.2.2.1 = 1 → ¬ (a.1 (a.2.1+1) = !a.2.2.2.1 ∧ a.1 (a.2.1+2) = !a.2.2.2.2)) ∧
    (a.2.2.1 = 2 → a.1 (a.2.1+2) = a.2.2.2.2) ∧
    (a.2.2.1 = 3 → xor (a.1 (a.2.1+1)) (a.1 (a.2.1+2)) = !(xor a.2.2.2.1 a.2.2.2.2))
  have h : PEqualNP.Outside.L_meta_25574.invariant origin a b :=
    PEqualNP.Outside.L_meta_25574.run_invariant n origin x y i j left inject
  rcases h with ⟨frontier, mode, _, _, agreement, bits, fit, _⟩
  refine ⟨frontier, mode, fun z hz => (agreement z hz).symm, bits, ?_, ?_, ?_⟩
  all_goals intro hm
  all_goals simpa [PEqualNP.Outside.L_meta_25574.fits, hm] using fit
