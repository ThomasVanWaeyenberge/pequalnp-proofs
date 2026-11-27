import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_25606

def mix (x : Int → Bool) (z : Int) : Bool :=
  xor (xor (x (z-1)) (x z)) (x (z+1))

def step (x inj : Int → Bool) (z : Int) : Bool :=
  xor (xor (mix x z) (!(mix x (z+1)) && mix x (z+2))) (inj z)

structure Config where
  base : Int → Bool
  inj : Nat → Int → Bool
  edge : Nat → Int
  width : Nat → Nat
  mask : Nat → Nat

def run (c : Config) (x : Int → Bool) (n : Nat) : Int → Bool :=
  (List.range n).foldl (fun state tick => step state (c.inj tick)) x

def cap (c : Config) (time : Nat) : Int := c.edge time + (c.width time : Int)

def word (c : Config) (layer pattern extraBits : Nat) (z : Int) : Bool :=
  if z ≤ c.edge layer then run c c.base layer z
  else if z ≤ cap c layer then pattern.testBit (z-c.edge layer-1).toNat
  else extraBits.testBit (z-cap c layer-1).toNat

def admitted (c : Config) (layer label : Nat) : Bool :=
  decide (label < 2^(c.width layer)) && (c.mask layer).testBit label

def link (c : Config) (oldTime source dest : Nat) : Bool :=
  let low := min (c.edge oldTime-3) (c.edge (oldTime+1))
  let extra := (cap c (oldTime+1)+3-cap c oldTime).toNat
  (List.range (2^extra)).any (fun completion =>
    (List.range (cap c (oldTime+1)-low).toNat).all (fun offset =>
      let site := low+1+(offset : Int)
      step (word c oldTime source completion) (c.inj oldTime) site == word c (oldTime+1) dest 0 site))

def carry (c : Config) (time label : Nat) (certified : Int) : Int :=
  if time = 0 then cap c 1 else
    min (cap c (time+1)) (certified-3 + ((mix (word c time label 0) (certified-1)).toNat : Int))

def limitAt (c : Config) (a : Nat → Nat) (n : Nat) : Int :=
  (List.range n).foldl (fun previous index => carry c index (a index) previous) (cap c 0)

def legal (c : Config) (n : Nat) (a : Nat → Nat) : Prop :=
  (∀ t ≤ n, admitted c t (a t) = true) ∧ ∀ t < n, link c t (a t) (a (t+1)) = true

theorem run_succ (c : Config) (x : Int → Bool) (n : Nat) :
    run c x (n+1) = step (run c x n) (c.inj n) := by
  simp [run,List.range_succ,List.foldl_append]

theorem limit_succ (c : Config) (a : Nat → Nat) (n : Nat) :
    limitAt c a (n+1) = carry c n (a n) (limitAt c a n) := by
  simp [limitAt,List.range_succ,List.foldl_append]

theorem cap_bound (c : Config) (a : Nat → Nat) (n : Nat) :
    limitAt c a n ≤ cap c n := by
  cases n with
  | zero => exact le_rfl
  | succ n =>
    rw [limit_succ]
    unfold carry
    split_ifs with h
    · subst n
      exact le_rfl
    · exact min_le_left _ _

theorem mix_same {x y : Int → Bool} {s : Int}
    (h : ∀ j, s-1 ≤ j → j ≤ s+1 → x j = y j) : mix x s = mix y s := by
  simp only [mix,h (s-1) le_rfl (by omega),h s (by omega) (by omega),h (s+1) (by omega) le_rfl]

theorem step_same {x y : Int → Bool} (inj : Int → Bool) (z : Int)
    (h : ∀ j, z-1 ≤ j → j ≤ z+3 → x j = y j) :
    step x inj z = step y inj z := by
  unfold step
  rw [mix_same (fun j lo hi => h j (by omega) (by omega)),
      mix_same (fun j lo hi => h j (by omega) (by omega)),
      mix_same (fun j lo hi => h j (by omega) (by omega))]

theorem step_bounded {x y : Int → Bool} (inj : Int → Bool) (b : Int)
    (agree : ∀ j ≤ b, x j = y j) (z : Int)
    (hz : z ≤ b-3 + ((mix y (b-1)).toNat : Int)) :
    step x inj z = step y inj z := by
  by_cases low : z ≤ b-3
  · exact step_same inj z (fun j _ hi => agree j (by omega))
  · have yes : mix y (b-1) = true := by
      cases h : mix y (b-1)
      · simp [h] at hz
        exact False.elim (low hz)
      · rfl
    rw [yes] at hz
    have index : z+1 = b-1 := by simp at hz; omega
    have mx : mix x z = mix y z := mix_same (fun j _ hi => agree j (by simp at hz; omega))
    have next : mix x (z+1) = true := by
      rw [index,mix_same (fun j _ hi => agree j (by omega)),yes]
    unfold step
    rw [mx,next,index,yes]
    rfl

theorem extra_prefix (c : Config) (t pattern a b : Nat) (z : Int) (hz : z ≤ cap c t) :
    word c t pattern a z = word c t pattern b z := by
  simp [word,hz]

theorem link_sound (c : Config) (t source dest : Nat) (h : link c t source dest = true) :
    ∃ extra, ∀ z ≤ cap c (t+1),
      step (word c t source extra) (c.inj t) z = word c (t+1) dest 0 z := by
  let low := min (c.edge t-3) (c.edge (t+1))
  let N := (cap c (t+1)+3-cap c t).toNat
  change (List.range (2^N)).any (fun completion =>
    (List.range (cap c (t+1)-low).toNat).all (fun offset =>
      step (word c t source completion) (c.inj t) (low+1+(offset : Int)) ==
        word c (t+1) dest 0 (low+1+(offset : Int)))) = true at h
  obtain ⟨completion,_,check⟩ := List.any_eq_true.mp h
  refine ⟨completion,fun z hz => ?_⟩
  by_cases left : z ≤ low
  · have old : z ≤ c.edge t - 3 := left.trans (min_le_left _ _)
    have new : z ≤ c.edge (t+1) := left.trans (min_le_right _ _)
    calc
      _ = step (run c c.base t) (c.inj t) z :=
        step_same _ _ (fun j _ hi => by simp [word,show j ≤ c.edge t by omega])
      _ = _ := by simp [word,new,run_succ]
  · let q := (z-low-1).toNat
    have qlt : q < (cap c (t+1)-low).toNat := by dsimp [q]; omega
    have idx : low+1+(q : Int) = z := by dsimp [q]; omega
    have checkBit := List.all_eq_true.mp check q (List.mem_range.mpr qlt)
    simpa only [beq_iff_eq,idx] using checkBit

theorem history (c : Config) (n : Nat) (labels : Nat → Nat) (legalPath : legal c n labels) :
    ∃ initial : Int → Bool, ∀ t ≤ n, ∀ z ≤ limitAt c labels t,
      run c initial t z = word c t (labels t) 0 z := by
  cases n with
  | zero =>
    refine ⟨word c 0 (labels 0) 0,fun t ht => ?_⟩
    have eq : t = 0 := by omega
    subst t
    exact fun _ _ => rfl
  | succ n =>
    obtain ⟨extra,checked⟩ := link_sound c 0 (labels 0) (labels 1) (legalPath.2 0 (by omega))
    let initial := word c 0 (labels 0) extra
    refine ⟨initial,fun t => ?_⟩
    induction t with
    | zero =>
      intro _ z hz
      exact extra_prefix c 0 (labels 0) extra 0 z hz
    | succ t ih =>
      intro ht z hz
      rw [run_succ]
      rw [limit_succ] at hz
      by_cases isZero : t = 0
      · subst t
        exact checked z hz
      · obtain ⟨completion,out⟩ :=
          link_sound c t (labels t) (labels (t+1)) (legalPath.2 t (by omega))
        let old := word c t (labels t) completion
        let b := limitAt c labels t
        have b_le : b ≤ cap c t := cap_bound c labels t
        have same (j : Int) (hj : j ≤ b) : run c initial t j = old j :=
          (ih (by omega) j hj).trans (extra_prefix c t (labels t) 0 completion j (hj.trans b_le))
        have mixEq : mix old (b-1) = mix (word c t (labels t) 0) (b-1) :=
          mix_same (fun j _ hi => extra_prefix c t (labels t) completion 0 j (by omega))
        have bound := hz
        change z ≤ carry c t (labels t) b at bound
        simp only [carry, ite_eq_right isZero] at bound
        calc
          _ = step old (c.inj t) z :=
            step_bounded _ b same z (by rw [mixEq]; exact le_trans bound (min_le_right _ _))
          _ = _ := out z (le_trans bound (min_le_left _ _))

def candidates (c : Config) (prev : Nat → Option Int) (stage child : Nat) : List Int :=
  (List.range (2^(c.width stage))).filterMap (fun parent =>
    if link c stage parent child then (prev parent).map (carry c stage parent) else none)

def scoreStep (c : Config) (prev : Nat → Option Int) (stage child : Nat) : Option Int :=
  if admitted c (stage+1) child then (candidates c prev stage child).max? else none

def scores (c : Config) (n : Nat) : Nat → Option Int :=
  (List.range n).foldl (scoreStep c) (fun parent => if admitted c 0 parent then some (cap c 0) else none)

theorem scores_succ (c : Config) (n : Nat) :
    scores c (n+1) = scoreStep c (scores c n) n := by
  simp [scores,List.range_succ,List.foldl_append]

theorem carry_mono (c : Config) (n p : Nat) : Monotone (carry c n p) := by
  intro x y h
  by_cases equal : x = y
  · rw [equal]
  · have strict : x < y := lt_of_le_of_ne h equal
    unfold carry
    split_ifs
    · exact le_rfl
    · apply min_le_min_left
      cases hx : mix (word c n p 0) (x-1) <;>
        cases hy : mix (word c n p 0) (y-1) <;> simp <;> omega

theorem limit_eq {c : Config} {a b : Nat → Nat} {n : Nat} (h : ∀ t < n, a t = b t) :
    limitAt c a n = limitAt c b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [limit_succ,limit_succ,h n (by omega),ih (fun t ht => h t (by omega))]

theorem extend_path {c : Config} {a : Nat → Nat} {n q : Nat} (path : legal c n a)
    (accept : admitted c (n+1) q = true) (connect : link c n (a n) q = true) :
    ∃ b : Nat → Nat, legal c (n+1) b ∧ b (n+1) = q ∧
      limitAt c b (n+1) = carry c n (a n) (limitAt c a n) := by
  let b := fun i => if i = n+1 then q else a i
  have final : b (n+1) = q := by simp [b]
  have early (i : Nat) (hi : i ≤ n) : b i = a i := by simp [b,show i ≠ n+1 by omega]
  refine ⟨b,⟨?_,?_⟩,final,?_⟩
  · intro t ht
    by_cases eq : t = n+1
    · subst t
      rwa [final]
    · rw [early t (by omega)]
      exact path.1 t (by omega)
  · intro t ht
    by_cases last : t = n
    · subst t
      rwa [early n le_rfl,final]
    · rw [early t (by omega),early (t+1) (by omega)]
      exact path.2 t (by omega)
  · rw [limit_succ,early n le_rfl,limit_eq (fun i hi => early i (by omega))]

def atEnd (c : Config) (n q : Nat) (a : Nat → Nat) : Prop :=
  legal c n a ∧ a n = q

def hasMax (c : Config) (n q : Nat) (best : Int) : Prop :=
  (∃ a, atEnd c n q a ∧ limitAt c a n = best) ∧ ∀ a, atEnd c n q a → limitAt c a n ≤ best

def tracks (c : Config) (n q : Nat) (value : Option Int) : Prop :=
  match value with
  | none => ∀ a, ¬ atEnd c n q a
  | some best => hasMax c n q best

theorem tracks_scores (c : Config) (n q : Nat) : tracks c n q (scores c n q) := by
  induction n generalizing q with
  | zero =>
    change tracks c 0 q (if admitted c 0 q then some (cap c 0) else none)
    cases bit : admitted c 0 q
    · rintro a ⟨p,last⟩
      have h := p.1 0 le_rfl
      rw [last,bit] at h
      contradiction
    · refine ⟨⟨fun _ => q,⟨⟨?_, by omega⟩,rfl⟩,rfl⟩,fun _ _ => le_rfl⟩
      intro t ht
      have eq : t = 0 := by omega
      subst t
      exact bit
  | succ n ih =>
    rw [scores_succ]
    cases final : admitted c (n+1) q
    · have noneScore : scoreStep c (scores c n) n q = none := by simp [scoreStep,final]
      rw [noneScore]
      rintro a ⟨p,last⟩
      have h := p.1 (n+1) le_rfl
      rw [last,final] at h
      contradiction
    · let cs := candidates c (scores c n) n q
      have equal : scoreStep c (scores c n) n q = cs.max? := by simp [cs,scoreStep,final]
      rw [equal]
      have realize (k : Int) (mem : k ∈ cs) :
          ∃ a, atEnd c (n+1) q a ∧ limitAt c a (n+1) = k := by
        obtain ⟨p,_,eq⟩ := List.mem_filterMap.mp mem
        change (if link c n p q then (scores c n p).map (carry c n p) else none) = some k at eq
        cases edge : link c n p q
        · simp [edge] at eq
        · cases old : scores c n p with
          | none => simp [edge,old] at eq
          | some v =>
            have valEq : carry c n p v = k := by simpa [edge,old] using eq
            have oldTracks := ih p
            rw [old] at oldTracks
            obtain ⟨path,⟨valid,dest⟩,score⟩ := (show hasMax c n p v from oldTracks).1
            obtain ⟨a,legalA,lastA,endA⟩ := extend_path valid final (by rwa [dest])
            exact ⟨a,⟨legalA,lastA⟩,by rwa [endA,dest,score]⟩
      have majorant (path : Nat → Nat) (ht : atEnd c (n+1) q path) :
          ∃ v ∈ cs, limitAt c path (n+1) ≤ v := by
        let p := path n
        have allowed : p < 2^(c.width n) := by
          have adm := ht.1.1 n (by omega)
          unfold admitted at adm
          exact decide_eq_true_eq.mp (Bool.and_eq_true_iff.mp adm).1
        have live : link c n p q = true := by
          rw [← ht.2]
          exact ht.1.2 n (by omega)
        have partialPath : atEnd c n p path :=
          ⟨⟨fun t ht' => ht.1.1 t (by omega),fun t ht' => ht.1.2 t (by omega)⟩,rfl⟩
        have track := ih p
        cases old : scores c n p with
        | none => rw [old] at track; exact (track path partialPath).elim
        | some v =>
          rw [old] at track
          refine ⟨carry c n p v,List.mem_filterMap.mpr ⟨p,List.mem_range.mpr allowed,?_⟩,?_⟩
          · simp [live,old]
          · rw [limit_succ]
            exact carry_mono c n p ((show hasMax c n p v from track).2 path partialPath)
      cases eqMax : cs.max? with
      | none =>
        intro path valid
        obtain ⟨k,hk,_⟩ := majorant path valid
        simp [List.max?_eq_none_iff.mp eqMax] at hk
      | some best =>
        obtain ⟨mem,top⟩ := List.max?_eq_some_iff.mp eqMax
        refine ⟨realize _ mem,fun path hp => ?_⟩
        obtain ⟨v,hv,vmax⟩ := majorant path hp
        exact vmax.trans (top _ hv)

theorem maximal (c : Config) (n q : Nat) (best : Int) :
    scores c n q = some best ↔ hasMax c n q best := by
  have ready := tracks_scores c n q
  constructor
  · intro h
    rw [h] at ready
    exact ready
  · intro bestPath
    cases eq : scores c n q with
    | none =>
      rw [eq] at ready
      obtain ⟨path,hp,_⟩ := bestPath.1
      exact (ready _ hp).elim
    | some value =>
      rw [eq] at ready
      have maxValue : hasMax c n q value := ready
      obtain ⟨a,ha,eqA⟩ := bestPath.1
      obtain ⟨b,hb,eqB⟩ := maxValue.1
      have le₁ := maxValue.2 a ha
      have le₂ := bestPath.2 b hb
      rw [eqA] at le₁
      rw [eqB] at le₂
      exact congrArg some (le_antisymm le₂ le₁)

end PEqualNP.Outside.L_meta_25606

theorem PEqualNP.Outside.L_meta_25606 : (let mix := fun (x : ℤ → Bool) (z : ℤ) => xor (xor (x (z-1)) (x z)) (x (z+1))
let step := fun (x inj : ℤ → Bool) (z : ℤ) =>
  xor (xor (mix x z) (!(mix x (z+1)) && mix x (z+2))) (inj z)
∀ (n : ℕ) (base : ℤ → Bool) (inj : ℕ → ℤ → Bool) (edge : ℕ → ℤ)
    (width mask : ℕ → ℕ),
  let run := fun (x : ℤ → Bool) (rounds : ℕ) =>
    (List.range rounds).foldl (fun state tick => step state (inj tick)) x
  let cap := fun time => edge time + (width time : ℤ)
  let word := fun (layer pattern extraBits : ℕ) (z : ℤ) =>
    if z ≤ edge layer then run base layer z
    else if z ≤ cap layer then pattern.testBit (z-edge layer-1).toNat
    else extraBits.testBit (z-cap layer-1).toNat
  let admitted := fun (layerIndex label : ℕ) => decide (label < 2^(width layerIndex)) && (mask layerIndex).testBit label
  let link := fun (oldTime source dest : ℕ) =>
    let low := min (edge oldTime-3) (edge (oldTime+1))
    let extra := (cap (oldTime+1)+3-cap oldTime).toNat
    (List.range (2^extra)).any (fun completion =>
      (List.range (cap (oldTime+1)-low).toNat).all (fun offset =>
        let site := low+1+(offset : ℤ)
        step (word oldTime source completion) (inj oldTime) site == word (oldTime+1) dest 0 site))
  let carry := fun (fromTime fromPattern : ℕ) (certified : ℤ) =>
    if fromTime = 0 then cap 1 else
      min (cap (fromTime+1)) (certified-3 + ((mix (word fromTime fromPattern 0) (certified-1)).toNat : ℤ))
  let scores := (List.range n).foldl (fun (prev : ℕ → Option ℤ) stage child =>
    if admitted (stage+1) child then
      ((List.range (2^(width stage))).filterMap (fun parent =>
        if link stage parent child then (prev parent).map (carry stage parent) else none)).max?
    else none) (fun parent => if admitted 0 parent then some (cap 0) else none)
  let legal := fun (a : ℕ → ℕ) => (∀ t ≤ n, admitted t (a t) = true) ∧
    ∀ t < n, link t (a t) (a (t+1)) = true
  let limitAt := fun (a : ℕ → ℕ) (length : ℕ) =>
    (List.range length).foldl (fun previous index => carry index (a index) previous) (cap 0)
  (∀ a : ℕ → ℕ, legal a → ∃ initial : ℤ → Bool, ∀ t ≤ n, ∀ z ≤ limitAt a t,
    run initial t z = word t (a t) 0 z) ∧
  ∀ (q : ℕ) (best : ℤ), scores q = some best ↔
    (∃ a : ℕ → ℕ, legal a ∧ a n = q ∧ limitAt a n = best) ∧
    ∀ b : ℕ → ℕ, legal b → b n = q → limitAt b n ≤ best) := by
  dsimp only
  intro n base inj edge width mask
  let config : PEqualNP.Outside.L_meta_25606.Config := ⟨base,inj,edge,width,mask⟩
  refine ⟨fun labels h => PEqualNP.Outside.L_meta_25606.history config n labels h,fun q best => ?_⟩
  change PEqualNP.Outside.L_meta_25606.scores config n q = some best ↔
    (∃ a, PEqualNP.Outside.L_meta_25606.legal config n a ∧ a n = q ∧
      PEqualNP.Outside.L_meta_25606.limitAt config a n = best) ∧
    ∀ a, PEqualNP.Outside.L_meta_25606.legal config n a → a n = q →
      PEqualNP.Outside.L_meta_25606.limitAt config a n ≤ best
  rw [PEqualNP.Outside.L_meta_25606.maximal]
  constructor
  · rintro ⟨⟨a,⟨h,last⟩,value⟩,top⟩
    exact ⟨⟨a,h,last,value⟩,fun a h last => top a ⟨h,last⟩⟩
  · rintro ⟨⟨a,h,last,value⟩,top⟩
    exact ⟨⟨a,⟨h,last⟩,value⟩,fun a h => top a h.1 h.2⟩
