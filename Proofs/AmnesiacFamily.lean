module

public import Lean

@[expose] public section

namespace FloodFamily

abbrev Role := Fin 6 -- a,b,c,d,e,x
abbrev Vertex (k : Nat) := Fin k × Role
abbrev Matrix := Role → Role → Bool

def roleEdges : List (Role × Role) :=
  [(0,1),(1,2),(2,3),(3,4),(1,5),(2,5),(3,5)]

def localAdj : Matrix := fun u v =>
  roleEdges.contains (u,v) || roleEdges.contains (v,u)

def linked {k : Nat} (u v : Vertex k) : Prop :=
  (u.2 = 4 ∧ v.2 = 0 ∧ u.1.val+1=v.1.val) ∨
  (u.2 = 0 ∧ v.2 = 4 ∧ v.1.val+1=u.1.val)

def adj {k : Nat} (u v : Vertex k) : Prop :=
  (u.1=v.1 ∧ localAdj u.2 v.2 = true) ∨ linked u v

def seed {k : Nat} (u : Vertex k) : Prop := u.2 = 2

def inside {k : Nat} (M : Matrix) (u v : Vertex k) : Prop :=
  u.1=v.1 ∧ M u.2 v.2 = true

def incoming (M : Matrix) (v : Role) : Bool :=
  (List.finRange 6).any (fun w => M w v)

def localNext (M : Matrix) : Matrix := fun u v =>
  localAdj u v && incoming M u && !M v u

def M1 : Matrix := fun u v => [(2,1),(2,3),(2,5)].contains (u,v)
def M2 : Matrix := fun u v => [(1,0),(1,5),(3,4),(3,5),(5,1),(5,3)].contains (u,v)
def M3 : Matrix := fun u v => [(1,0),(1,2),(3,4),(3,2),(5,2)].contains (u,v)

abbrev Msg (k : Nat) := Vertex k → Vertex k → Prop

def next {k : Nat} (M : Msg k) (u v : Vertex k) : Prop :=
  adj u v ∧ (∃ w, M w u) ∧ ¬ M v u

def rounds {k : Nat} : Nat → Msg k
  | 0 => fun u v => seed u ∧ adj u v
  | r+1 => next (rounds r)

theorem mem_range {n : Nat} (v : Fin n) : v ∈ List.finRange n := by
  have hv : v.val < (List.finRange n).length := by simp
  apply List.mem_of_getElem (h := hv)
  rw [List.getElem_finRange]
  rfl

theorem one_check {p : Role → Bool} (h : (List.finRange 6).all p = true) (u : Role) : p u = true :=
  List.all_eq_true.mp h u (mem_range u)

theorem two_check {p : Role → Role → Bool}
    (h : (List.finRange 6).all (fun u => (List.finRange 6).all (p u)) = true)
    (u v : Role) : p u v = true :=
  one_check (one_check h u) v

theorem local_init (u v : Role) : M1 u v = true ↔ u=2 ∧ localAdj u v = true :=
  of_decide_eq_true (two_check (p := fun a b =>
    decide (M1 a b = true ↔ a=2 ∧ localAdj a b=true)) (by decide) u v)

theorem tbl12 (u v : Role) : localNext M1 u v = M2 u v :=
  of_decide_eq_true (two_check (p := fun a b => decide (localNext M1 a b = M2 a b)) (by decide) u v)

theorem tbl23 (u v : Role) : localNext M2 u v = M3 u v :=
  of_decide_eq_true (two_check (p := fun a b => decide (localNext M2 a b = M3 a b)) (by decide) u v)

theorem tbl34 (u v : Role) : localNext M3 u v = false :=
  of_decide_eq_true (two_check (p := fun a b => decide (localNext M3 a b = false)) (by decide) u v)

theorem bridge_symm {k : Nat} {u v : Vertex k} : linked u v → linked v u := by
  rintro (h|h)
  · exact Or.inr ⟨h.2.1,h.1,h.2.2⟩
  · exact Or.inl ⟨h.2.1,h.1,h.2.2⟩

theorem bridge_diff {k : Nat} {u v : Vertex k} (h : linked u v) : u.1 ≠ v.1 := by
  intro e
  have ev := congrArg Fin.val e
  rcases h with h|h <;> omega

theorem bridge_ends {k : Nat} {u v : Vertex k} (h : linked u v) :
    (u.2 = 0 ∨ u.2 = 4) ∧ (v.2 = 0 ∨ v.2 = 4) := by
  rcases h with h|h
  · exact ⟨Or.inr h.1,Or.inl h.2.1⟩
  · exact ⟨Or.inl h.1,Or.inr h.2.1⟩

theorem incoming_iff {k : Nat} (M : Matrix) (u : Vertex k) :
    incoming M u.2 = true ↔ ∃ w : Vertex k, inside M w u := by
  simp only [incoming,List.any_eq_true]
  constructor
  · rintro ⟨t,_,ht⟩
    exact ⟨(u.1,t),rfl,ht⟩
  · rintro ⟨w,_,hw⟩
    exact ⟨w.2,mem_range _,hw⟩

theorem local_flag {M : Matrix} {u v : Role} :
    localNext M u v = true ↔
      localAdj u v = true ∧ incoming M u = true ∧ M v u ≠ true := by
  simp only [localNext,Bool.and_eq_true,Bool.not_eq_true',Bool.not_eq_true]
  constructor
  · rintro ⟨⟨h,g⟩,j⟩
    exact ⟨h,g,j⟩
  · rintro ⟨h,g,j⟩
    exact ⟨⟨h,g⟩,j⟩

theorem step_inside {k : Nat} (M : Matrix) (u v : Vertex k) :
    next (inside M) u v ↔ inside (localNext M) u v ∨
        (linked u v ∧ incoming M u.2=true) := by
  constructor
  · rintro ⟨ha,hi,hn⟩
    have ii := (incoming_iff M u).mpr hi
    rcases ha with ⟨hs,he⟩|hb
    · exact Or.inl ⟨hs,local_flag.mpr ⟨he,ii,fun h => hn ⟨hs.symm,h⟩⟩⟩
    · exact Or.inr ⟨hb,ii⟩
  · intro h
    rcases h with ⟨hs,hc⟩|⟨hb,hi⟩
    · obtain ⟨ha,ii,hn⟩ := local_flag.mp hc
      exact ⟨Or.inl ⟨hs,ha⟩,(incoming_iff M u).mp ii,fun h => hn h.2⟩
    · exact ⟨Or.inr hb,(incoming_iff M u).mp hi,fun h => bridge_diff hb h.1.symm⟩

theorem round_one {k : Nat} (u v : Vertex k) : rounds 0 u v ↔ inside M1 u v := by
  constructor
  · rintro ⟨hs,⟨he,ha⟩|hb⟩
    · exact ⟨he,(local_init _ _).mpr ⟨hs,ha⟩⟩
    · obtain h|h := (bridge_ends hb).1
      · exact False.elim ((by decide : (2:Role) ≠ 0) (hs.symm.trans h))
      · exact False.elim ((by decide : (2:Role) ≠ 4) (hs.symm.trans h))
  · rintro ⟨he,hm⟩
    obtain ⟨hs,ha⟩ := (local_init _ _).mp hm
    exact ⟨hs,Or.inl ⟨he,ha⟩⟩

theorem next_congr {k : Nat} {M N : Msg k} (h : ∀ u v, M u v ↔ N u v)
    (u v : Vertex k) : next M u v ↔ next N u v := by
  unfold next
  simp only [h]

theorem round_two {k : Nat} (u v : Vertex k) : rounds 1 u v ↔ inside M2 u v := by
  change next (rounds 0) u v ↔ _
  rw [next_congr round_one,step_inside]
  simp only [inside,tbl12]
  constructor
  · intro h
    rcases h with h|⟨hb,hi⟩
    · exact h
    · rcases (bridge_ends hb).1 with h|h <;> rw [h] at hi <;> contradiction
  · exact Or.inl

theorem round_three {k : Nat} (u v : Vertex k) :
    rounds 2 u v ↔ inside M3 u v ∨ linked u v := by
  change next (rounds 1) u v ↔ _
  rw [next_congr round_two,step_inside]
  simp only [inside,tbl23]
  constructor
  · intro h
    rcases h with h|h
    · exact Or.inl h
    · exact Or.inr h.1
  · intro h
    rcases h with h|hb
    · exact Or.inl h
    · refine Or.inr ⟨hb,?_⟩
      rcases (bridge_ends hb).1 with h|h <;> rw [h] <;> decide

theorem round_four_empty {k : Nat} (u v : Vertex k) : ¬ rounds 3 u v := by
  change ¬ next (rounds 2) u v
  rw [next_congr round_three]
  rintro ⟨ha,⟨w,hw⟩,hn⟩
  rcases ha with ⟨hs,ha⟩|hb
  · have iu : incoming M3 u.2 = true := by
      rcases hw with h|hb
      · exact (incoming_iff M3 u).mpr ⟨w,h⟩
      · rcases (bridge_ends hb).2 with h|h <;> rw [h] <;> decide
    have ls : localNext M3 u.2 v.2 = true :=
      local_flag.mpr ⟨ha,iu,fun h => hn (Or.inl ⟨hs.symm,h⟩)⟩
    rw [tbl34] at ls
    contradiction
  · exact hn (Or.inr (bridge_symm hb))

def label {k : Nat} (u : Vertex k) : Nat :=
  5*u.1.val + (if u.2 = 5 then 2 else u.2.val)

theorem local_label (u v : Role) (h : localAdj u v = true) :
    (if u=5 then 2 else u.val) ≤ (if v=5 then 2 else v.val)+1 ∧
    (if v=5 then 2 else v.val) ≤ (if u=5 then 2 else u.val)+1 :=
  (of_decide_eq_true (two_check (p := fun a b => decide (localAdj a b = true →
    (if a=5 then 2 else a.val) ≤ (if b=5 then 2 else b.val)+1 ∧
    (if b=5 then 2 else b.val) ≤ (if a=5 then 2 else a.val)+1)) (by decide) u v)) h

theorem label_step {k : Nat} {u v : Vertex k} (h : adj u v) :
    label u ≤ label v + 1 ∧ label v ≤ label u + 1 := by
  unfold label
  rcases h with ⟨h,ha⟩|h
  · obtain ⟨a,b⟩ := local_label u.2 v.2 ha
    rw [h]
    omega
  · rcases h with ⟨a,b,g⟩|⟨a,b,g⟩ <;> rw [a,b] <;> change
        (5*u.1.val + _ ≤ 5*v.1.val + _ + 1) ∧
        (5*v.1.val + _ ≤ 5*u.1.val + _ + 1) <;> simp <;> omega

inductive Walk {k : Nat} : Vertex k → Vertex k → Nat → Prop
  | nil (u) : Walk u u 0
  | cons {u v w l} : adj u v → Walk v w l → Walk u w (l+1)

def radiusAtMost {k : Nat} (r : Nat) : Prop :=
  ∃ u : Vertex k, ∀ v, ∃ l ≤ r, Walk u v l

theorem walk_label {k : Nat} {u v : Vertex k} {l : Nat} (h : Walk u v l) :
    label u ≤ label v+l ∧ label v ≤ label u+l := by
  induction h with
  | nil => simp
  | @cons u v w l e _ ih =>
    obtain ⟨a,b⟩ := label_step e
    obtain ⟨c,d⟩ := ih
    omega

theorem radius_lower_bound {k s : Nat} (hk : 0 < k) : radiusAtMost (k:=k) s → 5*k/2 ≤ s := by
  rintro ⟨u,h⟩
  let a : Vertex k := (⟨0,by omega⟩,0)
  let b : Vertex k := (⟨k-1,by omega⟩,4)
  obtain ⟨l,hl,wl⟩ := h a
  obtain ⟨r,hr,wr⟩ := h b
  have z : label a = 0 := by rfl
  have r' : label b = 5*(k-1)+4 := by rfl
  have h1 := (walk_label wl).1
  have h2 := (walk_label wr).2
  rw [z] at h1
  rw [r'] at h2
  omega

theorem radius_large {k : Nat} (hk : 4 ≤ k) : ¬radiusAtMost (k:=k) (2*k+1) := by
  intro h
  have e := radius_lower_bound (by omega : 0 < k) h
  omega

theorem quiet_forever {k : Nat} (t : Nat) (u v : Vertex k) : ¬ rounds (3+t) u v := by
  induction t generalizing u v with
  | zero => exact round_four_empty u v
  | succ t ih =>
    rw [Nat.add_succ]
    intro h
    obtain ⟨_,⟨w,e⟩,_⟩ := h
    exact ih w u e

theorem graph_symm {k : Nat} {u v : Vertex k} (h : adj u v) : adj v u := by
  rcases h with ⟨he,he'⟩|hb
  · refine Or.inl ⟨he.symm,?_⟩
    unfold localAdj at *
    rwa [Bool.or_comm]
  · exact Or.inr (bridge_symm hb)

theorem graph_loopless {k : Nat} (u : Vertex k) : ¬ adj u u := by
  rintro (⟨_,h⟩|h)
  · have hz : localAdj u.2 u.2 = false :=
      of_decide_eq_true (one_check (p := fun a => decide (localAdj a a=false)) (by decide) u.2)
    rw [hz] at h
    contradiction
  · exact bridge_diff h rfl

theorem graph_nonbip {k : Nat} (hk : 0 < k) :
    ¬ ∃ color : Vertex k → Bool, ∀ u v, adj u v → color u ≠ color v := by
  rintro ⟨f,h⟩
  let a : Vertex k := (⟨0,hk⟩,1)
  let b : Vertex k := (⟨0,hk⟩,2)
  let c : Vertex k := (⟨0,hk⟩,5)
  have impossible : ∀ a b c : Bool, a ≠ b → b ≠ c → c ≠ a → False := by decide
  exact impossible (f a) (f b) (f c)
    (h a b (Or.inl ⟨rfl,by change localAdj 1 2 = true; decide⟩))
    (h b c (Or.inl ⟨rfl,by change localAdj 2 5 = true; decide⟩))
    (h c a (Or.inl ⟨rfl,by change localAdj 5 1 = true; decide⟩))

theorem walk_append {k : Nat} {u v w : Vertex k} {a b : Nat}
    (h : Walk u v a) (j : Walk v w b) : Walk u w (a+b) := by
  induction h with
  | nil => simpa using j
  | cons e h ih => simpa only [Nat.add_comm 1 b, Nat.add_assoc] using Walk.cons e (ih j)

theorem walk_reverse {k : Nat} {u v : Vertex k} {l : Nat} (h : Walk u v l) : Walk v u l := by
  induction h with
  | nil => exact Walk.nil _
  | @cons u v w l e h ih => exact walk_append ih (Walk.cons (graph_symm e) (Walk.nil u))

def rolePaths : Array (List Role) := #[[],[1],[1,2],[1,2,3],[1,2,3,4],[1,5]]

def follow (r : Role) : List Role → Bool
  | [] => true
  | t::ts => localAdj r t && follow t ts

def arrive (r : Role) : List Role → Role
  | [] => r
  | t::ts => arrive t ts

theorem withinBlock {k : Nat} (i : Fin k) (r : Role) (xs : List Role)
    (h : follow r xs = true) : Walk (i,r) (i,arrive r xs) xs.length := by
  induction xs generalizing r with
  | nil => exact Walk.nil _
  | cons t ts ih =>
    simp only [follow,Bool.and_eq_true] at h
    have e : adj (i,r) (i,t) := Or.inl ⟨rfl,h.1⟩
    exact Walk.cons e (ih t h.2)

theorem from_left {k : Nat} (i : Fin k) (r : Role) : ∃ l, Walk (i,0) (i,r) l := by
  let xs := rolePaths[r.val]!
  have h := of_decide_eq_true (one_check
    (p := fun t => decide (follow 0 rolePaths[t.val]! = true ∧ arrive 0 rolePaths[t.val]! = t))
    (by decide) r)
  have w := withinBlock i 0 xs h.1
  have ht : arrive 0 xs = r := h.2
  rw [ht] at w
  exact ⟨xs.length,w⟩

theorem reach_block {k : Nat} (hk : 0 < k) (i : Nat) (hi : i < k) :
    ∃ l, Walk ((⟨0,hk⟩ : Fin k),0) ((⟨i,hi⟩ : Fin k),0) l := by
  induction i with
  | zero => exact ⟨0,Walk.nil _⟩
  | succ i ih =>
    have hip : i < k := by omega
    obtain ⟨a,wa⟩ := ih hip
    obtain ⟨b,wb⟩ := from_left (⟨i,hip⟩ : Fin k) (4 : Role)
    have e : adj ((⟨i,hip⟩ : Fin k),4) ((⟨i+1,hi⟩ : Fin k),0) :=
      Or.inr (Or.inl ⟨rfl,rfl,rfl⟩)
    exact ⟨(a+b)+1,walk_append (walk_append wa wb) (Walk.cons e (Walk.nil _))⟩

theorem graph_connected {k : Nat} (hk : 0 < k) (u v : Vertex k) :
    ∃ l, Walk u v l := by
  have reach (w : Vertex k) : ∃ l, Walk ((⟨0,hk⟩ : Fin k),0) w l := by
    obtain ⟨a,wa⟩ := reach_block hk w.1.val w.1.isLt
    obtain ⟨b,wb⟩ := from_left w.1 w.2
    exact ⟨a+b,walk_append wa wb⟩
  obtain ⟨a,wa⟩ := reach u
  obtain ⟨b,wb⟩ := reach v
  exact ⟨a+b,walk_append (walk_reverse wa) wb⟩

theorem seeds_exact {k : Nat} :
    ∃ f : Fin k → Vertex k, (∀ i j, f i = f j → i = j) ∧ ∀ v, seed v ↔ ∃ i, f i = v := by
  refine ⟨fun i => (i,2),fun i j h => congrArg Prod.fst h, ?_⟩
  intro v
  constructor
  · intro h
    exact ⟨v.1,Prod.ext rfl h.symm⟩
  · rintro ⟨i,rfl⟩
    rfl

/-- Uniform counterexample: a finite simple connected non-bipartite graph,
exactly k seeds, no fourth-round messages, and radius greater than 2k+1. -/
theorem family_counterexample (k : Nat) (hk : 4 ≤ k) :
    (∀ u v : Vertex k, adj u v → adj v u) ∧
    (∀ u : Vertex k, ¬ adj u u) ∧
    (∀ u v : Vertex k, ∃ l, Walk u v l) ∧
    (¬ ∃ color : Vertex k → Bool, ∀ u v, adj u v → color u ≠ color v) ∧
    (∃ f : Fin k → Vertex k, (∀ i j, f i = f j → i = j) ∧ ∀ v, seed v ↔ ∃ i, f i = v) ∧
    (∀ u v : Vertex k, ¬ rounds 3 u v) ∧
    ¬radiusAtMost (k:=k) (2*k+1) :=
  ⟨fun _ _ => graph_symm, graph_loopless, graph_connected (by omega), graph_nonbip (by omega),
   seeds_exact, round_four_empty, radius_large hk⟩

def pathVertex {k : Nat} (j : Fin (5*k)) : Vertex k :=
  (⟨j.val/5,by have h:=j.isLt; omega⟩, ⟨j.val%5,by omega⟩)

theorem local_consecutive (u v : Role) (h : u.val < 4 ∧ v.val=u.val+1) :
    localAdj u v = true :=
  (of_decide_eq_true (two_check (p := fun a b => decide
    (a.val < 4 ∧ b.val=a.val+1 → localAdj a b=true)) (by decide) u v)) h

theorem path_step {k j : Nat} (h : j+1 < 5*k) :
    adj (pathVertex ⟨j,by omega⟩) (pathVertex (⟨j+1,h⟩ : Fin (5*k))) := by
  by_cases e : j%5 = 4
  · apply Or.inr
    apply Or.inl
    refine ⟨?_,?_,?_⟩
    · apply Fin.ext; change j%5=4; exact e
    · apply Fin.ext; change (j+1)%5=0; omega
    · change j/5+1=(j+1)/5; omega
  · apply Or.inl
    refine ⟨?_,?_⟩
    · apply Fin.ext; change j/5=(j+1)/5; omega
    · apply local_consecutive
      change j%5 < 4 ∧ (j+1)%5 = j%5+1
      omega

theorem block_position {k : Nat} (i : Fin k) (r : Role) (hr : r.val<5) :
    pathVertex (⟨5*i.val+r.val,by have h := i.isLt; omega⟩ : Fin (5*k)) = (i,r) := by
  apply Prod.ext
  · apply Fin.ext; change (5*i.val+r.val)/5=i.val; omega
  · apply Fin.ext; change (5*i.val+r.val)%5=r.val; omega

theorem along_path {k : Nat} (i d : Nat) (h : i+d < 5*k) :
    Walk (pathVertex (⟨i,by omega⟩ : Fin (5*k))) (pathVertex ⟨i+d,h⟩) d := by
  induction d with
  | zero => exact Walk.nil _
  | succ d ih =>
    have h0 : i+d < 5*k := by omega
    have h1 : i+d+1 < 5*k := by omega
    have w := ih h0
    have e := Walk.cons (path_step h1) (Walk.nil _)
    exact walk_append w e

theorem path_between {k : Nat} (a b : Fin (5*k)) :
    Walk (pathVertex a) (pathVertex b) (a.val-b.val+(b.val-a.val)) := by
  rcases a with ⟨a,ha⟩
  rcases b with ⟨b,hb⟩
  by_cases h : a ≤ b
  · have es : a+(b-a)=b := by omega
    have x := along_path (k:=k) a (b-a) (by omega)
    have ev : (⟨a+(b-a),by omega⟩ : Fin (5*k))=⟨b,hb⟩ := Fin.ext es
    rw [ev] at x
    simpa only [Nat.sub_eq_zero_of_le h,Nat.zero_add] using x
  · have es : b+(a-b)=a := by omega
    have x := along_path (k:=k) b (a-b) (by omega)
    have ev : (⟨b+(a-b),by omega⟩ : Fin (5*k))=⟨a,ha⟩ := Fin.ext es
    rw [ev] at x
    have hba : b≤a := by omega
    simpa only [Nat.sub_eq_zero_of_le hba,Nat.add_zero] using walk_reverse x

theorem radius_upper {k : Nat} (hk : 0 < k) : radiusAtMost (k:=k) (5*k/2) := by
  let m : Fin (5*k) := ⟨5*k/2,by omega⟩
  refine ⟨pathVertex m,?_⟩
  rintro ⟨i,r⟩
  have hi := i.isLt
  have hrr := r.isLt
  have mval : m.val = 5*k/2 := rfl
  by_cases e : r=5
  · subst r
    let j : Fin (5*k) := ⟨5*i.val+2,by omega⟩
    have jval : j.val = 5*i.val+2 := rfl
    have pv : pathVertex j=(i,2) := block_position i 2 (by decide)
    have w := path_between m j
    rw [pv] at w
    have adj0 : adj (i,2) (i,5) :=
      Or.inl ⟨rfl,by change localAdj 2 5=true; decide⟩
    have w' := walk_append w (Walk.cons adj0 (Walk.nil _))
    refine ⟨m.val-j.val+(j.val-m.val)+1,?_,w'⟩
    rw [mval,jval]
    omega
  · have er : r.val≠5 := by
      intro h
      exact e (Fin.ext h)
    have hr : r.val<5 := by omega
    let j : Fin (5*k) := ⟨5*i.val+r.val,by omega⟩
    have jval : j.val = 5*i.val+r.val := rfl
    have pv : pathVertex j=(i,r) := block_position i r hr
    have w := path_between m j
    rw [pv] at w
    refine ⟨m.val-j.val+(j.val-m.val),?_,w⟩
    rw [mval,jval]
    omega

theorem radius_exact {k : Nat} (hk : 0 < k) :
    radiusAtMost (k:=k) (5*k/2) ∧ ∀ s, radiusAtMost (k:=k) s → 5*k/2 ≤ s :=
  ⟨radius_upper hk,fun _ => radius_lower_bound hk⟩

/-- The same paper protocol, initialized by any proposed seed set. -/
def roundsFrom {k : Nat} (S : Vertex k → Prop) : Nat → Msg k
  | 0 => fun u v => S u ∧ adj u v
  | t+1 => next (roundsFrom S t)

theorem same_run {k : Nat} (t : Nat) (u v : Vertex k) :
    roundsFrom seed t u v ↔ rounds t u v := by
  induction t generalizing u v with
  | zero => exact Iff.rfl
  | succ t ih => exact next_congr ih u v

def hasKSeeds {k : Nat} (S : Vertex k → Prop) : Prop :=
  ∃ f : Fin k → Vertex k, (∀ i j, f i = f j → i = j) ∧ ∀ v, S v ↔ ∃ i, f i = v

def quietAfter {k : Nat} (S : Vertex k → Prop) (t : Nat) : Prop :=
  ∀ u v : Vertex k, ¬ roundsFrom S t u v

/-- Definition 1 of the paper: the smallest number of physical rounds
after which the process is silent, among seed sets of cardinality k. -/
def isFloodNumber {k : Nat} (t : Nat) : Prop :=
  (∃ S : Vertex k → Prop, hasKSeeds S ∧ quietAfter S t) ∧
  ∀ (S : Vertex k → Prop) r, hasKSeeds S → quietAfter S r → t ≤ r

def isRadius {k : Nat} (r : Nat) : Prop :=
  radiusAtMost (k:=k) r ∧ ∀ s, radiusAtMost (k:=k) s → r ≤ s

theorem least_nat (P : Nat → Prop) (r : Nat) (h : P r) :
    ∃ t, P t ∧ ∀ s, P s → t ≤ s := by
  classical
  induction r using Nat.strongRecOn with
  | ind r ih =>
    by_cases hex : ∃ t < r, P t
    · obtain ⟨t,ht,hP⟩ := hex
      exact ih t ht hP
    · refine ⟨r,h,?_⟩
      intro s hs
      by_cases hh : r ≤ s
      · exact hh
      · exact False.elim (hex ⟨s,by omega,hs⟩)

/-- For every k≥4, the family refutes Turau's original inequality, with
its literal minimum seed termination time and exact ordinary radius. -/
theorem refutes_turau_for_each (k : Nat) (hk : 4 ≤ k) :
    ∃ t, isFloodNumber (k:=k) t ∧ isRadius (k:=k) (5*k/2) ∧
      t ≤ 3 ∧ k*t < (5*k/2)+k-1 ∧
      (5*k/2)+k-1-k*t ≥ k/2-1 := by
  let P := fun t => ∃ S : Vertex k → Prop, hasKSeeds S ∧ quietAfter S t
  have h3 : P 3 :=
    ⟨seed,seeds_exact,fun u v h => round_four_empty u v ((same_run 3 u v).mp h)⟩
  obtain ⟨t,ht,hleast⟩ := least_nat P 3 h3
  have hle := hleast 3 h3
  have hmul := Nat.mul_le_mul_left k hle
  refine ⟨t, ⟨ht,fun S r hS hr => hleast r ⟨S,hS,hr⟩⟩,
    radius_exact (by omega),hle,by omega,by omega⟩

end FloodFamily

#print axioms FloodFamily.round_four_empty
#print axioms FloodFamily.radius_large

#print axioms FloodFamily.family_counterexample

#print axioms FloodFamily.radius_lower_bound
#print axioms FloodFamily.quiet_forever

#print axioms FloodFamily.radius_exact

#print axioms FloodFamily.refutes_turau_for_each
