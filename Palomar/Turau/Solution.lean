module

public import Lean

@[expose] public section

namespace AmnesiacStretched

inductive Role (L : Nat)
  | center
  | ear
  | arm (right : Bool) (depth : Fin L)
  deriving DecidableEq

abbrev Vertex (k L : Nat) := Fin k × Role L
abbrev Msg (k L : Nat) := Vertex k L → Vertex k L → Prop

def localAdj {L : Nat} : Role L → Role L → Prop
  | .center, .ear | .ear, .center => True
  | .center, .arm _ j | .arm _ j, .center => j.val = 0
  | .ear, .arm _ j | .arm _ j, .ear => j.val = 0
  | .arm s i, .arm t j => s=t ∧ (i.val+1=j.val ∨ j.val+1=i.val)
  | _, _ => False

def bridge {k L : Nat} (u v : Vertex k L) : Prop :=
  match u.2,v.2 with
  | .arm s i,.arm t j => i.val+1=L ∧ j.val+1=L ∧
      ((s=true ∧ t=false ∧ u.1.val+1=v.1.val) ∨
       (s=false ∧ t=true ∧ v.1.val+1=u.1.val))
  | _, _ => False

def adj {k L : Nat} (u v : Vertex k L) : Prop :=
  (u.1=v.1 ∧ localAdj u.2 v.2) ∨ bridge u v

def seed {k L : Nat} (u : Vertex k L) : Prop := u.2=.center

def next {k L : Nat} (M : Msg k L) (u v : Vertex k L) : Prop :=
  adj u v ∧ (∃ w, M w u) ∧ ¬ M v u

/-- The index is one less than the physical send round, as in the registered proof. -/
def rounds {k L : Nat} : Nat → Msg k L
  | 0 => fun u v => seed u ∧ adj u v
  | r+1 => next (rounds r)

def localTrace {L : Nat} (r : Nat) : Role L → Role L → Prop
  | .center, .ear => r=0
  | .center, .arm _ j => j.val=0 ∧ r=0
  | .ear, .center => r=2
  | .ear, .arm _ j => j.val=0 ∧ r=1
  | .arm _ j, .center => j.val=0 ∧ r=2
  | .arm _ j, .ear => j.val=0 ∧ r=1
  | .arm s i, .arm t j => s=t ∧ i.val+1=j.val ∧ (r=i.val+1 ∨ r=i.val+2)
  | _,_ => False

def trace {k L : Nat} (r : Nat) (u v : Vertex k L) : Prop :=
  (u.1=v.1 ∧ localTrace r u.2 v.2) ∨ (bridge u v ∧ r=L)

def arrived {L : Nat} (r : Nat) : Role L → Prop
  | .center => r=2
  | .ear => r=0 ∨ r=1
  | .arm _ j => r=j.val ∨ r=j.val+1

theorem local_symm {L : Nat} (u v : Role L) : localAdj u v ↔ localAdj v u := by
  cases u <;> cases v <;> simp [localAdj,eq_comm,or_comm]

theorem bridge_symm {k L : Nat} (u v : Vertex k L) : bridge u v ↔ bridge v u := by
  rcases u with ⟨i,a⟩
  rcases v with ⟨j,b⟩
  cases a <;> cases b <;> simp [bridge] <;> grind

theorem bridge_diff {k L : Nat} {u v : Vertex k L} (h : bridge u v) : u.1≠v.1 := by
  rcases u with ⟨i,a⟩
  rcases v with ⟨j,b⟩
  cases a <;> cases b <;> simp [bridge] at h ⊢
  intro eq
  have he := congrArg Fin.val eq
  obtain ⟨_,_,h|h⟩ := h <;> omega

theorem bridge_arrived {k L : Nat} {u v : Vertex k L} {r : Nat}
    (h : bridge u v) : arrived r u.2 ↔ r+1=L ∨ r=L := by
  rcases u with ⟨i,a⟩
  rcases v with ⟨j,b⟩
  cases a <;> cases b <;> simp [bridge] at h
  simp [arrived]
  omega

theorem local_arrived_forward {L r : Nat} {u v : Role L} (h : localTrace r u v) :
    arrived r v := by
  cases u <;> cases v <;> simp [localTrace,arrived] at h ⊢ <;> omega

theorem local_arrived_exists {L r : Nat} (hL : 0<L) (v : Role L) (h : arrived r v) :
    ∃ u, localTrace r u v := by
  cases v with
  | center => exact ⟨.ear,h⟩
  | ear =>
    rcases h with h|h
    · exact ⟨.center,h⟩
    · exact ⟨.arm false ⟨0,hL⟩,rfl,h⟩
  | arm b j =>
    by_cases hj : j.val=0
    · rcases h with h|h
      · exact ⟨.center,hj,by omega⟩
      · exact ⟨.ear,hj,by omega⟩
    · let j' : Fin L := ⟨j.val-1,by omega⟩
      refine ⟨.arm b j',rfl,?_,?_⟩
      · change j.val-1+1=j.val
        omega
      · change r=j.val-1+1 ∨ r=j.val-1+2
        change r=j.val ∨ r=j.val+1 at h
        omega

theorem local_zero {L : Nat} (u v : Role L) :
    localTrace 0 u v ↔ u=.center ∧ localAdj u v := by
  cases u <;> cases v <;> simp [localTrace,localAdj]

theorem local_step {L r : Nat} (u v : Role L) :
    localAdj u v ∧ arrived r u ∧ ¬ localTrace r v u ↔ localTrace (r+1) u v := by
  cases u <;> cases v <;> simp [localAdj,arrived,localTrace] <;> try omega
  case arm.arm b i c j =>
    cases b <;> cases c <;> simp_all <;> omega

theorem trace_arrived {k L r : Nat} (hL : 0<L) (u : Vertex k L) :
    (∃ w, trace r w u) ↔ arrived r u.2 := by
  constructor
  · rintro ⟨w,h|h⟩
    · exact local_arrived_forward h.2
    · have hg := bridge_arrived (r:=r) ((bridge_symm w u).mp h.1)
      exact hg.mpr (Or.inr h.2)
  · intro h
    obtain ⟨w,hw⟩ := local_arrived_exists hL u.2 h
    exact ⟨(u.1,w),Or.inl ⟨rfl,hw⟩⟩

theorem zero_trace {k L : Nat} (hL : 0<L) (u v : Vertex k L) :
    rounds 0 u v ↔ trace 0 u v := by
  simp only [rounds,seed,adj,trace,local_zero]
  constructor
  · rintro ⟨hs,h|h⟩
    · exact Or.inl ⟨h.1,hs,h.2⟩
    · exfalso
      unfold bridge at h
      rw [hs] at h
      cases v.2 <;> contradiction
  · rintro (h|h)
    · exact ⟨h.2.1,Or.inl ⟨h.1,h.2.2⟩⟩
    · omega

theorem step_trace {k L r : Nat} (hL : 0<L) (u v : Vertex k L) :
    next (trace r) u v ↔ trace (r+1) u v := by
  unfold next
  rw [trace_arrived hL u]
  by_cases he : u.1=v.1
  · have hb : ¬ bridge u v := fun h=>bridge_diff h he
    have hbr : ¬ bridge v u := fun h=>bridge_diff h he.symm
    simp only [adj,trace,he,hb,hbr,true_and,false_and,or_false]
    exact local_step u.2 v.2
  · have hne : v.1≠u.1 := Ne.symm he
    simp only [adj,trace,he,hne,false_and,false_or]
    by_cases hb : bridge u v
    · have hb' := (bridge_symm u v).mp hb
      simp only [hb,hb',true_and,bridge_arrived hb]
      omega
    · simp [hb]

theorem literal_trace {k L : Nat} (hL : 0<L) (r : Nat) (u v : Vertex k L) :
    rounds r u v ↔ trace r u v := by
  induction r generalizing u v with
  | zero => exact zero_trace hL u v
  | succ r ih =>
    change next (rounds r) u v ↔ trace (r+1) u v
    have eqv : next (rounds r) u v ↔ next (trace r) u v := by
      simp only [next,ih]
    exact eqv.trans (step_trace hL u v)


theorem local_trace_bound {L r : Nat} (hL : 2≤L) {u v : Role L}
    (h : localTrace r u v) : r≤L := by
  cases u <;> cases v <;> simp [localTrace] at h
  all_goals omega

theorem quiet_after {k L r : Nat} (hL : 2≤L) (hr : L<r) (u v : Vertex k L) :
    ¬rounds r u v := by
  intro h
  rcases (literal_trace (by omega : 0<L) r u v).mp h with h|h
  · exact (Nat.not_le_of_gt hr) (local_trace_bound hL h.2)
  · omega

theorem alive_through {k L r : Nat} (hk : 0<k) (hL : 2≤L) (hr : r≤L) :
    ∃ u v : Vertex k L, rounds r u v := by
  let j : Fin k := ⟨0,hk⟩
  by_cases hr0 : r=0
  · refine ⟨(j,.center),(j,.ear),?_⟩
    exact (literal_trace (by omega : 0<L) _ _ _).mpr (Or.inl ⟨rfl,hr0⟩)
  · by_cases hrL : r=L
    · let a : Fin L := ⟨L-2,by omega⟩
      let b : Fin L := ⟨L-1,by omega⟩
      refine ⟨(j,.arm false a),(j,.arm false b),?_⟩
      apply (literal_trace (by omega : 0<L) _ _ _).mpr
      refine Or.inl ⟨rfl,rfl,?_,Or.inr ?_⟩ <;> dsimp [a,b] <;> omega
    · let a : Fin L := ⟨r-1,by omega⟩
      let b : Fin L := ⟨r,by omega⟩
      refine ⟨(j,.arm false a),(j,.arm false b),?_⟩
      apply (literal_trace (by omega : 0<L) _ _ _).mpr
      refine Or.inl ⟨rfl,rfl,?_,Or.inl ?_⟩ <;> dsimp [a,b] <;> omega

def width (L : Nat) : Nat := 2*L+1

def offset {L : Nat} : Role L → Nat
  | .center | .ear => L
  | .arm false i => L-1-i.val
  | .arm true i => L+1+i.val

def label {k L : Nat} (u : Vertex k L) : Nat :=
  u.1.val*width L+offset u.2

theorem offset_bound {L : Nat} (u : Role L) : offset u < width L := by
  cases u with
  | center | ear => simp [offset,width]; omega
  | arm b i => cases b <;> simp [offset,width] <;> omega

theorem label_bound {k L : Nat} (u : Vertex k L) : label u < k*width L := by
  have h := Nat.mul_le_mul_right (width L) (Nat.succ_le_of_lt u.1.isLt)
  rw [Nat.succ_mul] at h
  have hi := offset_bound u.2
  unfold label
  omega

theorem local_offset_step {L : Nat} {u v : Role L} (h : localAdj u v) :
    offset u ≤ offset v+1 ∧ offset v ≤ offset u+1 := by
  cases u <;> cases v <;> simp [localAdj,offset] at h ⊢ <;> try omega
  case center.arm b i => cases b <;> simp <;> omega
  case ear.arm b i => cases b <;> simp <;> omega
  case arm.center b i => cases b <;> simp <;> omega
  case arm.ear b i => cases b <;> simp <;> omega
  case arm.arm b i c j =>
    obtain ⟨rfl,h⟩ := h
    cases b <;> simp <;> omega

theorem bridge_offset_step {k L : Nat} {u v : Vertex k L} (h : bridge u v) :
    label u + 1 = label v ∨ label v + 1 = label u := by
  rcases u with ⟨i,a⟩
  rcases v with ⟨j,b⟩
  cases a <;> cases b <;> simp [bridge] at h
  rcases h with ⟨hi,hj,h|h⟩
  · rcases h with ⟨rfl,rfl,hn⟩
    left
    unfold label
    simp only [offset]
    rw [←hn,Nat.succ_mul]
    unfold width
    omega
  · rcases h with ⟨rfl,rfl,hn⟩
    right
    unfold label
    simp only [offset]
    rw [←hn,Nat.succ_mul]
    unfold width
    omega

theorem edge_step {k L : Nat} {u v : Vertex k L} (h : adj u v) :
    label u ≤ label v+1 ∧ label v ≤ label u+1 := by
  rcases h with ⟨hh,h⟩|h
  · obtain ⟨h₁,h₂⟩ := local_offset_step h
    unfold label
    rw [hh]
    omega
  · rcases bridge_offset_step h with e|e <;> omega

theorem graph_symm {k L : Nat} {u v : Vertex k L} (h : adj u v) : adj v u := by
  rcases h with ⟨s,t⟩|h
  · exact Or.inl ⟨s.symm,(local_symm _ _).mp t⟩
  · exact Or.inr ((bridge_symm _ _).mp h)

theorem graph_loopless {k L : Nat} (u : Vertex k L) : ¬ adj u u := by
  rcases u with ⟨i,t⟩
  rintro (⟨_,h⟩|h)
  · change localAdj t t at h
    cases t <;> simp [localAdj] at h
  · exact bridge_diff h rfl

theorem graph_nonbip {k L : Nat} (hk : 0<k) (hL : 0<L) :
    ¬ ∃ f : Vertex k L → Bool, ∀ u v, adj u v → f u ≠ f v := by
  rintro ⟨f,h⟩
  let i : Fin k := ⟨0,hk⟩
  let a : Vertex k L := (i,.center)
  let b : Vertex k L := (i,.ear)
  let c : Vertex k L := (i,.arm false ⟨0,hL⟩)
  have nope : ∀ a b c : Bool, a≠b → b≠c → c≠a → False := by decide
  exact nope (f a) (f b) (f c)
    (h a b (Or.inl ⟨rfl,True.intro⟩))
    (h b c (Or.inl ⟨rfl,rfl⟩))
    (h c a (Or.inl ⟨rfl,rfl⟩))

inductive Walk {k L : Nat} : Vertex k L → Vertex k L → Nat → Prop
  | nil (u) : Walk u u 0
  | cons {u v w n} : adj u v → Walk v w n → Walk u w (n+1)

theorem walk_append {k L : Nat} {u v w : Vertex k L} {a b : Nat}
    (h : Walk u v a) (g : Walk v w b) : Walk u w (a+b) := by
  induction h with
  | nil => simpa using g
  | cons e p ih => simpa only [Nat.add_comm 1 b,Nat.add_assoc] using Walk.cons e (ih g)

theorem walk_reverse {k L : Nat} {u v : Vertex k L} {n : Nat}
    (h : Walk u v n) : Walk v u n := by
  induction h with
  | nil => exact Walk.nil _
  | cons e p ih => exact walk_append ih (Walk.cons (graph_symm e) (Walk.nil _))

theorem walk_label {k L : Nat} {u v : Vertex k L} {n : Nat} (h : Walk u v n) :
    label u ≤ label v+n ∧ label v ≤ label u+n := by
  induction h with
  | nil => simp
  | cons e p ih =>
    obtain ⟨h₁,h₂⟩ := edge_step e
    omega

def radiusAtMost {k L : Nat} (r : Nat) : Prop :=
  ∃ u : Vertex k L, ∀ v, ∃ n≤r, Walk u v n

theorem radius_lower {k L r : Nat} (hk : 0<k) (hL : 0<L)
    (h : radiusAtMost (k:=k) (L:=L) r) : k*width L/2≤r := by
  obtain ⟨u,h⟩ := h
  let a : Vertex k L := (⟨0,hk⟩,.arm false ⟨L-1,by omega⟩)
  let b : Vertex k L := (⟨k-1,by omega⟩,.arm true ⟨L-1,by omega⟩)
  have ha : label a=0 := by simp [a,label,offset]
  have hb : label b+1=k*width L := by
    have hw : k*width L=(k-1)*width L+width L := by
      have he : k-1+1=k := by omega
      have H := congrArg (fun v => v*width L) he
      rw [Nat.add_mul] at H
      simpa using H.symm
    simp only [b,label,offset]
    rw [hw]
    unfold width
    omega
  obtain ⟨m,hm,wa⟩ := h a
  obtain ⟨n,hn,wb⟩ := h b
  have p := (walk_label wa).1
  have q := (walk_label wb).2
  rw [ha] at p
  omega


def spineRole {L : Nat} (j : Fin (width L)) : Role L :=
  if h : j.val<L then .arm false ⟨L-1-j.val,by omega⟩
  else if h₂ : j.val=L then .center
  else .arm true ⟨j.val-L-1,by have hh := j.isLt; unfold width at hh; omega⟩

theorem offset_spineRole {L : Nat} (j : Fin (width L)) : offset (spineRole j)=j.val := by
  unfold spineRole
  split
  · simp [offset]
    omega
  · split
    · simp [offset]
      omega
    · simp [offset]
      omega

theorem spineRole_not_ear {L : Nat} (j : Fin (width L)) : spineRole j ≠ .ear := by
  unfold spineRole
  split <;> simp
  split <;> simp

theorem spineRole_inverse {L : Nat} {v : Role L} (hn : v≠.ear) :
    spineRole ⟨offset v,offset_bound v⟩=v := by
  cases v with
  | center => simp [spineRole,offset]
  | ear => exact False.elim (hn rfl)
  | arm d i =>
    have hb := i.isLt
    cases d
    · unfold spineRole
      split
      · apply congrArg (Role.arm false)
        apply Fin.ext
        change L-1-(L-1-i.val)=i.val
        omega
      · rename_i h
        change ¬ L-1-i.val<L at h
        omega
    · unfold spineRole
      split
      · rename_i h
        change L+1+i.val<L at h
        omega
      · split
        · rename_i h
          change L+1+i.val=L at h
          omega
        · apply congrArg (Role.arm true)
          apply Fin.ext
          change L+1+i.val-L-1=i.val
          omega

theorem local_adj_of_offsets {L : Nat} {u v : Role L}
    (hu : u≠.ear) (hv : v≠.ear) (h : offset u+1=offset v) :
    localAdj u v := by
  cases u <;> cases v <;> simp_all [offset,localAdj] <;> try omega
  case center.arm b i => cases b <;> simp_all <;> omega
  case arm.center b i => cases b <;> simp_all <;> omega
  case arm.arm b i c j => cases b <;> cases c <;> simp_all <;> omega

theorem offset_zero {L : Nat} (hL : 0<L) {u : Role L} (h : offset u=0) :
    ∃ j, u=.arm false j ∧ j.val+1=L := by
  cases u with
  | center | ear => simp [offset] at h; omega
  | arm b j =>
    cases b
    · refine ⟨j,rfl,?_⟩
      simp [offset] at h
      omega
    · simp [offset] at h

theorem offset_last {L : Nat} {u : Role L} (hL : 0<L) (h : offset u+1=width L) :
    ∃ j, u=.arm true j ∧ j.val+1=L := by
  cases u with
  | center | ear => simp [offset,width] at h; omega
  | arm b j =>
    cases b
    · simp [offset,width] at h
      omega
    · refine ⟨j,rfl,?_⟩
      simp [offset,width] at h
      omega

theorem adj_of_consecutive_labels {k L : Nat} (hL : 0<L)
    {u v : Vertex k L} (hu : u.2≠.ear) (hv : v.2≠.ear)
    (h : label u+1=label v) : adj u v := by
  have huO := offset_bound u.2
  have hvO := offset_bound v.2
  have ww : 0<width L := by simp [width]
  unfold label at h
  by_cases he : u.1=v.1
  · refine Or.inl ⟨he,local_adj_of_offsets hu hv ?_⟩
    rw [he] at h
    omega
  · have hc : u.1.val≠v.1.val := fun h=>he (Fin.ext h)
    have hh : u.1.val<v.1.val := by
      by_cases hn : u.1.val<v.1.val
      · exact hn
      · have hlt : v.1.val+1≤u.1.val := by omega
        have H := Nat.mul_le_mul_right (width L) hlt
        rw [Nat.add_mul,Nat.one_mul] at H
        omega
    have hh' : u.1.val+1=v.1.val := by
      by_cases hn : u.1.val+1=v.1.val
      · exact hn
      · have hlt : u.1.val+2≤v.1.val := by omega
        have H := Nat.mul_le_mul_right (width L) hlt
        rw [Nat.add_mul,Nat.two_mul] at H
        omega
    rw [←hh',Nat.add_mul,Nat.one_mul] at h
    obtain ⟨i,hi,hi'⟩ := offset_last hL (by omega : offset u.2+1=width L)
    obtain ⟨j,hj,hj'⟩ := offset_zero hL (by omega : offset v.2=0)
    apply Or.inr
    unfold bridge
    rw [hi,hj]
    exact ⟨hi',hj',Or.inl ⟨rfl,rfl,hh'⟩⟩

def spineAt {k L : Nat} (i : Fin (k*width L)) : Vertex k L :=
  (⟨i.val / width L,(Nat.div_lt_iff_lt_mul (by simp [width])).mpr i.isLt⟩,
   spineRole ⟨i.val % width L,Nat.mod_lt _ (by simp [width])⟩)

theorem spineAt_label {k L : Nat} (i : Fin (k*width L)) :
    label (spineAt i)=i.val := by
  simp only [label,spineAt,offset_spineRole]
  rw [Nat.mul_comm]
  exact Nat.div_add_mod i.val (width L)

theorem spineAt_not_ear {k L : Nat} (i : Fin (k*width L)) :
    (spineAt i).2 ≠ .ear := spineRole_not_ear _

theorem spineAt_inverse {k L : Nat} {u : Vertex k L} (h : u.2≠.ear) :
    spineAt ⟨label u,label_bound u⟩=u := by
  rcases u with ⟨i,r⟩
  change r≠.ear at h
  have hr := offset_bound r
  have hw : 0<width L := by simp [width]
  apply Prod.ext
  · apply Fin.ext
    change (i.val*width L+offset r)/width L=i.val
    rw [Nat.mul_comm i.val (width L),Nat.mul_add_div hw,Nat.div_eq_of_lt hr,Nat.add_zero]
  · have he : (spineAt ⟨label (i,r),label_bound (i,r)⟩).2 = spineRole ⟨offset r,hr⟩ := by
      apply congrArg spineRole
      apply Fin.ext
      change (i.val*width L+offset r)%width L=offset r
      rw [Nat.mul_comm i.val (width L),Nat.mul_add_mod,Nat.mod_eq_of_lt hr]
    exact he.trans (spineRole_inverse h)

theorem spineAt_edge {k L : Nat} (hL : 0<L) (a b : Fin (k*width L))
    (h : a.val+1=b.val) : adj (spineAt a) (spineAt b) := by
  apply adj_of_consecutive_labels hL (spineAt_not_ear a) (spineAt_not_ear b)
  simpa only [spineAt_label] using h

theorem spine_walk_length {k L : Nat} (hL : 0<L)
    (a d : Nat) (hb : a+d<k*width L) :
    Walk (spineAt ⟨a,by omega⟩) (spineAt ⟨a+d,hb⟩) d := by
  induction d with
  | zero => exact Walk.nil _
  | succ d ih =>
    let m : Fin (k*width L) := ⟨a+d,by omega⟩
    let e : Fin (k*width L) := ⟨a+(d+1),hb⟩
    exact walk_append (ih (by omega))
      (Walk.cons (spineAt_edge hL m e (by dsimp [m,e];omega)) (Walk.nil _))

theorem between_spine {k L : Nat} (hL : 0<L) {u v : Vertex k L}
    (hu : u.2≠.ear) (hv : v.2≠.ear) :
    Walk u v ((label u-label v)+(label v-label u)) := by
  by_cases h : label u≤label v
  · have e := spine_walk_length hL (label u) (label v-label u)
      (by rw [Nat.add_sub_of_le h]; exact label_bound v)
    simpa only [Nat.sub_eq_zero_of_le h,Nat.zero_add,Nat.add_sub_of_le h,
      spineAt_inverse hu,spineAt_inverse hv] using e
  · have hh : label v≤label u := by omega
    have e := spine_walk_length hL (label v) (label u-label v)
      (by rw [Nat.add_sub_of_le hh]; exact label_bound u)
    simpa only [Nat.sub_eq_zero_of_le hh,Nat.add_zero,Nat.add_sub_of_le hh,
      spineAt_inverse hu,spineAt_inverse hv] using walk_reverse e

theorem radius_upper {k L : Nat} (hk : 0<k) (hL : 0<L) :
    radiusAtMost (k:=k) (L:=L) (k*width L/2) := by
  have hp : 0<k*width L := Nat.mul_pos hk (by simp [width])
  let mid : Fin (k*width L) := ⟨k*width L/2,by omega⟩
  let u : Vertex k L := spineAt mid
  have hm : label u = k*width L/2 := spineAt_label mid
  have hn : u.2≠.ear := spineAt_not_ear mid
  refine ⟨u,fun v=>?_⟩
  by_cases he : v.2=.ear
  · let w : Vertex k L := (v.1,.center)
    have ww : label w=v.1.val*width L+L := rfl
    have hi := Nat.mul_le_mul_right (width L) (Nat.succ_le_of_lt v.1.isLt)
    rw [Nat.succ_mul] at hi
    have hw : w.2≠.ear := by
      change (Role.center : Role L)≠.ear
      intro h
      cases h
    have e := between_spine hL hn hw
    have ee : adj w v := Or.inl ⟨rfl,by rw [he];exact True.intro⟩
    have hlow : 1≤label w := by omega
    have w0 : width L=2*L+1 := rfl
    have hhigh : label w+1<k*width L := by omega
    refine ⟨_,?_,walk_append e (Walk.cons ee (Walk.nil _))⟩
    rw [hm]
    omega
  · have h := label_bound v
    refine ⟨_,?_,between_spine hL hn he⟩
    rw [hm]
    omega


theorem exact_radius {k L r : Nat} (hk : 0<k) (hL : 0<L) :
    radiusAtMost (k:=k) (L:=L) r ↔ k*width L/2≤r := by
  constructor
  · exact radius_lower hk hL
  · intro h
    obtain ⟨u,hu⟩ := radius_upper hk hL
    refine ⟨u,fun v =>?_⟩
    obtain ⟨n,hn,hw⟩ := hu v
    exact ⟨n,Nat.le_trans hn h,hw⟩

theorem radius_arithmetic (k L : Nat) :
    k*width L/2=k*L+k/2 := by
  have h : k*width L=2*(k*L)+k := by
    unfold width
    grind
  rw [h]
  omega

theorem time_radius_arithmetic {k t : Nat} (tpos : 0<t) :
    k*width (t-1)/2=k*t-(k+1)/2 := by
  have h : k*t=k*(t-1)+k := by
    have he : t-1+1=t := by omega
    have H := congrArg (fun n => k*n) he
    rw [Nat.mul_add,Nat.mul_one] at H
    exact H.symm
  rw [radius_arithmetic,h]
  omega

theorem graph_connected {k L : Nat} (hk : 0<k) (hL : 0<L)
    (u v : Vertex k L) : ∃ n, Walk u v n := by
  obtain ⟨mid,hm⟩ := radius_upper (k:=k) (L:=L) hk hL
  obtain ⟨a,_,ha⟩ := hm u
  obtain ⟨b,_,hb⟩ := hm v
  exact ⟨a+b,walk_append (walk_reverse ha) hb⟩

def centerOf {L : Nat} {k : Nat} (i : Fin k) : Vertex k L := (i,.center)

theorem center_injective {k L : Nat} : Function.Injective (centerOf (k:=k) (L:=L)) := by
  intro i j h
  exact congrArg Prod.fst h

theorem seed_image {k L : Nat} (u : Vertex k L) :
    seed u ↔ ∃ i : Fin k, centerOf i=u := by
  rcases u with ⟨i,r⟩
  constructor
  · intro h
    change r=.center at h
    subst r
    exact ⟨i,rfl⟩
  · rintro ⟨j,h⟩
    change (j,Role.center)=(i,r) at h
    exact (congrArg Prod.snd h).symm

theorem all_vertices_receive {k L : Nat} (hL : 2≤L) (u : Vertex k L) :
    ∃ r≤L, ∃ v, rounds r v u := by
  have h0 : 0<L := by omega
  rcases u with ⟨i,a⟩
  have H : ∃ r≤L, arrived r a := by
    cases a with
    | center => exact ⟨2,hL,rfl⟩
    | ear => exact ⟨0,by omega,Or.inl rfl⟩
    | arm s j => exact ⟨j.val,by omega,Or.inl rfl⟩
  obtain ⟨r,hr,ha⟩ := H
  have H' := (trace_arrived (r:=r) h0 (i,a)).mpr ha
  obtain ⟨v,hv⟩ := H'
  exact ⟨r,hr,v,(literal_trace h0 r v (i,a)).mpr hv⟩

/-- Displayed sources send in each of physical rounds 1 through t,
and in no round after t. Round indices in the implementation start at 0. -/
theorem exact_displayed_time {k t : Nat} (hk : 0<k) (ht : 3≤t) (n : Nat) :
    (∃ u v : Vertex k (t-1), rounds n u v) ↔ n<t := by
  constructor
  · rintro ⟨u,v,h⟩
    by_cases H : n<t
    · exact H
    · exact False.elim (quiet_after (by omega : 2≤t-1) (by omega : t-1<n) u v h)
  · intro h
    exact alive_through hk (by omega : 2≤t-1) (by omega : n≤t-1)

/-- The stated radius and the time of the exhibited source set already
contradict Turau §8; this theorem does not need optimality. -/
theorem stretched_disproof {k t : Nat} (hk : 4≤k) (ht : 3≤t) :
    (∀ r, radiusAtMost (k:=k) (L:=t-1) r ↔ k*t-(k+1)/2≤r) ∧
    (∀ n, (∃ u v : Vertex k (t-1), rounds n u v) ↔ n<t) ∧
    k*t<(k*t-(k+1)/2)+k-1 := by
  have hk0 : 0<k := by omega
  have ht0 : 0<t := by omega
  refine ⟨?_,exact_displayed_time hk0 ht,?_⟩
  · intro r
    rw [exact_radius hk0 (by omega : 0<t-1),time_radius_arithmetic ht0]
  · have H := Nat.mul_le_mul_left k (show 1≤t by omega)
    simp only [Nat.mul_one] at H
    omega

/-- Merely the arithmetic consequence of the externally cited
Theorem 4(3). This asserts no unformalized fact about other source sets. -/
theorem cited_bound_implies_optimum {k t m : Nat} (hk : 0<k) (ht : 3≤t)
    (h : 2*(k*t-(k+1)/2)+k ≤ 2*(k*m)) : t≤m := by
  by_cases hh : t≤m
  · exact hh
  · have hm : m≤t-1 := by omega
    have hb := Nat.mul_le_mul_left k hm
    have he : t-1+1=t := by omega
    have H := congrArg (fun z=>k*z) he
    rw [Nat.mul_add,Nat.mul_one] at H
    omega


end AmnesiacStretched
