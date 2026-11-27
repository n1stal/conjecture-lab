module

public import Std

@[expose] public section


namespace InverseZ.TriangleCycleCertificate

/-- F(k,v,b) with v=b-k-2. This presentation has no subtraction. -/
def F (k v b : Nat) : Nat :=
  b*(b+1)*(v+2)+(v+3)*(v+2)*v+k*(k*(v+2)+v*(v+3)+1)

set_option maxHeartbeats 4000000

theorem regularIdentity (x d : Nat) :
    let b := 2*x+d+4
    let y := x+d+3
    let c := F (x+1) (x+d+1) b
    let l := F x (x+d+2) b
    let r := F (x+2) (x+d) b
    c*c*(x+2)*(y+2) = l*r*(x+1)*(y+1) +
      98*x^7 + 441*x^6*d + 1701*x^6 + 840*x^5*d^2 + 6489*x^5*d +
      12425*x^5 + 882*x^4*d^3 + 10224*x^4*d^2 + 39132*x^4*d + 49525*x^4 +
      554*x^3*d^4 + 8560*x^3*d^3 + 49092*x^3*d^2 + 123979*x^3*d + 116513*x^3 +
      209*x^2*d^5 + 4035*x^2*d^4 + 30814*x^2*d^3 + 116452*x^2*d^2 + 218049*x^2*d +
      162106*x^2 + 44*x*d^6 + 1019*x*d^5 + 9715*x*d^4 + 48840*x*d^3 +
      136684*x*d^2 + 202178*x*d + 123720*x + 4*d^7 + 108*d^6 +
      1234*d^5 + 7738*d^4 + 28780*d^3 + 63556*d^2 + 77280*d + 40000 := by
  dsimp [F]
  grind

theorem regularStrict (x d : Nat) :
    let b := 2*x+d+4
    let y := x+d+3
    let c := F (x+1) (x+d+1) b
    let l := F x (x+d+2) b
    let r := F (x+2) (x+d) b
    l*r*(x+1)*(y+1) < c*c*(x+2)*(y+2) := by
  dsimp
  rw [regularIdentity x d]
  omega

#print axioms regularStrict

theorem evenNearIdentity (x : Nat) :
    let b := 2*x+4
    let y := x+3
    let c := F (x+1) (x+1) b
    let l := F x (x+2) b
    let r := F (x+2) x b+b
    c*c*(x+2)*(y+2) = l*r*(x+1)*(y+1) +
      98*x^7 + 1687*x^6 + 12215*x^5 + 48263*x^4 + 112619*x^3 +
      155582*x^2 + 118104*x + 38080 := by
  dsimp [F]
  grind

theorem evenNearStrict (x : Nat) :
    let b := 2*x+4
    let y := x+3
    let c := F (x+1) (x+1) b
    let l := F x (x+2) b
    let r := F (x+2) x b+b
    l*r*(x+1)*(y+1) < c*c*(x+2)*(y+2) := by
  dsimp
  rw [evenNearIdentity x]
  omega

#print axioms evenNearStrict

theorem evenCenterIdentity (x : Nat) :
    let b := 2*x+4
    (x+4)*(F (x+2) x b+b) = (x+2)*F (x+1) (x+1) b +
      7*x^3 + 43*x^2 + 86*x + 56 := by
  dsimp [F]
  grind

theorem evenCenterStrict (x : Nat) :
    let b := 2*x+4
    (x+2)*F (x+1) (x+1) b < (x+4)*(F (x+2) x b+b) := by
  dsimp
  rw [evenCenterIdentity x]
  omega

#print axioms evenCenterStrict

theorem oddCenterIdentity (x : Nat) :
    let b := 2*x+3
    (x+4)*F (x+1) x b = (x+1)*F x (x+1) b +
      14*x^3 + 75*x^2 + 121*x + 60 := by
  dsimp [F]
  grind

theorem oddCenterStrict (x : Nat) :
    let b := 2*x+3
    (x+1)*F x (x+1) b < (x+4)*F (x+1) x b := by
  dsimp
  rw [oddCenterIdentity x]
  omega

#print axioms oddCenterStrict
end InverseZ.TriangleCycleCertificate

namespace InverseZ.TriangleCycle

def choose : Nat → Nat → Nat :=
  Nat.rec (fun k => Nat.casesOn k 1 (fun _ => 0))
    (fun _ prev k => Nat.casesOn k 1 (fun j => prev j + prev (j+1)))

@[simp] theorem choose_zero_right (n : Nat) : choose n 0 = 1 := by cases n <;> rfl
@[simp] theorem choose_zero_succ (k : Nat) : choose 0 (k+1) = 0 := rfl
@[simp] theorem choose_succ_succ (n k : Nat) :
    choose (n+1) (k+1) = choose n k + choose n (k+1) := rfl

theorem choose_eq_zero_of_lt {n k : Nat} (h : n<k) : choose n k=0 := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => omega
    | succ k => rfl
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k =>
      rw [choose_succ_succ,ih (by omega),ih (by omega)]

theorem choose_pos_of_le {n k : Nat} (h : k≤n) : 0 < choose n k := by
  induction n generalizing k with
  | zero =>
    have e : k=0 := by omega
    simp [e]
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      have hp : 0 < choose n k := ih (by omega)
      rw [choose_succ_succ]
      omega

theorem choose_ratio (n k : Nat) : (k+1)*choose n (k+1)=(n-k)*choose n k := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    cases k with
    | zero =>
      have h := ih 0
      simp at h
      simp [h,Nat.add_comm]
    | succ k =>
      by_cases hk : k+1≤n
      · have hk' : k≤n := by omega
        have hn : (n+1)-(k+1) = n-k := by omega
        have h1 : (n-(k+1))+(k+2)=n+1 := by omega
        have h2 : (n-k)+(k+1)=n+1 := by omega
        have e1 := ih k
        have e2 := ih (k+1)
        simp only [choose_succ_succ,hn]
        grind
      · by_cases he : k = n
        · subst k
          have hz1 := choose_eq_zero_of_lt (show n<n+1 by omega)
          have hz2 := choose_eq_zero_of_lt (show n<n+1+1 by omega)
          simp [choose_succ_succ,hz1,hz2]
        · have hl : n+1<k+1 := by omega
          rw [choose_eq_zero_of_lt hl,choose_eq_zero_of_lt (show n+1<k+1+1 by omega)]
          simp

theorem choose_self (n : Nat) : choose n n = 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [choose_succ_succ,ih,choose_eq_zero_of_lt (by omega : n<n+1)]

theorem choose_swap (a b : Nat) : choose (a+b) a=choose (a+b) b := by
  induction a generalizing b with
  | zero => simp [choose_self]
  | succ a ih =>
    induction b with
    | zero => simpa only [Nat.add_zero, choose_zero_right] using choose_self (a+1)
    | succ b jh =>
      have h₀ : choose (a+b+1) a = choose (a+b+1) (b+1) := ih (b+1)
      have h₁ : choose (a+b+1) (a+1) = choose (a+b+1) b := by
        have e : (a+1)+b=a+b+1 := by omega
        rw [← e]
        exact jh
      have e : (a+1)+(b+1)=(a+b+1)+1 := by omega
      rw [e,choose_succ_succ (a+b+1) a,choose_succ_succ (a+b+1) b,h₀,h₁]
      omega

theorem choose_reflect (n i : Nat) (hi : i≤n) : choose n (n-i)=choose n i := by
  have h := choose_swap i (n-i)
  have e : i+(n-i)=n := by omega
  rw [e] at h
  exact h.symm


open InverseZ.TriangleCycleCertificate

theorem choose_down (n k : Nat) :
    (n+1)*choose n k=(n+1-k)*choose (n+1) k := by
  cases k with
  | zero => simp
  | succ k =>
    have h := choose_ratio n k
    by_cases hk : k≤n
    · have hn : n+1-(k+1)=n-k := by omega
      have e : (n-k)+(k+1)=n+1 := by omega
      rw [choose_succ_succ,hn]
      grind
    · rw [choose_eq_zero_of_lt (by omega : n<k+1),choose_eq_zero_of_lt (by omega : n+1<k+1)]
      simp

theorem choose_down_shift (n k : Nat) :
    (n+1)*choose n k=(k+1)*choose (n+1) (k+1) := by
  rw [choose_succ_succ]
  have h := choose_ratio n k
  by_cases hk : k≤n
  · have e : (n-k)+(k+1)=n+1 := by omega
    grind
  · rw [choose_eq_zero_of_lt (by omega : n<k),choose_eq_zero_of_lt (by omega : n<k+1)]
    simp

def cycleRow (r i : Nat) : Nat :=
  if i≤r then
    let j := min i (r-i)
    choose (r+1) j*(r-j)
  else 0

def raw (r i : Nat) : Nat := choose (r+1) i*(r-i)

def shift (f : Nat → Nat) (i : Nat) : Nat :=
  match i with | 0 => 0 | j+1 => f j

def convolve (f : Nat → Nat) (i : Nat) : Nat :=
  f i+shift f i+shift (shift f) i

def baseline (b i : Nat) : Nat := raw b i+convolve (raw (b-2)) i

def dent (m : Nat) : Nat := choose (2*m) m-choose (2*m) (m+1)

def bfmCoeff (b i : Nat) : Int :=
  (cycleRow b i:Int)+(convolve (cycleRow (b-2)) i:Int)-
    if b%2=1 ∧ (i=b/2 ∨ i=b/2+1) then (dent (b/2):Int) else 0

theorem cycle_raw (r i : Nat) (h : 2*i≤r) : cycleRow r i=raw r i := by
  have hi : i≤r := by omega
  have hm : i≤r-i := by omega
  simp [cycleRow,raw,hi,Nat.min_eq_left hm]

theorem cycle_reflected (r i : Nat) (h : r≤2*i) (hi : i≤r) :
    cycleRow r i=i*choose (r+1) (i+1) := by
  have h' : r-i≤i := by omega
  have hr : r+1-(i+1)=r-i := by omega
  have he := choose_reflect (r+1) (i+1) (by omega)
  unfold cycleRow
  rw [ite_eq_left hi,Nat.min_eq_right h']
  have hchoose : choose (r+1) (r-i)=choose (r+1) (i+1) := hr ▸ he
  dsimp
  rw [hchoose,show r-(r-i)=i by omega]
  exact Nat.mul_comm _ _

theorem dent_relation (m : Nat) :
    m*choose (2*m) (m+1) + choose (2*m) (m+1) = m*choose (2*m) m := by
  have h := choose_ratio (2*m) m
  have e : 2*m-m=m := by omega
  rw [e,Nat.add_mul,Nat.one_mul] at h
  exact h

theorem dent_mul (m : Nat) :
    (m+1)*dent m=choose (2*m) m := by
  have h := dent_relation m
  have hle : choose (2*m) (m+1)≤choose (2*m) m := by
    by_cases hh : choose (2*m) (m+1)≤choose (2*m) m
    · exact hh
    · have hp := Nat.mul_le_mul_left m (show choose (2*m) m≤choose (2*m) (m+1) by omega)
      omega
  have he := Nat.sub_add_cancel hle
  unfold dent
  grind

theorem odd_dent_cancel (m : Nat) (hm : 1≤m) :
    cycleRow (2*m-1) m = raw (2*m-1) m+dent m := by
  rw [cycle_reflected _ _ (by omega) (by omega)]
  have h := dent_relation m
  have hle : choose (2*m) (m+1)≤choose (2*m) m := by
    by_cases hh : choose (2*m) (m+1)≤choose (2*m) m
    · exact hh
    · have hp := Nat.mul_le_mul_left m (show choose (2*m) m≤choose (2*m) (m+1) by omega)
      omega
  have he := Nat.sub_add_cancel hle
  simp only [raw,dent,show 2*m-1+1=2*m by omega,show 2*m-1-m=m-1 by omega]
  have hh : m-1+1=m := by omega
  grind
  

theorem choose_double_down (n k : Nat) (_hk : k≤n+1) :
    (n+2)*(n+1)*choose n k=(n+2-k)*(n+1-k)*choose (n+2) k := by
  have a := choose_down n k
  have b := choose_down (n+1) k
  grind

theorem choose_double_middle (n k : Nat) :
    (n+2)*(n+1)*choose n k=(k+1)*(n+1-k)*choose (n+2) (k+1) := by
  have a := choose_down n k
  have b := choose_down_shift (n+1) k
  grind

theorem choose_double_up (n k : Nat) :
    (n+2)*(n+1)*choose n k=(k+1)*(k+2)*choose (n+2) (k+2) := by
  have a := choose_down_shift n k
  have b := choose_down_shift (n+1) (k+1)
  grind

theorem even_dent_scaled (m : Nat) (hm : 2≤m) :
    (2*m)*(2*m+1)*cycleRow (2*m-2) m =
      (2*m)*(2*m+1)*raw (2*m-2) m+(2*m)*choose (2*m+1) m := by
  rw [cycle_reflected _ _ (by omega) (by omega)]
  let a := choose (2*m-1) m
  let b := choose (2*m-1) (m+1)
  let c := choose (2*m+1) m
  let d := (2*m)*(2*m+1)
  have ha := choose_ratio (2*m-1) m
  have hb := choose_double_down (2*m-1) m (by omega)
  simp only [show 2*m-1-m=m-1 by omega] at ha
  simp only [show 2*m-1+2=2*m+1 by omega,show 2*m-1+1=2*m by omega,
    show 2*m+1-m=m+1 by omega,show 2*m-m=m by omega] at hb
  have h1 : (m+1)*b=(m-1)*a := ha
  have h2 : d*a=(m+1)*m*c := by simpa [d,a,c,Nat.mul_comm] using hb
  have h3 : (m-2)+2=m := by omega
  have h4 : (m-1)+1=m := by omega
  unfold raw
  simp only [show 2*m-2+1=2*m-1 by omega,show 2*m-2-m=m-2 by omega]
  change d*(m*b) = d*(a*(m-2))+(2*m)*c
  apply Nat.eq_of_mul_eq_mul_left (n:=m+1) (by omega)
  grind


theorem baseline_scaled (b k : Nat) (hb : 3≤b) (hk : 2*k≤b) :
    b*(b+1)*baseline b k=choose (b+1) k*F k (b-k-2) b := by
  let y := b-k
  let d := b*(b+1)
  have hy : 2≤y := by dsimp [y]; omega
  have hR : b-2+1=b-1 := by omega
  have e0 : d*choose (b-1) k=(y+1)*y*choose (b+1) k := by
    have hh := choose_double_down (b-1) k (by omega)
    have e1 : b-1+2=b+1 := by omega
    have e2 : b-1+1=b := by omega
    have e3 : b+1-k=y+1 := by dsimp [y]; omega
    rw [e1,e2,e3] at hh
    simpa only [d,y,Nat.mul_comm (b+1) b] using hh
  have e1 (j : Nat) (he : k=j+1) : d*choose (b-1) j=k*(y+1)*choose (b+1) k := by
    have hh := choose_double_middle (b-1) j
    have e1 : b-1+2=b+1 := by omega
    have e2 : b-1+1=b := by omega
    have e3 : b-j=y+1 := by dsimp [y]; omega
    rw [e1,e2,e3,←he] at hh
    simpa only [d,Nat.mul_comm (b+1) b] using hh
  have e2 (j : Nat) (he : k=j+2) : d*choose (b-1) j=k*(k-1)*choose (b+1) k := by
    have hh := choose_double_up (b-1) j
    have e1 : b-1+2=b+1 := by omega
    have e2 : b-1+1=b := by omega
    have e3 : j+1=k-1 := by omega
    rw [e1,e2,e3,←he] at hh
    simpa only [d,Nat.mul_comm (b+1) b,Nat.mul_comm (k-1) k] using hh
  have yf : y-2+2=y := by omega
  have y1 : y-2+3=y+1 := by omega
  have yy : b-2-k=y-2 := by dsimp [y]; omega
  change d*baseline b k=choose (b+1) k*F k (y-2) b
  unfold baseline convolve F
  simp only [yf,y1,raw,hR,yy]
  cases k with
  | zero =>
    simp only [shift,Nat.add_zero,Nat.zero_mul]
    dsimp [y] at *
    grind
  | succ k =>
    cases k with
    | zero =>
      have e := e1 0 rfl
      have a : b-2-0=y-1 := by dsimp [y]; omega
      have s : y-1+1=y := by omega
      simp only [shift,raw,hR,a,Nat.add_zero]
      grind
    | succ j =>
      have ea := e1 (j+1) rfl
      have eb := e2 j rfl
      have a : b-2-(j+1)=y-1 := by dsimp [y]; omega
      have bb : b-2-j=y := by dsimp [y]; omega
      have s' : y-1+1=y := by omega
      have js : j+1+1=j+2 := by omega
      have hs : j+1+1-1=j+1 := by omega
      simp only [shift,raw,hR,a,bb]
      grind


theorem shift_cycle_raw (r k : Nat) (h : 2*k≤r+2) :
    shift (cycleRow r) k=shift (raw r) k := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [shift]
    exact cycle_raw r k (by omega)

theorem shift2_cycle_raw (r k : Nat) (h : 2*k≤r+4) :
    shift (shift (cycleRow r)) k=shift (shift (raw r)) k := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [shift]
    exact shift_cycle_raw r k (by omega)

theorem bfm_below_center (b k : Nat) (hb : 3≤b) (hk : 2*k+2≤b) :
    bfmCoeff b k=(baseline b k:Int) := by
  have hlo : 2*k≤b-2 := by omega
  have ha := cycle_raw b k (by omega)
  have hb' := cycle_raw (b-2) k hlo
  have hs := shift_cycle_raw (b-2) k (by omega)
  have ht := shift2_cycle_raw (b-2) k (by omega)
  have hp : ¬(b%2=1 ∧ (k=b/2 ∨ k=b/2+1)) := by omega
  simp only [bfmCoeff,baseline,convolve,ha,hb',hs,ht,ite_eq_right hp,Int.sub_zero,Int.natCast_add]

theorem bfm_odd_center (m : Nat) (hm : 1≤m) :
    bfmCoeff (2*m+1) m=(baseline (2*m+1) m:Int) := by
  have hs := shift_cycle_raw (2*m+1-2) m (by omega)
  have ht := shift2_cycle_raw (2*m+1-2) m (by omega)
  have hd := odd_dent_cancel m hm
  have hd' : cycleRow (2*m+1-2) m=raw (2*m+1-2) m+dent m := by
    simpa only [show 2*m+1-2=2*m-1 by omega] using hd
  have hc := cycle_raw (2*m+1) m (by omega)
  have hp : (2*m+1)%2=1 ∧ (m=(2*m+1)/2 ∨ m=(2*m+1)/2+1) := by omega
  have hq : (2*m+1)/2=m := by omega
  unfold bfmCoeff
  rw [ite_eq_left hp,hq]
  simp only [baseline,convolve,hc,hd',hs,ht,Int.natCast_add]
  omega

theorem bfm_even_center_scaled (m : Nat) (hm : 2≤m) :
    ((2*m)*(2*m+1):Int)*bfmCoeff (2*m) m =
      ((2*m)*(2*m+1):Int)*(baseline (2*m) m:Int)+(2*m:Int)*(choose (2*m+1) m:Int) := by
  have hs := shift_cycle_raw (2*m-2) m (by omega)
  have ht := shift2_cycle_raw (2*m-2) m (by omega)
  have hc := cycle_raw (2*m) m (by omega)
  have hp : ¬((2*m)%2=1 ∧ (m=(2*m)/2 ∨ m=(2*m)/2+1)) := by omega
  simp only [bfmCoeff,baseline,convolve,hc,hs,ht,ite_eq_right hp,Int.sub_zero,Int.natCast_add]
  have hh := congrArg (fun x : Nat => (x:Int)) (even_dent_scaled m hm)
  simp only [Int.natCast_mul,Int.natCast_add,Int.natCast_one] at hh
  grind

def numerator (b k : Nat) : Nat :=
  F k (b-k-2) b + if b=2*k then b else 0

theorem bfm_left_scaled (b k : Nat) (hb : 3≤b) (hk : 2*k≤b) :
    ((b:Int)*(b+1))*bfmCoeff b k=(choose (b+1) k:Int)*(numerator b k:Int) := by
  have hc := congrArg (fun x : Nat => (x:Int)) (baseline_scaled b k hb hk)
  simp only [Int.natCast_mul,Int.natCast_add,Int.natCast_one] at hc
  by_cases h : 2*k+2≤b
  · rw [bfm_below_center b k hb h]
    simp only [numerator,ite_eq_right (show b≠2*k by omega),Nat.add_zero]
    exact hc
  · by_cases he : b=2*k
    · subst b
      have hd := bfm_even_center_scaled k (by omega)
      simp only [numerator,Int.natCast_add] 
      simp only [Int.natCast_mul] at hc
      grind
    · have hf : b=2*k+1 := by omega
      subst b
      rw [bfm_odd_center k (by omega)]
      simp only [numerator,ite_eq_right he,Nat.add_zero]
      exact hc

#print axioms dent_mul
#print axioms odd_dent_cancel
#print axioms even_dent_scaled
#print axioms bfm_left_scaled

theorem cycleRow_symm (r i : Nat) (hi : i≤r) :
    cycleRow r i=cycleRow r (r-i) := by
  have ha : r-i≤r := by omega
  have hb : r-(r-i)=i := by omega
  simp only [cycleRow,ite_eq_left hi,ite_eq_left ha,hb]
  rw [Nat.min_comm]

theorem shift_apply (f : Nat → Nat) (i : Nat) (hi : 0<i) :
    shift f i=f (i-1) := by
  cases i with
  | zero => omega
  | succ _ => rfl

theorem shift2_apply (f : Nat → Nat) (i : Nat) (hi : 2≤i) :
    shift (shift f) i=f (i-2) := by
  rw [shift_apply (shift f) i (by omega),shift_apply f (i-1) (by omega)]
  rw [show i-1-1=i-2 by omega]

theorem cycle_shift2_reflect (r i : Nat) (hi : i≤r+2) :
    cycleRow r i=shift (shift (cycleRow r)) (r+2-i) := by
  by_cases he : i≤r
  · rw [shift2_apply _ _ (by omega),show r+2-i-2=r-i by omega]
    exact cycleRow_symm r i he
  · have hh : r+2-i=0 ∨ r+2-i=1 := by omega
    rcases hh with hh|hh <;> simp [cycleRow,he,hh,shift]

theorem cycle_shift_reflect (r i : Nat) (hi : i≤r+2) :
    shift (cycleRow r) i=shift (cycleRow r) (r+2-i) := by
  by_cases h0 : i=0
  · subst i
    rw [Nat.sub_zero,shift_apply (cycleRow r) (r+2) (by omega)]
    simp only [shift,cycleRow,ite_eq_right (show ¬(r+2-1≤r) by omega)]
  · by_cases h1 : i=r+2
    · subst i
      simp only [Nat.sub_self]
      rw [shift_apply (cycleRow r) (r+2) (by omega)]
      simp only [shift,cycleRow,ite_eq_right (show ¬(r+2-1≤r) by omega)]
    · rw [shift_apply _ _ (by omega),shift_apply _ _ (by omega),
          show r+2-i-1=r-(i-1) by omega]
      exact cycleRow_symm r (i-1) (by omega)

theorem convolve_symm (r i : Nat) (hi : i≤r+2) :
    convolve (cycleRow r) i=convolve (cycleRow r) (r+2-i) := by
  have ha := cycle_shift2_reflect r i hi
  have hb := cycle_shift_reflect r i hi
  have hc := cycle_shift2_reflect r (r+2-i) (by omega)
  rw [show r+2-(r+2-i)=i by omega] at hc
  unfold convolve
  rw [ha,hb,←hc]
  ac_rfl

theorem bfm_symm (b i : Nat) (hb : 3≤b) (hi : i≤b) :
    bfmCoeff b i=bfmCoeff b (b-i) := by
  have hc := cycleRow_symm b i hi
  have ht := convolve_symm (b-2) i (by omega)
  rw [show b-2+2=b by omega] at ht
  unfold bfmCoeff
  rw [hc,ht]
  by_cases hh : b%2=1
  · have he : (i=b/2 ∨ i=b/2+1) ↔ (b-i=b/2 ∨ b-i=b/2+1) := by omega
    by_cases h0 : i=b/2 ∨ i=b/2+1
    · rw [ite_eq_left ⟨hh,h0⟩,ite_eq_left ⟨hh,he.mp h0⟩]
    · rw [ite_eq_right (show ¬(b%2=1 ∧ (i=b/2 ∨ i=b/2+1)) from fun h=>h0 h.2),
          ite_eq_right (show ¬(b%2=1 ∧ (b-i=b/2 ∨ b-i=b/2+1)) from fun h=>h0 (he.mpr h.2))]
  · simp [hh]


theorem factor_lc (D f B CL C CR NL N NR G : Int)
    (hD : 0<D) (hf : 0<f) (hG : 0<G) (hB : 0<B)
    (hc : D*C=B*N) (hl : D*CL*G=B*NL) (hr : D*CR*f=B*NR)
    (hn : G*f*N*N>NL*NR) : C*C>CL*CR := by
  have e : (D*D)*(G*f)*(C*C-CL*CR)=B*B*(G*f*N*N-NL*NR) := by grind
  have hp : 0 < B*B*(G*f*N*N-NL*NR) := Int.mul_pos (Int.mul_pos hB hB) (by omega)
  have hleft : 0 < (D*D)*(G*f)*(C*C-CL*CR) := e ▸ hp
  have h0 : 0 < (D*D)*(G*f) := Int.mul_pos (Int.mul_pos hD hD) (Int.mul_pos hG hf)
  have he : 0 < C*C-CL*CR := Int.pos_of_mul_pos_right hleft h0
  omega


theorem numerator_lc (b k : Nat) (hk : 1≤k) (hr : 2*(k+1)≤b) :
    numerator b (k-1)*numerator b (k+1)*k*(b+1-k) <
      numerator b k*numerator b k*(k+1)*(b+2-k) := by
  let x := k-1
  have hx : k=x+1 := by dsimp [x]; omega
  by_cases he : b=2*(k+1)
  · have hb : b=2*x+4 := by omega
    have hv : b-k-2=x+1 := by omega
    have hv0 : b-(k-1)-2=x+2 := by omega
    have hv1 : b-(k+1)-2=x := by omega
    have hq : b+1-k=x+3+1 := by omega
    have hq' : b+2-k=x+3+2 := by omega
    have hn0 : b≠2*(k-1) := by omega
    have hn1 : b≠2*k := by omega
    have hn2 : k+1=x+2 := by omega
    have h := evenNearStrict x
    dsimp at h
    unfold numerator
    rw [ite_eq_right hn0,ite_eq_right hn1,ite_eq_left he,hv,hv0,hv1,hq,hq',hn2,
      show k-1=x from rfl,hx,hb]
    simpa only [Nat.add_zero] using h
  · let d := b-(2*x+4)
    have hb : b=2*x+d+4 := by dsimp [d]; omega
    have hv : b-k-2=x+d+1 := by omega
    have hv0 : b-(k-1)-2=x+d+2 := by omega
    have hv1 : b-(k+1)-2=x+d := by omega
    have hq : b+1-k=x+d+3+1 := by omega
    have hq' : b+2-k=x+d+3+2 := by omega
    have hn0 : b≠2*(k-1) := by omega
    have hn1 : b≠2*k := by omega
    have hn2 : k+1=x+2 := by omega
    have h := regularStrict x d
    dsimp at h
    unfold numerator
    rw [ite_eq_right hn0,ite_eq_right hn1,ite_eq_right he,hv,hv0,hv1,hq,hq',hn2,
      show k-1=x from rfl,hx,hb]
    simpa only [Nat.add_zero] using h

theorem bfm_minor_left (b k : Nat) (hb : 3≤b) (hk : 1≤k) (hr : 2*(k+1)≤b) :
    bfmCoeff b (k-1)*bfmCoeff b (k+1) < bfmCoeff b k*bfmCoeff b k := by
  let D := (b:Int)*(b+1)
  let B := (choose (b+1) k:Int)
  let P := (choose (b+1) (k-1):Int)
  let R := (choose (b+1) (k+1):Int)
  let N := (numerator b k:Int)
  let NP := (numerator b (k-1):Int)
  let NR := (numerator b (k+1):Int)
  let f := (k:Int)+1
  let g := (b+2-k : Nat)
  let h := (b+1-k : Nat)
  have hc : D*bfmCoeff b k=B*N := bfm_left_scaled b k hb (by omega)
  have hp : D*bfmCoeff b (k-1)=P*NP := bfm_left_scaled b (k-1) hb (by omega)
  have hR : D*bfmCoeff b (k+1)=R*NR := bfm_left_scaled b (k+1) hb hr
  have ep : (g:Int)*P=(k:Int)*B := by
    have e := choose_ratio (b+1) (k-1)
    have ek : k-1+1=k := by omega
    have ea : b+1-(k-1)=g := by dsimp [g]; omega
    rw [ek,ea] at e
    have hi := congrArg (fun i : Nat=>(i:Int)) e.symm
    simpa only [Int.natCast_mul] using hi
  have er : f*R=(h:Int)*B := by
    have e := congrArg (fun i : Nat=>(i:Int)) (choose_ratio (b+1) k)
    simpa only [Int.natCast_mul,Int.natCast_add,Int.natCast_one] using e
  have ed : 0<D := Int.mul_pos (by omega) (by omega)
  have eg : 0<(g:Int) := by dsimp [g]; omega
  have ef : 0<f := by dsimp [f]; omega
  have eb : 0<B := by exact Int.ofNat_lt.mpr (choose_pos_of_le (by omega))
  have e1 : D*bfmCoeff b (k-1)*(g:Int)=B*(NP*(k:Int)) := by grind
  have e2 : D*bfmCoeff b (k+1)*f=B*(NR*(h:Int)) := by grind
  have e3 : (g:Int)*f*N*N>(NP*(k:Int))*(NR*(h:Int)) := by
    have e := Int.ofNat_lt.mpr (numerator_lc b k hk hr)
    simp only [Int.natCast_mul,Int.natCast_add,Int.natCast_one] at e
    dsimp [g,f,N,NP,NR,h]
    grind
  exact factor_lc D f B _ _ _ (NP*(k:Int)) N (NR*(h:Int)) g ed ef eg eb hc e1 e2 e3


theorem numerator_center (b k : Nat) (hb : 3≤b) (hk : k=b/2) :
    k*numerator b (k-1) < (b+2-k)*numerator b k := by
  by_cases he : b=2*k
  · let x := k-2
    have hx : k=x+2 := by dsimp [x]; omega
    have e : b=2*x+4 := by omega
    have e1 : b-(k-1)-2=x+1 := by omega
    have e2 : b-k-2=x := by omega
    have e3 : b+2-k=x+4 := by omega
    have ep : k-1=x+1 := by omega
    have en : b≠2*(k-1) := by omega
    unfold numerator
    rw [ite_eq_right en,ite_eq_left he,e1,e2,e3,ep,hx,e]
    exact evenCenterStrict x
  · let x := k-1
    have hx : k=x+1 := by dsimp [x]; omega
    have e : b=2*x+3 := by omega
    have e1 : b-(k-1)-2=x+1 := by omega
    have e2 : b-k-2=x := by omega
    have e3 : b+2-k=x+4 := by omega
    have ep : k-1=x := rfl
    have en : b≠2*(k-1) := by omega
    unfold numerator
    rw [ite_eq_right en,ite_eq_right he,e1,e2,e3,ep,hx,e]
    exact oddCenterStrict x

theorem bfm_center_growth (b k : Nat) (hb : 3≤b) (hk : k=b/2) :
    bfmCoeff b (k-1)<bfmCoeff b k := by
  let D := (b:Int)*(b+1)
  let C := bfmCoeff b k
  let L := bfmCoeff b (k-1)
  let B := (choose (b+1) k:Int)
  let P := (choose (b+1) (k-1):Int)
  let N := (numerator b k:Int)
  let M := (numerator b (k-1):Int)
  let g := (b+2-k : Nat)
  have hc : D*C=B*N := bfm_left_scaled b k hb (by omega)
  have hp : D*L=P*M := bfm_left_scaled b (k-1) hb (by omega)
  have he : (g:Int)*P=(k:Int)*B := by
    have e := choose_ratio (b+1) (k-1)
    have ek : k-1+1=k := by omega
    have ea : b+1-(k-1)=g := by dsimp [g]; omega
    rw [ek,ea] at e
    have hi := congrArg (fun i : Nat=>(i:Int)) e.symm
    simpa only [Int.natCast_mul] using hi
  have hn : (k:Int)*M < (g:Int)*N := by
    have h := Int.ofNat_lt.mpr (numerator_center b k hb hk)
    simpa only [Int.natCast_mul] using h
  have eh : (g:Int)*D*(C-L)=B*((g:Int)*N-(k:Int)*M) := by grind
  have eb : 0<B := Int.ofNat_lt.mpr (choose_pos_of_le (by omega))
  have hpos : 0<B*((g:Int)*N-(k:Int)*M) := Int.mul_pos eb (by omega)
  have hleft : 0<(g:Int)*D*(C-L) := eh ▸ hpos
  have hg : 0<(g:Int) := by dsimp [g]; omega
  have hD : 0<D := Int.mul_pos (by omega) (by omega)
  have hfin := Int.pos_of_mul_pos_right hleft (Int.mul_pos hg hD)
  change L<C
  omega

theorem bfm_positive_left (b i : Nat) (hb : 3≤b) (hi : 2*i≤b) :
    0<bfmCoeff b i := by
  have he := bfm_left_scaled b i hb hi
  have hb' : 0<choose (b+1) i := choose_pos_of_le (by omega)
  have hf : 0<F i (b-i-2) b := by
    have hp : 0<b*(b+1)*(b-i-2+2) := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    unfold F
    omega
  have hn : 0<numerator b i := by unfold numerator; omega
  have hprod : 0<(choose (b+1) i:Int)*(numerator b i:Int) :=
    Int.mul_pos (Int.ofNat_lt.mpr hb') (Int.ofNat_lt.mpr hn)
  have hl : 0<((b:Int)*(b+1))*bfmCoeff b i := he ▸ hprod
  exact Int.pos_of_mul_pos_right hl (Int.mul_pos (by omega) (by omega))

theorem bfm_positive (b i : Nat) (hb : 3≤b) (hi : i≤b) : 0<bfmCoeff b i := by
  by_cases hl : 2*i≤b
  · exact bfm_positive_left b i hb hl
  · rw [bfm_symm b i hb hi]
    exact bfm_positive_left b (b-i) hb (by omega)

theorem bfm_lc_left (b k : Nat) (hb : 3≤b) (hk : 1≤k) (hl : 2*k≤b) :
    bfmCoeff b (k-1)*bfmCoeff b (k+1)<bfmCoeff b k*bfmCoeff b k := by
  by_cases he : 2*(k+1)≤b
  · exact bfm_minor_left b k hb hk he
  · have hc : k=b/2 := by omega
    have hm := bfm_center_growth b k hb hc
    have hm0 := bfm_positive b (k-1) hb (by omega)
    have hm1 := bfm_positive b k hb (by omega)
    rw [bfm_symm b (k+1) hb (by omega)]
    by_cases h : b=2*k
    · rw [show b-(k+1)=k-1 by omega]
      have h1 := Int.mul_lt_mul_of_pos_left hm hm0
      have h2 := Int.mul_lt_mul_of_pos_right hm hm1
      exact Int.lt_trans h1 h2
    · rw [show b-(k+1)=k by omega]
      exact Int.mul_lt_mul_of_pos_right hm hm1

theorem bfm_lc (b k : Nat) (hb : 3≤b) (hlo : 1≤k) (hhi : k<b) :
    bfmCoeff b (k-1)*bfmCoeff b (k+1)<bfmCoeff b k*bfmCoeff b k := by
  by_cases hl : 2*k≤b
  · exact bfm_lc_left b k hb hlo hl
  · have he := bfm_lc_left b (b-k) hb (by omega) (by omega)
    rw [bfm_symm b (k-1) hb (by omega),bfm_symm b (k+1) hb (by omega),
      bfm_symm b k hb (by omega),show b-(k-1)=(b-k)+1 by omega,
      show b-(k+1)=(b-k)-1 by omega,Int.mul_comm]
    exact he

theorem bfm_strict_and_positive :
    (∀ b i : Nat, 3≤b → i≤b → 0<bfmCoeff b i) ∧
    (∀ b k : Nat, 3≤b → 1≤k → k<b →
      bfmCoeff b (k-1)*bfmCoeff b (k+1)<bfmCoeff b k*bfmCoeff b k) :=
  ⟨bfm_positive,bfm_lc⟩

#print axioms bfm_symm
#print axioms bfm_strict_and_positive

theorem dent_quotient (m : Nat) : dent m=choose (2*m) m/(m+1) :=
  Nat.eq_div_of_mul_eq_right (by omega) (dent_mul m)

def timesOnePlus (f : Nat → Nat) (i : Nat) : Nat := f i+shift f i

def point (a i : Nat) : Nat := if i=a then 1 else 0

def oddTau (b : Nat) : Nat :=
  if b%2=1 then choose (2*(b/2)) (b/2)/(b/2+1) else 0

/-- Coefficient form of BFMN Proposition 4.2 specialized to the two cycles
of lengths 3 and b, keeping contraction and the two corrections separate. -/
def proposition42Coeff (b i : Nat) : Int :=
  let f := cycleRow (b-2)
  (cycleRow b i:Int) + (timesOnePlus (timesOnePlus f) i:Int)
    - (shift f i:Int) - (oddTau b:Int)*((point (b/2) i:Int)+(point (b/2+1) i:Int))

theorem shift_add (f g : Nat → Nat) (i : Nat) :
    shift (fun j=>f j+g j) i=shift f i+shift g i := by
  cases i <;> rfl

theorem proposition42Coeff_eq (b i : Nat) : proposition42Coeff b i=bfmCoeff b i := by
  have e : timesOnePlus (timesOnePlus (cycleRow (b-2))) i =
      convolve (cycleRow (b-2)) i+shift (cycleRow (b-2)) i := by
    have hs : shift (timesOnePlus (cycleRow (b-2))) i=
        shift (cycleRow (b-2)) i+shift (shift (cycleRow (b-2))) i :=
      shift_add _ _ _
    simp only [timesOnePlus,convolve,hs]
    omega
  unfold proposition42Coeff
  dsimp only
  rw [e]
  simp only [bfmCoeff,Int.natCast_add]
  have ec : (choose (2*(b/2)) (b/2)/(b/2+1):Nat) = dent (b/2) :=
    (dent_quotient _).symm
  by_cases hb : b%2=1
  · have ht : oddTau b=dent (b/2) := by simp [oddTau,hb,ec]
    rw [ht]
    by_cases he : i=b/2
    · have hn : i≠b/2+1 := by omega
      rw [ite_eq_left (And.intro hb (Or.inl he))]
      simp only [point,ite_eq_left he,ite_eq_right hn,Int.natCast_one,Int.natCast_zero,
        Int.add_zero,Int.mul_one]
      omega
    · by_cases hf : i=b/2+1
      · rw [ite_eq_left (And.intro hb (Or.inr hf))]
        simp only [point,ite_eq_left hf,ite_eq_right he,Int.natCast_one,Int.natCast_zero,
          Int.zero_add,Int.mul_one]
        omega
      · have hh : ¬(b%2=1 ∧ (i=b/2 ∨ i=b/2+1)) := fun h=>h.2.elim he hf
        rw [ite_eq_right hh]
        simp only [point,ite_eq_right he,ite_eq_right hf,Int.natCast_zero,Int.add_zero,
          Int.mul_zero,Int.sub_zero]
        omega
  · have hh : ¬(b%2=1 ∧ (i=b/2 ∨ i=b/2+1)) := fun h=>hb h.1
    rw [ite_eq_right hh]
    simp only [oddTau,ite_eq_right hb,Int.natCast_zero,Int.zero_mul,Int.sub_zero]
    omega

theorem proposition42_strict_and_positive :
    (∀ b i : Nat, 3≤b → i≤b → 0<proposition42Coeff b i) ∧
    (∀ b k : Nat, 3≤b → 1≤k → k<b →
      proposition42Coeff b (k-1)*proposition42Coeff b (k+1) <
      proposition42Coeff b k*proposition42Coeff b k) := by
  simpa only [proposition42Coeff_eq] using bfm_strict_and_positive

#print axioms dent_quotient
#print axioms proposition42Coeff_eq
#print axioms proposition42_strict_and_positive
end InverseZ.TriangleCycle


namespace InverseZ.RatioDefect

abbrev Row := Nat → Int

def conv (a b : Row) (k : Nat) : Int :=
  Nat.rec (fun a : Row => a 0*b 0)
    (fun j prev a => a 0*b (j+1)+prev (fun i => a (i+1))) k a

theorem conv_zero (a b : Row) : conv a b 0=a 0*b 0 := rfl

theorem conv_succ (a b : Row) (k : Nat) :
    conv a b (k+1)=a 0*b (k+1)+conv (fun j=>a (j+1)) b k := rfl

def later (a : Row) : Row := fun j=>a (j+1)
def forward (a : Row) : Row := fun j=>((j:Int)+1)*a (j+1)
def complement (d : Int) (a : Row) : Row := fun j=>(d-(j:Int))*a j
def scale (z : Int) (a : Row) : Row := fun j=>z*a j
def add (a b : Row) : Row := fun j=>a j+b j
def sub (a b : Row) : Row := fun j=>a j-b j
def err (d : Int) (a : Row) : Row := sub (forward a) (complement d a)

theorem conv_add_left (a b c : Row) (k : Nat) :
    conv (add a b) c k=conv a c k+conv b c k := by
  induction k generalizing a b with
  | zero => simp only [conv_zero,add,Int.add_mul]
  | succ k ih =>
    simp only [conv_succ,add,Int.add_mul]
    have h := ih (later a) (later b)
    unfold later add at h
    rw [h]
    omega

theorem conv_add_right (a b c : Row) (k : Nat) :
    conv a (add b c) k=conv a b k+conv a c k := by
  induction k generalizing a with
  | zero => simp only [conv_zero,add,Int.mul_add]
  | succ k ih =>
    simp only [conv_succ,add,Int.mul_add,ih]
    omega

theorem conv_sub_left (a b c : Row) (k : Nat) :
    conv (sub a b) c k=conv a c k-conv b c k := by
  induction k generalizing a b with
  | zero => simp only [conv_zero,sub,Int.sub_mul]
  | succ k ih =>
    simp only [conv_succ,sub,Int.sub_mul]
    have h := ih (later a) (later b)
    unfold later sub at h
    rw [h]
    omega

theorem conv_sub_right (a b c : Row) (k : Nat) :
    conv a (sub b c) k=conv a b k-conv a c k := by
  induction k generalizing a with
  | zero => simp only [conv_zero,sub,Int.mul_sub]
  | succ k ih =>
    simp only [conv_succ,sub,Int.mul_sub,ih]
    omega

theorem conv_scale_left (z : Int) (a b : Row) (k : Nat) :
    conv (scale z a) b k=z*conv a b k := by
  induction k generalizing a with
  | zero => simp only [conv_zero,scale,Int.mul_assoc]
  | succ k ih =>
    simp only [conv_succ,scale,Int.mul_assoc,Int.mul_add]
    have h := ih (later a)
    unfold later scale at h
    rw [h]

theorem conv_scale_right (z : Int) (a b : Row) (k : Nat) :
    conv a (scale z b) k=z*conv a b k := by
  induction k generalizing a with
  | zero =>
    simp only [conv_zero,scale]; ac_rfl
  | succ k ih =>
    simp only [conv_succ,scale,Int.mul_add,ih]
    rw [show a 0*(z*b (k+1))=z*(a 0*b (k+1)) by ac_rfl]

theorem conv_mono_left (a b c : Row) (k : Nat) (h : ∀ j, a j≤b j)
    (hc : ∀ j, 0≤c j) : conv a c k≤conv b c k := by
  induction k generalizing a b with
  | zero => exact Int.mul_le_mul_of_nonneg_right (h 0) (hc 0)
  | succ k ih =>
    simp only [conv_succ]
    exact Int.add_le_add (Int.mul_le_mul_of_nonneg_right (h 0) (hc (k+1)))
      (ih _ _ (fun j=>h (j+1)))

theorem conv_mono_right (a b c : Row) (k : Nat) (h : ∀ j, b j≤c j)
    (ha : ∀ j, 0≤a j) : conv a b k≤conv a c k := by
  induction k generalizing a with
  | zero => exact Int.mul_le_mul_of_nonneg_left (h 0) (ha 0)
  | succ k ih =>
    simp only [conv_succ]
    exact Int.add_le_add (Int.mul_le_mul_of_nonneg_left (h (k+1)) (ha 0))
      (ih _ (fun j=>ha (j+1)))

theorem derivative (a b : Row) (k : Nat) :
    ((k:Int)+1)*conv a b (k+1)=conv (forward a) b k+conv a (forward b) k := by
  induction k generalizing a with
  | zero => simp only [conv_zero,conv_succ,forward,Int.natCast_zero,Int.zero_add,Int.one_mul,Int.add_comm]
  | succ k ih =>
    have hh := ih (later a)
    have hF : (fun j=>forward a (j+1))=add (forward (later a)) (later (later a)) := by
      funext j
      simp only [forward,later,add,Int.natCast_succ]
      grind
    simp only [conv_succ,Int.natCast_succ]
    rw [hF,conv_add_left]
    change (((k:Int)+1)+1)*(a 0*b (k+2)+conv (later a) b (k+1)) =
      forward a 0*b (k+1)+
        (conv (forward (later a)) b k+conv (later (later a)) b k)+
        (a 0*forward b (k+1)+conv (later a) (forward b) k)
    rw [show conv (later a) b (k+1)=later a 0*b (k+1)+conv (later (later a)) b k from rfl] at hh
    rw [show conv (later a) b (k+1)=later a 0*b (k+1)+conv (later (later a)) b k from rfl]
    simp only [forward,later,Int.natCast_zero,Int.zero_add,Int.one_mul] at hh ⊢
    grind

theorem complement_conv (d e : Int) (a b : Row) (k : Nat) :
    conv (complement d a) b k+conv a (complement e b) k =
      (d+e-(k:Int))*conv a b k := by
  induction k generalizing d a with
  | zero =>
    simp only [conv_zero,complement,Int.natCast_zero,Int.sub_zero]
    grind
  | succ k ih =>
    have h : (fun j=>complement d a (j+1))=complement (d-1) (later a) := by
      funext j
      simp only [complement,later,Int.natCast_succ]
      grind
    simp only [conv_succ,Int.natCast_succ]
    rw [h]
    change complement d a 0*b (k+1)+conv (complement (d-1) (later a)) b k+
      (a 0*complement e b (k+1)+conv (later a) (complement e b) k) =
      (d+e-((k:Int)+1))*(a 0*b (k+1)+conv (later a) b k)
    have he := ih (d-1) (later a)
    simp only [complement,Int.natCast_zero,Int.sub_zero,Int.natCast_succ]
    grind

theorem error_conv (d e : Int) (a b : Row) (k : Nat) :
    err (d+e) (conv a b) k=conv (err d a) b k+conv a (err e b) k := by
  change ((k:Int)+1)*conv a b (k+1)-(d+e-(k:Int))*conv a b k =
    conv (sub (forward a) (complement d a)) b k+conv a (sub (forward b) (complement e b)) k
  have h1 := derivative a b k
  have h2 := complement_conv d e a b k
  rw [conv_sub_left,conv_sub_right]
  omega

#print axioms error_conv

def Nonneg (a : Row) : Prop := ∀ k, 0≤a k

def Window (d : Int) (a : Row) (L E : Int) : Prop :=
  ∀ k, -E*a k≤L*err d a k ∧ L*err d a k≤E*a k

def StrictWindow (d : Int) (a : Row) (L E : Int) : Prop :=
  ∀ k : Nat, (k:Int)<d → -E*a k<L*err d a k ∧ L*err d a k<E*a k

theorem window_rescale {d L E z : Int} {a : Row}
    (h : Window d a L E) (hz : 0≤z) : Window d a (z*L) (z*E) := by
  intro k
  obtain ⟨hlo,hhi⟩ := h k
  have h1 := Int.mul_le_mul_of_nonneg_left hlo hz
  have h2 := Int.mul_le_mul_of_nonneg_left hhi hz
  constructor <;> grind

theorem window_diag_widen {d L E : Int} {a : Row}
    (h : Window d a L E) (ha : Nonneg a) (hL : 0<L) (hEL : E≤L) : Window d a 1 1 := by
  intro k
  obtain ⟨hlo,hhi⟩ := h k
  have hh := ha k
  have h1 := Int.mul_le_mul_of_nonneg_right hEL hh
  have ha' : L* (-a k) ≤ L*err d a k := by grind
  have hb' : L*err d a k ≤L*a k := by grind
  have hlo' := Int.le_of_mul_le_mul_left ha' hL
  have hhi' := Int.le_of_mul_le_mul_left hb' hL
  simpa only [Int.neg_mul,Int.one_mul] using And.intro hlo' hhi'

theorem window_conv {d e L E F : Int} {a b : Row}
    (ha : Nonneg a) (hb : Nonneg b)
    (h1 : Window d a L E) (h2 : Window e b L F) : Window (d+e) (conv a b) L (E+F) := by
  intro k
  have lo1 := conv_mono_left (scale (-E) a) (scale L (err d a)) b k (fun j=>(h1 j).1) hb
  have hi1 := conv_mono_left (scale L (err d a)) (scale E a) b k (fun j=>(h1 j).2) hb
  have lo2 := conv_mono_right a (scale (-F) b) (scale L (err e b)) k (fun j=>(h2 j).1) ha
  have hi2 := conv_mono_right a (scale L (err e b)) (scale F b) k (fun j=>(h2 j).2) ha
  simp only [conv_scale_left,conv_scale_right] at lo1 hi1 lo2 hi2
  rw [error_conv]
  constructor <;> grind

theorem window_conv_distinct {d e L M E F : Int} {a b : Row}
    (ha : Nonneg a) (hb : Nonneg b) (hL : 0<L) (hM : 0<M)
    (h1 : Window d a L E) (h2 : Window e b M F) :
    Window (d+e) (conv a b) (L*M) (M*E+L*F) := by
  have ha' := window_rescale h1 (z:=M) (by omega)
  have hb' := window_rescale h2 (z:=L) (by omega)
  rw [Int.mul_comm M L] at ha'
  exact window_conv ha hb ha' hb'

theorem err_add (d : Int) (a b : Row) (k : Nat) :
    err d (add a b) k=err d a k+err d b k := by
  simp only [err,add,sub,forward,complement]
  grind

theorem err_scale (d z : Int) (a : Row) (k : Nat) :
    err d (scale z a) k=z*err d a k := by
  simp only [err,scale,sub,forward,complement]
  grind

theorem window_add {d L E : Int} {a b : Row} (ha : Window d a L E)
    (hb : Window d b L E) : Window d (add a b) L E := by
  intro k
  obtain ⟨ha1,ha2⟩ := ha k
  obtain ⟨hb1,hb2⟩ := hb k
  rw [err_add]
  simp only [add]
  constructor <;> grind

theorem strict_add {d L E : Int} {a b : Row} (ha : StrictWindow d a L E)
    (hb : Window d b L E) : StrictWindow d (add a b) L E := by
  intro k hk
  obtain ⟨ha1,ha2⟩ := ha k hk
  obtain ⟨hb1,hb2⟩ := hb k
  rw [err_add]
  simp only [add]
  constructor <;> grind

theorem strict_scale {d L E z : Int} {a : Row} (ha : StrictWindow d a L E)
    (hz : 0<z) : StrictWindow d (scale z a) L E := by
  intro k hk
  obtain ⟨h1,h2⟩ := ha k hk
  have h1' := Int.mul_lt_mul_of_pos_left h1 hz
  have h2' := Int.mul_lt_mul_of_pos_left h2 hz
  rw [err_scale]
  simp only [scale]
  constructor <;> grind

theorem strict_of_subunit {d L E : Int} {a : Row} (ha : Window d a L E)
    (hp : ∀ k : Nat, (k:Int)<d → 0<a k) (hL : 0<L) (he : E<L) :
      StrictWindow d a 1 1 := by
  intro k hk
  obtain ⟨hlo,hhi⟩ := ha k
  have h := Int.mul_lt_mul_of_pos_right he (hp k hk)
  have hlo' : L*(-a k)<L*err d a k := by grind
  have hhi' : L*err d a k<L*a k := by grind
  have hl := Int.lt_of_mul_lt_mul_left hlo' (show 0≤L by omega)
  have hh := Int.lt_of_mul_lt_mul_left hhi' (show 0≤L by omega)
  simpa only [Int.neg_mul,Int.one_mul] using And.intro hl hh

theorem strict_left_minor {d k : Nat} {a : Row}
    (hs : StrictWindow (d:Int) a 1 1) (hk : 0<k) (hh : k<d) (hleft : 2*k≤d)
    (ha : 0<a (k-1)) (hb : 0<a k) :
    a (k-1)*a (k+1)<a k*a k := by
  have h0 := (hs (k-1) (by omega)).1
  have h1 := (hs k (by omega)).2
  have hK : k-1+1=k := by omega
  have p : ((d:Int)-k)*a (k-1)<(k:Int)*a k := by
    simp only [err,sub,forward,complement,Int.neg_mul,Int.one_mul,hK] at h0
    have hh : ((k-1:Nat):Int)+1=(k:Int) := by omega
    have hg : (d:Int)-((k-1:Nat):Int)=((d:Int)-k)+1 := by omega
    rw [hh,hg,Int.add_mul,Int.one_mul] at h0
    omega
  have q : ((k:Int)+1)*a (k+1)<((d:Int)-k+1)*a k := by
    simp only [err,sub,forward,complement,Int.one_mul] at h1
    grind
  let k' := (k:Int)
  let g := (d:Int)-k'
  let A := a (k-1)
  let B := a k
  let C := a (k+1)
  have e0 : k'*(g+1)≤(k'+1)*g := by
    have e : k'≤g := by dsimp [k',g]; omega
    grind
  have e1 : (k'+1)*C < (g+1)*B := q
  have e2 : g*A < k'*B := p
  have hp : 0<k' := by dsimp [k']; omega
  have hp' : 0<k'+1 := by omega
  have aa : 0<A := ha
  have bb : 0<B := hb
  have hm : (k'*(k'+1))*(A*C)<(k'*(k'+1))*(B*B) := calc
    _ = (k'*A)*((k'+1)*C) := by ac_rfl
    _ < (k'*A)*((g+1)*B) := Int.mul_lt_mul_of_pos_left e1 (Int.mul_pos hp aa)
    _ = (k'*(g+1))*(A*B) := by ac_rfl
    _ ≤ ((k'+1)*g)*(A*B) := Int.mul_le_mul_of_nonneg_right e0
      (Int.le_of_lt (Int.mul_pos aa bb))
    _ = ((k'+1)*B)*(g*A) := by ac_rfl
    _ < ((k'+1)*B)*(k'*B) := Int.mul_lt_mul_of_pos_left e2 (Int.mul_pos hp' bb)
    _ = _ := by ac_rfl
  exact Int.lt_of_mul_lt_mul_left hm (Int.le_of_lt (Int.mul_pos hp hp'))

#print axioms window_conv_distinct
#print axioms strict_add
#print axioms strict_left_minor
end InverseZ.RatioDefect


namespace InverseZ.GluedCyclesResidual
open TriangleCycle

def w (r i : Nat) : Int :=
  (timesOnePlus (cycleRow r) i : Int) -
    if r%2=1 ∧ i=(r+1)/2 then 2*(dent ((r+1)/2):Int) else 0

def mulCoeff (p q : Nat → Int) (k : Nat) : Int :=
  ((List.range (k+1)).map (fun j=>p j*q (k-j))).sum

def twiceY (r s k : Nat) : Int :=
  2*(cycleRow (r+s+1) k:Int) +
    mulCoeff (w r) (fun i=>(cycleRow s i:Int)) k +
    mulCoeff (fun i=>(cycleRow r i:Int)) (w s) k

def residual : List (Nat×Nat) :=
  [(3,2),(3,3),(3,4),(3,5),(3,6),(3,7),(3,8),(2,5)]

def checks : Bool :=
  residual.all fun (r,s) =>
    (List.range (r+s+2)).all (fun k=>decide (0<twiceY r s k)) &&
    (List.range (r+s)).all (fun k=>decide (
      twiceY r s k*twiceY r s (k+2)<twiceY r s (k+1)*twiceY r s (k+1)))

set_option maxRecDepth 20000 in
theorem residual_checked : checks=true := by decide

#print axioms residual_checked
end InverseZ.GluedCyclesResidual

namespace InverseZ.GluedCycleBounds
open TriangleCycle RatioDefect

def A (r i : Nat) : Int := (cycleRow r i : Int)

def budgetA (r : Nat) : Int := (((r+1)/2+1 : Nat):Int)

theorem A_nonneg (r : Nat) : Nonneg (A r) := by
  intro i
  exact Int.natCast_nonneg _

theorem A_pos (r j : Nat) (hr : 1≤r) (hj : j≤r) : 0<A r j := by
  let i := min j (r-j)
  have hi : i≤r := by dsimp [i]; omega
  have h0 : i<r := by dsimp [i]; omega
  have hb := choose_pos_of_le (n:=r+1) (k:=i) (by omega)
  unfold A cycleRow
  rw [ite_eq_left hj]
  exact Int.ofNat_lt.mpr (Nat.mul_pos hb (by omega))

theorem err_actual (r i : Nat) (hi : 1≤i) :
    err (r:Int) (A r) (i-1)=(i:Int)*A r i-((r:Int)+1-i)*A r (i-1) := by
  have he : i-1+1=i := by omega
  have hf : ((i-1:Nat):Int)+1=(i:Int) := by omega
  have hg : (r:Int)-((i-1:Nat):Int)=(r:Int)+1-i := by omega
  simp only [err,sub,forward,complement,he,hf,hg]

theorem A_left_values (r i : Nat) (hi : 1≤i) (hl : 2*i≤r) :
    let u := (r:Int)+1-i
    let b := (choose (r+1) (i-1):Int)
    A r (i-1)=u*b ∧ (i:Int)*A r i=(u*u-1)*b := by
  have ha0 := cycle_raw r (i-1) (by omega)
  have ha1 := cycle_raw r i hl
  have he := congrArg (fun n : Nat => (n:Int)) (choose_ratio (r+1) (i-1))
  have e1 : i-1+1=i := by omega
  rw [e1] at he
  have hb : i-1≤r+1 := by omega
  have hR0 : i-1≤r := by omega
  have hR1 : i≤r := by omega
  simp only [Int.natCast_mul,Int.natCast_sub hb,Int.natCast_add,Int.natCast_one] at he
  have eq : ((i-1:Nat):Int)=(i:Int)-1 := by omega
  rw [eq] at he
  dsimp
  simp only [A,ha0,ha1,raw,Int.natCast_mul,Int.natCast_sub hR0,Int.natCast_sub hR1,eq]
  constructor <;> grind

theorem A_left_window (r i : Nat) (hi : 1≤i) (hl : 2*i≤r) :
    -(A r (i-1))≤budgetA r*err (r:Int) (A r) (i-1) ∧
      budgetA r*err (r:Int) (A r) (i-1)≤A r (i-1) := by
  let u := (r:Int)+1-i
  let b := (choose (r+1) (i-1):Int)
  have ha : A r (i-1)=u*b := (A_left_values r i hi hl).1
  have hb : (i:Int)*A r i=(u*u-1)*b := (A_left_values r i hi hl).2
  have hv : err (r:Int) (A r) (i-1)= -b := by
    rw [err_actual r i hi]
    change (i:Int)*A r i-u*A r (i-1)=_
    rw [ha,hb]
    grind
  have hL : budgetA r≤u := by unfold budgetA; dsimp [u]; omega
  have hpos : 0≤budgetA r := by unfold budgetA; omega
  have hb0 : 0≤b := Int.natCast_nonneg _
  have hh := Int.mul_le_mul_of_nonneg_right hL hb0
  have hp := Int.mul_nonneg hpos hb0
  have hq : 0≤A r (i-1) := A_nonneg r _
  rw [hv]
  constructor <;> grind

theorem A_right_window (r i : Nat) (hi : 1≤i) (hj : i≤r) (hl : 2*(r+1-i)≤r) :
    -(A r (i-1))≤budgetA r*err (r:Int) (A r) (i-1) ∧
      budgetA r*err (r:Int) (A r) (i-1)≤A r (i-1) := by
  let j := r+1-i
  let u := (r:Int)+1-j
  let b := (choose (r+1) (j-1):Int)
  have hj0 : 1≤j := by dsimp [j]; omega
  have ha : A r (j-1)=u*b := (A_left_values r j hj0 hl).1
  have hb : (j:Int)*A r j=(u*u-1)*b := (A_left_values r j hj0 hl).2
  have a0 : A r i=A r (j-1) := by
    unfold A
    rw [cycleRow_symm r i hj,show r-i=j-1 by dsimp [j]; omega]
  have a1 : A r (i-1)=A r j := by
    unfold A
    rw [cycleRow_symm r (i-1) (by omega),show r-(i-1)=j by dsimp [j]; omega]
  have eu : u=(i:Int) := by dsimp [j,u]; omega
  have ej : (r:Int)+1-i=(j:Int) := by dsimp [j]; omega
  have hv : err (r:Int) (A r) (i-1)=b := by
    rw [err_actual r i hi,a0,a1,ej,←eu,ha,hb]
    grind
  have hL : budgetA r≤u := by unfold budgetA; dsimp [u,j]; omega
  have hu : 1≤u := by dsimp [u,j]; omega
  have hju : (j:Int)≤u-1 := by dsimp [j,u]; omega
  have hb0 : 0≤b := Int.natCast_nonneg _
  have h1 := Int.mul_le_mul_of_nonneg_right hL hb0
  have hh : u*b≤A r j := by
    have hJ : 0<(j:Int) := by omega
    have h2 := Int.mul_le_mul_of_nonneg_right hju (show 0≤u by omega)
    have hc : (j:Int)*u≤u*u-1 := by grind
    have hh1 := Int.mul_le_mul_of_nonneg_right hc hb0
    have hh2 : (j:Int)*(u*b)≤(j:Int)*A r j := by grind
    exact Int.le_of_mul_le_mul_left hh2 hJ
  have hpos : 0≤budgetA r := by unfold budgetA; omega
  have h2 := Int.mul_nonneg hpos hb0
  have h3 : 0≤A r (i-1) := A_nonneg r _
  rw [hv,a1]
  constructor
  · have h3' := A_nonneg r j
    omega
  · exact Int.le_trans h1 hh

theorem A_window (r : Nat) : Window (r:Int) (A r) (budgetA r) 1 := by
  intro k
  let i := k+1
  have ie : i-1=k := rfl
  have hi : 1≤i := by dsimp [i]; omega
  simp only [Int.neg_mul,Int.one_mul]
  by_cases inrange : i≤r
  · by_cases hl : 2*i≤r
    · simpa only [ie] using A_left_window r i hi hl
    · by_cases hr : 2*(r+1-i)≤r
      · simpa only [ie] using A_right_window r i hi inrange hr
      · have he : r=2*i-1 := by omega
        have h0 : A r i=A r (i-1) := by
          unfold A
          rw [cycleRow_symm r i inrange,show r-i=i-1 by omega]
        have h1 : err (r:Int) (A r) k=0 := by
          rw [←ie,err_actual r i hi,h0,show (r:Int)+1-i=(i:Int) by omega]
          omega
        have h2 := A_nonneg r k
        rw [h1,Int.mul_zero]
        omega
  · have h0 : A r i=0 := by unfold A cycleRow; simp [inrange]
    have h1 : err (r:Int) (A r) k=0 := by
      rw [←ie,err_actual r i hi,h0,Int.mul_zero]
      by_cases ha : i=r+1
      · rw [show (r:Int)+1-i=0 by omega]
        simp
      · have hb : A r (i-1)=0 := by unfold A cycleRow; simp [show ¬i-1≤r by omega]
        simp [hb]
    have hp := A_nonneg r k
    rw [h1,Int.mul_zero]
    omega

#print axioms A_window

def U : Row := fun j=> if j=0 ∨ j=1 then 1 else 0

theorem U_zeroLater : later (later U)=fun _=>0 := by
  funext j
  unfold later U
  simp

theorem conv_zero_left (b : Row) (k : Nat) :
    conv (fun _=>0) b k=0 := by
  induction k with
  | zero => simp [conv_zero]
  | succ k ih => simp [conv_succ,ih]

theorem U_window (L : Int) : Window 1 U L 0 := by
  intro k
  have h : err 1 U k=0 := by
    cases k with
    | zero => decide
    | succ k =>
      cases k with
      | zero => decide
      | succ k =>
        simp [err,sub,forward,complement,U]
  simp [h]

def W0 (r i : Nat) : Int := (timesOnePlus (cycleRow r) i:Int)

theorem U_conv (r : Nat) : conv U (A r)=W0 r := by
  funext k
  cases k with
  | zero => simp [conv_zero,U,A,W0,timesOnePlus,shift]
  | succ k =>
    cases k with
    | zero => simp [conv_zero,conv_succ,U,A,W0,timesOnePlus,shift,Int.natCast_add,Int.add_comm]
    | succ k =>
      have h : (fun j : Nat=>U (j+1+1))=(fun _=>0) := U_zeroLater
      unfold W0 timesOnePlus
      simp only [conv_succ,h,conv_zero_left,shift,Int.natCast_add]
      simp [U,A,Int.add_comm]

theorem W0_window (r : Nat) : Window ((r:Int)+1) (W0 r) (budgetA r) 1 := by
  have h : Nonneg U := by intro k; unfold U; split <;> omega
  have e := window_conv h (A_nonneg r) (U_window (budgetA r)) (A_window r)
  rw [U_conv] at e
  rw [Int.add_comm 1 (r:Int),Int.zero_add] at e
  exact e

theorem W0_succ (r j : Nat) :
    W0 r (j+1)=A r (j+1)+A r j := by
  simp [W0,A,timesOnePlus,shift,Int.natCast_add]

theorem w_odd (m i : Nat) (hm : 1≤m) :
    GluedCyclesResidual.w (2*m-1) i=W0 (2*m-1) i -
      if i=m then 2*(dent m:Int) else 0 := by
  have h : (2*m-1)%2=1 := by omega
  have he : (2*m-1+1)/2=m := by omega
  simp [GluedCyclesResidual.w,W0,h,he]

theorem X_val (m : Nat) (hm : 2≤m) :
    A (2*m-1) (m-1)=(m:Int)*m*(dent m:Int) := by
  have h := cycle_raw (2*m-1) (m-1) (by omega)
  have e0 : 2*m-1+1=2*m := by omega
  have e1 : 2*m-1-(m-1)=m := by omega
  have he : choose (2*m) (m-1)=choose (2*m) (m+1) := by
    have e : 2*m-(m+1)=m-1 := by omega
    have h' := choose_reflect (2*m) (m+1) (by omega)
    simpa only [e] using h'
  have hh := dent_mul m
  have hr := dent_relation m
  have hc : choose (2*m) (m+1)=m*dent m := by
    unfold dent at *
    have hle : choose (2*m) (m+1)≤choose (2*m) m := by
      by_cases h : choose (2*m) (m+1)≤choose (2*m) m
      · exact h
      · have ha := Nat.mul_le_mul_left m (show choose (2*m) m≤choose (2*m) (m+1) by omega)
        omega
    have hz := Nat.sub_add_cancel hle
    grind
  simp only [A,h,raw,e0,e1,he,hc,Int.natCast_mul]
  grind

theorem w_center_values (m : Nat) (hm : 2≤m) :
    let r := 2*m-1
    let C := 2*(m:Int)*m+2*m-1
    let D := (dent m:Int)
    let prev := GluedCyclesResidual.w r (m-1)
    let mid := GluedCyclesResidual.w r m
    let next := GluedCyclesResidual.w r (m+1)
    ((m:Int)+2)*prev=(m:Int)*D*C ∧ mid=2*((m:Int)*m-1)*D ∧ next=prev := by
  let r := 2*m-1
  let x := A r (m-1)
  let u := A r (m-2)
  let D := (dent m:Int)
  have hX : x=(m:Int)*m*D := X_val m hm
  have he : A r m=x := by
    unfold A x
    rw [cycleRow_symm r m (by dsimp [r]; omega),show r-m=m-1 by dsimp [r]; omega]
    rfl
  have hf : A r (m+1)=u := by
    unfold A u
    rw [cycleRow_symm r (m+1) (by dsimp [r]; omega),show r-(m+1)=m-2 by dsimp [r]; omega]
    rfl
  have hv := A_left_values r (m-1) (by omega) (by dsimp [r]; omega)
  have hy : ((r:Int)+1-((m-1:Nat):Int))=(m:Int)+1 := by dsimp [r]; omega
  simp only [show m-1-1=m-2 by omega,show ((m-1:Nat):Int)=(m:Int)-1 by omega] at hv
  have hU : ((m:Int)+2)*u=((m:Int)-1)*((m:Int)+1)*(m:Int)*D := by
    unfold x at hX
    obtain ⟨h0,h1⟩ := hv
    change u=_ at h0
    change ((m:Int)-1)*x=_ at h1
    have hmult : (m:Int)*(((m:Int)+2)*u) =
        (m:Int)*(((m:Int)-1)*((m:Int)+1)*(m:Int)*D) := by
      have hX' : x=(m:Int)*m*D := hX
      grind
    exact Int.eq_of_mul_eq_mul_left (by omega) hmult
  have w0 : GluedCyclesResidual.w r (m-1)=x+u := by
    rw [w_odd m (m-1) (by omega),ite_eq_right (show m-1≠m by omega),Int.sub_zero]
    rw [show m-1=(m-2)+1 by omega,W0_succ,show m-2+1=m-1 by omega]
  have w1 : GluedCyclesResidual.w r m=2*x-2*D := by
    rw [w_odd m m (by omega),ite_eq_left rfl]
    have h := W0_succ r (m-1)
    rw [show m-1+1=m by omega,he] at h
    rw [h]
    change x+x-2*D=_
    omega
  have w2 : GluedCyclesResidual.w r (m+1)=x+u := by
    rw [w_odd m (m+1) (by omega),ite_eq_right (by omega),Int.sub_zero,W0_succ,hf,he]
    omega
  dsimp
  change ((m:Int)+2)*GluedCyclesResidual.w r (m-1)=_ ∧
    GluedCyclesResidual.w r m=_ ∧ GluedCyclesResidual.w r (m+1)=GluedCyclesResidual.w r (m-1)
  rw [w0,w1,w2]
  constructor
  · have hX' : x=(m:Int)*m*D := hX
    grind
  · constructor
    · have hX' : x=(m:Int)*m*D := hX
      grind
    · rfl


theorem W0_nonneg (r : Nat) : Nonneg (W0 r) := by
  intro i
  exact Int.natCast_nonneg _

theorem w_even (r : Nat) (hr : r%2=0) : GluedCyclesResidual.w r=W0 r := by
  funext i
  have he : ¬(r%2=1 ∧ i=(r+1)/2) := by omega
  simp [GluedCyclesResidual.w,W0,he]

theorem w_odd_off (m i : Nat) (hm : 1≤m) (hi : i≠m) :
    GluedCyclesResidual.w (2*m-1) i=W0 (2*m-1) i := by
  rw [w_odd m i hm,ite_eq_right hi,Int.sub_zero]

theorem center_window (m : Nat) (hm : 2≤m) :
    let r := 2*m-1
    let C := 2*(m:Int)*m+2*m-1
    let E := 3*((m:Int)+1)
    let w := GluedCyclesResidual.w r
    C*err ((r:Int)+1) w (m-1)= -E*w (m-1) ∧
    C*err ((r:Int)+1) w m=E*w (m-1) ∧ w (m-1)≤w m ∧ 0≤w m := by
  let r := 2*m-1
  let C := 2*(m:Int)*m+2*m-1
  let E := 3*((m:Int)+1)
  let w := GluedCyclesResidual.w r
  let D := (dent m:Int)
  let A := w (m-1)
  let B := w m
  have h := w_center_values m hm
  change ((m:Int)+2)*A=(m:Int)*D*C ∧ B=2*((m:Int)*m-1)*D ∧ w (m+1)=A at h
  obtain ⟨hA,hB,hC⟩ := h
  have er : (r:Int)+1=2*(m:Int) := by dsimp [r]; omega
  have ei : ((m-1:Nat):Int)+1=(m:Int) := by omega
  have em : (2*(m:Int))-((m-1:Nat):Int)=(m:Int)+1 := by omega
  have e1 : err ((r:Int)+1) w (m-1) = (m:Int)*B-((m:Int)+1)*A := by
    simp only [err,sub,forward,complement,er,ei,em,show m-1+1=m by omega]
    rfl
  have e2 : err ((r:Int)+1) w m = ((m:Int)+1)*A-(m:Int)*B := by
    simp only [err,sub,forward,complement,er,hC,show 2*(m:Int)-m=(m:Int) by omega]
    rfl
  have ed : (m:Int)+2≠0 := by omega
  have hEq : C*((m:Int)*B-((m:Int)+1)*A) = -E*A := by
    apply Int.eq_of_mul_eq_mul_left ed
    dsimp only [C,E] at *
    grind
  have hmZ : 2≤(m:Int) := by omega
  have hSq := Int.mul_le_mul_of_nonneg_right hmZ (show 0≤(m:Int) by omega)
  have h0 : 0≤(m:Int)*m-1 := by omega
  have hB0 : 0≤B := by
    rw [hB]
    exact Int.mul_nonneg (Int.mul_nonneg (by decide) h0) (Int.natCast_nonneg _)
  have hp : 0≤2*(m:Int)*m-m-4 := by
    rw [show 2*(m:Int)*m=2*((m:Int)*m) by ac_rfl]
    omega
  have hG : A≤B := by
    have he : ((m:Int)+2)*(B-A)=D*(2*(m:Int)*m-m-4) := by
      dsimp only [C] at *
      grind
    have hx : 0≤D*(2*(m:Int)*m-m-4) := Int.mul_nonneg (Int.natCast_nonneg _) hp
    have hh : 0≤((m:Int)+2)*(B-A) := he ▸ hx
    have hg : 0≤B-A := Int.nonneg_of_mul_nonneg_right hh (by omega)
    omega
  change C*err ((r:Int)+1) w (m-1)= -E*A ∧
    C*err ((r:Int)+1) w m=E*A ∧ A≤B ∧ 0≤B
  rw [e1,e2,hEq]
  exact ⟨rfl,by grind,hG,hB0⟩

theorem rebudget {d L E M F : Int} {a : Row}
    (h : Window d a L E) (ha : Nonneg a) (hL : 0<L) (hM : 0≤M) (hEF : M*E≤L*F) :
    Window d a M F := by
  intro k
  obtain ⟨p,q⟩ := h k
  have hp := Int.mul_le_mul_of_nonneg_left p hM
  have hq := Int.mul_le_mul_of_nonneg_left q hM
  have hh := Int.mul_le_mul_of_nonneg_right hEF (ha k)
  have he1 : L*(-F*a k)≤L*(M*err d a k) := by grind
  have he2 : L*(M*err d a k)≤L*(F*a k) := by grind
  exact ⟨Int.le_of_mul_le_mul_left he1 hL,Int.le_of_mul_le_mul_left he2 hL⟩

theorem w_odd_window (m : Nat) (hm : 2≤m) :
    Window (2*(m:Int)) (GluedCyclesResidual.w (2*m-1))
      (2*(m:Int)*m+2*m-1) (3*((m:Int)+1)) := by
  let r := 2*m-1
  let C := 2*(m:Int)*m+2*m-1
  let E := 3*((m:Int)+1)
  let w := GluedCyclesResidual.w r
  have er : (r:Int)+1=2*(m:Int) := by dsimp [r]; omega
  have h := center_window m hm
  change C*err ((r:Int)+1) w (m-1)= -E*w (m-1) ∧
    C*err ((r:Int)+1) w m=E*w (m-1) ∧ w (m-1)≤w m ∧ 0≤w m at h
  obtain ⟨hp,hq,hgrow,hmid⟩ := h
  rw [er] at hp hq
  have hE : 0≤E := by dsimp [E]; omega
  have hprev : 0≤w (m-1) := by
    have he := w_odd_off m (m-1) (by omega) (by omega)
    change w (m-1)=W0 r (m-1) at he
    rw [he]
    exact W0_nonneg _ _
  intro k
  change -E*w k≤C*err (2*(m:Int)) w k ∧ C*err (2*(m:Int)) w k≤E*w k
  by_cases hk : k=m-1
  · subst k
    rw [hp]
    have he := Int.mul_nonneg hE hprev
    constructor <;> grind
  · by_cases hk' : k=m
    · subst k
      rw [hq]
      have he := Int.mul_le_mul_of_nonneg_left hgrow hE
      have hf := Int.mul_nonneg hE hmid
      have hg := Int.mul_nonneg hE hprev
      constructor <;> grind
    · have h1 : w k=W0 r k := w_odd_off m k (by omega) hk'
      have h2 : w (k+1)=W0 r (k+1) := w_odd_off m (k+1) (by omega) (by omega)
      have herr : err (2*(m:Int)) w k=err (2*(m:Int)) (W0 r) k := by
        simp only [err,sub,forward,complement,h1,h2]
      rw [h1,herr,←er]
      have L : budgetA r=(m:Int)+1 := by unfold budgetA; dsimp [r]; omega
      have he : C*1≤budgetA r*E := by
        rw [L]
        dsimp [C,E]
        have h0 : 0≤(m:Int)*(m:Int) := Int.mul_nonneg (by omega) (by omega)
        grind
      have hh := rebudget (W0_window r) (W0_nonneg r)
        (show 0<budgetA r by rw [L]; omega)
        (show 0≤C by dsimp [C]; have h0 := Int.mul_nonneg (show 0≤(m:Int) by omega) (show 0≤(m:Int) by omega); grind)
        he
      exact hh k

#print axioms center_window
#print axioms w_odd_window
end InverseZ.GluedCycleBounds



namespace InverseZ.GluedCycleBounds
open TriangleCycle RatioDefect GluedCyclesResidual

def scaleW (r : Nat) : Int :=
  if r%2=0 then budgetA r else let m := ((r+1)/2:Nat); 2*(m:Int)*m+2*m-1

def errorW (r : Nat) : Int :=
  if r%2=0 then 1 else 3*(((r+1)/2:Nat):Int)+3

theorem w_nonneg (r : Nat) (hr : 2≤r) : Nonneg (w r) := by
  by_cases he : r%2=0
  · rw [w_even r he]
    exact W0_nonneg r
  · let m := (r+1)/2
    have hm : 2≤m := by dsimp [m]; omega
    have eq : r=2*m-1 := by dsimp [m]; omega
    intro k
    by_cases hk : k=m
    · subst k
      have h := (center_window m hm).2.2.2
      rw [←eq] at h
      exact h
    · have h := w_odd_off m k (by omega) hk
      rw [←eq] at h
      rw [h]
      exact W0_nonneg _ _

theorem w_window (r : Nat) (hr : 2≤r) :
    Window ((r:Int)+1) (w r) (scaleW r) (errorW r) := by
  by_cases he : r%2=0
  · rw [scaleW,errorW,ite_eq_left he,ite_eq_left he,w_even r he]
    exact W0_window r
  · let m := (r+1)/2
    have hm : 2≤m := by dsimp [m]; omega
    have eq : r=2*m-1 := by dsimp [m]; omega
    have b : (r:Int)+1=2*(m:Int) := by dsimp [m]; omega
    unfold scaleW errorW
    rw [ite_eq_right he,ite_eq_right he,b]
    have ec : 3*(m:Int)+3=3*((m:Int)+1) := by omega
    change Window (2*(m:Int)) (w r) (2*(m:Int)*m+2*m-1) (3*(m:Int)+3)
    rw [ec]
    have h := w_odd_window m hm
    rw [←eq] at h
    exact h

theorem scaleW_pos (r : Nat) (hr : 2≤r) : 0<scaleW r := by
  unfold scaleW
  by_cases h : r%2=0
  · simp [h,budgetA]; omega
  · rw [ite_eq_right h]
    let m := ((r+1)/2:Nat)
    have h0 : 2≤(m:Int) := by dsimp [m]; omega
    have hh := Int.mul_le_mul_of_nonneg_right h0 (show 0≤(m:Int) by omega)
    change 0<2*(m:Int)*m+2*m-1
    rw [show 2*(m:Int)*m=2*((m:Int)*m) by ac_rfl]
    omega

theorem budgetA_pos (r : Nat) : 0<budgetA r := by
  unfold budgetA
  omega

theorem conv_nonneg {a b : Row} (ha : Nonneg a) (hb : Nonneg b) :
    Nonneg (conv a b) := by
  intro k
  induction k generalizing a with
  | zero => exact Int.mul_nonneg (ha 0) (hb 0)
  | succ k ih =>
    simp only [conv_succ]
    exact Int.add_nonneg (Int.mul_nonneg (ha 0) (hb (k+1)))
      (ih (a:=later a) (fun j=>ha (j+1)))

def built (r s : Nat) : Row :=
  add (add (scale 2 (A (r+s+1))) (conv (w r) (A s))) (conv (A r) (w s))

theorem built_positive (r s i : Nat) (hr : 2≤r) (hs : 2≤s) (hi : i≤r+s+1) :
    0<built r s i := by
  have h0 := A_pos (r+s+1) i (by omega) hi
  have h1 := conv_nonneg (w_nonneg r hr) (A_nonneg s) i
  have h2 := conv_nonneg (A_nonneg r) (w_nonneg s hs) i
  unfold built add scale
  omega

def BudgetOK (r s : Nat) : Prop := errorW r*budgetA s+scaleW r≤scaleW r*budgetA s

theorem built_strict_window (r s : Nat) (hr : 2≤r) (hs : 2≤s)
    (hRS : BudgetOK r s) (hSR : BudgetOK s r) :
    StrictWindow ((r+s+1:Nat):Int) (built r s) 1 1 := by
  have hA : StrictWindow ((r+s+1:Nat):Int) (A (r+s+1)) 1 1 :=
    strict_of_subunit (A_window _) (fun k hk=>A_pos _ _ (by omega) (by omega))
      (budgetA_pos _) (by unfold budgetA; omega)
  have hA' := strict_scale hA (show (0:Int)<2 by decide)
  have hWS := window_conv_distinct (w_nonneg r hr) (A_nonneg s) (scaleW_pos r hr)
      (budgetA_pos s) (w_window r hr) (A_window s)
  have hAW := window_conv_distinct (A_nonneg r) (w_nonneg s hs) (budgetA_pos r)
      (scaleW_pos s hs) (A_window r) (w_window s hs)
  have hO : Window ((r+s+1:Nat):Int) (conv (w r) (A s)) 1 1 := by
    have he : budgetA s*errorW r+scaleW r*1≤scaleW r*budgetA s := by
      unfold BudgetOK at hRS
      rw [Int.mul_comm (budgetA s) (errorW r),Int.mul_one]
      exact hRS
    have hw := window_diag_widen hWS (conv_nonneg (w_nonneg r hr) (A_nonneg s))
      (Int.mul_pos (scaleW_pos r hr) (budgetA_pos s)) he
    rwa [show (r:Int)+1+s=((r+s+1:Nat):Int) by omega] at hw
  have hP : Window ((r+s+1:Nat):Int) (conv (A r) (w s)) 1 1 := by
    have he : scaleW s*1+budgetA r*errorW s≤budgetA r*scaleW s := by
      unfold BudgetOK at hSR
      rw [Int.mul_comm (budgetA r) (errorW s),Int.mul_comm (budgetA r) (scaleW s),
        Int.mul_one,Int.add_comm]
      exact hSR
    have hw := window_diag_widen hAW (conv_nonneg (A_nonneg r) (w_nonneg s hs))
      (Int.mul_pos (budgetA_pos r) (scaleW_pos s hs)) he
    rwa [show (r:Int)+((s:Int)+1)=((r+s+1:Nat):Int) by omega] at hw
  exact strict_add (strict_add hA' hO) hP

theorem built_left_minor (r s k : Nat) (hr : 2≤r) (hs : 2≤s)
    (hRS : BudgetOK r s) (hSR : BudgetOK s r) (hk : 1≤k) (hleft : 2*k≤r+s+1) :
      built r s (k-1)*built r s (k+1)<built r s k*built r s k :=
  strict_left_minor (built_strict_window r s hr hs hRS hSR) (by omega) (by omega) hleft
    (built_positive r s (k-1) hr hs (by omega)) (built_positive r s k hr hs (by omega))

#print axioms built_left_minor

theorem budget_from_half (C E L : Int) (hE : 0≤E) (hC : 2*E≤C) (hL : 2≤L) :
    E*L+C≤C*L := by
  have h := Int.mul_le_mul_of_nonneg_left hL (show 0≤C-E by omega)
  grind

theorem budgetA_ge_two (r : Nat) (hr : 2≤r) : 2≤budgetA r := by unfold budgetA; omega

theorem budgetOK (r s : Nat) (hr : 2≤r) (hs : 2≤s)
    (h3 : r=3 → 9≤s) (h5 : r=5 → 3≤s) : BudgetOK r s := by
  have hL := budgetA_ge_two s hs
  unfold BudgetOK
  by_cases he : r%2=0
  · rw [errorW,scaleW,ite_eq_left he,ite_eq_left he]
    exact budget_from_half (budgetA r) 1 (budgetA s) (by decide) (budgetA_ge_two r hr) hL
  · by_cases hR : r=3
    · subst r
      have h : 6≤budgetA s := by unfold budgetA; have hh := h3 rfl; omega
      have hE : errorW 3=9 := by decide
      have hC : scaleW 3=11 := by decide
      rw [hE,hC]
      omega
    · by_cases hR' : r=5
      · subst r
        have h : 3≤budgetA s := by unfold budgetA; have hh := h5 rfl; omega
        have hE : errorW 5=12 := by decide
        have hC : scaleW 5=23 := by decide
        rw [hE,hC]
        omega
      · let m := (r+1)/2
        have hm : 4≤(m:Int) := by dsimp [m]; omega
        have hm0 : 0≤(m:Int) := by omega
        have hx := Int.mul_le_mul_of_nonneg_right hm hm0
        rw [errorW,scaleW,ite_eq_right he,ite_eq_right he]
        change (3*(m:Int)+3)*budgetA s+
            (2*(m:Int)*m+2*m-1)≤(2*(m:Int)*m+2*m-1)*budgetA s
        apply budget_from_half _ _ _ (by omega) _ hL
        rw [show 2*(m:Int)*m=2*((m:Int)*m) by ac_rfl]
        omega

#print axioms budgetOK
end InverseZ.GluedCycleBounds


namespace InverseZ.GluedCycleBounds
open TriangleCycle RatioDefect GluedCyclesResidual

theorem conv_eq_list (a b : Row) (k : Nat) : conv a b k=mulCoeff a b k := by
  induction k generalizing a with
  | zero => simp [conv_zero,mulCoeff]
  | succ k ih =>
    change a 0*b (k+1)+conv (later a) b k=mulCoeff a b (k+1)
    rw [ih]
    unfold mulCoeff
    rw [List.range_succ_eq_map (n:=k+1),List.map_cons,List.sum_cons,List.map_map]
    simp only [Nat.sub_zero]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro j hj
    change a (j+1)*b (k-j)=a (j+1)*b (k+1-(j+1))
    rw [show k+1-(j+1)=k-j by omega]

theorem conv_succ_right (a b : Row) (k : Nat) :
    conv a b (k+1)=conv a (later b) k+a (k+1)*b 0 := by
  induction k generalizing a with
  | zero => simp [conv_zero,conv_succ,later]
  | succ k ih =>
    change a 0*b (k+2)+conv (later a) b (k+1)=
      a 0*b (k+2)+conv (later a) (later b) k+a (k+2)*b 0
    rw [ih (later a)]
    unfold later
    rw [show k+1+1=k+2 by omega]
    omega

theorem conv_comm (a b : Row) (k : Nat) : conv a b k=conv b a k := by
  induction k generalizing a b with
  | zero => simp [conv_zero,Int.mul_comm]
  | succ k ih =>
    rw [conv_succ_right b a k]
    change a 0*b (k+1)+conv (later a) b k=
      conv b (later a) k+b (k+1)*a 0
    rw [ih (later a) b,Int.mul_comm (a 0) (b (k+1)),Int.add_comm]

def ZeroAfter (d : Nat) (a : Row) : Prop := ∀ i, d<i → a i=0

def Symmetric (d : Nat) (a : Row) : Prop := ∀ i, i≤d → a i=a (d-i)

def sprefix (f : Row) (k : Nat) : Int := ((List.range k).map f).sum

theorem prefix_step (f : Row) (k : Nat) :
    sprefix f (k+1)=sprefix f k+f k := by
  simp [sprefix,List.range_succ,List.map_append,List.sum_append]

theorem prefix_stable (f : Row) (k n : Nat) (hk : k≤n)
    (h : ∀ j, k≤j → f j=0) : sprefix f n=sprefix f k := by
  induction n with
  | zero =>
    have e : k=0 := by omega
    subst k
    rfl
  | succ n ih =>
    by_cases he : k=n+1
    · rw [he]
    · rw [prefix_step,ih (by omega),h n (by omega),Int.add_zero]

theorem prefix_reverse (f : Row) (d : Nat) :
    sprefix f (d+1)=sprefix (fun j=>f (d-j)) (d+1) := by
  unfold sprefix
  rw [←List.sum_reverse_int ((List.range (d+1)).map f)]
  have h : (List.range (d+1)).reverse=(List.range (d+1)).map (fun j=>d-j) := by
    calc
      _ = (List.range' 0 (d+1)).reverse := congrArg List.reverse List.range_eq_range'
      _ = _ := by simpa using (List.reverse_range' (s:=0) (n:=d+1))
  rw [←List.map_reverse,h,List.map_map]
  rfl

def column (a b : Row) (k i : Nat) : Int :=
  if i≤k then a i*b (k-i) else 0

theorem conv_prefix (d : Nat) (a b : Row) (ha : ZeroAfter d a) (k : Nat) :
    conv a b k=sprefix (column a b k) (d+1) := by
  rw [conv_eq_list]
  have h : mulCoeff a b k=sprefix (column a b k) (k+1) := by
    unfold mulCoeff sprefix
    apply congrArg List.sum
    apply List.map_congr_left
    intro j hj
    have h := List.mem_range.mp hj
    simp [column,show j≤k by omega]
  rw [h]
  by_cases hle : d≤k
  · apply prefix_stable _ _ _ (by omega)
    intro j hj
    simp [column,ha j (by omega)]
  · symm
    apply prefix_stable _ _ _ (by omega)
    intro j hj
    simp [column,show ¬j≤k by omega]

theorem conv_symm (d e : Nat) (a b : Row)
    (ha : ZeroAfter d a) (hb : ZeroAfter e b)
    (sa : Symmetric d a) (sb : Symmetric e b) : Symmetric (d+e) (conv a b) := by
  intro k hk
  rw [conv_prefix d a b ha k,conv_prefix d a b ha (d+e-k),
    prefix_reverse (column a b k) d]
  unfold sprefix
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  have hj' : j≤d := by have h:= List.mem_range.mp hj; omega
  have he0 : d-(d-j)=j := by omega
  have he := sa (d-j) (by omega)
  rw [he0] at he
  unfold column
  by_cases h1 : d-j≤k <;> by_cases h2 : j≤d+e-k
  · rw [ite_eq_left h1,ite_eq_left h2,he]
    have h3 : k-(d-j)≤e := by omega
    rw [sb _ h3,show e-(k-(d-j))=d+e-k-j by omega]
  · have h3 : e<k-(d-j) := by omega
    simp [h1,h2,hb _ h3]
  · have h3 : e<d+e-k-j := by omega
    simp [h1,h2,hb _ h3]
  · simp [h1,h2]

theorem A_support (r : Nat) : ZeroAfter r (A r) := by
  intro i h
  simp [A,cycleRow,show ¬i≤r by omega]

theorem A_symm (r : Nat) : Symmetric r (A r) := by
  intro i h
  exact congrArg (fun x : Nat=>(x:Int)) (cycleRow_symm r i h)

theorem W0_support (r : Nat) : ZeroAfter (r+1) (W0 r) := by
  intro i h
  cases i with
  | zero => omega
  | succ k =>
    rw [W0_succ,A_support _ _ (by omega),A_support _ _ (by omega),Int.add_zero]

theorem W0_symm (r : Nat) : Symmetric (r+1) (W0 r) := by
  have hU : ZeroAfter 1 U := by intro i hi; unfold U; split <;> omega
  have hS : Symmetric 1 U := by
    intro i hi
    have e : i=0 ∨ i=1 := by omega
    rcases e with e|e <;> subst i <;> decide
  have h := conv_symm 1 r U (A r) hU (A_support r) hS (A_symm r)
  rw [U_conv, Nat.add_comm 1 r] at h
  exact h

theorem w_support (r : Nat) : ZeroAfter (r+1) (w r) := by
  intro i h
  have hN : ¬(r%2=1 ∧ i=(r+1)/2) := by omega
  have e : w r i=W0 r i := by simp [w,W0,hN]
  rw [e]
  exact W0_support r i h

theorem w_symm (r : Nat) : Symmetric (r+1) (w r) := by
  intro i h
  have hS := W0_symm r i h
  change W0 r i- (if r%2=1 ∧ i=(r+1)/2 then 2*(dent ((r+1)/2):Int) else 0) =
    W0 r (r+1-i) - (if r%2=1 ∧ r+1-i=(r+1)/2 then 2*(dent ((r+1)/2):Int) else 0)
  rw [hS]
  by_cases he : r%2=1 ∧ i=(r+1)/2
  · have hR : r%2=1 ∧ r+1-i=(r+1)/2 := by omega
    rw [ite_eq_left he,ite_eq_left hR]
  · have hR : ¬(r%2=1 ∧ r+1-i=(r+1)/2) := by omega
    rw [ite_eq_right he,ite_eq_right hR]

theorem built_eq (r s i : Nat) : built r s i=twiceY r s i := by
  unfold built add scale twiceY A
  rw [conv_eq_list,conv_eq_list]

theorem built_symm (r s : Nat) : Symmetric (r+s+1) (built r s) := by
  intro i hi
  have h1 := conv_symm (r+1) s (w r) (A s) (w_support r) (A_support s) (w_symm r) (A_symm s)
  have h2 := conv_symm r (s+1) (A r) (w s) (A_support r) (w_support s) (A_symm r) (w_symm s)
  rw [show r+1+s=r+s+1 by omega] at h1
  rw [show r+(s+1)=r+s+1 by omega] at h2
  simp only [built,add,scale,A_symm _ _ hi,h1 i hi,h2 i hi]

theorem built_comm (r s i : Nat) : built r s i=built s r i := by
  simp only [built,add,scale]
  rw [Nat.add_comm r s,conv_comm (w r) (A s),conv_comm (A r) (w s)]
  omega

theorem built_minor (r s k : Nat) (hr : 2≤r) (hs : 2≤s)
    (hRS : BudgetOK r s) (hSR : BudgetOK s r) (hk : 1≤k) (hhi : k<r+s+1) :
    built r s (k-1)*built r s (k+1)<built r s k*built r s k := by
  by_cases hl : 2*k≤r+s+1
  · exact built_left_minor r s k hr hs hRS hSR hk hl
  · let r' := r+s+1
    let k' := r'-k
    have he := built_left_minor r s k' hr hs hRS hSR (by dsimp [k',r']; omega) (by dsimp [k',r']; omega)
    have hm := built_symm r s
    rw [hm (k-1) (by omega),hm (k+1) (by omega),hm k (by omega),
      show r+s+1-(k-1)=k'+1 by dsimp [k',r']; omega,
      show r+s+1-(k+1)=k'-1 by dsimp [k',r']; omega,Int.mul_comm]
    exact he

#print axioms built_minor
end InverseZ.GluedCycleBounds

namespace InverseZ.GluedCycleBounds
open TriangleCycle RatioDefect GluedCyclesResidual

def back (f : Row) : Row
  | 0 => 0
  | j+1 => f j

theorem conv_U_any (f : Row) (i : Nat) : conv U f i=f i+back f i := by
  cases i with
  | zero => simp [conv_zero,U,back]
  | succ i =>
    cases i with
    | zero => simp [conv_zero,conv_succ,U,back]
    | succ i =>
      have h : (fun j : Nat=>U (j+1+1))=(fun _=>0) := U_zeroLater
      simp only [conv_succ,h,conv_zero_left,back]
      simp [U]

theorem A1_eq_U : A 1=U := by
  funext i
  cases i with
  | zero => decide
  | succ i =>
    cases i with
    | zero => decide
    | succ i =>
      have h := A_support 1 (i+1+1) (by omega)
      rw [h]
      simp [U]

def sparseW : Row := fun i=> if i=0 ∨ i=2 then 1 else 0

theorem w1_eq_sparse : w 1=sparseW := by
  funext i
  cases i with
  | zero => decide
  | succ i =>
    cases i with
    | zero => decide
    | succ i =>
      cases i with
      | zero => decide
      | succ i =>
        have h := w_support 1 (i+1+1+1) (by omega)
        rw [h]
        simp [sparseW]

theorem conv_sparseW (f : Row) (i : Nat) :
    conv sparseW f i=f i+back (back f) i := by
  cases i with
  | zero => simp [conv_zero,back,sparseW]
  | succ i =>
    cases i with
    | zero => simp [conv_zero,conv_succ,back,sparseW]
    | succ i =>
      cases i with
      | zero => simp [conv_zero,conv_succ,back,sparseW]
      | succ i =>
        have h : (fun j : Nat=>sparseW (j+1+1+1))=(fun _=>0) := by
          funext j
          simp [sparseW,show j+1+1+1≠2 by omega]
        simp only [conv_succ,back,h,conv_zero_left]
        simp [sparseW]

def penalty (r i : Nat) : Int :=
  if r%2=1 ∧ i=(r+1)/2 then 2*(dent ((r+1)/2):Int) else 0

theorem w_split (r i : Nat) : w r i=A r i+back (A r) i-penalty r i := by
  change W0 r i-penalty r i=_
  rw [←U_conv,conv_U_any]

theorem back_w_split (r i : Nat) :
    back (w r) i=back (A r) i+back (back (A r)) i-back (penalty r) i := by
  cases i with
  | zero => simp [back]
  | succ i =>
    simp only [back]
    exact w_split r i

theorem back_cast (f : Nat → Nat) (i : Nat) :
    back (fun j=>(f j:Int)) i=(shift f i:Int) := by
  cases i <;> rfl

theorem pen_sum (s i : Nat) :
    penalty s i+back (penalty s) i =
      2*(if (s+2)%2=1 ∧ (i=(s+2)/2 ∨ i=(s+2)/2+1)
         then (dent ((s+2)/2):Int) else 0) := by
  have hr : (s+2)%2=s%2 := by omega
  rw [hr]
  by_cases hp : s%2=1
  · have he : (s+1)/2=(s+2)/2 := by omega
    have happ : penalty s i=(if i=(s+2)/2 then 2*(dent ((s+2)/2):Int) else 0) := by
      simp [penalty,hp,he]
    have hback : back (penalty s) i=(if i=(s+2)/2+1 then 2*(dent ((s+2)/2):Int) else 0) := by
      cases i with
      | zero => simp [back]
      | succ i =>
        simp only [back,penalty,hp,true_and,he,Nat.add_right_cancel_iff]
    rw [happ,hback]
    by_cases h0 : i=(s+2)/2 <;> by_cases h1 : i=(s+2)/2+1
    · omega
    · simp only [hp,true_and,ite_eq_left h0,ite_eq_right h1,
        ite_eq_left (Or.inl h0 : i=(s+2)/2 ∨ i=(s+2)/2+1),Int.add_zero]
    · simp only [hp,true_and,ite_eq_right h0,ite_eq_left h1,
        ite_eq_left (Or.inr h1 : i=(s+2)/2 ∨ i=(s+2)/2+1),Int.zero_add]
    · have hn : ¬(i=(s+2)/2 ∨ i=(s+2)/2+1) := fun h=>h.elim h0 h1
      simp only [hp,true_and,ite_eq_right h0,ite_eq_right h1,ite_eq_right hn,
        Int.add_zero,Int.mul_zero]
  · have happ : penalty s i=0 := by simp [penalty,hp]
    have hback : back (penalty s) i=0 := by cases i <;> simp [back,penalty,hp]
    simp [happ,hback,hp]

theorem built_triangle (s i : Nat) : built 1 s i=2*bfmCoeff (s+2) i := by
  unfold built add scale
  rw [w1_eq_sparse,A1_eq_U,conv_sparseW,conv_U_any,w_split,back_w_split]
  have hh := pen_sum s i
  unfold bfmCoeff convolve
  have hr : 1+s+1=s+2 := by omega
  have hc : s+2-2=s := by omega
  have h1 : back (A s) i=(shift (cycleRow s) i:Int) := back_cast _ _
  have hx : back (back (A s)) i=(shift (shift (cycleRow s)) i:Int) := by
    rw [show back (A s)=(fun j=>(shift (cycleRow s) j:Int)) from funext (back_cast _)]
    exact back_cast _ _
  simp only [hr,hc,h1,hx,A,Int.natCast_add]
  grind

#print axioms built_triangle
end InverseZ.GluedCycleBounds

namespace InverseZ.GluedCycleBounds
open TriangleCycle RatioDefect GluedCyclesResidual

theorem residualFacts (r s : Nat) (hm : (r,s)∈residual) :
    (∀ i, i≤r+s+1 → 0<twiceY r s i) ∧
    (∀ k, 1≤k → k<r+s+1 →
      twiceY r s (k-1)*twiceY r s (k+1)<twiceY r s k*twiceY r s k) := by
  have allH := residual_checked
  unfold checks at allH
  have he := List.all_eq_true.mp allH (r,s) hm
  simp only [Bool.and_eq_true] at he
  refine ⟨?_,?_⟩
  · intro i hi
    have H := List.all_eq_true.mp he.1 i (List.mem_range.mpr (by omega))
    exact of_decide_eq_true H
  · intro k hlo hhi
    have H := List.all_eq_true.mp he.2 (k-1) (List.mem_range.mpr (by omega))
    have h := of_decide_eq_true H
    simpa only [show k-1+1=k by omega,show k-1+2=k+1 by omega] using h

theorem budget_no_resid (r s : Nat) (hr : 2≤r) (hs : 2≤s)
    (h : (r,s)∉residual) (ht : (s,r)∉residual) : BudgetOK r s := by
  apply budgetOK r s hr hs
  · intro e
    subst r
    by_cases H : 9≤s
    · exact H
    · exfalso
      have hsmall : s=2 ∨ s=3 ∨ s=4 ∨ s=5 ∨ s=6 ∨ s=7 ∨ s=8 := by omega
      apply h
      rcases hsmall with hs|hs|hs|hs|hs|hs|hs <;> subst s <;> decide
  · intro e
    subst r
    by_cases H : 3≤s
    · exact H
    · have e : s=2 := by omega
      subst s
      exact False.elim (ht (by decide))

theorem built_global_positive (r s i : Nat) (hr : 1≤r) (hs : 1≤s) (hi : i≤r+s+1) :
    0<built r s i := by
  by_cases h : r=1
  · subst r
    rw [built_triangle]
    exact Int.mul_pos (by decide) (bfm_positive _ _ (by omega) (by omega))
  · by_cases h' : s=1
    · subst s
      rw [built_comm r 1,built_triangle]
      exact Int.mul_pos (by decide) (bfm_positive _ _ (by omega) (by omega))
    · exact built_positive r s i (by omega) (by omega) hi

theorem built_triangle_minor (s k : Nat) (hs : 1≤s) (hk : 1≤k)
    (hhi : k<1+s+1) :
    built 1 s (k-1)*built 1 s (k+1)<built 1 s k*built 1 s k := by
  simp only [built_triangle]
  have hm := bfm_lc (s+2) k (by omega) hk (by omega)
  have he := Int.mul_lt_mul_of_pos_left hm (show (0:Int)<2*2 by decide)
  grind

theorem built_global_minor (r s k : Nat) (hr : 1≤r) (hs : 1≤s) (hlo : 1≤k) (hhi : k<r+s+1) :
    built r s (k-1)*built r s (k+1)<built r s k*built r s k := by
  by_cases h : r=1
  · subst r
    exact built_triangle_minor s k hs hlo hhi
  · by_cases h' : s=1
    · subst s
      simp only [built_comm r 1]
      exact built_triangle_minor r k hr hlo (by omega)
    · by_cases he : (r,s)∈residual
      · simp only [built_eq]
        exact (residualFacts r s he).2 k hlo hhi
      · by_cases he' : (s,r)∈residual
        · simp only [built_comm r s,built_eq]
          exact (residualFacts s r he').2 k hlo (by omega)
        · exact built_minor r s k (by omega) (by omega)
            (budget_no_resid r s (by omega) (by omega) he he')
            (budget_no_resid s r (by omega) (by omega) he' he) hlo hhi

theorem twiceY_strict_and_positive :
    (∀ r s i : Nat, 1≤r → 1≤s → i≤r+s+1 → 0<twiceY r s i) ∧
    (∀ r s k : Nat, 1≤r → 1≤s → 1≤k → k<r+s+1 →
      twiceY r s (k-1)*twiceY r s (k+1)<twiceY r s k*twiceY r s k) := by
  simp only [←built_eq]
  exact ⟨built_global_positive,built_global_minor⟩

#print axioms twiceY_strict_and_positive
end InverseZ.GluedCycleBounds

namespace InverseZ.GluedCycleBounds
open TriangleCycle RatioDefect GluedCyclesResidual

def halfPenalty (r i : Nat) : Int :=
  if r%2=1 ∧ i=(r+1)/2 then (dent ((r+1)/2):Int) else 0

theorem penalty_eq (r : Nat) : penalty r=scale 2 (halfPenalty r) := by
  funext i
  unfold penalty scale halfPenalty
  split <;> simp_all

theorem w_row (r : Nat) : w r=sub (add (A r) (back (A r))) (scale 2 (halfPenalty r)) := by
  funext i
  have h := w_split r i
  rw [penalty_eq] at h
  exact h

theorem conv_back_left (a b : Row) (k : Nat) :
    conv (back a) b k=back (conv a b) k := by
  cases k with
  | zero => simp [conv_zero,back]
  | succ k =>
    simp only [conv_succ,back,Int.zero_mul,Int.zero_add]

theorem conv_back_right (a b : Row) (k : Nat) :
    conv a (back b) k=back (conv a b) k := by
  rw [conv_comm,conv_back_left]
  cases k with
  | zero => rfl
  | succ k => exact conv_comm b a k

/-- BFMN Prop.4.2 for two cycles of lengths r+2,s+2 in coefficient form,
using the ordinary inverse Z rows of uniform cycle matroids. -/
def sourceCoeff (r s k : Nat) : Int :=
  A (r+s+1) k+conv U (conv (A r) (A s)) k
    - conv (halfPenalty r) (A s) k-conv (A r) (halfPenalty s) k

theorem sourceCoeff_twice (r s k : Nat) : 2*sourceCoeff r s k=twiceY r s k := by
  rw [←built_eq]
  unfold built add scale sourceCoeff
  rw [w_row r,conv_sub_left,conv_add_left,conv_scale_left,conv_back_left,
      w_row s,conv_sub_right,conv_add_right,conv_scale_right,conv_back_right,conv_U_any]
  grind

theorem sourceCoeff_strict_and_positive :
    (∀ r s i : Nat, 1≤r → 1≤s → i≤r+s+1 → 0<sourceCoeff r s i) ∧
    (∀ r s k : Nat, 1≤r → 1≤s → 1≤k → k<r+s+1 →
      sourceCoeff r s (k-1)*sourceCoeff r s (k+1)<sourceCoeff r s k*sourceCoeff r s k) := by
  constructor
  · intro r s i hr hs hi
    have he := twiceY_strict_and_positive.1 r s i hr hs hi
    rw [←sourceCoeff_twice] at he
    omega
  · intro r s k hr hs hk hhi
    have he := twiceY_strict_and_positive.2 r s k hr hs hk hhi
    simp only [←sourceCoeff_twice] at he
    have h :
        (2*2 : Int)*(sourceCoeff r s (k-1)*sourceCoeff r s (k+1)) <
        (2*2 : Int)*(sourceCoeff r s k*sourceCoeff r s k) := by
      calc
        _ = (2*sourceCoeff r s (k-1))*(2*sourceCoeff r s (k+1)) := by ac_rfl
        _ < (2*sourceCoeff r s k)*(2*sourceCoeff r s k) := he
        _ = _ := by ac_rfl
    exact Int.lt_of_mul_lt_mul_left h (by decide)

#print axioms sourceCoeff_twice
#print axioms sourceCoeff_strict_and_positive
end InverseZ.GluedCycleBounds
