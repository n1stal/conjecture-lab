module

public import Std

@[expose] public section

namespace InverseZ.ThagomizerCertificate

/-- Denominator-cleared adjacent minor. Here p=i+1, q=j+1;
T,U are the unnormalized binomial suffix and prefix and b is the middle binomial. -/
theorem adjacentIdentity (i j T U b : Nat) :
    let p := i+1
    let q := j+1
    let mid := q*T+p*(U+b)
    let prev := p*q*(q+1)*T+p*p*(q+1)*b+p*i*q*U
    let next := j*T+(p+1)*(U+b)
    let slack := (p+q)*(q*(q+1)*T*T+2*p*q*T*U+p*(q+1)*T*b+p*(p+1)*(U*U+U*b))
    (q+1)*(p+1)*mid*mid = prev*next + slack := by
  dsimp
  grind

theorem adjacentStrict (i j T U b : Nat) (hT : 0 < T) :
    let p := i+1
    let q := j+1
    let mid := q*T+p*(U+b)
    let prev := p*q*(q+1)*T+p*p*(q+1)*b+p*i*q*U
    let next := j*T+(p+1)*(U+b)
    prev*next < (q+1)*(p+1)*mid*mid := by
  dsimp
  rw [adjacentIdentity i j T U b]
  have h0 : 0 < (j+1)*(j+1+1)*T*T :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) hT) hT
  have h1 : 0 < ((i+1)+(j+1))*((j+1)*(j+1+1)*T*T+
      2*(i+1)*(j+1)*T*U+(i+1)*(j+1+1)*T*b+(i+1)*(i+1+1)*(U*U+U*b)) :=
    Nat.mul_pos (by omega) (by omega)
  omega

#print axioms adjacentIdentity
#print axioms adjacentStrict

end InverseZ.ThagomizerCertificate



namespace InverseZ.ThagomizerRows

def choose : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _+1 => 0
  | _+1, 0 => 1
  | n+1,k+1 => choose n k + choose n (k+1)

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

def csum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i+1 => csum f i + f i

theorem csum_mono (f : Nat → Nat) {i j : Nat} (h : i≤j) : csum f i ≤ csum f j := by
  induction j with
  | zero =>
    have e : i=0 := by omega
    simp [e]
  | succ j ih =>
    by_cases e : i=j+1
    · simp [e]
    · have h' := ih (by omega)
      simp only [csum]
      omega

def tail (n i : Nat) : Nat := csum (choose n) (n+1) - csum (choose n) i
def predChoose (n : Nat) : Nat → Nat
  | 0 => 0
  | i+1 => choose n i

def row (n i : Nat) : Nat := choose n i * tail n i +
  predChoose n i * csum (choose n) (i+1)

theorem tail_step (n i : Nat) (h : i≤n) : tail n (i+1)+choose n i=tail n i := by
  have hm := csum_mono (choose n) (show i+1≤n+1 by omega)
  simp only [tail,csum] at hm ⊢
  omega

theorem row_minor (n i : Nat) (hi : i+1 ≤ n) :
    row n i * row n (i+2) < row n (i+1) * row n (i+1) := by
  let j := n-(i+1)
  let p := i+1
  let q := j+1
  let b := choose n (i+1)
  let bp := choose n i
  let bm := predChoose n i
  let bn := choose n (i+2)
  let T := tail n (i+1)
  let U := csum (choose n) (i+1)
  have hT : 0 < T := by
    have h := tail_step n (i+1) hi
    have hb := choose_pos_of_le hi
    dsimp [T]
    omega
  have hb : 0 < b := choose_pos_of_le hi
  have ep : p*b=q*bp := by
    have h := choose_ratio n i
    have h1 : n-i=q := by dsimp [q,j]; omega
    simpa only [p,b,bp,h1] using h
  have em : (q+1)*bm=i*bp := by
    cases i with
    | zero => simp [bm,bp,predChoose]
    | succ i =>
      have h := choose_ratio n i
      have h1 : n-i=q+1 := by dsimp [q,j]; omega
      simpa only [bm,bp,predChoose,h1] using h.symm
  have ex : (p+1)*bn=j*b := by
    have h := choose_ratio n (i+1)
    simpa only [p,bn,j,b] using h
  have e0 : row n (i+1)= b*T + bp*(U+b) := rfl
  have e1 : row n i=bp*(T+bp)+bm*U := by
    have e := tail_step n i (by omega : i≤n)
    change T+bp=tail n i at e
    change bp*tail n i + bm*U = _
    rw [← e]
  have e2 : row n (i+2)=bn*T+b*(U+b) := by
    have e := tail_step n (i+1) hi
    change tail n (i+2)+b=T at e
    change bn*tail n (i+2) + b*(U+b+bn)=_
    rw [←e]
    grind
  let mid := q*T+p*(U+b)
  let prev := p*q*(q+1)*T+p*p*(q+1)*b+p*i*q*U
  let next := j*T+(p+1)*(U+b)
  have E0 : q * row n (i+1) = b*mid := by
    rw [e0]
    dsimp [mid]
    grind
  have E1 : q*q*(q+1)*row n i = b*prev := by
    rw [e1]
    dsimp [prev]
    grind
  have E2 : (p+1)*row n (i+2) = b*next := by
    rw [e2, Nat.mul_add]
    calc
      _ = ((p+1)*bn)*T + b*((p+1)*(U+b)) := by ac_rfl
      _ = b*next := by
        rw [ex]
        simp only [next,Nat.mul_add]
        ac_rfl
  have hcert : prev*next < (q+1)*(p+1)*mid*mid :=
    InverseZ.ThagomizerCertificate.adjacentStrict i j T U b hT
  have hprod := Nat.mul_lt_mul_of_pos_left hcert (Nat.mul_pos hb hb)
  let D := q*q*(q+1)*(p+1)
  have Eleft : D*(row n i*row n (i+2))=(b*b)*(prev*next) := by
    calc
      _ = (q*q*(q+1)*row n i)*((p+1)*row n (i+2)) := by unfold D; ac_rfl
      _ = _ := by rw [E1,E2]; ac_rfl
  have Eright : D*(row n (i+1)*row n (i+1))=(b*b)*((q+1)*(p+1)*mid*mid) := by
    calc
      _ = ((q+1)*(p+1))*(q*row n (i+1))*(q*row n (i+1)) := by unfold D; ac_rfl
      _ = _ := by rw [E0]; ac_rfl
  apply Nat.lt_of_mul_lt_mul_left (a:=D)
  rw [Eleft,Eright]
  exact hprod

#print axioms choose_ratio
#print axioms tail_step
#print axioms row_minor
theorem row_positive (n k : Nat) (hk : k ≤ n+1) : 0 < row n k := by
  by_cases h : k ≤ n
  · have hb := choose_pos_of_le h
    have he := tail_step n k h
    have ht : 0 < tail n k := by omega
    unfold row
    have hp := Nat.mul_pos hb ht
    omega
  · have e : k=n+1 := by omega
    subst k
    have hb : 0 < choose n n := choose_pos_of_le (by omega)
    have ht : 0 < csum (choose n) (n+1+1) := by
      simp only [csum]
      omega
    unfold row
    have hh : predChoose n (n+1) = choose n n := rfl
    rw [hh]
    have hp := Nat.mul_pos hb ht
    omega

#print axioms row_positive
def bitWords : Nat → List (List Bool) :=
  Nat.rec [[]] (fun _ xs => xs.map (false::·) ++ xs.map (true::·))

theorem bitWords_zero : bitWords 0 = [[]] := rfl

theorem bitWords_succ (n : Nat) : bitWords (n+1) =
    (bitWords n).map (false::·) ++ (bitWords n).map (true::·) := rfl

def bitOnes : List Bool → Nat
  | [] => 0
  | false::l => bitOnes l
  | true::l => bitOnes l+1

theorem bit_words_choose (n k : Nat) :
    (bitWords n).countP (fun l => bitOnes l == k) = choose n k := by
  induction n generalizing k with
  | zero =>
    cases k <;> simp [bitWords_zero,bitOnes]
  | succ n ih =>
    cases k with
    | zero =>
      simp only [bitWords_succ,List.countP_append,List.countP_map,Function.comp_def,bitOnes]
      have h : (fun l => bitOnes l + 1 == 0) = (fun _ : List Bool => false) := by
        funext l
        simp
      rw [h,ih]
      simp
    | succ k =>
      simp only [bitWords_succ,List.countP_append,List.countP_map,Function.comp_def,bitOnes]
      have h : (fun l => bitOnes l+1 == k+1) = (fun l => bitOnes l == k) := by
        funext l
        simp
      rw [h,ih,ih,choose_succ_succ]
      omega

#print axioms bit_words_choose
end InverseZ.ThagomizerRows



namespace InverseZ.ThagomizerReflection

abbrev Step := Bool × Bool
def ones (b : Bool) : Nat := if b then 1 else 0
def inc (a : Step) : Int := Int.ofNat (ones a.2) - Int.ofNat (ones a.1)
def flip (a : Step) : Step := (a.2,a.1)

@[simp] theorem flip_flip (a : Step) : flip (flip a) = a := by cases a; rfl
@[simp] theorem inc_flip (a : Step) : inc (flip a) = -inc a := by simp [inc,flip]; omega

/-- Split at the first prefix hitting the target, including the empty prefix. -/
def hit (target h : Int) : List Step → Option (List Step × List Step)
  | [] => if h=target then some ([],[]) else none
  | a::as =>
      if h=target then some ([],a::as)
      else (hit target (h+inc a) as).map (fun (p,q) => (a::p,q))

def weight : List Step → Int
  | [] => 0
  | a::as => inc a + weight as

def left : List Step → Nat
  | [] => 0
  | a::as => ones a.1 + left as

def right : List Step → Nat
  | [] => 0
  | a::as => ones a.2 + right as

@[simp] theorem weight_append (p q : List Step) : weight (p++q) = weight p + weight q := by
  induction p with
  | nil => simp [weight]
  | cons a p ih => simp [weight,ih]; omega

@[simp] theorem left_append (p q : List Step) : left (p++q) = left p + left q := by
  induction p with
  | nil => simp [left]
  | cons a p ih => simp [left,ih]; omega

@[simp] theorem right_append (p q : List Step) : right (p++q) = right p + right q := by
  induction p with
  | nil => simp [right]
  | cons a p ih => simp [right,ih]; omega

@[simp] theorem left_map_flip (p : List Step) : left (p.map flip) = right p := by
  induction p with
  | nil => rfl
  | cons a p ih => simp [left,right,flip,ih]

@[simp] theorem right_map_flip (p : List Step) : right (p.map flip) = left p := by
  induction p with
  | nil => rfl
  | cons a p ih => simp [left,right,flip,ih]

theorem weight_counts (p : List Step) : weight p = (right p : Int) - left p := by
  induction p with
  | nil => rfl
  | cons a p ih => simp [weight,inc,left,right,ih]; omega

theorem hit_split {target h : Int} {l p q : List Step} (e : hit target h l = some (p,q)) :
    l=p++q ∧ h+weight p=target := by
  induction l generalizing h p q with
  | nil =>
    simp only [hit] at e
    split at e
    · simp_all [weight]
    · contradiction
  | cons a l ih =>
    simp only [hit] at e
    split at e
    · simp_all [weight]
    · cases he : hit target (h+inc a) l with
      | none => simp [he] at e
      | some pq =>
        obtain ⟨p',q'⟩ := pq
        have hn := ih he
        simp only [he,Option.map_some,Option.some.injEq,Prod.mk.injEq] at e
        obtain ⟨rfl,rfl⟩ := e
        constructor
        · simp [hn.1]
        · simp only [weight]
          omega

/-- Reflection preserves the first hitting index, with opposite target. -/
theorem hit_reflect {target h : Int} {l p q : List Step}
    (e : hit target h l = some (p,q)) :
    hit (-target) (-h) (p.map flip ++ q) = some (p.map flip,q) := by
  induction l generalizing h p q with
  | nil =>
    simp only [hit] at e
    split at e
    · simp_all [hit]
    · contradiction
  | cons a l ih =>
    simp only [hit] at e
    split at e
    · rename_i heq
      simp only [Option.some.injEq,Prod.mk.injEq] at e
      obtain ⟨rfl,rfl⟩ := e
      simp [hit,heq]
    · rename_i hne
      cases he : hit target (h+inc a) l with
      | none => simp [he] at e
      | some pq =>
        obtain ⟨p',q'⟩ := pq
        have hr := ih he
        simp only [he,Option.map_some,Option.some.injEq,Prod.mk.injEq] at e
        obtain ⟨rfl,rfl⟩ := e
        have hne' : -h ≠ -target := by omega
        have hs : -h + inc (flip a) = -(h+inc a) := by simp; omega
        simp only [List.map_cons,List.cons_append,hit,hne',ite_false,hs,hr,Option.map_some]

def reflect (target : Int) (l : List Step) : List Step :=
  match hit target 0 l with
  | none => l
  | some (p,q) => p.map flip ++ q

theorem reflect_involution {target : Int} {l p q : List Step}
    (e : hit target 0 l = some (p,q)) :
    reflect (-target) (reflect target l) = l := by
  have hp : (p.map flip).map flip = p := by simp [List.map_map,Function.comp_def]
  have h := hit_reflect e
  simp only [Int.neg_zero] at h
  have h1 : reflect target l = p.map flip ++ q := by simp [reflect,e]
  rw [h1]
  unfold reflect
  rw [h]
  change (p.map flip).map flip ++ q = l
  rw [hp]
  exact (hit_split e).1.symm

theorem inc_bounds (a : Step) : -1 ≤ inc a ∧ inc a ≤ 1 := by
  obtain ⟨a,b⟩ := a
  cases a <;> cases b <;> decide

theorem hit_up (target h : Int) (l : List Step)
    (h₀ : h≤target) (h₁ : target≤h+weight l) : ∃ p q, hit target h l = some (p,q) := by
  induction l generalizing h with
  | nil =>
    have e : h=target := by simp [weight] at h₁; omega
    exact ⟨[],[],by simp [hit,e]⟩
  | cons a l ih =>
    by_cases e : h=target
    · exact ⟨[],a::l,by simp [hit,e]⟩
    · have hb := (inc_bounds a).2
      have hc : target≤(h+inc a)+weight l := by simp [weight] at h₁; omega
      obtain ⟨p,q,he⟩ := ih (h:=h+inc a) (by omega) hc
      exact ⟨a::p,q,by simp [hit,e,he]⟩

theorem hit_down (target h : Int) (l : List Step)
    (h₀ : target≤h) (h₁ : h+weight l≤target) : ∃ p q, hit target h l = some (p,q) := by
  induction l generalizing h with
  | nil =>
    have e : h=target := by simp [weight] at h₁; omega
    exact ⟨[],[],by simp [hit,e]⟩
  | cons a l ih =>
    by_cases e : h=target
    · exact ⟨[],a::l,by simp [hit,e]⟩
    · have hb := (inc_bounds a).1
      have hc : (h+inc a)+weight l≤target := by simp [weight] at h₁; omega
      obtain ⟨p,q,he⟩ := ih (h:=h+inc a) (by omega) hc
      exact ⟨a::p,q,by simp [hit,e,he]⟩

theorem hit_append {target h : Int} {l p q : List Step}
    (e : hit target h l = some (p,q)) (tail : List Step) :
    hit target h (l++tail) = some (p,q++tail) := by
  induction l generalizing h p q with
  | nil =>
    simp only [hit] at e
    split at e
    · rename_i eh
      simp only [Option.some.injEq,Prod.mk.injEq] at e
      obtain ⟨rfl,rfl⟩ := e
      cases tail <;> simp [hit,eh]
    · contradiction
  | cons a l ih =>
    by_cases eh : h=target
    · simp only [hit,eh,ite_true,Option.some.injEq,Prod.mk.injEq] at e
      obtain ⟨rfl,rfl⟩ := e
      simp [hit,eh]
    · cases hs : hit target (h+inc a) l with
      | none => simp [hit,eh,hs] at e
      | some pq =>
        obtain ⟨p',q'⟩ := pq
        have h' := ih hs
        simp only [hit,eh,ite_false,hs,Option.map_some,Option.some.injEq,Prod.mk.injEq] at e
        obtain ⟨rfl,rfl⟩ := e
        simp [hit,eh,h']

def Bad (l : List Step) : Prop := ∃ p q : List Step, l=p++q ∧ weight p<0

theorem bad_iff_hit (l : List Step) :
    Bad l ↔ ∃ p q, hit (-1) 0 l = some (p,q) := by
  constructor
  · rintro ⟨p,q,rfl,hn⟩
    obtain ⟨u,v,e⟩ := hit_down (-1) 0 p (by decide) (by omega)
    exact ⟨u,v++q,hit_append e q⟩
  · rintro ⟨p,q,e⟩
    have h := hit_split e
    exact ⟨p,q,h.1,by omega⟩

theorem reflect_totals {target : Int} {l p q : List Step}
    (e : hit target 0 l = some (p,q)) :
    (reflect target l).length=l.length ∧
    (left (reflect target l) : Int)=(left l : Int)+target ∧
    (right (reflect target l) : Int)=(right l : Int)-target := by
  obtain ⟨hl,hp⟩ := hit_split e
  have hw := weight_counts p
  have hr : reflect target l = p.map flip ++ q := by simp [reflect,e]
  rw [hr,hl]
  simp only [List.length_append,List.length_map,left_append,right_append,
    left_map_flip,right_map_flip,Int.natCast_add,true_and]
  omega

#print axioms reflect_involution
#print axioms bad_iff_hit
#print axioms reflect_totals

def BadRow (n : Nat) (i k : Int) := {l : List Step //
  l.length=n ∧ (left l : Int)=i ∧ (right l : Int)=k ∧ Bad l}
def PairRow (n : Nat) (i k : Int) := {l : List Step //
  l.length=n ∧ (left l : Int)=i ∧ (right l : Int)=k}

def toReflected (n : Nat) (i k : Int) (l : BadRow n i k) : PairRow n (i-1) (k+1) :=
  ⟨reflect (-1) l.val, by
    obtain ⟨p,q,e⟩ := (bad_iff_hit _).mp l.property.2.2.2
    have h := reflect_totals e
    obtain ⟨hl,hi,hk,_⟩ := l.property
    exact ⟨h.1.trans hl,by omega,by omega⟩⟩

private theorem reflected_hit (n : Nat) (i k : Int) (hik : i≤k)
    (l : PairRow n (i-1) (k+1)) : ∃ p q, hit 1 0 l.val = some (p,q) := by
  apply hit_up
  · decide
  · rw [weight_counts]
    obtain ⟨_,hi,hk⟩ := l.property
    omega

def fromReflected (n : Nat) (i k : Int) (hik : i≤k)
    (l : PairRow n (i-1) (k+1)) : BadRow n i k :=
  ⟨reflect 1 l.val, by
    obtain ⟨p,q,e⟩ := reflected_hit n i k hik l
    have h := reflect_totals e
    have he := hit_reflect e
    simp only [Int.neg_zero] at he
    obtain ⟨hl,hi,hk⟩ := l.property
    refine ⟨h.1.trans hl,by omega,by omega,?_⟩
    have hlist : reflect 1 l.val = p.map flip ++ q := by simp [reflect,e]
    apply (bad_iff_hit _).mpr
    exact ⟨p.map flip,q,by simpa only [hlist] using he⟩⟩

theorem bad_row_bijection (n : Nat) (i k : Int) (hik : i≤k) :
    (∀ l : BadRow n i k, fromReflected n i k hik (toReflected n i k l) = l) ∧
    (∀ l : PairRow n (i-1) (k+1), toReflected n i k (fromReflected n i k hik l) = l) := by
  constructor
  · intro l
    apply Subtype.ext
    obtain ⟨p,q,e⟩ := (bad_iff_hit _).mp l.property.2.2.2
    exact reflect_involution e
  · intro l
    apply Subtype.ext
    obtain ⟨p,q,e⟩ := reflected_hit n i k hik l
    exact reflect_involution e

#print axioms bad_row_bijection

end InverseZ.ThagomizerReflection

namespace InverseZ.ThagomizerCount
open InverseZ.ThagomizerReflection
open InverseZ.ThagomizerRows

def words : Nat → List (List Step)
  | 0 => [[]]
  | n+1 =>
    (words n).map ((false,false)::·) ++
    (words n).map ((false,true)::·) ++
    (words n).map ((true,false)::·) ++
    (words n).map ((true,true)::·)

theorem words_mem (n : Nat) (p : List Step) : p ∈ words n ↔ p.length=n := by
  induction n generalizing p with
  | zero => simp [words]
  | succ n ih =>
    cases p with
    | nil => simp [words]
    | cons a p =>
      obtain ⟨a,b⟩ := a
      cases a <;> cases b <;> simp [words,ih]

private theorem nodupMap {α β : Type} (f : α → β) (hf : ∀ {x y}, f x=f y → x=y)
    {l : List α} (h : l.Nodup) : (l.map f).Nodup := by
  apply List.pairwise_map.mpr
  exact List.Pairwise.imp (fun hne h' => hne (hf h')) h

theorem words_nodup (n : Nat) : (words n).Nodup := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
    simp only [words,List.nodup_append]
    repeat' apply And.intro
    all_goals first
      | apply nodupMap _ (by simp) ih
      | simp only [List.mem_append,List.mem_map]
        grind

def countPair (n i k : Nat) : Nat :=
  (words n).countP (fun l => (left l == i) && (right l == k))

@[simp] private theorem left_false (b : Bool) (l : List Step) :
    left ((false,b)::l) = left l := by simp [left,ones]
@[simp] private theorem left_true (b : Bool) (l : List Step) :
    left ((true,b)::l) = left l+1 := by simp [left,ones,Nat.add_comm]
@[simp] private theorem right_false (a : Bool) (l : List Step) :
    right ((a,false)::l) = right l := by simp [right,ones]
@[simp] private theorem right_true (a : Bool) (l : List Step) :
    right ((a,true)::l) = right l+1 := by simp [right,ones,Nat.add_comm]

theorem count_pair_product (n i k : Nat) :
    countPair n i k = choose n i * choose n k := by
  induction n generalizing i k with
  | zero =>
    cases i <;> cases k <;> simp [countPair,words,left,right]
  | succ n ih =>
    simp only [countPair] at ih
    cases i <;> cases k <;>
      simp [countPair,words,List.countP_append,List.countP_map,Function.comp_def,ih] <;>
      grind

#print axioms words_nodup
#print axioms count_pair_product
def pairList (n : Nat) (i k : Int) : List (List Step) :=
  (words n).filter (fun l => decide ((left l : Int)=i ∧ (right l : Int)=k))

def badFlag (l : List Step) : Bool := (hit (-1) 0 l).isSome

def badList (n : Nat) (i k : Int) : List (List Step) :=
  (pairList n i k).filter badFlag

def goodList (n : Nat) (i k : Int) : List (List Step) :=
  (pairList n i k).filter (fun l => !badFlag l)

theorem mem_pairList (n : Nat) (i k : Int) (l : List Step) :
    l ∈ pairList n i k ↔ l.length=n ∧ (left l : Int)=i ∧ (right l : Int)=k := by
  simp [pairList,words_mem]

theorem flag_iff (l : List Step) : badFlag l = true ↔ Bad l := by
  simp only [badFlag, Option.isSome_iff_exists,bad_iff_hit]
  exact ⟨fun ⟨⟨p,q⟩,h⟩ => ⟨p,q,h⟩,fun ⟨p,q,h⟩ => ⟨(p,q),h⟩⟩

theorem mem_badList (n : Nat) (i k : Int) (l : List Step) :
    l ∈ badList n i k ↔ l.length=n ∧ (left l : Int)=i ∧ (right l : Int)=k ∧ Bad l := by
  simp [badList,mem_pairList,flag_iff, and_assoc]

private theorem nodupMapOn {α β : Type} {l : List α} (f : α → β) (hn : l.Nodup)
    (hi : ∀ x∈l, ∀ y∈l, f x = f y → x=y) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons,List.nodup_cons] at hn ⊢
    refine ⟨?_,ih hn.2 (fun x hx y hy h => hi x (by simp [hx]) y (by simp [hy]) h)⟩
    intro ha
    obtain ⟨b,hb,he⟩ := List.mem_map.mp ha
    have := hi b (by simp [hb]) a (by simp) he
    subst b
    exact hn.1 hb

theorem pairList_nodup (n : Nat) (i k : Int) : (pairList n i k).Nodup :=
  List.Pairwise.filter _ (words_nodup n)

theorem badList_nodup (n : Nat) (i k : Int) : (badList n i k).Nodup :=
  List.Pairwise.filter _ (pairList_nodup n i k)

theorem reflected_badList_perm (n : Nat) (i k : Int) (hik : i≤k) :
    ((badList n i k).map (reflect (-1))).Perm (pairList n (i-1) (k+1)) := by
  have hl : ((badList n i k).map (reflect (-1))).Nodup := by
    apply nodupMapOn _ (badList_nodup n i k)
    intro x hx y hy e
    let a : BadRow n i k := ⟨x,(mem_badList _ _ _ _).mp hx⟩
    let b : BadRow n i k := ⟨y,(mem_badList _ _ _ _).mp hy⟩
    have h : toReflected n i k a = toReflected n i k b := Subtype.ext e
    have h' := congrArg (fromReflected n i k hik) h
    rw [(bad_row_bijection n i k hik).1 a,(bad_row_bijection n i k hik).1 b] at h'
    exact congrArg Subtype.val h'
  apply (List.perm_ext_iff_of_nodup hl (pairList_nodup n _ _)).mpr
  intro l
  constructor
  · intro h
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp h
    let a : BadRow n i k := ⟨x,(mem_badList _ _ _ _).mp hx⟩
    exact (mem_pairList _ _ _ _).mpr (toReflected n i k a).property
  · intro h
    let a : PairRow n (i-1) (k+1) := ⟨l,(mem_pairList _ _ _ _).mp h⟩
    let x := fromReflected n i k hik a
    refine List.mem_map.mpr ⟨x.val,(mem_badList _ _ _ _).mpr x.property,?_⟩
    exact congrArg Subtype.val ((bad_row_bijection n i k hik).2 a)

theorem reflected_card (n : Nat) (i k : Int) (hik : i≤k) :
    (badList n i k).length = (pairList n (i-1) (k+1)).length := by
  simpa only [List.length_map] using (reflected_badList_perm n i k hik).length_eq

theorem split_card (n : Nat) (i k : Int) :
    (goodList n i k).length+(badList n i k).length=(pairList n i k).length := by
  have h := (List.filter_append_perm badFlag (pairList n i k)).length_eq
  simpa [goodList,badList,List.length_append,Nat.add_comm] using h

theorem reflected_subtraction (n : Nat) (i k : Int) (hik : i≤k) :
    (goodList n i k).length + (pairList n (i-1) (k+1)).length = (pairList n i k).length := by
  rw [← reflected_card n i k hik]
  exact split_card n i k

theorem pairList_nat_length (n i k : Nat) :
    (pairList n (i:Int) (k:Int)).length = choose n i * choose n k := by
  rw [← count_pair_product]
  have h : (fun l : List Step => decide ((left l:Int)=(i:Int) ∧ (right l:Int)=(k:Int))) =
      (fun l : List Step => (left l == i) && (right l == k)) := by
    funext l
    apply Bool.eq_iff_iff.mpr
    simp [Int.natCast_inj]
  unfold pairList countPair
  rw [List.countP_eq_length_filter,h]

#print axioms reflected_subtraction
#print axioms pairList_nat_length
def goodN (n i k : Nat) : Nat := (goodList n (i:Int) (k:Int)).length

theorem reflected_subtraction_nat (n i k : Nat) (hik : i≤k) :
    goodN n i k + predChoose n i * choose n (k+1) = choose n i * choose n k := by
  have h := reflected_subtraction n (i:Int) (k:Int) (by omega)
  rw [pairList_nat_length] at h
  cases i with
  | zero =>
    have hn : pairList n ((0:Int)-1) ((k:Int)+1) = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro l hl
      have hj := ((mem_pairList _ _ _ _).mp hl).2.1
      omega
    change (goodList n 0 (k:Int)).length + (pairList n ((0:Int)-1) ((k:Int)+1)).length =
      choose n 0 * choose n k at h
    rw [hn] at h
    simpa [goodN,predChoose] using h
  | succ i =>
    have hi : ((i+1 : Nat) : Int)-1=(i:Int) := by omega
    have hk : (k:Int)+1=((k+1:Nat):Int) := by omega
    simpa only [hi,hk,pairList_nat_length,goodN,predChoose] using h

def span (f : Nat → Nat) (start : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => span f start k + f (start+k)

theorem span_eq_csum (f : Nat → Nat) (s l : Nat) :
    csum f s + span f s l = csum f (s+l) := by
  induction l with
  | zero => simp [span]
  | succ l ih =>
    change csum f s+(span f s l+f (s+l))=csum f (s+l)+f (s+l)
    rw [← Nat.add_assoc,ih]

theorem sum_reflection (n i l : Nat) :
    span (goodN n i) i l + predChoose n i * span (choose n) (i+1) l =
      choose n i * span (choose n) i l := by
  induction l with
  | zero => simp [span]
  | succ l ih =>
    have h := reflected_subtraction_nat n i (i+l) (by omega)
    have e : i+1+l=i+l+1 := by omega
    simp only [span,e,Nat.mul_add]
    omega

def modelCoeff (n i : Nat) : Nat :=
  span (goodN n i) i (n+1-i) + predChoose n i * csum (choose n) (n+1)

theorem model_eq_row (n i : Nat) (hi : i≤n+1) : modelCoeff n i = row n i := by
  let l := n+1-i
  have h := sum_reflection n i l
  have hs := span_eq_csum (choose n) i l
  have hs' := span_eq_csum (choose n) (i+1) l
  have e : i+l=n+1 := by dsimp [l]; omega
  have e' : i+1+l=n+1+1 := by omega
  rw [e] at hs
  rw [e'] at hs'
  have hz : choose n (n+1)=0 := choose_eq_zero_of_lt (by omega)
  have hp : csum (choose n) (n+1+1)=csum (choose n) (n+1) := by
    rw [csum,hz,Nat.add_zero]
  rw [hp] at hs'
  have ht : span (choose n) i l=tail n i := by
    unfold tail
    omega
  have hmid := congrArg (fun z => predChoose n i*z) hs'
  rw [Nat.mul_add] at hmid
  rw [ht] at h
  unfold modelCoeff row
  change span (goodN n i) i l + predChoose n i * csum (choose n) (n+1) = _
  omega

theorem model_minor (n i : Nat) (hi : i+1≤n) :
    modelCoeff n i * modelCoeff n (i+2) < modelCoeff n (i+1)*modelCoeff n (i+1) := by
  rw [model_eq_row n i (by omega),model_eq_row n (i+2) (by omega),
    model_eq_row n (i+1) (by omega)]
  exact row_minor n i hi

#print axioms reflected_subtraction_nat
#print axioms model_eq_row
#print axioms model_minor
end InverseZ.ThagomizerCount


namespace InverseZ.ThagomizerFlatCounts
open InverseZ.ThagomizerRows

def assignments : Nat → List (List (Option Bool)) :=
  Nat.rec [[]] (fun _ xs =>
    xs.map ((none : Option Bool)::·) ++
    xs.map ((some false)::·) ++ xs.map ((some true)::·))

theorem assignments_zero : assignments 0 = [[]] := rfl

theorem assignments_succ (n : Nat) : assignments (n+1) =
    (assignments n).map ((none : Option Bool)::·) ++
    (assignments n).map ((some false)::·) ++ (assignments n).map ((some true)::·) := rfl

def assigned : List (Option Bool) → Nat
  | [] => 0
  | none::as => assigned as
  | some _::as => assigned as+1

theorem assignments_mem (n : Nat) (l : List (Option Bool)) :
    l ∈ assignments n ↔ l.length=n := by
  induction n generalizing l with
  | zero => simp [assignments_zero]
  | succ n ih =>
    cases l with
    | nil => simp [assignments_succ]
    | cons a l =>
      cases a with
      | none => simp [assignments_succ,ih]
      | some s => cases s <;> simp [assignments_succ,ih]

theorem assignments_count (n k : Nat) :
    (assignments n).countP (fun l => assigned l == k) = choose n k*2^k := by
  induction n generalizing k with
  | zero => cases k <;> simp [assignments_zero,assigned]
  | succ n ih =>
    cases k with
    | zero =>
      simp [assignments_succ,assigned,List.countP_append,List.countP_map,Function.comp_def,ih]
    | succ k =>
      simp [assignments_succ,assigned,List.countP_append,List.countP_map,Function.comp_def,ih,Nat.pow_succ]
      grind

#print axioms assignments_count
end InverseZ.ThagomizerFlatCounts


namespace InverseZ.ThagomizerRigidity
open InverseZ.ThagomizerRows

theorem choose_self (n : Nat) : choose n n = 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [choose_succ_succ,ih,choose_eq_zero_of_lt (by omega : n<n+1)]

theorem csum_congr {f g : Nat → Nat} (m : Nat) (h : ∀ k, k<m → f k=g k) :
    csum f m=csum g m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [csum]
    rw [ih (fun k hk => h k (by omega)),h m (by omega)]

def term (Q : Nat → Nat → Nat) (n i k : Nat) : Nat :=
  if n-k≤i then choose n k*Q k (i-(n-k)) else 0

/-- Weighted flat aggregate with the joined and split contributions. -/
def flatCoeff (Q : Nat → Nat → Nat) (n i : Nat) : Nat :=
  2^n*predChoose n i+csum (term Q n i) (n+1)

def earlier (Q : Nat → Nat → Nat) (n i : Nat) : Nat :=
  2^n*predChoose n i+csum (term Q n i) n

theorem flat_reduce (Q : Nat → Nat → Nat) (n i : Nat) :
    flatCoeff Q n i=earlier Q n i + Q n i := by
  simp [flatCoeff,earlier,csum,term,choose_self,Nat.add_assoc]

theorem earlier_congr (Q R : Nat → Nat → Nat) (n i : Nat)
    (h : ∀ k, k<n → ∀ j, Q k j=R k j) : earlier Q n i=earlier R n i := by
  unfold earlier
  rw [csum_congr (f:=term Q n i) (g:=term R n i) n (fun k hk => by simp [term,h k hk])]

def DegreeCut (Q : Nat → Nat → Nat) : Prop :=
  ∀ n i, n/2 < i → Q n i=0

def Palindrome (Q : Nat → Nat → Nat) : Prop :=
  ∀ n i, i≤n+1 → flatCoeff Q n i=flatCoeff Q n (n+1-i)

/-- No use of a conjectural identity: row symmetry and the standard
inverse-KL degree cut give rigidity of the flat recursion. -/
theorem Q_unique (Q R : Nat → Nat → Nat)
    (hQd : DegreeCut Q) (hRd : DegreeCut R)
    (hQp : Palindrome Q) (hRp : Palindrome R) :
    ∀ n i, Q n i=R n i := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro i
    by_cases h : n/2<i
    · rw [hQd n i h,hRd n i h]
    · have hi : i≤n+1 := by omega
      have hj : n/2<n+1-i := by omega
      have em := earlier_congr Q R n (n+1-i) ih
      have ei := earlier_congr Q R n i ih
      have hw : flatCoeff Q n (n+1-i)=flatCoeff R n (n+1-i) := by
        rw [flat_reduce,flat_reduce,hQd n _ hj,hRd n _ hj,em]
      have w := (hQp n i hi).trans (hw.trans (hRp n i hi).symm)
      rw [flat_reduce,flat_reduce,ei] at w
      omega

theorem computed_Y_unique (Q R : Nat → Nat → Nat)
    (hQd : DegreeCut Q) (hRd : DegreeCut R)
    (hQp : Palindrome Q) (hRp : Palindrome R) :
    flatCoeff Q = flatCoeff R := by
  have h : Q=R := funext fun n => funext fun i => Q_unique Q R hQd hRd hQp hRp n i
  rw [h]

#print axioms Q_unique
#print axioms computed_Y_unique
end InverseZ.ThagomizerRigidity


namespace InverseZ.ThagomizerMarker
open InverseZ.ThagomizerRows
open InverseZ.ThagomizerRigidity

abbrev Row := Nat → Int → Nat

def A (f : Row) (h : Nat) (i : Int) : Nat :=
  f h i + f (h+1) i + (if h=0 then 0 else f (h-1) (i-1))
def mark (f : Row) (h : Nat) (i : Int) := f h (i-1)
def unmarked : Nat → Row :=
  Nat.rec (fun _ i => if i=0 then 1 else 0) (fun _ f => A f)

theorem unmarked_zero : unmarked 0 = (fun _ i => if i=0 then 1 else 0) := rfl

theorem unmarked_succ (n : Nat) : unmarked (n+1) = A (unmarked n) := rfl
def marked : Nat → Row
  | 0 => fun _ i => if i=0 then 1 else 0
  | n+1 => fun h i => A (marked n) h i + mark (marked n) h i

private theorem csum_add (f g : Nat → Nat) (n : Nat) :
    csum (fun i => f i+g i) n=csum f n+csum g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [csum]
    rw [ih]
    omega

private theorem csum_mul_left (r : Nat) (f : Nat → Nat) (n : Nat) :
    csum (fun i => r*f i) n=r*csum f n := by
  induction n with
  | zero => simp [csum]
  | succ n ih =>
    simp only [csum]
    rw [ih,Nat.mul_add]

private theorem csum_head (f : Nat → Nat) (n : Nat) :
    csum f (n+1)=f 0+csum (fun k=>f (k+1)) n := by
  induction n with
  | zero => simp [csum]
  | succ n ih =>
    change csum f (n+1)+f (n+1)=f 0+(csum (fun k=>f (k+1)) n+f (n+1))
    rw [ih]
    omega

def transform (n : Nat) (h : Nat) (i : Int) : Nat :=
  csum (fun k => choose n k*unmarked k h (i-((n:Int)-(k:Int)))) (n+1)

private theorem transform_A (n h : Nat) (i : Int) :
    A (transform n) h i =
      csum (fun k=>choose n k*unmarked (k+1) h (i-((n:Int)-(k:Int)))) (n+1) := by
  unfold A transform
  by_cases hh : h=0
  · rw [ite_eq_left hh,Nat.add_zero,← csum_add]
    apply csum_congr
    intro k _
    rw [←Nat.mul_add]
    simp [unmarked_succ,A,hh]
  · rw [ite_eq_right hh,←csum_add,←csum_add]
    apply csum_congr
    intro k _
    rw [←Nat.mul_add,←Nat.mul_add]
    have hEq : (i-1)-((n:Int)-(k:Int))=(i-((n:Int)-(k:Int)))-1 := by omega
    simp only [unmarked_succ,A,hh,ite_false,hEq]

private theorem transform_mark (n h : Nat) (i : Int) :
    mark (transform n) h i =
      csum (fun k => choose n k*unmarked k h (i-((n+1:Int)-(k:Int)))) (n+1) := by
  unfold mark transform
  apply csum_congr
  intro k _
  have hEq : (i-1)-((n:Int)-(k:Int))=i-((n+1:Int)-(k:Int)) := by omega
  rw [hEq]

private theorem transform_step (n h : Nat) (i : Int) :
    transform (n+1) h i = A (transform n) h i + mark (transform n) h i := by
  rw [transform_A,transform_mark]
  let F : Nat → Nat := fun k=>unmarked k h (i-((n+1:Int)-(k:Int)))
  have hF (k : Nat) :
      unmarked (k+1) h (i-((n:Int)-(k:Int))) = F (k+1) := by
    unfold F
    congr 1 <;> omega
  unfold transform
  change csum (fun k=>choose (n+1) k*F k) (n+1+1) =
    csum (fun k=>choose n k*unmarked (k+1) h (i-((n:Int)-(k:Int)))) (n+1) +
      csum (fun k=>choose n k*F k) (n+1)
  rw [csum_congr (f:=fun k=>choose n k*unmarked (k+1) h (i-((n:Int)-(k:Int))))
       (g:=fun k=>choose n k*F (k+1)) (n+1) (fun k _=>by rw [hF])]
  rw [csum_head (fun k=>choose (n+1) k*F k) (n+1)]
  simp only [choose_zero_right,Nat.one_mul,choose_succ_succ,Nat.add_mul,csum_add]
  have hm : csum (fun k => choose n (k+1)*F (k+1)) (n+1) + F 0 =
      csum (fun k=>choose n k*F k) (n+1) := by
    have hz : choose n (n+1)=0 := choose_eq_zero_of_lt (by omega)
    change (csum (fun k => choose n (k+1)*F (k+1)) n + choose n (n+1)*F (n+1)) + F 0 =
      csum (fun k=>choose n k*F k) (n+1)
    rw [hz,Nat.zero_mul,Nat.add_zero,csum_head]
    simp [Nat.add_comm]
  omega

theorem marked_binomial (n h : Nat) (i : Int) :
    marked n h i = transform n h i := by
  induction n generalizing h i with
  | zero => simp [marked,unmarked_zero,transform,csum]
  | succ n ih =>
    have hEq : marked n=transform n := funext fun h => funext fun i => ih h i
    rw [marked,hEq,transform_step]


theorem unmarked_negative (n h : Nat) (i : Int) (hi : i<0) : unmarked n h i=0 := by
  induction n generalizing h i with
  | zero => simp [unmarked_zero,show i≠0 by omega]
  | succ n ih =>
    have hip : i-1<0 := by omega
    simp [unmarked_succ,A,ih h i hi,ih (h+1) i hi,ih (h-1) (i-1) hip]

theorem unmarked_degree (n h : Nat) (i : Int) (hi : (h:Int)+(n:Int)<2*i) :
    unmarked n h i=0 := by
  induction n generalizing h i with
  | zero => simp [unmarked_zero,show i≠0 by omega]
  | succ n ih =>
    have h0 : (h:Int)+(n:Int)<2*i := by omega
    have h1 : ((h+1:Nat):Int)+(n:Int)<2*i := by omega
    by_cases he : h=0
    · subst h
      have ha := ih 0 i h0
      have hb := ih 1 i h1
      simp [unmarked_succ,A,ha,hb]
    · have h2 : ((h-1:Nat):Int)+(n:Int)<2*(i-1) := by omega
      simp [unmarked_succ,A,he,ih h i h0,ih (h+1) i h1,ih (h-1) (i-1) h2]

def Qmodel (n i : Nat) : Nat := unmarked n 0 (i:Int)

theorem Qmodel_degree : DegreeCut Qmodel := by
  intro n i hi
  exact unmarked_degree n 0 _ (by omega)

theorem flatCoeff_marked (n i : Nat) :
    flatCoeff Qmodel n i=2^n*predChoose n i+marked n 0 (i:Int) := by
  rw [marked_binomial]
  unfold flatCoeff transform
  congr 1
  apply csum_congr
  intro k hk
  have hkn : k≤n := by omega
  by_cases he : n-k≤i
  · simp only [term,he,ite_true,Qmodel]
    have h : ((i-(n-k):Nat):Int)=(i:Int)-((n:Int)-(k:Int)) := by omega
    rw [h]
  · rw [term,ite_eq_right he]
    have h : (i:Int)-((n:Int)-(k:Int))<0 := by omega
    rw [unmarked_negative k 0 _ h,Nat.mul_zero]

#print axioms marked_binomial
#print axioms Qmodel_degree
#print axioms flatCoeff_marked
end InverseZ.ThagomizerMarker


namespace InverseZ.ThagomizerIntegration
open InverseZ.ThagomizerRows
open InverseZ.ThagomizerReflection
open InverseZ.ThagomizerCount
open InverseZ.ThagomizerMarker
open InverseZ.ThagomizerRigidity

def safe (h : Int) : List Step → Bool
  | [] => decide (0≤h)
  | a::l => decide (0≤h) && safe (h+inc a) l

theorem safe_negative (h : Int) (l : List Step) (hh : h<0) : safe h l=false := by
  have hf : ¬ 0≤h := by omega
  cases l <;> simp [safe,hf]

theorem safe_iff (h : Int) (l : List Step) :
    safe h l=true ↔ ∀ p q, l=p++q → 0≤h+weight p := by
  induction l generalizing h with
  | nil =>
    constructor
    · intro hh p q he
      have hnil : p=[] := by
        cases p with
        | nil => rfl
        | cons b p => simp at he
      simpa [hnil,weight,safe] using hh
    · intro hh
      have hh' := hh [] [] rfl
      simpa [weight,safe] using hh'
  | cons a l ih =>
    simp only [safe,Bool.and_eq_true,decide_eq_true_eq,ih]
    constructor
    · intro hh p q he
      cases p with
      | nil => simpa [weight] using hh.1
      | cons b p =>
        have hb : a=b := (List.cons.inj he).1
        have he' : l=p++q := (List.cons.inj he).2
        have hw := hh.2 p q he'
        subst b
        simp only [weight]
        omega
    · intro hh
      refine ⟨by simpa [weight] using hh [] (a::l) rfl,?_⟩
      intro p q he
      have hw := hh (a::p) q (by simp [he])
      simp only [weight] at hw
      omega

theorem safe_zero_iff (l : List Step) : safe 0 l=true ↔ ¬ Bad l := by
  rw [safe_iff]
  constructor
  · intro hl hb
    obtain ⟨p,q,he,hp⟩ := hb
    have hh := hl p q he
    omega
  · intro hb p q he
    by_cases hn : weight p<0
    · exact (hb ⟨p,q,he,hn⟩).elim
    · omega

def concrete (n h : Nat) (i : Int) : Nat :=
  (words n).countP (fun l => (decide ((left l:Int)=i)) && safe (h:Int) l)

@[simp] private theorem left_ff (b : Bool) (l : List Step) :
    left ((false,b)::l)=left l := by simp [left,ones]
@[simp] private theorem left_tt (b : Bool) (l : List Step) :
    left ((true,b)::l)=left l+1 := by simp [left,ones,Nat.add_comm]

private theorem castShift (a : Nat) (i : Int) :
    decide (((a+1:Nat):Int)=i)=decide ((a:Int)=i-1) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  omega

theorem concrete_eq_marked (n h : Nat) (i : Int) : concrete n h i=marked n h i := by
  induction n generalizing h i with
  | zero =>
    by_cases he : i=0
    · simp [he,concrete,words,safe,left,marked]
    · simp [he,Ne.symm he,concrete,words,safe,left,marked]
  | succ n ih =>
    have hu : (h:Int)+inc (false,true)=((h+1:Nat):Int) := by simp [inc,ones]
    have hd : (h:Int)+inc (true,false)=(h:Int)-1 := by simp [inc,ones,Int.sub_eq_add_neg]
    have hh : decide (0≤(h:Int))=true := by simp
    have hz0 : inc (false,false)=0 := by decide
    have hz1 : inc (true,true)=0 := by decide
    have both : (fun l : List Step => decide ((left l:Int)=i-1) && safe ((h:Int)-1) l)
          = if h=0 then (fun _ => false)
            else fun l => decide ((left l:Int)=i-1) && safe ((h-1:Nat):Int) l := by
      funext l
      by_cases he : h=0
      · simp [he,safe_negative (-1) l (by decide)]
      · have hc : (h:Int)-1=((h-1:Nat):Int) := by omega
        simp [he,hc]
    simp only [concrete,words,List.countP_append,List.countP_map,Function.comp_def,
      left_ff,left_tt,safe,hh,Bool.true_and,hu,hd,hz0,hz1,Int.add_zero,castShift, both]
    have hd' :
        (words n).countP (if h=0 then (fun _ => false)
            else fun l => decide ((left l:Int)=i-1) && safe ((h-1:Nat):Int) l) =
        (if h=0 then 0 else concrete n (h-1) (i-1)) := by
      by_cases he : h=0 <;> simp [he,concrete]
    rw [hd']
    change concrete n h i+concrete n (h+1) i+
      (if h=0 then 0 else concrete n (h-1) (i-1))+concrete n h (i-1)=_
    simp [ih,marked,A,mark]


private theorem right_le_length (p : List Step) : right p≤p.length := by
  induction p with
  | nil => simp [right]
  | cons a p ih =>
    obtain ⟨a,b⟩ := a
    cases b <;> simp [right,ones] <;> omega

def goodPred (i : Nat) (p : List Step) : Bool :=
  decide ((left p:Int)=(i:Int)) && safe 0 p

theorem goodN_filter (n i k : Nat) :
    goodN n i k = (words n).countP (fun p => goodPred i p && (right p == k)) := by
  have h :
      (fun p : List Step => !badFlag p && decide ((left p:Int)=(i:Int) ∧ (right p:Int)=(k:Int))) =
      (fun p : List Step => goodPred i p && (right p == k)) := by
    funext p
    apply Bool.eq_iff_iff.mpr
    have hb : badFlag p=false ↔ ¬Bad p := by
      cases hh : badFlag p <;> simp [← flag_iff,hh]
    simp [goodPred,hb,safe_zero_iff,Int.natCast_inj,and_assoc,and_comm]
  unfold goodN goodList pairList
  rw [List.filter_filter,h,List.countP_eq_length_filter]

private theorem csum_zero (f : Nat → Nat) (m : Nat) (h : ∀ k, k<m → f k=0) :
    csum f m=0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [csum,ih (fun k hk=>h k (by omega)),h m (by omega)]

private theorem csum_add' (f g : Nat → Nat) (m : Nat) :
    csum (fun k=>f k+g k) m=csum f m+csum g m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [csum]
    rw [ih]
    omega

private theorem csum_indicator (k m : Nat) :
    csum (fun j=>if j=k then 1 else 0) m = if k<m then 1 else 0 := by
  induction m with
  | zero => simp [csum]
  | succ m ih =>
    simp only [csum]
    rw [ih]
    by_cases h₀ : k<m
    · have h₁ : m≠k := by omega
      have h₂ : k<m+1 := by omega
      simp [h₀,h₁,h₂]
    · by_cases h₁ : m=k
      · subst m
        simp
      · have h₂ : ¬k<m+1 := by omega
        simp [h₀,h₁,h₂]

private theorem partition_count (L : List (List Step)) (P : List Step → Bool)
    (n : Nat) (hL : ∀ l∈L, right l≤n) :
    csum (fun k => L.countP (fun l=>P l && (right l == k))) (n+1) = L.countP P := by
  induction L with
  | nil =>
    exact csum_zero _ _ (fun _ _=>rfl)
  | cons a L ih =>
    have har := hL a (by simp)
    have htail := ih (fun l hl=>hL l (by simp [hl]))
    simp only [List.countP_cons]
    rw [csum_add',htail]
    cases hp : P a with
    | false =>
      have hz : csum (fun _ => 0) (n+1)=0 := csum_zero _ _ (fun _ _=>rfl)
      simp [hz]
    | true =>
      have h : csum (fun k => if (true && (right a == k))=true then 1 else 0) (n+1)=1 := by
        simp only [Bool.true_and,beq_iff_eq]
        have heq : (fun k => if right a=k then 1 else 0) =
            (fun k => if k=right a then 1 else 0) := by
          funext k
          simp [eq_comm]
        rw [heq,csum_indicator,ite_eq_left (by omega : right a<n+1)]
      rw [h]
      simp

private theorem good_below_zero (n i k : Nat) (hk : k<i) : goodN n i k=0 := by
  unfold goodN
  have he : goodList n (i:Int) (k:Int)=[] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro w hw
    obtain ⟨hr,hg⟩ := List.mem_filter.mp hw
    obtain ⟨_,hl,hr'⟩ := (mem_pairList _ _ _ _).mp hr
    have hbad : Bad w := by
      refine ⟨w,[],by simp,?_⟩
      rw [weight_counts,hl,hr']
      omega
    have hb := (flag_iff _).mpr hbad
    simp [hb] at hg
  simp [he]

theorem concrete_eq_summed (n i : Nat) (hi : i≤n+1) :
    concrete n 0 (i:Int) = span (goodN n i) i (n+1-i) := by
  have he0 : csum (goodN n i) i=0 :=
    csum_zero _ _ (fun k hk=>good_below_zero n i k hk)
  have hsum := span_eq_csum (goodN n i) i (n+1-i)
  have hNat : i+(n+1-i)=n+1 := by omega
  rw [he0,Nat.zero_add,hNat] at hsum
  rw [hsum]
  have hp := partition_count (words n) (goodPred i) n (fun w hw=>by
    rw [← (words_mem n w).mp hw]
    exact right_le_length w)
  rw [csum_congr (f:=goodN n i)
    (g:=fun k => (words n).countP (fun p => goodPred i p && (right p == k))) (n+1)
    (fun k _=>goodN_filter n i k)]
  exact hp.symm


private theorem csum_head' (f : Nat → Nat) (n : Nat) :
    csum f (n+1)=f 0+csum (fun k=>f (k+1)) n := by
  induction n with
  | zero => simp [csum]
  | succ n ih =>
    change csum f (n+1)+f (n+1)=f 0+(csum (fun k=>f (k+1)) n+f (n+1))
    rw [ih]
    omega

theorem choose_total (n : Nat) : csum (choose n) (n+1)=2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hz : choose n (n+1)=0 := choose_eq_zero_of_lt (by omega)
    have hh := csum_head' (choose n) n
    have hs : csum (fun k=>choose n (k+1)) (n+1) =
        csum (fun k=>choose n (k+1)) n := by
      change csum (fun k=>choose n (k+1)) n+choose n (n+1)=_
      rw [hz,Nat.add_zero]
    rw [csum_head',choose_zero_right]
    simp only [choose_succ_succ,csum_add',hs]
    rw [Nat.pow_succ]
    rw [choose_zero_right] at hh
    omega

theorem flatCoeff_eq_row (n i : Nat) (hi : i≤n+1) :
    flatCoeff Qmodel n i=row n i := by
  rw [flatCoeff_marked,← concrete_eq_marked,concrete_eq_summed n i hi,← choose_total]
  have hh := model_eq_row n i hi
  unfold modelCoeff at hh
  simpa only [Nat.mul_comm, Nat.add_comm] using hh

theorem flatCoeff_positive (n i : Nat) (hi : i≤n+1) :
    0<flatCoeff Qmodel n i := by
  rw [flatCoeff_eq_row n i hi]
  exact row_positive n i hi

theorem flatCoeff_minor (n i : Nat) (hi : i+1≤n) :
    flatCoeff Qmodel n i*flatCoeff Qmodel n (i+2) <
    flatCoeff Qmodel n (i+1)*flatCoeff Qmodel n (i+1) := by
  rw [flatCoeff_eq_row n i (by omega),flatCoeff_eq_row n (i+2) (by omega),
    flatCoeff_eq_row n (i+1) (by omega)]
  exact row_minor n i hi


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

theorem tail_csum_reflect (n i : Nat) (hi : i≤n+1) :
    tail n (n+1-i)=csum (choose n) i := by
  induction i with
  | zero => simp [tail,csum]
  | succ i ih =>
    have hi' : i≤n := by omega
    have h := tail_step n (n-i) (by omega)
    have e : n+1-(i+1)=n-i := by omega
    have e' : n-i+1=n+1-i := by omega
    rw [e',ih (by omega),choose_reflect n i hi'] at h
    rw [e,csum,← h]

theorem row_palindrome (n i : Nat) (hi : i≤n+1) :
    row n i=row n (n+1-i) := by
  by_cases he : i=0
  · subst i
    have hz : choose n (n+1)=0 := choose_eq_zero_of_lt (by omega)
    have hP : csum (choose n) (n+1+1)=csum (choose n) (n+1) := by
      rw [csum,hz,Nat.add_zero]
    simp [row,tail,predChoose,csum,choose_self,hz]
  · by_cases hh : i=n+1
    · have hz : choose n (n+1)=0 := choose_eq_zero_of_lt (by omega)
      subst i
      simp [row,tail,predChoose,csum,choose_self,hz]
    · have hni : i≤n := by omega
      let j := n+1-i
      have hj : 0<j := by dsimp [j]; omega
      have hnj : j≤n := by dsimp [j]; omega
      have e₀ : j=n-(i-1) := by dsimp [j]; omega
      have e₁ : j-1=n-i := by dsimp [j]; omega
      have b₀ : choose n j = predChoose n i := by
        rw [e₀,choose_reflect n (i-1) (by omega)]
        cases i with
        | zero => contradiction
        | succ i => rfl
      have b₁ : predChoose n j = choose n i := by
        have je : predChoose n j = choose n (j-1) := by
          have h : j=(j-1)+1 := by omega
          exact congrArg (predChoose n) h
        rw [je,e₁,choose_reflect n i hni]
      have hT : tail n j=csum (choose n) i := tail_csum_reflect n i hi
      have hU : csum (choose n) (j+1)=tail n (i-1) := by
        have h := tail_csum_reflect n (j+1) (by omega)
        have e : n+1-(j+1)=i-1 := by dsimp [j]; omega
        rw [e] at h
        exact h.symm
      have ht : tail n (i-1)=tail n i+predChoose n i := by
        cases i with
        | zero => contradiction
        | succ i => exact (tail_step n i (by omega)).symm
      change row n i=row n j
      unfold row
      rw [b₀,b₁,hT,hU,ht,csum]
      grind

theorem Qmodel_palindrome : Palindrome Qmodel := by
  intro n i hi
  rw [flatCoeff_eq_row n i hi,flatCoeff_eq_row n (n+1-i) (by omega)]
  exact row_palindrome n i hi

/-- The literal weighted-flat family has the desired strict minors for
any source inverse-KL realization of the standard cutoff and palindrome identities. -/
theorem source_family_strict (Q : Nat → Nat → Nat) (hd : DegreeCut Q) (hp : Palindrome Q)
    (n i : Nat) (hi : i+1≤n) :
    flatCoeff Q n i*flatCoeff Q n (i+2) <
    flatCoeff Q n (i+1)*flatCoeff Q n (i+1) := by
  rw [computed_Y_unique Q Qmodel hd Qmodel_degree hp Qmodel_palindrome]
  exact flatCoeff_minor n i hi

#print axioms row_palindrome
#print axioms source_family_strict
#print axioms flatCoeff_eq_row
#print axioms flatCoeff_minor
#print axioms concrete_eq_marked
#print axioms concrete_eq_summed
end InverseZ.ThagomizerIntegration


namespace InverseZ.ThagomizerMobius
open InverseZ.ThagomizerRows
open InverseZ.ThagomizerRigidity

def sumZ (f : Nat → Int) : Nat → Int
  | 0 => 0
  | i+1 => sumZ f i+f i

theorem sumZ_congr {f g : Nat → Int} (m : Nat) (h : ∀ k, k<m → f k=g k) :
    sumZ f m=sumZ g m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [sumZ]
    rw [ih (fun k hk=>h k (by omega)),h m (by omega)]

theorem sumZ_head (f : Nat → Int) (n : Nat) :
    sumZ f (n+1)=f 0+sumZ (fun k=>f (k+1)) n := by
  induction n with
  | zero => simp [sumZ]
  | succ n ih =>
    change sumZ f (n+1)+f (n+1)=f 0+(sumZ (fun k=>f (k+1)) n+f (n+1))
    rw [ih]
    omega

theorem sumZ_add (f g : Nat → Int) (n : Nat) :
    sumZ (fun k=>f k+g k) n=sumZ f n+sumZ g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumZ]
    rw [ih]
    omega

theorem sumZ_neg (f : Nat → Int) (n : Nat) :
    sumZ (fun k=> -f k) n= -sumZ f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumZ]
    rw [ih]
    omega

def boolMu (k : Nat) : Int := (-1)^k
def thagMu (k : Nat) : Int := -((-2)^k)

theorem boolMu_step (k : Nat) : boolMu (k+1)= - boolMu k := by
  unfold boolMu
  rw [Int.pow_succ]
  omega

/-- This is the Boolean lattice Möbius recursion, grouped by cardinality. -/
theorem boolMu_sum (n : Nat) :
    sumZ (fun k => (choose (n+1) k:Int)*boolMu k) (n+1+1)=0 := by
  let b : Nat → Int := fun k=> (choose n k:Int)*boolMu k
  have hz : choose n (n+1)=0 := choose_eq_zero_of_lt (by omega)
  have hx : sumZ (fun k => b (k+1)) (n+1)=sumZ (fun k=>b (k+1)) n := by
    rw [sumZ]
    have he : b (n+1)=0 := by simp [b,hz]
    simp [he]
  have h := sumZ_head b n
  rw [sumZ_head (fun k => (choose (n+1) k:Int)*boolMu k) (n+1)]
  simp only [choose_zero_right,Int.ofNat_one,Int.one_mul,choose_succ_succ,
    Int.natCast_add,Int.add_mul,sumZ_add]
  have he : sumZ (fun k => (choose n k:Int)*boolMu (k+1)) (n+1) = -sumZ b (n+1) := by
    rw [← sumZ_neg]
    apply sumZ_congr
    intro k _
    simp [boolMu_step,b,Int.mul_neg]
  have h₀ : b 0 = boolMu 0 := by simp [b]
  rw [he]
  change boolMu 0 + (-sumZ b (n+1)+sumZ (fun k=>b (k+1)) (n+1))=0
  rw [hx,h,h₀]
  omega

theorem split_orbit_mu (k : Nat) : (2:Int)^k*boolMu k=(-2)^k := by
  unfold boolMu
  have h : ((2:Int)*(-1))^k=(2:Int)^k*(-1)^k := by
    induction k with
    | zero => decide
    | succ k ih =>
      simp only [Int.pow_succ]
      rw [ih]
      ac_rfl
  exact h.symm

/-- Möbius sum over all thagomizer flats, split and joined, including top once. -/
def TopRec (M : Nat → Int) : Prop := ∀ n,
    M n + sumZ (fun k => (choose n k:Int)*M k) n +
      sumZ (fun k => (choose n k:Int)*(-2)^k) (n+1)=0

theorem thagMu_valid : TopRec thagMu := by
  intro n
  have hc : sumZ (fun k => (choose n k:Int)*thagMu k) n =
      -sumZ (fun k => (choose n k:Int)*(-2)^k) n := by
    rw [←sumZ_neg]
    apply sumZ_congr
    intro k _
    simp [thagMu,Int.mul_neg]
  rw [hc]
  have hf : sumZ (fun k => (choose n k:Int)*(-2)^k) (n+1) =
      sumZ (fun k => (choose n k:Int)*(-2)^k) n+(-2)^n := by
    rw [sumZ]
    simp [choose_self]
  rw [hf]
  unfold thagMu
  omega

theorem thagMu_unique (M : Nat → Int) (hM : TopRec M) : M=thagMu := by
  funext n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have h₀ := hM n
    have h₁ := thagMu_valid n
    have he : sumZ (fun k => (choose n k:Int)*M k) n =
      sumZ (fun k => (choose n k:Int)*thagMu k) n := by
      apply sumZ_congr
      intro k hk
      rw [ih k hk]
    rw [he] at h₀
    omega

#print axioms boolMu_sum
#print axioms thagMu_unique
end InverseZ.ThagomizerMobius



namespace InverseZ.ThagomizerFlat

inductive Vertex (n : Nat)
  | hub (side : Bool)
  | leaf (i : Fin n)

inductive Edge (n : Nat)
  | spine
  | spoke (side : Bool) (i : Fin n)

def src : Edge n → Vertex n
  | .spine => .hub false
  | .spoke side _ => .hub side
def dst : Edge n → Vertex n
  | .spine => .hub true
  | .spoke _ i => .leaf i

inductive Reach (f : Edge n → Bool) : Vertex n → Vertex n → Prop
  | refl (a) : Reach f a a
  | edge (e) : f e = true → Reach f (src e) (dst e)
  | symm : Reach f a b → Reach f b a
  | trans : Reach f a b → Reach f b c → Reach f a c

/-- Closure criterion for an edge set in a graphic matroid. -/
def Flat (f : Edge n → Bool) : Prop := ∀ e, Reach f (src e) (dst e) → f e=true

def Joined (f : Edge n → Bool) : Prop :=
  f .spine=true ∧ ∀ i, f (.spoke false i)=f (.spoke true i)
def Split (f : Edge n → Bool) : Prop :=
  f .spine=false ∧ ∀ i, ¬ (f (.spoke false i)=true ∧ f (.spoke true i)=true)

theorem flat_joined_or_split {f : Edge n → Bool} (hf : Flat f) : Joined f ∨ Split f := by
  cases he : f Edge.spine with
  | false =>
    right
    refine ⟨he,?_⟩
    intro i h
    have z : Reach f (Vertex.hub false) (Vertex.hub true) :=
      Reach.trans (Reach.edge (Edge.spoke false i) h.1)
      (Reach.symm (Reach.edge (Edge.spoke true i) h.2))
    have ht := hf .spine z
    rw [he] at ht
    contradiction
  | true =>
    left
    refine ⟨he,?_⟩
    intro i
    have z : Reach f (Vertex.hub false) (Vertex.hub true) := Reach.edge .spine he
    by_cases hl : f (.spoke false i)=true
    · have hr : f (.spoke true i)=true :=
        hf (.spoke true i) (Reach.trans (Reach.symm z) (Reach.edge (.spoke false i) hl))
      exact hl.trans hr.symm
    · have hr : f (.spoke true i)≠true := by
        intro ht
        exact hl (hf (.spoke false i) (Reach.trans z (Reach.edge (.spoke true i) ht)))
      grind

theorem reach_preserves_label {f : Edge n → Bool} {label : Vertex n → α}
    (h : ∀ e, f e=true → label (src e)=label (dst e))
    {a b : Vertex n} (hr : Reach f a b) : label a=label b := by
  induction hr with
  | refl => rfl
  | edge e he => exact h e he
  | symm _ ih => exact ih.symm
  | trans _ _ ih jh => exact ih.trans jh

def jlabel (f : Edge n → Bool) : Vertex n → Vertex n
  | .hub _ => .hub false
  | .leaf i => if f (.spoke false i) then .hub false else .leaf i

def slabel (f : Edge n → Bool) : Vertex n → Vertex n
  | .hub s => .hub s
  | .leaf i => if f (.spoke false i) then .hub false
    else if f (.spoke true i) then .hub true else .leaf i

theorem joined_edge_label {f : Edge n → Bool} (hj : Joined f) (e : Edge n) :
    f e=true ↔ jlabel f (src e)=jlabel f (dst e) := by
  cases e with
  | spine => simp [src,dst,jlabel,hj.1]
  | spoke s i =>
    have hh := hj.2 i
    cases s <;> cases he : f (Edge.spoke false i) <;> simp [src,dst,jlabel,he] at hh ⊢
    all_goals simp [hh]

theorem split_edge_label {f : Edge n → Bool} (hs : Split f) (e : Edge n) :
    f e=true ↔ slabel f (src e)=slabel f (dst e) := by
  cases e with
  | spine => simp [src,dst,slabel,hs.1]
  | spoke s i =>
    have hn := hs.2 i
    cases s <;> cases hl : f (Edge.spoke false i) <;>
      cases hr : f (Edge.spoke true i) <;> simp [src,dst,slabel,hl,hr] at hn ⊢

theorem joined_flat {f : Edge n → Bool} (hj : Joined f) : Flat f := by
  intro e hr
  exact (joined_edge_label hj e).mpr
    (reach_preserves_label (fun a => (joined_edge_label hj a).mp) hr)

theorem split_flat {f : Edge n → Bool} (hs : Split f) : Flat f := by
  intro e hr
  exact (split_edge_label hs e).mpr
    (reach_preserves_label (fun a => (split_edge_label hs a).mp) hr)

theorem flat_iff (f : Edge n → Bool) : Flat f ↔ Joined f ∨ Split f :=
  ⟨flat_joined_or_split,fun h => h.elim joined_flat split_flat⟩


theorem reach_jlabel {f : Edge n → Bool} (h : Joined f) (v : Vertex n) :
    Reach f v (jlabel f v) := by
  cases v with
  | hub side =>
    cases side
    · exact Reach.refl _
    · exact Reach.symm (Reach.edge .spine h.1)
  | leaf i =>
    change Reach f (.leaf i)
      (if f (.spoke false i) then .hub false else .leaf i)
    split
    · rename_i hi
      exact Reach.symm (Reach.edge (.spoke false i) hi)
    · exact Reach.refl _

theorem reach_slabel {f : Edge n → Bool} (v : Vertex n) :
    Reach f v (slabel f v) := by
  cases v with
  | hub side => exact Reach.refl _
  | leaf i =>
    change Reach f (.leaf i)
      (if f (.spoke false i) then .hub false else
        if f (.spoke true i) then .hub true else .leaf i)
    split
    · rename_i hi
      exact Reach.symm (Reach.edge (.spoke false i) hi)
    · split
      · rename_i hi
        exact Reach.symm (Reach.edge (.spoke true i) hi)
      · exact Reach.refl _

theorem joined_component {f : Edge n → Bool} (h : Joined f) (a b : Vertex n) :
    Reach f a b ↔ jlabel f a=jlabel f b := by
  constructor
  · exact fun r => reach_preserves_label (fun e => (joined_edge_label h e).mp) r
  · intro he
    exact Reach.trans (he ▸ reach_jlabel h a) (Reach.symm (reach_jlabel h b))

theorem split_component {f : Edge n → Bool} (h : Split f) (a b : Vertex n) :
    Reach f a b ↔ slabel f a=slabel f b := by
  constructor
  · exact fun r => reach_preserves_label (fun e => (split_edge_label h e).mp) r
  · intro he
    exact Reach.trans (he ▸ reach_slabel a) (Reach.symm (reach_slabel b))

def ofJoined (S : Fin n → Bool) : Edge n → Bool :=
  fun e => Edge.casesOn e true (fun _ i => S i)

def ofSplit (S : Fin n → Option Bool) : Edge n → Bool :=
  fun e => Edge.casesOn e false (fun side i => S i == some side)

def toJoined (f : Edge n → Bool) (i : Fin n) : Bool := f (.spoke false i)

def toSplit (f : Edge n → Bool) (i : Fin n) : Option Bool :=
  if f (.spoke false i) then some false
  else if f (.spoke true i) then some true else none

theorem encode_joined (f : Edge n → Bool) (h : Joined f) : ofJoined (toJoined f)=f := by
  funext e
  cases e with
  | spine => exact h.1.symm
  | spoke side i =>
    cases side
    · rfl
    · exact h.2 i

@[simp] theorem decode_joined (S : Fin n → Bool) : toJoined (ofJoined S)=S := rfl

theorem encode_split (f : Edge n → Bool) (h : Split f) : ofSplit (toSplit f)=f := by
  funext e
  cases e with
  | spine => exact h.1.symm
  | spoke side i =>
    have hn := h.2 i
    cases side <;> cases hl : f (Edge.spoke false i) <;> cases hr : f (Edge.spoke true i) <;>
      simp [ofSplit,toSplit,hl,hr] at hn ⊢

@[simp] theorem decode_split (S : Fin n → Option Bool) : toSplit (ofSplit S)=S := by
  funext i
  cases he : S i with
  | none => simp [ofSplit,toSplit,he]
  | some s => cases s <;> simp [ofSplit,toSplit,he]

theorem joined_code_flat (S : Fin n → Bool) : Flat (ofJoined S) :=
  joined_flat ⟨rfl,fun _ => rfl⟩

theorem split_code_flat (S : Fin n → Option Bool) : Flat (ofSplit S) :=
  split_flat ⟨rfl,fun i => by cases h : S i with
    | none => simp [ofSplit,h]
    | some s => cases s <;> simp [ofSplit,h]⟩

/-- Endpoints of nonloop edges in a joined contraction.  Both spokes
of an unselected leaf become the same endpoint pair. -/
theorem joined_unselected_spoke (S : Fin n → Bool) (i : Fin n) (h : S i=false)
    (side : Bool) :
    (jlabel (ofJoined S) (src (.spoke side i)),
     jlabel (ofJoined S) (dst (.spoke side i))) = (.hub false,.leaf i) := by
  simp [src,dst,jlabel,ofJoined,h]

theorem split_unselected_spoke (S : Fin n → Option Bool) (i : Fin n) (h : S i=none)
    (side : Bool) :
    (slabel (ofSplit S) (src (.spoke side i)),
     slabel (ofSplit S) (dst (.spoke side i))) = (.hub side,.leaf i) := by
  simp [src,dst,slabel,ofSplit,h]

theorem split_other_spoke (S : Fin n → Option Bool) (i : Fin n) (a : Bool) (h : S i=some a) :
    (slabel (ofSplit S) (src (.spoke (!a) i)),
     slabel (ofSplit S) (dst (.spoke (!a) i))) = (.hub (!a),.hub a) := by
  cases a <;> simp [src,dst,slabel,ofSplit,h]

#print axioms flat_iff
#print axioms joined_component
#print axioms split_component
#print axioms encode_joined
#print axioms encode_split
#print axioms split_other_spoke
end InverseZ.ThagomizerFlat


namespace InverseZ.ThagomizerRank
open InverseZ.ThagomizerFlat

def bit (b : Bool) : Nat := if b then 1 else 0

def countOn (L : List α) (f : α → Nat) : Nat := (L.map f).sum
def finSum (f : Fin n → Nat) : Nat := countOn (List.finRange n) f

private theorem countOn_le {L : List α} {f g : α → Nat} (h : ∀ i ∈ L, f i ≤ g i) :
    countOn L f ≤ countOn L g := by
  induction L with
  | nil => exact Nat.le_refl _
  | cons a L ih =>
    exact Nat.add_le_add (h a (by simp)) (ih (fun i hi => h i (by simp [hi])))

private theorem countOn_congr {L : List α} {f g : α → Nat} (h : ∀ i ∈ L, f i = g i) :
    countOn L f = countOn L g :=
  Nat.le_antisymm (countOn_le (fun i hi => Nat.le_of_eq (h i hi)))
    (countOn_le (fun i hi => Nat.le_of_eq (h i hi).symm))

private theorem finSum_le {f g : Fin n → Nat} (h : ∀ i, f i ≤ g i) :
    finSum f ≤ finSum g := countOn_le (fun i _ => h i)
private theorem finSum_congr {f g : Fin n → Nat} (h : ∀ i, f i = g i) :
    finSum f = finSum g := countOn_congr (fun i _ => h i)

private theorem countOn_add (L : List α) (f g : α → Nat) :
    countOn L (fun i => f i+g i) = countOn L f+countOn L g := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    change f a+g a+countOn L _ = f a+countOn L f+(g a+countOn L g)
    rw [ih]
    omega

private theorem countOn_zero (L : List α) : countOn L (fun _ => 0) = 0 := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    change 0+countOn L (fun _ => 0)=0
    omega

private theorem finSum_positive {f : Fin n → Nat} (h : 0 < finSum f) :
    ∃ i, 0 < f i := by
  classical
  by_cases hx : ∃ i, 0 < f i
  · exact hx
  · have he : finSum f=0 := calc
      _ = finSum (fun _ => 0) := finSum_congr (fun i => by
        by_cases h0 : f i=0
        · exact h0
        · exact (hx ⟨i,by omega⟩).elim)
      _ = 0 := countOn_zero _
    omega

private theorem countOn_indicator {α : Type} [DecidableEq α] (a : α)
    {L : List α} (hn : L.Nodup) (ha : a ∈ L) :
    countOn L (fun i => if i=a then 1 else 0) = 1 := by
  induction L with
  | nil => simp at ha
  | cons i L ih =>
    have hn' := (List.nodup_cons.mp hn)
    by_cases e : i=a
    · subst i
      have hL : countOn L (fun i => if i=a then 1 else 0)=0 := calc
        _ = countOn L (fun _ => 0) := countOn_congr (fun i hi => by
          have hh : i≠a := fun hh => hn'.1 (hh ▸ hi)
          simp [hh])
        _ = 0 := countOn_zero _
      change (if a=a then 1 else 0)+countOn L _=1
      rw [hL]
      simp
    · have hl : a ∈ L := by simpa [e, Ne.symm e] using ha
      have he := ih hn'.2 hl
      change (if i=a then 1 else 0)+countOn L _=1
      rw [he]
      simp [e]

private theorem finSum_indicator (a : Fin n) :
    finSum (fun i => if i=a then 1 else 0)=1 :=
  countOn_indicator a (List.nodup_finRange n) (List.mem_finRange a)

def active (f : Edge n → Bool) (i : Fin n) : Nat :=
  bit (f (.spoke false i) || f (.spoke true i))
def double (f : Edge n → Bool) (i : Fin n) : Nat :=
  bit (f (.spoke false i) && f (.spoke true i))
def S (f : Edge n → Bool) : Nat := finSum (active f)
def E (f : Edge n → Bool) : Nat := bit (f .spine) + finSum (double f)

def size (f : Edge n → Bool) : Nat :=
  bit (f .spine) + finSum (fun i => bit (f (.spoke false i)) + bit (f (.spoke true i)))

theorem size_decomp (f : Edge n → Bool) : size f = S f+E f := by
  have hh (i : Fin n) : bit (f (.spoke false i)) + bit (f (.spoke true i)) =
      active f i + double f i := by
    cases hl : f (.spoke false i) <;> cases hr : f (.spoke true i) <;>
      simp [active,double,bit,hl,hr]
  unfold size S E finSum
  rw [countOn_congr (fun i _ => hh i),countOn_add]
  omega

def Sub (f g : Edge n → Bool) : Prop := ∀ e, f e=true → g e=true
def Indep (f : Edge n → Bool) : Prop := E f≤1
def rank (f : Edge n → Bool) : Nat := S f + min 1 (E f)

theorem active_mono {f g : Edge n → Bool} (h : Sub f g) (i : Fin n) : active f i≤active g i := by
  specialize h
  simp only [active,bit]
  have hfalse := h (.spoke false i)
  have htrue := h (.spoke true i)
  grind

theorem extra_mono {f g : Edge n → Bool} (h : Sub f g) : E f≤E g := by
  have h1 : bit (f .spine)≤bit (g .spine) := by
    have hp := h .spine
    simp only [bit]
    grind
  have h2 : finSum (double f)≤finSum (double g) := by
    apply finSum_le
    intro i
    have hfalse := h (.spoke false i)
    have htrue := h (.spoke true i)
    simp only [double,bit]
    grind
  exact Nat.add_le_add h1 h2

theorem indep_hereditary {f g : Edge n → Bool} (h : Sub f g) (hg : Indep g) : Indep f :=
  Nat.le_trans (extra_mono h) hg

theorem size_bound {f g : Edge n → Bool} (h : Sub f g) (hf : Indep f) : size f ≤ rank g := by
  rw [size_decomp]
  exact Nat.add_le_add (finSum_le (active_mono h))
    (Nat.le_min.mpr ⟨hf,extra_mono h⟩)

def thin (f : Edge n → Bool) (sp : Bool) (key : Option (Fin n)) : Edge n → Bool
  | .spine => sp
  | .spoke false i => f (.spoke false i)
  | .spoke true i => f (.spoke true i) && (! f (.spoke false i) || key == some i)

theorem thin_sub (f : Edge n → Bool) (sp : Bool) (key : Option (Fin n))
    (hsp : sp=true → f .spine=true) : Sub (thin f sp key) f := by
  intro e he
  cases e with
  | spine => exact hsp he
  | spoke b i =>
    cases b
    · exact he
    · exact (Bool.and_eq_true_iff.mp he).1

theorem thin_active (f : Edge n → Bool) (sp : Bool) (key : Option (Fin n)) :
    S (thin f sp key) = S f := by
  apply finSum_congr
  intro i
  cases hf : f (.spoke false i) <;> cases hg : f (.spoke true i) <;>
    simp [active,thin,hf,hg]

theorem thin_double_none (f : Edge n → Bool) (sp : Bool) :
    finSum (double (thin f sp none))=0 := calc
  _ = finSum (fun _ => 0) := by
    apply finSum_congr
    intro i
    cases hf : f (.spoke false i) <;> cases hg : f (.spoke true i) <;>
      simp [double,thin,bit,hf,hg]
  _ = 0 := countOn_zero _

theorem thin_double_some (f : Edge n → Bool) (sp : Bool) (i : Fin n)
    (hf : f (.spoke false i)=true) (hg : f (.spoke true i)=true) :
    finSum (double (thin f sp (some i)))=1 := calc
  _ = finSum (fun j => if j=i then 1 else 0) := by
    apply finSum_congr
    intro j
    by_cases he : j=i
    · subst j
      simp [double,thin,bit,hf,hg]
    · cases hl : f (.spoke false j) <;> cases hr : f (.spoke true j) <;>
        simp [double,thin,bit,hl,hr,he,Ne.symm he]
  _ = 1 := finSum_indicator i

theorem rank_attained (f : Edge n → Bool) :
    ∃ g, Sub g f ∧ Indep g ∧ size g = rank f := by
  by_cases hE : E f=0
  · let g := thin f false none
    have he : E g=0 := by simp [g,E,thin,bit,thin_double_none]
    refine ⟨g,thin_sub _ _ _ (by simp),?_,?_⟩
    · simp [Indep,he]
    · rw [size_decomp,thin_active,he,rank,hE]
      simp
  · cases he : f Edge.spine with
    | true =>
      let g := thin f true none
      have h1 : E g=1 := by simp [g,E,thin,bit,thin_double_none]
      refine ⟨g,thin_sub _ _ _ (by simp [he]),?_,?_⟩
      · simp [Indep,h1]
      · rw [size_decomp,thin_active,h1,rank]
        have hpos : 1≤E f := by omega
        rw [Nat.min_eq_left hpos]
    | false =>
      have hpos : 0 < finSum (double f) := by
        simp [E,he,bit] at hE
        omega
      obtain ⟨i,hi⟩ := finSum_positive hpos
      have hf : f (.spoke false i)=true := by
        cases hf : f (.spoke false i) <;> simp [double,bit,hf] at hi ⊢
      have hg : f (.spoke true i)=true := by
        cases hg : f (.spoke true i) <;> simp [double,bit,hg] at hi ⊢
      let g := thin f false (some i)
      have h1 : E g=1 := by simp [g,E,thin,bit,thin_double_some f false i hf hg]
      refine ⟨g,thin_sub _ _ _ (by simp),?_,?_⟩
      · simp [Indep,h1]
      · rw [size_decomp,thin_active,h1,rank]
        have hpos' : 1≤E f := by omega
        rw [Nat.min_eq_left hpos']


def insertSpine (f : Edge n → Bool) : Edge n → Bool
  | .spine => true
  | .spoke s i => f (.spoke s i)

def insertSpoke (f : Edge n → Bool) (side : Bool) (j : Fin n) : Edge n → Bool
  | .spine => f .spine
  | .spoke s i => if s=side ∧ i=j then true else f (.spoke s i)

def insert (f : Edge n → Bool) : Edge n → (Edge n → Bool)
  | .spine => insertSpine f
  | .spoke s j => insertSpoke f s j

theorem insert_self (f : Edge n → Bool) (e : Edge n) : insert f e e=true := by
  cases e <;> simp [insert,insertSpine,insertSpoke]

theorem insert_sup (f : Edge n → Bool) (e : Edge n) : Sub f (insert f e) := by
  cases e <;> intro x h
  all_goals cases x <;> simp [insert,insertSpine,insertSpoke,h]

theorem spine_insert_size (f : Edge n → Bool) (h : f .spine=false) :
    S (insertSpine f)=S f ∧ E (insertSpine f)=E f+1 := by
  constructor
  · rfl
  · have he : finSum (double (insertSpine f)) = finSum (double f) := rfl
    simp [E,bit,insertSpine,h,he,Nat.add_comm]

private theorem finSum_bump (f g : Fin n → Nat) (j : Fin n) (δ : Nat)
    (h : ∀ i, g i = f i+(if i=j then δ else 0)) :
    finSum g = finSum f+δ := by
  have h1 : finSum (fun i => if i=j then δ else 0) = δ := by
    have h2 : ∀ i : Fin n, (if i=j then δ else 0) = (if i=j then 1 else 0)*δ := by
      intro i
      by_cases he : i=j <;> simp [he]
    have hscale (L : List (Fin n)) :
        countOn L (fun i => (if i=j then 1 else 0)*δ) =
        countOn L (fun i => if i=j then 1 else 0)*δ := by
      induction L with
      | nil => simp [countOn]
      | cons i L ih =>
        change (if i=j then 1 else 0)*δ+countOn L _ =
          ((if i=j then 1 else 0)+countOn L _)*δ
        rw [ih,Nat.add_mul]
    calc
      _ = finSum (fun i => (if i=j then 1 else 0)*δ) := finSum_congr h2
      _ = finSum (fun i => if i=j then 1 else 0)*δ := hscale _
      _ = _ := by rw [finSum_indicator]; simp
  calc
    _ = finSum (fun i => f i+(if i=j then δ else 0)) := finSum_congr h
    _ = finSum f+finSum (fun i => if i=j then δ else 0) := countOn_add _ _ _
    _ = _ := by rw [h1]

theorem spoke_insert_size (f : Edge n → Bool) (s : Bool) (j : Fin n)
    (h : f (.spoke s j)=false) :
    S (insertSpoke f s j)=S f+bit (! f (.spoke (!s) j)) ∧
    E (insertSpoke f s j)=E f+bit (f (.spoke (!s) j)) := by
  constructor
  · apply finSum_bump (j:=j)
    intro i
    by_cases he : i=j
    · subst i
      cases s <;> simp [active,insertSpoke,bit,h] <;> split <;> simp_all
    · simp [active,insertSpoke,he]
  · have he : finSum (double (insertSpoke f s j)) =
        finSum (double f)+bit (f (.spoke (!s) j)) := by
      apply finSum_bump (j:=j)
      intro i
      by_cases he : i=j
      · subst i
        cases s <;> simp [double,insertSpoke,bit,h]
      · simp [double,insertSpoke,he]
    unfold E
    have hsp : insertSpoke f s j .spine = f .spine := rfl
    rw [hsp,he]
    omega

theorem insert_extra_le (f : Edge n → Bool) (e : Edge n) (he : f e=false) :
    E (insert f e)≤E f+1 := by
  cases e with
  | spine =>
    exact Nat.le_of_eq (spine_insert_size f he).2
  | spoke s j =>
    change E (insertSpoke f s j)≤E f+1
    rw [(spoke_insert_size f s j he).2]
    cases h : f (.spoke (!s) j) <;> simp [bit]

theorem E_zero_iff (f : Edge n → Bool) : E f=0 ↔ Split f := by
  constructor
  · intro h
    have hsp : f .spine=false := by
      cases he : f Edge.spine <;> simp [E,he,bit] at h ⊢
    refine ⟨hsp,?_⟩
    intro i hh
    have hh' : finSum (fun j => if j=i then 1 else 0)≤finSum (double f) := by
      apply finSum_le
      intro j
      by_cases he : j=i
      · subst j
        simp [double,bit,hh.1,hh.2]
      · simp [he]
    rw [finSum_indicator] at hh'
    simp [E,hsp,bit] at h
    omega
  · intro h
    have hh : finSum (double f)=0 := calc
      _ = finSum (fun _ => 0) := by
        apply finSum_congr
        intro i
        have hs := h.2 i
        cases hl : f (.spoke false i) <;> cases hr : f (.spoke true i) <;>
          simp [double,bit,hl,hr] at hs ⊢
      _ = 0 := countOn_zero _
    simp [E,h.1,bit,hh]

theorem spine_closure (f : Edge n → Bool) (h : f .spine=false) :
    rank (insert f .spine)=rank f ↔ 0<E f := by
  have hs := spine_insert_size f h
  change rank (insertSpine f)=rank f ↔ _
  unfold rank
  rw [hs.1,hs.2]
  omega

theorem spoke_closure (f : Edge n → Bool) (s : Bool) (j : Fin n) (h : f (.spoke s j)=false) :
    rank (insert f (.spoke s j))=rank f ↔ f (.spoke (!s) j)=true ∧ 0<E f := by
  have hs := spoke_insert_size f s j h
  change rank (insertSpoke f s j)=rank f ↔ _
  unfold rank
  rw [hs.1,hs.2]
  cases he : f (.spoke (!s) j) <;> simp [bit] <;> omega

def RankFlat (f : Edge n → Bool) : Prop := ∀ e, rank (insert f e)=rank f → f e=true

theorem rankFlat_iff (f : Edge n → Bool) : RankFlat f ↔ Flat f := by
  rw [flat_iff]
  constructor
  · intro h
    cases he : f Edge.spine with
    | false =>
      right
      apply (E_zero_iff f).mp
      by_cases hz : E f=0
      · exact hz
      · have hp : 0<E f := by omega
        have h' := h .spine ((spine_closure f he).mpr hp)
        simp [he] at h'
    | true =>
      left
      refine ⟨he,?_⟩
      intro i
      have hp : 0<E f := by simp [E,he,bit]; omega
      cases hl : f (.spoke false i) <;> cases hr : f (.spoke true i)
      · rfl
      · have h' := h (.spoke false i) ((spoke_closure f false i hl).mpr ⟨hr,hp⟩)
        simp [hl] at h'
      · have h' := h (.spoke true i) ((spoke_closure f true i hr).mpr ⟨hl,hp⟩)
        simp [hr] at h'
      · rfl
  · intro h e hr
    cases he : f e with
    | true => rfl
    | false =>
      exfalso
      cases e with
      | spine =>
        have hp := (spine_closure f he).mp hr
        rcases h with h|h
        · have hh := h.1
          simp [he] at hh
        · have h' := (E_zero_iff f).mpr h
          omega
      | spoke s i =>
        have hp := (spoke_closure f s i he).mp hr
        rcases h with h|h
        · have h' := h.2 i
          cases s <;> simp_all
        · have h' := (E_zero_iff f).mpr h
          omega


theorem size_mono {f g : Edge n → Bool} (h : Sub f g) : size f ≤ size g := by
  rw [size_decomp,size_decomp]
  exact Nat.add_le_add (finSum_le (active_mono h)) (extra_mono h)

/-- Finite augmentation for the concrete graphic independence predicate. -/
theorem augment {f g : Edge n → Bool} (hf : Indep f) (hg : Indep g)
    (hs : size f < size g) :
    ∃ e, g e=true ∧ f e=false ∧ Indep (insert f e) := by
  classical
  by_cases hz : E f=0
  · have hx : ∃ e, g e=true ∧ f e=false := by
      by_cases hh : ∃ e, g e=true ∧ f e=false
      · exact hh
      · have hsub : Sub g f := by
          intro e he
          cases hf' : f e
          · exact (hh ⟨e,he,hf'⟩).elim
          · rfl
        have hmono := size_mono hsub
        omega
    obtain ⟨e,hge,hfe⟩ := hx
    refine ⟨e,hge,hfe,?_⟩
    have h := insert_extra_le f e hfe
    simpa [Indep,hz] using h
  · have hEf : E f≤1 := hf
    have hEg : E g≤1 := hg
    rw [size_decomp,size_decomp] at hs
    have hS : S f < S g := by omega
    have hdiff : ∃ j, active f j < active g j := by
      by_cases hh : ∃ j, active f j < active g j
      · exact hh
      · have h : S g ≤ S f := finSum_le (fun j => by
          by_cases he : active g j≤active f j
          · exact he
          · exact (hh ⟨j,by omega⟩).elim)
        omega
    obtain ⟨j,hj⟩ := hdiff
    have hlocal : f (.spoke false j)=false ∧ f (.spoke true j)=false ∧
        (g (.spoke false j)=true ∨ g (.spoke true j)=true) := by
      cases hf₀ : f (.spoke false j) <;> cases hf₁ : f (.spoke true j) <;>
        cases hg₀ : g (.spoke false j) <;> cases hg₁ : g (.spoke true j) <;>
        simp [active,bit,hf₀,hf₁,hg₀,hg₁] at hj ⊢
    obtain ⟨hf₀,hf₁,hgg⟩ := hlocal
    rcases hgg with hh|hh
    · refine ⟨.spoke false j,hh,hf₀,?_⟩
      change E (insertSpoke f false j)≤1
      rw [(spoke_insert_size f false j hf₀).2]
      simpa [bit,hf₁] using hEf
    · refine ⟨.spoke true j,hh,hf₁,?_⟩
      change E (insertSpoke f true j)≤1
      rw [(spoke_insert_size f true j hf₁).2]
      simpa [bit,hf₀] using hEf

#print axioms augment
#print axioms rankFlat_iff
#print axioms size_bound
#print axioms rank_attained
end InverseZ.ThagomizerRank



namespace InverseZ.ThagomizerLiteral
open InverseZ.ThagomizerRows
open InverseZ.ThagomizerFlatCounts
open InverseZ.ThagomizerRigidity
open InverseZ.ThagomizerMobius
open InverseZ.ThagomizerMarker
open InverseZ.ThagomizerIntegration
open InverseZ.ThagomizerFlat
open InverseZ.ThagomizerRank

private theorem grade_bit_le (l : List Bool) : bitOnes l≤l.length := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons b l ih => cases b <;> simp [bitOnes] <;> omega

private theorem grade_assign_le (l : List (Option Bool)) : assigned l≤l.length := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons b l ih => cases b <;> simp [assigned] <;> omega

theorem bitWords_mem (n : Nat) (l : List Bool) : l ∈ bitWords n ↔ l.length=n := by
  induction n generalizing l with
  | zero => simp [bitWords_zero]
  | succ n ih =>
    cases l with
    | nil => simp [bitWords_succ]
    | cons b l => cases b <;> simp [bitWords_succ,ih]

private theorem csum_plus (f g : Nat → Nat) (n : Nat) :
    csum (fun i=>f i+g i) n=csum f n+csum g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [csum]
    rw [ih]
    omega

private theorem csum_scaled (f : Nat → Nat) (r n : Nat) :
    csum (fun k => f k*r) n = csum f n*r := by
  induction n with
  | zero => simp [csum]
  | succ n ih => simp [csum,ih,Nat.add_mul]

private theorem csum_delta (x y n : Nat) :
    csum (fun j => if j=x then y else 0) n = if x<n then y else 0 := by
  induction n with
  | zero => simp [csum]
  | succ n ih =>
    simp only [csum]
    rw [ih]
    by_cases h₀ : x<n
    · have h₁ : n≠x := by omega
      have h₂ : x<n+1 := by omega
      simp [h₀,h₁,h₂]
    · by_cases h₁ : n=x
      · subst n
        simp
      · have h₂ : ¬x<n+1 := by omega
        simp [h₀,h₁,h₂]

private theorem groupedList {α : Type} (L : List α) (grade : α → Nat)
    (v : Nat → Nat) (n : Nat) (hL : ∀ x ∈ L, grade x≤n) :
    (L.map (fun x=>v (grade x))).sum =
      csum (fun k => L.countP (fun x=>grade x==k)*v k) (n+1) := by
  induction L with
  | nil =>
    symm
    exact csum_zero (fun k => ([] : List α).countP (fun x=>grade x==k)*v k) _
      (fun _ _=>by simp)
  | cons a L ih =>
    have ha : grade a≤n := hL a (by simp)
    have hl := ih (fun a ha=>hL a (by simp [ha]))
    simp only [List.map_cons,List.sum_cons,List.countP_cons,Nat.add_mul,csum_plus]
    have hf : (fun k => (if (grade a==k)=true then 1 else 0)*v k) =
        (fun k => if k=grade a then v (grade a) else 0) := by
      funext k
      by_cases he : k=grade a
      · subst k
        simp
      · simp [he,Ne.symm he]
    rw [hf,csum_delta,ite_eq_left (by omega : grade a<n+1),←hl]
    omega

theorem boolMu_abs (k : Nat) : (boolMu k).natAbs=1 := by
  unfold boolMu
  rw [Int.natAbs_pow]
  simp

theorem thagMu_abs (k : Nat) : (thagMu k).natAbs=2^k := by
  unfold thagMu
  rw [Int.natAbs_neg,Int.natAbs_pow]
  rfl

def joinedSummand (Q : Nat → Nat → Nat) (n i k : Nat) : Nat :=
  if n-k≤i then (boolMu (n-k)).natAbs * Q k (i-(n-k)) else 0

def splitSummand (n i k : Nat) : Nat :=
  if i=n-k+1 then (thagMu (n-k)).natAbs else 0


abbrev FullList (α : Type) (n : Nat) := {l : List α // l.length=n}
abbrev FlatCode (n : Nat) := FullList Bool n ⊕ FullList (Option Bool) n

theorem readCodeBound (l : FullList α n) (i : Fin n) : i.val < l.val.length :=
  Eq.mpr (congrArg (fun m => i.val < m) l.property) i.isLt

def readCode (l : FullList α n) (i : Fin n) : α :=
  l.val.get ⟨i.val, readCodeBound l i⟩

def writeCode (f : Fin n → α) : FullList α n := ⟨List.ofFn f,List.length_ofFn⟩

@[simp] theorem read_write (f : Fin n → α) : readCode (writeCode f)=f := by
  funext i
  simp [readCode,writeCode,List.get_eq_getElem]

@[simp] theorem write_read (l : FullList α n) : writeCode (readCode l)=l := by
  apply Subtype.ext
  apply List.ext_get
  · simp [writeCode,l.property]
  · intro i h₁ h₂
    simp [writeCode,readCode,List.get_eq_getElem]

def graphOfCode : FlatCode n → (Edge n → Bool) :=
  Sum.elim (fun bs => ofJoined (readCode bs)) (fun bs => ofSplit (readCode bs))

theorem graphOfCode_flat (c : FlatCode n) : Flat (graphOfCode c) := by
  cases c with
  | inl bs => exact joined_code_flat (readCode bs)
  | inr bs => exact split_code_flat (readCode bs)

theorem flat_has_code (f : Edge n → Bool) (hf : Flat f) :
    ∃ c : FlatCode n, graphOfCode c=f := by
  rcases (flat_iff f).mp hf with h|h
  · exact ⟨.inl (writeCode (toJoined f)),by simp [graphOfCode,encode_joined f h]⟩
  · exact ⟨.inr (writeCode (toSplit f)),by simp [graphOfCode,encode_split f h]⟩

theorem graphOfCode_injective {a b : FlatCode n} (h : graphOfCode a=graphOfCode b) : a=b := by
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have hr : readCode a=readCode b := by
        simpa [graphOfCode] using congrArg toJoined h
      exact congrArg Sum.inl (by simpa using congrArg writeCode hr)
    | inr b =>
      have hh := congrArg (fun f => f Edge.spine) h
      simp [graphOfCode,ofJoined,ofSplit] at hh
  | inr a =>
    cases b with
    | inl b =>
      have hh := congrArg (fun f => f Edge.spine) h
      simp [graphOfCode,ofJoined,ofSplit] at hh
    | inr b =>
      have hr : readCode a=readCode b := by
        simpa [graphOfCode] using congrArg toSplit h
      exact congrArg Sum.inr (by simpa using congrArg writeCode hr)

private theorem consMap_nodup {α : Type} (a : α) (L : List (List α)) (h : L.Nodup) :
    (L.map (a::·)).Nodup := by
  apply List.pairwise_map.mpr
  exact List.Pairwise.imp (fun hne he => hne (List.cons.inj he).2) h

theorem bitWords_nodup (n : Nat) : (bitWords n).Nodup := by
  induction n with
  | zero => simp [bitWords_zero]
  | succ n ih =>
    rw [bitWords_succ,List.nodup_append]
    refine ⟨consMap_nodup _ _ ih, consMap_nodup _ _ ih, ?_⟩
    simp only [List.mem_map]
    grind

theorem assignments_nodup (n : Nat) : (assignments n).Nodup := by
  induction n with
  | zero => simp [assignments_zero]
  | succ n ih =>
    simp only [assignments_succ,List.nodup_append]
    repeat' apply And.intro
    all_goals first
      | exact consMap_nodup _ _ ih
      | simp only [List.mem_map,List.mem_append]; grind


private theorem finSum_readCode (φ : α → Nat) (l : FullList α n) :
    finSum (fun i=>φ (readCode l i))=(l.val.map φ).sum := by
  unfold finSum countOn
  rw [List.finRange,List.map_ofFn]
  have h : List.ofFn (readCode l) = l.val := congrArg Subtype.val (write_read l)
  have hm := congrArg (List.map φ) h
  rw [List.map_ofFn] at hm
  rw [← hm]
  rfl

private theorem bitOnes_map (l : List Bool) :
    bitOnes l=(l.map (fun b=>if b then 1 else 0)).sum := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [bitOnes,ih,Nat.add_comm]

private theorem assigned_map (l : List (Option Bool)) :
    assigned l=(l.map (fun b=>if b.isSome then 1 else 0)).sum := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [assigned,ih,Nat.add_comm]

theorem rank_joined_code (l : FullList Bool n) :
    rank (graphOfCode (.inl l)) = bitOnes l.val+1 := by
  change rank (ofJoined (readCode l)) = _
  have hS : S (ofJoined (readCode l)) = bitOnes l.val := by
    rw [bitOnes_map,←finSum_readCode (fun b : Bool=>if b then 1 else 0)]
    unfold S
    congr 1
    funext i
    cases hi : readCode l i <;> simp [active,ofJoined,bit,hi]
  have hE : 1≤E (ofJoined (readCode l)) := by
    simp [E,ofJoined,bit]
  unfold rank
  rw [hS,Nat.min_eq_left hE]

theorem rank_split_code (l : FullList (Option Bool) n) :
    rank (graphOfCode (.inr l)) = assigned l.val := by
  change rank (ofSplit (readCode l)) = _
  have hS : S (ofSplit (readCode l)) = assigned l.val := by
    rw [assigned_map,←finSum_readCode (fun b : Option Bool=>if b.isSome then 1 else 0)]
    unfold S
    congr 1
    funext i
    cases hi : readCode l i with
    | none => simp [active,ofSplit,bit,hi]
    | some b => cases b <;> simp [active,ofSplit,bit,hi]
  have hE : E (ofSplit (readCode l))=0 := by
    apply (E_zero_iff _).mpr
    exact ((flat_iff _).mp (split_code_flat (readCode l))).resolve_left (fun h=>by cases h.1)
  unfold rank
  rw [hS,hE]
  simp

theorem full_rank (n : Nat) : rank (fun _ : Edge n => true) = n+1 := by
  let l := writeCode (fun _ : Fin n => true)
  have he : graphOfCode (.inl l : FlatCode n)=(fun _=>true) := by
    funext e
    cases e <;> simp [graphOfCode,l,ofJoined]
  have h := rank_joined_code l
  rw [he] at h
  have hs : ∀ m, bitOnes (List.ofFn (fun _ : Fin m => true)) = m := by
    intro m
    induction m with
    | zero => simp [List.ofFn_zero,bitOnes]
    | succ m ih => simp [List.ofFn_succ,bitOnes,ih]
  rw [show bitOnes l.val=n from hs n] at h
  exact h

theorem joined_corank_code (l : FullList Bool n) :
    rank (fun _ : Edge n=>true)-rank (graphOfCode (.inl l))=n-bitOnes l.val := by
  rw [full_rank,rank_joined_code]
  omega

theorem split_corank_code (l : FullList (Option Bool) n) :
    rank (fun _ : Edge n=>true)-rank (graphOfCode (.inr l))=n-assigned l.val+1 := by
  have h : assigned l.val≤n := by simpa only [l.property] using grade_assign_le l.val
  rw [full_rank,rank_split_code]
  omega

/-- Literal finite flat-code sum: every joined bit assignment and split
ternary assignment contributes its signed-flat coefficient separately.
Ternary choices are no spoke, hub-0 spoke, and hub-1 spoke. -/
def graphicFlatCoeff (Q : Nat → Nat → Nat) (n i : Nat) : Nat :=
    ((bitWords n).map (fun mask=>joinedSummand Q n i (bitOnes mask))).sum +
    ((assignments n).map (fun mask=>splitSummand n i (assigned mask))).sum

theorem joined_sum_grouped (Q : Nat → Nat → Nat) (n i : Nat) :
    ((bitWords n).map (fun mask=>joinedSummand Q n i (bitOnes mask))).sum =
      csum (term Q n i) (n+1) := by
  rw [groupedList (bitWords n) bitOnes (joinedSummand Q n i) n (fun l hl=>by
    rw [← (bitWords_mem n l).mp hl]
    exact grade_bit_le l)]
  apply csum_congr
  intro k _
  rw [bit_words_choose]
  by_cases h : n-k≤i <;> simp [joinedSummand,term,h,boolMu_abs]

theorem split_sum_grouped (n i : Nat) (hi : i≤n+1) :
    ((assignments n).map (fun mask=>splitSummand n i (assigned mask))).sum =
      2^n*predChoose n i := by
  rw [groupedList (assignments n) assigned (splitSummand n i) n (fun l hl=>by
    rw [← (assignments_mem n l).mp hl]
    exact grade_assign_le l)]
  have h :
      csum (fun k => ((assignments n).countP fun x => assigned x == k) *
                         splitSummand n i k) (n+1) =
      csum (fun k => if i=n-k+1 then choose n k*2^n else 0) (n+1) := by
    apply csum_congr
    intro k hk
    rw [assignments_count]
    by_cases he : i=n-k+1
    · have hk' : k+(n-k)=n := by omega
      simp only [splitSummand,he,ite_true,thagMu_abs,Nat.mul_assoc,←Nat.pow_add,hk']
    · simp [splitSummand,he]
  rw [h]
  cases i with
  | zero =>
    have h' : csum (fun k => if 0=n-k+1 then choose n k*2^n else 0) (n+1)=0 := by
      exact csum_zero _ _ (fun k _=>by simp)
    rw [h']
    simp [predChoose]
  | succ i =>
    have hn : i≤n := by omega
    have h' : csum (fun k => if i+1=n-k+1 then choose n k*2^n else 0) (n+1) =
        csum (fun k => if k=n-i then choose n (n-i)*2^n else 0) (n+1) := by
      apply csum_congr
      intro k hk
      have he : i+1=n-k+1 ↔ k=n-i := by omega
      by_cases hh : k=n-i
      · rw [ite_eq_left (he.mpr hh),ite_eq_left hh,hh]
      · rw [ite_eq_right (fun hp=>hh (he.mp hp)),ite_eq_right hh]
    rw [h',csum_delta,ite_eq_left (by omega : n-i<n+1),
      choose_reflect n i hn]
    simp [predChoose,Nat.mul_comm]

theorem graphicFlatCoeff_grouped (Q : Nat → Nat → Nat) (n i : Nat) (hi : i≤n+1) :
    graphicFlatCoeff Q n i=flatCoeff Q n i := by
  unfold graphicFlatCoeff flatCoeff
  rw [joined_sum_grouped,split_sum_grouped n i hi]
  omega


/-- The full-rank difference is computed on the actual coded edge subset.
Joined restrictions use Q at their rank minus one; split restrictions are free. -/
def rankedSummand (Q : Nat → Nat → Nat) (n i : Nat) (c : FlatCode n) : Nat :=
  let r := rank (graphOfCode c)
  let d := rank (fun _ : Edge n => true)-r
  Sum.elim (fun _ => if d≤i then (boolMu d).natAbs*Q (r-1) (i-d) else 0)
    (fun _ => if i=d then (thagMu (d-1)).natAbs else 0) c

theorem ranked_join (Q : Nat → Nat → Nat) (n i : Nat) (l : FullList Bool n) :
    rankedSummand Q n i (.inl l)=joinedSummand Q n i (bitOnes l.val) := by
  simp only [rankedSummand,Sum.elim_inl,rank_joined_code,full_rank,joinedSummand,Nat.add_sub_cancel]
  have h : n+1-(bitOnes l.val+1)=n-bitOnes l.val := by omega
  rw [h]

theorem ranked_split (Q : Nat → Nat → Nat) (n i : Nat) (l : FullList (Option Bool) n) :
    rankedSummand Q n i (.inr l)=splitSummand n i (assigned l.val) := by
  simp only [rankedSummand,Sum.elim_inr,full_rank,rank_split_code,splitSummand]
  have ha : assigned l.val≤n := by simpa only [l.property] using grade_assign_le l.val
  have h : n+1-assigned l.val=n-assigned l.val+1 := by omega
  rw [h]
  simp

/-- Literal graph-flat sum, once per actual flat (via the certified bijective
code), using rank of that edge subset and the contraction Möbius factor. -/
def graphicRankFlatCoeff (Q : Nat → Nat → Nat) (n i : Nat) : Nat :=
  ((bitWords n).map (fun l=>if h : l.length=n then rankedSummand Q n i (.inl ⟨l,h⟩) else 0)).sum +
  ((assignments n).map (fun l=>if h : l.length=n then rankedSummand Q n i (.inr ⟨l,h⟩) else 0)).sum

theorem graphicRankFlatCoeff_eq (Q : Nat → Nat → Nat) (n i : Nat) :
    graphicRankFlatCoeff Q n i=graphicFlatCoeff Q n i := by
  unfold graphicRankFlatCoeff graphicFlatCoeff
  have h₀ : (bitWords n).map (fun l=>if h : l.length=n then rankedSummand Q n i (.inl ⟨l,h⟩) else 0) =
      (bitWords n).map (fun mask=>joinedSummand Q n i (bitOnes mask)) := by
    apply List.map_congr_left
    intro l hl
    have h := (bitWords_mem n l).mp hl
    simp [h,ranked_join]
  have h₁ : (assignments n).map (fun l=>if h : l.length=n then rankedSummand Q n i (.inr ⟨l,h⟩) else 0) =
      (assignments n).map (fun mask=>splitSummand n i (assigned mask)) := by
    apply List.map_congr_left
    intro l hl
    have h := (assignments_mem n l).mp hl
    simp [h,ranked_split]
  rw [h₀,h₁]

def InverseZSource (Q : Nat → Nat → Nat) : Prop :=
  DegreeCut Q ∧ ∀ n i, i≤n+1 → graphicFlatCoeff Q n i=graphicFlatCoeff Q n (n+1-i)

theorem source_valid : InverseZSource Qmodel := by
  refine ⟨Qmodel_degree,?_⟩
  intro n i hi
  rw [graphicFlatCoeff_grouped _ n i hi,graphicFlatCoeff_grouped _ n (n+1-i) (by omega)]
  exact Qmodel_palindrome n i hi

theorem source_Q_unique (Q : Nat → Nat → Nat) (h : InverseZSource Q) : Q=Qmodel := by
  have hp : Palindrome Q := by
    intro n i hi
    have h' := h.2 n i hi
    rw [graphicFlatCoeff_grouped _ n i hi,graphicFlatCoeff_grouped _ n (n+1-i) (by omega)] at h'
    exact h'
  exact funext fun n=>funext fun i=>Q_unique Q Qmodel h.1 Qmodel_degree hp Qmodel_palindrome n i

theorem literal_inverse_Z_strict (Q : Nat → Nat → Nat) (h : InverseZSource Q)
    (n i : Nat) (hi : i+1≤n) :
    graphicRankFlatCoeff Q n i*graphicRankFlatCoeff Q n (i+2) <
    graphicRankFlatCoeff Q n (i+1)*graphicRankFlatCoeff Q n (i+1) := by
  simp only [graphicRankFlatCoeff_eq]
  rw [source_Q_unique Q h,graphicFlatCoeff_grouped _ n i (by omega),
    graphicFlatCoeff_grouped _ n (i+2) (by omega),
    graphicFlatCoeff_grouped _ n (i+1) (by omega)]
  exact flatCoeff_minor n i hi

theorem literal_inverse_Z_positive (Q : Nat → Nat → Nat) (h : InverseZSource Q)
    (n i : Nat) (hi : i≤n+1) :
    0 < graphicRankFlatCoeff Q n i := by
  rw [graphicRankFlatCoeff_eq,source_Q_unique Q h,graphicFlatCoeff_grouped _ n i hi]
  exact flatCoeff_positive n i hi


/-- Ordinary inverse-Z of the thagomizer in the literal finite graph-flat
model. The chosen Q is the unique solution to the source characterization. -/
def inverseZCoeff (n i : Nat) : Nat := graphicRankFlatCoeff Qmodel n i

theorem inverseZCoeff_strict_and_positive :
    (∀ n i : Nat, i≤n+1 → 0<inverseZCoeff n i) ∧
    (∀ n i : Nat, i+1≤n →
      inverseZCoeff n i*inverseZCoeff n (i+2) <
      inverseZCoeff n (i+1)*inverseZCoeff n (i+1)) :=
  ⟨literal_inverse_Z_positive Qmodel source_valid,
    literal_inverse_Z_strict Qmodel source_valid⟩

#print axioms inverseZCoeff_strict_and_positive
#print axioms graphicRankFlatCoeff_eq
#print axioms rank_joined_code
#print axioms rank_split_code
#print axioms full_rank
#print axioms joined_corank_code
#print axioms split_corank_code
#print axioms graphOfCode_injective
#print axioms flat_has_code
#print axioms graphicFlatCoeff_grouped
#print axioms source_valid
#print axioms literal_inverse_Z_strict
#print axioms literal_inverse_Z_positive
end InverseZ.ThagomizerLiteral
