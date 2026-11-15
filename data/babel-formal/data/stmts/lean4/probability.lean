inductive mynat : Type
| O  : mynat
| S  : mynat → mynat
deriving DecidableEq

open mynat

def mynat_add : mynat → mynat → mynat
| O,        m => m
| (S n'),   m => S (mynat_add n' m)

theorem mynat_add_O_left (m : mynat) :
  mynat_add O m = m := rfl

theorem mynat_add_S_left (n m : mynat) :
  mynat_add (S n) m = S (mynat_add n m) := rfl

inductive mylist (A : Type) : Type
| nilL  : mylist A
| consL : A → mylist A → mylist A

namespace mylist

notation h "::L" t => mylist.consL h t

def mapL {A B : Type} (f : A → B) : mylist A → mylist B
| mylist.nilL    => mylist.nilL
| (x ::L xs)     => f x ::L mapL f xs

def fold_add {R : Type} (add : R → R → R) (z : R) : mylist R → R
| mylist.nilL    => z
| (x ::L xs)     => add x (fold_add add z xs)

end mylist

open mylist

inductive InL {A : Type} (x : A) : mylist A → Prop
| In_head : ∀ xs, InL x (x ::L xs)
| In_tail : ∀ y xs, InL (x := x) xs → InL (x := x) (y ::L xs)

inductive NoDupL {A : Type} : mylist A → Prop
| ND_nil  : NoDupL mylist.nilL
| ND_cons : ∀ x xs, (¬ InL x xs) → NoDupL xs → NoDupL (x ::L xs)

class ring (R : Type) where
  (zero      : R)
  (opp       : R → R)
  (one       : R)
  (add       : R → R → R)
  (mul       : R → R → R)

  (one_neq_zero  : one ≠ zero)

  (add_comm  : ∀ x y,    add x y = add y x)
  (add_assoc : ∀ x y z,  add (add x y) z = add x (add y z))
  (add_zero  : ∀ x,      add x zero = x)
  (add_opp   : ∀ x,      add x (opp x) = zero)

  (mul_comm  : ∀ x y,    mul x y = mul y x)
  (mul_assoc : ∀ x y z,  mul (mul x y) z = mul x (mul y z))
  (mul_one   : ∀ x,      mul x one = x)
  (dist_l    : ∀ x y z,  mul x (add y z) = add (mul x y) (mul x z))
  (mul_zero  : ∀ x,      mul x zero = zero)

  (no_zero_div :
    ∀ x y, mul x y = zero → x = zero ∨ y = zero)

notation:35 "-R " x   => ring.opp x

section Probability

variable {R : Type} [rR : ring R]
variable {Ω : Type}

def event (Ω : Type) := Ω → Prop

def ev_false : event Ω := fun _ => False
def ev_true  : event Ω := fun _ => True

def ev_inter (A B : event Ω) : event Ω := fun ω => A ω ∧ B ω
def ev_union (A B : event Ω) : event Ω := fun ω => A ω ∨ B ω
def ev_compl (A : event Ω)   : event Ω := fun ω => ¬ A ω
def ev_diff (A B : event Ω)  : event Ω := fun ω => A ω ∧ ¬ B ω

theorem ev_inter_comm (A B : event Ω) : ∀ ω, (ev_inter A B) ω ↔ (ev_inter B A) ω := by sorry
theorem ev_union_comm (A B : event Ω) : ∀ ω, (ev_union A B) ω ↔ (ev_union B A) ω := by sorry
theorem ev_inter_assoc (A B C : event Ω) : ∀ ω,
  (ev_inter (ev_inter A B) C) ω ↔ (ev_inter A (ev_inter B C)) ω := by sorry
theorem ev_union_assoc (A B C : event Ω) : ∀ ω,
  (ev_union (ev_union A B) C) ω ↔ (ev_union A (ev_union B C)) ω := by sorry
theorem ev_inter_distrib_left (A B C : event Ω) : ∀ ω,
  (ev_inter A (ev_union B C)) ω ↔ (ev_union (ev_inter A B) (ev_inter A C)) ω := by sorry
def disjoint (A B : event Ω) : Prop := ∀ ω, ¬ ((ev_inter A B) ω)

def pairwise_disjoint : mylist (event Ω) → Prop
| mylist.nilL      => True
| (_ ::L mylist.nilL) => True
| (A ::L (B ::L xs))  => disjoint A B ∧ (∀ C, InL C (B ::L xs) → disjoint A C) ∧ pairwise_disjoint (B ::L xs)

def bigUnion : mylist (event Ω) → event Ω
| mylist.nilL      => ev_false
| (A ::L xs)       => ev_union A (bigUnion xs)

variable (prob : event Ω → R)

axiom prob_ext : ∀ {A B : event Ω}, (∀ ω, A ω ↔ B ω) → prob A = prob B
axiom prob_false : prob ev_false = rR.zero
axiom prob_true  : prob ev_true  = rR.one

axiom prob_union : ∀ (A B : event Ω),
  prob (ev_union A B) = rR.add (prob A) (rR.add (prob B) (rR.opp (prob (ev_inter A B))))

axiom prob_compl : ∀ (A : event Ω), prob (ev_compl A) = rR.add rR.one (rR.opp (prob A))

axiom em : ∀ p : Prop, p ∨ ¬ p

axiom cprob : event Ω → event Ω → R
axiom cprob_mul : ∀ A B, prob (ev_inter A B) = rR.mul (cprob A B) (prob B)

def indep (A B : event Ω) : Prop := prob (ev_inter A B) = rR.mul (prob A) (prob B)

local notation:55 x " -R " y => rR.add x (rR.opp y)

axiom opp_zero  : rR.opp rR.zero = rR.zero
axiom opp_opp   : ∀ x, rR.opp (rR.opp x) = x
axiom opp_mul_right : ∀ x y, rR.mul x (rR.opp y) = rR.opp (rR.mul x y)
axiom opp_mul_left  : ∀ x y, rR.mul (rR.opp x) y = rR.opp (rR.mul x y)

axiom prob_union_disjoint : ∀ (A B : event Ω), disjoint A B → prob (ev_union A B) = rR.add (prob A) (prob B)
axiom disjoint_head_tail : ∀ (A : event Ω) (xs : mylist (event Ω)), pairwise_disjoint (A ::L xs) → disjoint A (bigUnion xs)

theorem prob_union_comm (A B : event Ω) :
  prob (ev_union A B) = prob (ev_union B A) := by sorry
theorem prob_union_idem (A : event Ω) :
  prob (ev_union A A) = prob A := by sorry
theorem prob_diff (A B : event Ω) :
  prob (ev_diff A B) = prob A -R prob (ev_inter A B) := by sorry
theorem bayes_symm (A B : event Ω) :
  rR.mul (cprob A B) (prob B) = rR.mul (cprob B A) (prob A) := by sorry
theorem law_total_prob (A B : event Ω) :
  prob A = rR.add (rR.mul (cprob A B) (prob B)) (rR.mul (cprob A (ev_compl B)) (prob (ev_compl B))) := by sorry
theorem prob_union_indep (A B : event Ω) :
  indep (prob := prob) A B →
  prob (ev_union A B) = rR.add (prob A) (rR.add (prob B) (rR.opp (rR.mul (prob A) (prob B)))) := by sorry
theorem indep_compl_right (A B : event Ω) :
  indep (prob := prob) A B → indep (prob := prob) A (ev_compl B) := by sorry
theorem indep_symm (A B : event Ω) :
  indep (prob := prob) A B → indep (prob := prob) B A := by sorry
theorem indep_compl_left (A B : event Ω) :
  indep (prob := prob) A B → indep (prob := prob) (ev_compl A) B := by sorry
axiom indep_compl_both (A B : event Ω) :
  indep (prob := prob) A B → indep (prob := prob) (ev_compl A) (ev_compl B)

theorem prob_bigUnion_disjoint
  (xs : mylist (event Ω))
  (hp : pairwise_disjoint xs) :
  prob (bigUnion xs)
    = mylist.fold_add rR.add rR.zero (mylist.mapL prob xs) := by sorry
theorem prob_bigUnion_disjoint_zero
  (xs : mylist (event Ω))
  (hp : pairwise_disjoint xs)
  (hzero : ∀ A, InL A xs → prob A = rR.zero) :
  prob (bigUnion xs) = rR.zero := by sorry
axiom inclusion_exclusion_three (A B C : event Ω) :
  prob (ev_union (ev_union A B) C)
    = rR.add (prob A)
      (rR.add (prob B)
        (rR.add (prob C)
          (rR.opp (rR.add (prob (ev_inter A B))
                 (rR.add (prob (ev_inter A C))
                         (rR.add (prob (ev_inter B C))
                                 (rR.opp (prob (ev_inter (ev_inter A B) C)))))))))

end Probability
