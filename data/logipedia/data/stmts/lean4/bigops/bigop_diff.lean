-- Statement-only formalization of Logipedia artifact "bigops.bigop_diff":
-- removing a selected index from a Boolean-filtered finite product factors out
-- the value at that index. This file contains no proof.

namespace bigops

def bigop (H : Type) :
    Nat -> (Nat -> Bool) -> H -> (H -> H -> H) -> (Nat -> H) -> H
  | 0, _p, nil, _op, _f => nil
  | n + 1, p, nil, op, f =>
      match p n with
      | true => op (f n) (bigop H n p nil op f)
      | false => bigop H n p nil op f

theorem bigop_diff
    (p : Nat -> Bool) (f : Nat -> Nat) (i n : Nat)
    (hin : i < n) (hpi : p i = true) :
    bigop Nat n p 1 Nat.mul f =
      f i * bigop Nat n (fun x => !(i == x) && p x) 1 Nat.mul f := sorry

end bigops
