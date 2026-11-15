(*
  Statement-only formalization of miniF2F valid problem aimeI_2000_p7. This file contains no
  proof.
*)

let statement = `!x y z m:real. !p q:num.
    &0 < x /\ &0 < y /\ &0 < z /\
    x * y * z = &1 /\
    x + &1 / z = &5 /\
    y + &1 / x = &29 /\
    z + &1 / y = m /\
    &0 < m /\
    ~(q = 0) /\
    coprime(p,q) /\
    m = &p / &q
    ==> p + q = 5`;;
