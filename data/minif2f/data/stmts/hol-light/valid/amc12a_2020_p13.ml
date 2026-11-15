(* Statement-only formalization of miniF2F valid problem amc12a_2020_p13. *)
let statement = `!a b c:num n:real.
    (&0 < n) /\
    ~(n = &1) /\
    (1 < a /\ 1 < b /\ 1 < c) /\
    (exp
       ((&1 / &a) *
        ln (n * exp ((&1 / &b) * ln (n * exp ((&1 / &c) * ln n))))) =
     exp ((&1 / &36) * ln (n pow 25)))
    ==> b = 3
`;;
