(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/euler002_Solve_fqtvc: the Euler problem 2 verification condition for
  initializing and advancing a recurrence that sums even Fibonacci numbers up
  to a nonnegative bound. This file contains no proof.
*)

let statement =
 `!fib:int->int.
  !fib_sum_even:int->int->int.
    (!n:int.
       (&0:int) <= n
       ==>
       (if n = (&0:int) then
          fib n = (&0:int)
        else if n = (&1:int) then
          fib n = (&1:int)
        else
          fib n = fib (n - (&1:int)) + fib (n - (&2:int))))
    ==>
    (!m:int. fib_sum_even m (&0:int) = (&0:int))
    ==>
    (!n m:int.
       (&0:int) <= n
       ==>
       fib n <= m
       ==>
       fib n rem (&2:int) = (&0:int)
       ==>
       fib_sum_even m (n + (&1:int)) = fib_sum_even m n + fib n)
    ==>
    (!n m:int.
       (&0:int) <= n
       ==>
       m < fib n
       ==>
       fib n rem (&2:int) = (&0:int)
       ==>
       fib_sum_even m (n + (&1:int)) = fib_sum_even m n)
    ==>
    (!n m:int.
       (&0:int) <= n
       ==>
       ~(fib n rem (&2:int) = (&0:int))
       ==>
       fib_sum_even m (n + (&1:int)) = fib_sum_even m n)
    ==>
    let fib_even = \n:int. fib ((&3:int) * n) in
    !m:int.
      (&0:int) <= m
      ==>
      (&0:int) <= (&0:int) /\
      (&0:int) <= (&0:int) /\
      (&0:int) = fib_even (&0:int) /\
      (&0:int) = fib (&0:int) /\
      (&2:int) = fib_even ((&0:int) + (&1:int)) /\
      (&2:int) = fib ((&0:int) + (&3:int)) /\
      (&0:int) = fib_sum_even m (&0:int) /\
      (&0:int) <= (&0:int) /\
      (&0:int) < (&2:int) /\
      (!k n:int.
         (&0:int) <= n /\
         (&0:int) <= k /\
         fib_even n = fib k /\
         fib_even (n + (&1:int)) = fib (k + (&3:int)) /\
         (&0:int) <= fib_even n /\
         fib_even n < fib_even (n + (&1:int))
         ==>
         (if fib_even n <= m then
            (((&0:int) <= m - fib_even n /\
              m - fib_even (n + (&1:int)) < m - fib_even n) /\
             (&0:int) <= n + (&1:int) /\
             (&0:int) <= k + (&3:int) /\
             fib_even (n + (&1:int)) = fib (k + (&3:int)) /\
             (&4:int) * fib_even (n + (&1:int)) + fib_even n =
               fib_even (n + (&1:int) + (&1:int)) /\
             (&4:int) * fib_even (n + (&1:int)) + fib_even n =
               fib (k + (&3:int) + (&3:int)) /\
             fib_sum_even m k + fib_even n =
               fib_sum_even m (k + (&3:int)) /\
             (&0:int) <= fib_even (n + (&1:int)) /\
             fib_even (n + (&1:int)) <
               (&4:int) * fib_even (n + (&1:int)) + fib_even n)
          else
            ?n1:int.
              fib_sum_even m k = fib_sum_even m n1 /\
              m < fib n1))`;;
