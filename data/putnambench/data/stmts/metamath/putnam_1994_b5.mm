$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1994_b5: existence of a real parameter whose floor-multiplication
  map and its power-parameter variants have the prescribed values through
  the first n iterates at n squared. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN is SetMM's class of positive integers, ZZ is its class of integers,
  and |_ is the real floor function. The mapping

    ( x e. ZZ |-> ( |_ ` ( a x. x ) ) )

  is definitionally the source family f_a(x) = floor(a*x), so inlining it
  eliminates only the auxiliary universally defined function f. IterComp is
  SetMM's native finite-iteration operator. Thus its value at k and n^2 is
  exactly the k-fold iterate f_a^k(n^2), while the second conjunct applies
  floor multiplication with the shared real witness raised to k.

  The interval 1 ... n contains exactly the positive integers from 1 through
  n. The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a k n x $.

  putnambench-putnam-1994-b5 $a |- A. n e. NN
    E. a e. RR
      A. k e. ( 1 ... n )
        (
          (
            (
              (
                (
                  IterComp
                  `
                  ( x e. ZZ |-> ( |_ ` ( a x. x ) ) )
                )
                `
                k
              )
              `
              ( n ^ 2 )
            )
            =
            ( ( n ^ 2 ) - k )
          )
          /\
          (
            ( |_ ` ( ( a ^ k ) x. ( n ^ 2 ) ) )
            =
            ( ( n ^ 2 ) - k )
          )
        )
  $.
$}
