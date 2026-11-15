$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2023_a1: the least positive integer n for which the absolute value
  of the second derivative at zero of the product of cos(i x), for
  1 <= i <= n, exceeds 2023 is 18. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P23A1F maps every nonnegative integer n to the total real function
  x |-> product_(1 <= i <= n) cos(i*x). Set.mm's finite interval 1 ... n
  and finite-product binder therefore give exactly the source family f_n.
  The entry at index 2 of ( RR Dn ( P23A1F ` n ) ) is its second real
  derivative.

  The final conjunction expands the source IsLeast assertion: 18 is a
  positive index satisfying the strict derivative bound, and every positive
  index satisfying that bound is at least 18. All declarations are unproved
  $a statement encodings; this database contains no $p proof declaration.
$)

$c P23A1F $.

p23a1-function-syntax $a class P23A1F $.

${
  $d i n x $.

  p23a1-function-definition $a |- P23A1F =
    (
      n e. NN0 |->
        (
          x e. RR |->
            prod_ i e. ( 1 ... n )
              ( cos ` ( i x. x ) )
        )
    )
  $.
$}

putnambench-putnam-2023-a1 $a |- (
    (
      ( ; 1 8 ) e. NN
      /\
      (
        abs
        `
        (
          (
            ( RR Dn ( P23A1F ` ( ; 1 8 ) ) )
            ` 2
          )
          ` 0
        )
      )
      >
      ( ; ; ; 2 0 2 3 )
    )
    /\
    A. n e. NN
      (
        (
          abs
          `
          (
            (
              ( RR Dn ( P23A1F ` n ) )
              ` 2
            )
            ` 0
          )
        )
        >
        ( ; ; ; 2 0 2 3 )
        ->
        ( ; 1 8 ) <_ n
      )
  ) $.
