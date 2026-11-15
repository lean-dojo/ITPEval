$(
  Statement-only formalization of Thousand Theorems corpus artifact Q193286
  (thousand-theorems__metamath__Q193286), "Rolle's theorem": a real function
  continuous on a closed interval with equal endpoint values has an interior
  point where its totalized real derivative is zero. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  Membership in RR ^m RR makes F an arbitrary total real-valued function.
  ContinuityOn F [A,B] is represented by continuity of the restriction from
  the interval's subspace topology to the real topology.

  Q193286Deriv totalizes set.mm's partial real derivative by assigning zero
  where the derivative does not exist. This is definitionally equivalent to
  Mathlib's deriv convention used by the source theorem, including its zero
  value at nondifferentiable points. The witness remains existentially
  quantified in the open interval. The final declaration is the single
  unproved corpus statement.
$)

$c Q193286Deriv $.

q193286-deriv-syntax $a class ( Q193286Deriv A ) $.

${
  $d A x $.

  q193286-deriv-definition $a |- ( Q193286Deriv A ) =
    (
      x e. RR |->
        if (
          x e. dom ( RR _D A ) ,
          ( ( RR _D A ) ` x ) ,
          0
        )
    )
  $.
$}

${
  $d c A $.
  $d c B $.
  $d c F $.

  thousand-theorems-metamath-Q193286-rolle-theorem $a |-
    A. A e. RR
      A. B e. RR
        A. F e. ( RR ^m RR )
          (
            (
              (
                A < B
                /\
                (
                  F |` ( A [,] B )
                )
                e.
                (
                  ( ( TopOpen ` RRfld ) |`t ( A [,] B ) )
                  Cn
                  ( TopOpen ` RRfld )
                )
              )
              /\
              ( ( F ` A ) = ( F ` B ) )
            )
            ->
            E. c e. ( A (,) B )
              ( ( Q193286Deriv F ) ` c ) = 0
          ) $.
$}
