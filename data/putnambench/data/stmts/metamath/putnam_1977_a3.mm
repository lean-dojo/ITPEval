$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1977_a3: recovery of a real function from its symmetric averages at
  shifts one and four. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  f, g, and h range over all total real-valued functions on the reals. The
  two universally quantified equations are exactly the source averaging
  hypotheses. The pointwise conclusion is equivalent by function
  extensionality to equality of h with the explicit source solution function
  x |-> g(x) - f(x-3) + f(x-1) + f(x+1) - f(x+3).

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d f g h x $.

  putnambench-putnam-1977-a3 $a |-
    A. f e. ( RR ^m RR )
    A. g e. ( RR ^m RR )
    A. h e. ( RR ^m RR )
      (
        (
          A. x e. RR
            ( f ` x )
            =
            (
              (
                ( h ` ( x + 1 ) )
                +
                ( h ` ( x - 1 ) )
              )
              /
              2
            )
          /\
          A. x e. RR
            ( g ` x )
            =
            (
              (
                ( h ` ( x + 4 ) )
                +
                ( h ` ( x - 4 ) )
              )
              /
              2
            )
        )
        ->
        A. x e. RR
          ( h ` x )
          =
          (
            (
              (
                (
                  ( g ` x )
                  -
                  ( f ` ( x - 3 ) )
                )
                +
                ( f ` ( x - 1 ) )
              )
              +
              ( f ` ( x + 1 ) )
            )
            -
            ( f ` ( x + 3 ) )
          )
      )
  $.
$}
