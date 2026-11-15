$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2015_a4: the greatest universal lower bound on the binary series
  selected by even values of floor(n x), for real x in [0, 1), is 4 / 7.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN is the class of positive integers, |_ is the real floor
  function, || is integer divisibility, and an unbounded sum_ is the
  convergent infinite series sum. Thus

    { n e. NN | 2 || ( |_ ` ( n x. x ) ) }

  is exactly the source set S_x, and the displayed summand is 1 / 2^n.
  The first conjunct states that 4 / 7 is a universal lower bound on
  [0, 1). The second states that every real universal lower bound is at most
  4 / 7. Together they are equivalent to saying that 4 / 7 is the greatest
  such lower bound.

  The source's definitionally specified S, f, and p are inlined. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof declaration.
$)

${
  $d l n x $.

  putnambench-putnam-2015-a4 $a |-
    (
      A. x e. RR
        (
          (
            0 <_ x
            /\
            x < 1
          )
          ->
          (
            ( 4 / 7 )
            <_
            sum_ n e.
              { n e. NN | 2 || ( |_ ` ( n x. x ) ) }
              ( 1 / ( 2 ^ n ) )
          )
        )
      /\
      A. l e. RR
        (
          (
            A. x e. RR
              (
                (
                  0 <_ x
                  /\
                  x < 1
                )
                ->
                (
                  l
                  <_
                  sum_ n e.
                    { n e. NN | 2 || ( |_ ` ( n x. x ) ) }
                    ( 1 / ( 2 ^ n ) )
                )
              )
          )
          ->
          l <_ ( 4 / 7 )
        )
    )
  $.
$}
