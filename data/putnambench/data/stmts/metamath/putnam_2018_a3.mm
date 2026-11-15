$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2018_a3: the greatest possible sum of the ten values cos(3 x_i)
  for real x_i whose cosines sum to zero is 480/49. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  The carrier 0 ..^ 10 has exactly ten indices, and RR ^m (0 ..^ 10) is
  the class of all real-valued tuples on that carrier. The first conjunct
  supplies an admissible tuple attaining 480/49; the second bounds the same
  objective by 480/49 for every admissible tuple. Together these conjuncts
  expand the source IsGreatest assertion.

  The finite sums follow the published problem and the Lean and Isabelle
  sources. The product-valued Rocq auxiliary conflicts with that problem
  statement and with the other formal sources, so it is treated as a
  transcription error. The declaration is the single unproved $a corpus
  statement; this database contains no $p proof declaration.
$)

${
  $d i x $.

  putnambench-putnam-2018-a3 $a |- (
    E. x e. ( RR ^m ( 0 ..^ ; 1 0 ) )
      (
        (
          sum_ i e. ( 0 ..^ ; 1 0 )
            ( cos ` ( x ` i ) )
        )
        =
        0
        /\
        (
          sum_ i e. ( 0 ..^ ; 1 0 )
            (
              cos
              `
              (
                3
                x.
                ( x ` i )
              )
            )
        )
        =
        ( ( ; ; 4 8 0 ) / ( ; 4 9 ) )
      )
    /\
    A. x e. ( RR ^m ( 0 ..^ ; 1 0 ) )
      (
        (
          sum_ i e. ( 0 ..^ ; 1 0 )
            ( cos ` ( x ` i ) )
        )
        =
        0
        ->
        (
          sum_ i e. ( 0 ..^ ; 1 0 )
            (
              cos
              `
              (
                3
                x.
                ( x ` i )
              )
            )
        )
        <_
        ( ( ; ; 4 8 0 ) / ( ; 4 9 ) )
      )
  ) $.
$}
