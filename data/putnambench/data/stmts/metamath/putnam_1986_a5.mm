$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1986_a5: a real vector field with continuous second-order partial
  derivatives and constant antisymmetric first-partial differences admits a
  scalar potential correction whose components are linear. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  For n in NN, P86A5V n is the full real coordinate space on 1 ... n.
  P86A5Repl replaces one coordinate, P86A5Slice is the resulting real
  one-variable slice, and P86A5Part is its native set.mm derivative at the
  original coordinate. The zero fallback makes P86A5Part total, as are the
  derivative operators in the Lean and Isabelle sources; the fallback is
  inactive for the vector-field components under P86A5C2.

  P86A5C2 requires every first and second coordinate partial derivative to
  exist everywhere and every second-partial function to be continuous in the
  standard finite product topology on RR^(1...n). This is the coordinate
  characterization of global C^2 regularity in finite-dimensional real
  space. P86A5Linear expands real linearity as additivity and scalar
  homogeneity. The constants and the potential remain internally
  existentially quantified. All declarations are unproved $a statement
  encodings; this database contains no $p proof declaration.
$)

$c
  P86A5V P86A5Top P86A5Repl P86A5Slice P86A5Part
  P86A5D1 P86A5D2 P86A5C2 P86A5Linear
$.

p86a5-vector-space-syntax $a class ( P86A5V n ) $.
p86a5-vector-topology-syntax $a class ( P86A5Top n ) $.
p86a5-replace-syntax $a class ( P86A5Repl n x i r ) $.
p86a5-slice-syntax $a class ( P86A5Slice n F i x ) $.
p86a5-partial-syntax $a class ( P86A5Part n F i x ) $.
p86a5-first-partial-function-syntax $a class ( P86A5D1 n F i ) $.
p86a5-second-partial-function-syntax $a class ( P86A5D2 n F i j ) $.
p86a5-c2-syntax $a wff ( P86A5C2 n F ) $.
p86a5-linear-syntax $a wff ( P86A5Linear n F ) $.

p86a5-vector-space-definition $a |- (
  P86A5V n
) = (
  RR ^m ( 1 ... n )
) $.

p86a5-vector-topology-definition $a |- (
  P86A5Top n
) = (
  Xt_ `
    (
      ( 1 ... n )
      X.
      { ( TopOpen ` RRfld ) }
    )
) $.

${
  $d i j n r x $.

  p86a5-replace-definition $a |- (
    P86A5Repl n x i r
  ) = (
    j e. ( 1 ... n ) |->
      if (
        j = i ,
        r ,
        ( x ` j )
      )
  ) $.
$}

${
  $d F i n r x $.

  p86a5-slice-definition $a |- (
    P86A5Slice n F i x
  ) = (
    r e. RR |->
      ( F ` ( P86A5Repl n x i r ) )
  ) $.
$}

${
  $d F i n x $.

  p86a5-partial-definition $a |- (
    P86A5Part n F i x
  ) = if (
    ( x ` i ) e.
      dom
        (
          RR _D
            ( P86A5Slice n F i x )
        ) ,
    (
      (
        RR _D
          ( P86A5Slice n F i x )
      )
      ` ( x ` i )
    ) ,
    0
  ) $.
$}

${
  $d F i n x $.

  p86a5-first-partial-function-definition $a |- (
    P86A5D1 n F i
  ) = (
    x e. ( P86A5V n ) |->
      ( P86A5Part n F i x )
  ) $.
$}

${
  $d F i j n x $.

  p86a5-second-partial-function-definition $a |- (
    P86A5D2 n F i j
  ) = (
    x e. ( P86A5V n ) |->
      (
        P86A5Part
          n
          ( P86A5D1 n F i )
          j
          x
      )
  ) $.
$}

${
  $d F i j n x $.

  p86a5-c2-definition $a |- (
    ( P86A5C2 n F )
    <->
    (
      F e. ( RR ^m ( P86A5V n ) )
      /\
      (
        A. i e. ( 1 ... n )
          A. x e. ( P86A5V n )
            ( x ` i ) e.
              dom
                (
                  RR _D
                    ( P86A5Slice n F i x )
                )
        /\
        A. i e. ( 1 ... n )
          A. j e. ( 1 ... n )
            (
              A. x e. ( P86A5V n )
                ( x ` j ) e.
                  dom
                    (
                      RR _D
                        (
                          P86A5Slice
                            n
                            ( P86A5D1 n F i )
                            j
                            x
                        )
                    )
              /\
              ( P86A5D2 n F i j ) e.
                (
                  ( P86A5Top n )
                  Cn
                  ( TopOpen ` RRfld )
                )
            )
      )
    )
  ) $.
$}

${
  $d F a i n x y $.

  p86a5-linear-definition $a |- (
    ( P86A5Linear n F )
    <->
    (
      F e. ( RR ^m ( P86A5V n ) )
      /\
      (
        A. x e. ( P86A5V n )
          A. y e. ( P86A5V n )
            ( F `
              (
                i e. ( 1 ... n ) |->
                  ( ( x ` i ) + ( y ` i ) )
              )
            )
            =
            ( ( F ` x ) + ( F ` y ) )
        /\
        A. a e. RR
          A. x e. ( P86A5V n )
            ( F `
              (
                i e. ( 1 ... n ) |->
                  ( a x. ( x ` i ) )
              )
            )
            =
            ( a x. ( F ` x ) )
      )
    )
  ) $.
$}

${
  $d C F g i j n x $.

  putnambench-putnam-1986-a5 $a |-
    A. n e. NN
      A. F e.
        (
          ( RR ^m ( P86A5V n ) )
          ^m
          ( 1 ... n )
        )
        (
          (
            (
              A. i e. ( 1 ... n )
                ( P86A5C2 n ( F ` i ) )
              /\
              E. C e.
                (
                  ( RR ^m ( 1 ... n ) )
                  ^m
                  ( 1 ... n )
                )
                A. i e. ( 1 ... n )
                  A. j e. ( 1 ... n )
                    A. x e. ( P86A5V n )
                      (
                        (
                          P86A5Part
                            n
                            ( F ` i )
                            j
                            x
                        )
                        -
                        (
                          P86A5Part
                            n
                            ( F ` j )
                            i
                            x
                        )
                      )
                      =
                      ( ( C ` i ) ` j )
            )
          )
          ->
          E. g e. ( RR ^m ( P86A5V n ) )
            A. i e. ( 1 ... n )
              (
                P86A5Linear
                  n
                  (
                    x e. ( P86A5V n ) |->
                      (
                        ( ( F ` i ) ` x )
                        +
                        ( P86A5Part n g i x )
                      )
                  )
              )
        )
  $.
$}
