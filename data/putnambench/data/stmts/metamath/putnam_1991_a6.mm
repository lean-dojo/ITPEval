$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1991_a6: equality between two counts of positive-integer
  compositions, one defined by strict next-term inequalities and the other
  by a nonincreasing recurrence-valued representation using every recurrence
  value through its largest term. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A composition is represented exactly as in the sources by a pair p whose
  first component is its positive length and whose second component is a
  total NN0-indexed NN0-valued function. P91A6Base requires positive entries
  before the length, a zero tail, and the prescribed finite sum.

  P91A6A is the source agt condition. P91A6B combines the source bge, bg1,
  and bg2 conditions: the entries are nonincreasing, every entry is a value
  of g, and if the first entry is g(k), every g(j) for j at most k occurs.
  The final assertion inlines the source definitions of A and B and equates
  the cardinalities for every positive n and every natural-valued g satisfying
  the stated recurrence. All declarations are unproved $a statement
  encodings; this database contains no $p proof declaration.
$)

$c P91A6Base P91A6A P91A6B $.

p91a6-base-syntax $a wff ( P91A6Base n p ) $.
p91a6-a-syntax $a wff ( P91A6A p ) $.
p91a6-b-syntax $a wff ( P91A6B g p ) $.

${
  $d i n p $.

  p91a6-base-definition $a |- (
    P91A6Base n p
  ) <->
  (
    (
      A. i e. ( 0 ..^ ( 1st ` p ) )
        0 < ( ( 2nd ` p ) ` i )
      /\
      A. i e. NN0
        (
          ( 1st ` p ) <_ i
          ->
          ( ( 2nd ` p ) ` i ) = 0
        )
    )
    /\
    (
      sum_ i e. ( 0 ..^ ( 1st ` p ) )
        ( ( 2nd ` p ) ` i )
    )
    =
    n
  ) $.
$}

${
  $d i p $.

  p91a6-a-definition $a |- (
    P91A6A p
  ) <->
  (
    A. i e. ( 0 ..^ ( ( 1st ` p ) - 2 ) )
      (
        (
          ( ( 2nd ` p ) ` ( i + 1 ) )
          +
          ( ( 2nd ` p ) ` ( i + 2 ) )
        )
        <
        ( ( 2nd ` p ) ` i )
      )
    /\
    (
      1 < ( 1st ` p )
      ->
      (
        ( ( 2nd ` p ) ` ( ( 1st ` p ) - 1 ) )
        <
        ( ( 2nd ` p ) ` ( ( 1st ` p ) - 2 ) )
      )
    )
  ) $.
$}

${
  $d g i j k p $.

  p91a6-b-definition $a |- (
    P91A6B g p
  ) <->
  (
    A. i e. ( 0 ..^ ( ( 1st ` p ) - 1 ) )
      (
        ( ( 2nd ` p ) ` ( i + 1 ) )
        <_
        ( ( 2nd ` p ) ` i )
      )
    /\
    (
      A. i e. ( 0 ..^ ( 1st ` p ) )
        E. j e. NN0
          ( ( 2nd ` p ) ` i ) = ( g ` j )
      /\
      E. k e. NN0
        (
          ( ( 2nd ` p ) ` 0 ) = ( g ` k )
          /\
          A. j e. ( 0 ... k )
            E. i e. ( 0 ..^ ( 1st ` p ) )
              ( ( 2nd ` p ) ` i ) = ( g ` j )
        )
    )
  ) $.
$}

${
  $d g j n p $.

  putnambench-putnam-1991-a6 $a |-
    A. g e. ( NN0 ^m NN0 )
      (
        (
          ( g ` 0 ) = 1
          /\
          (
            ( g ` 1 ) = 2
            /\
            A. j e. NN0
              (
                2 <_ j
                ->
                ( g ` j )
                =
                (
                  ( ( g ` ( j - 1 ) ) + ( g ` ( j - 2 ) ) )
                  +
                  1
                )
              )
          )
        )
        ->
        A. n e. NN
          (
            #
            `
            {
              p e. ( NN X. ( NN0 ^m NN0 ) ) |
                ( ( P91A6Base n p ) /\ ( P91A6A p ) )
            }
          )
          =
          (
            #
            `
            {
              p e. ( NN X. ( NN0 ^m NN0 ) ) |
                ( ( P91A6Base n p ) /\ ( P91A6B g p ) )
            }
          )
      )
  $.
$}
