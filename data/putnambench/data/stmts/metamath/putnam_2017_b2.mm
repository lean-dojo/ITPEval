$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2017_b2: the least positive starting integer whose sum of 2017
  consecutive positive integers has no representation by another number
  k greater than 1 of consecutive positive integers. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  P17B2Valid(a) says that a is a positive integer and that whenever its
  2017-term consecutive sum equals a k-term consecutive sum beginning at a
  positive integer b, with k > 1, then k = 2017. Thus it is exactly the
  source property that the represented positive integer has no other
  admissible length.

  The carrier 0 ..^ k is the set of natural indices from 0 through k - 1,
  so each displayed finite sum is a + (a+1) + ... + (a+k-1). The final
  conjunction states that 16 has the property and is no greater than every
  other positive integer having it, which is the explicit attained-minimum
  form of the source IsLeast/LEAST statement. All declarations are unproved
  $a statement encodings; this database contains no $p proof declaration.
$)

$c P17B2Valid $.

p17b2-valid-syntax $a wff ( P17B2Valid A ) $.

${
  $d A b i k $.

  p17b2-valid-definition $a |- (
    ( P17B2Valid A )
    <->
    (
      (
        A e. ZZ
        /\
        0 < A
      )
      /\
      A. b e. ZZ A. k e. NN0
        (
          (
            (
              0 < b
              /\
              1 < k
            )
            /\
            (
              sum_ i e. ( 0 ..^ ( ; ; ; 2 0 1 7 ) )
                ( A + i )
            )
            =
            (
              sum_ i e. ( 0 ..^ k )
                ( b + i )
            )
          )
          ->
          k = ( ; ; ; 2 0 1 7 )
        )
    )
  ) $.
$}

putnambench-putnam-2017-b2 $a |- (
  ( P17B2Valid ; 1 6 )
  /\
  A. a e. ZZ
    (
      ( P17B2Valid a )
      ->
      ; 1 6 <_ a
    )
) $.
