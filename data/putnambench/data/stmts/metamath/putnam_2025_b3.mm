$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2025_b3 (putnambench__metamath__putnam_2025_b3): every nonempty
  set of positive integers closed under positive divisors of
  2025^n - 15^n for each member n is the set of all positive integers.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN is the class of positive integers. Thus S C_ NN combines the
  source type S : Set Nat with its explicit condition that every member is
  positive, while S =/= (/) preserves nonemptiness.

  The restricted quantifier over d in NN is equivalent to quantifying over
  all natural d and assuming 0 < d. For positive n, 2025^n - 15^n is
  positive, so SetMM's integer subtraction and divisibility agree with the
  source's natural subtraction and natural divisibility. The source solution
  annotation is True, so eliminating the wrapper True <-> P leaves exactly
  P. The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d S d n $.

  putnambench-putnam-2025-b3 $a |- A. S
    (
      (
        (
          S C_ NN
          /\
          S =/= (/)
        )
        /\
        A. n e. S
          A. d e. NN
            (
              d || (
                ( ( ; ; ; 2 0 2 5 ) ^ n )
                -
                ( ( ; 1 5 ) ^ n )
              )
              ->
              d e. S
            )
      )
      ->
      S = NN
    )
  $.
$}
