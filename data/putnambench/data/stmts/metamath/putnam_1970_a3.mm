$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1970_a3: the longest nonzero repeated decimal suffix of a perfect
  square has length three, and the least square attaining that length is
  1444. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P70A3Run S K D says that the last K base-10 digits of the nonnegative
  integer S are all the nonzero digit D. The residue formula is exactly the
  least-significant-first digit-list condition in the sources. P70A3Exact
  additionally says that the run does not extend to the next digit; this also
  handles a run reaching the most significant digit because the next leading
  digit is zero.

  The source function L is uniquely characterized by these exact runs on
  numbers with nonzero final digit. Thus the existence and upper-bound
  conjuncts state that its greatest value on squares is 3, while the last
  three conjuncts state that 1444 is a square, has exact run length 3, and is
  no larger than any square with that exact run length. The final declaration
  is the single unproved $a corpus statement; this database contains no $p
  proof statement.
$)

$c P70A3Run P70A3Exact $.

p70a3-run-syntax $a wff ( P70A3Run S K D ) $.
p70a3-exact-syntax $a wff ( P70A3Exact S K ) $.

${
  $d D I K S $.

  p70a3-run-definition $a |- (
    ( P70A3Run S K D )
    <->
    (
      (
        S e. NN0
        /\
        K e. NN
      )
      /\
      (
        D e. ( 1 ... 9 )
        /\
        (
          S mod ( ; 1 0 ^ K )
        )
        =
        (
          D
          x.
          sum_ I e. ( 0 ..^ K ) ( ; 1 0 ^ I )
        )
      )
    )
  ) $.
$}

${
  $d D K S $.

  p70a3-exact-definition $a |- (
    ( P70A3Exact S K )
    <->
    E. D e. ( 1 ... 9 )
      (
        ( P70A3Run S K D )
        /\
        -. ( P70A3Run S ( K + 1 ) D )
      )
  ) $.
$}

${
  $d D K N R $.

  putnambench-putnam-1970-a3 $a |-
    (
      (
        E. N e. NN0 ( P70A3Exact ( N ^ 2 ) 3 )
        /\
        A. N e. NN0
          A. K e. NN
            A. D e. ( 1 ... 9 )
              (
                ( P70A3Run ( N ^ 2 ) K D )
                ->
                K <_ 3
              )
      )
      /\
      (
        E. R e. NN0
          ( R ^ 2 ) = ; ; ; 1 4 4 4
        /\
        (
          ( P70A3Exact ; ; ; 1 4 4 4 3 )
          /\
          A. N e. NN0
            (
              ( P70A3Exact ( N ^ 2 ) 3 )
              ->
              ; ; ; 1 4 4 4 <_ ( N ^ 2 )
            )
        )
      )
    )
  $.
$}
