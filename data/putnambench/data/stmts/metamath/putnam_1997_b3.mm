$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1997_b3: positive integers whose harmonic sum has reduced
  denominator not divisible by 5 are exactly 1 through 4, 20 through 24,
  100 through 104, and 120 through 124. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN is set.mm's class of positive integers. The sum binder ranges over the
  inclusive interval 1 ... n, and denom gives the positive denominator of
  the unique reduced rational representation of that harmonic sum. Thus
  nondivisibility by 5 is exactly the denominator condition in the sources.

  The four inclusive intervals inline the solution set defined in the Rocq
  source and documented in the Lean and Isabelle sources. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

${
  $d m n $.

  putnambench-putnam-1997-b3 $a |- A. n e. NN
    (
      (
        n e. ( 1 ... 4 )
        \/
        (
          n e. ( ; 2 0 ... ; 2 4 )
          \/
          (
            n e. ( ; ; 1 0 0 ... ; ; 1 0 4 )
            \/
            n e. ( ; ; 1 2 0 ... ; ; 1 2 4 )
          )
        )
      )
      <->
      -. 5 ||
        (
          denom
          `
          (
            sum_ m e. ( 1 ... n ) ( 1 / m )
          )
        )
    )
  $.
$}
