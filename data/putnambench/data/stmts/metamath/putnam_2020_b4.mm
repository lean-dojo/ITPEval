$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2020_b4: the reciprocal average over integer lattice paths of
  length 4040 that start and end at zero equals 1/4040. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  P20B4V is the finite set of all integer-valued paths s on the inclusive
  index interval 0 ... 4040 with s(0) = s(4040) = 0 and every successive
  difference of absolute value one. Restriction to this interval is
  bijective to the source's natural-indexed sequences that are zero from
  index 4040 onward.

  SetMM's integer power 3 ^ (s ` j) agrees with the real integer power in
  the source, including at negative path heights. The numerator sums the
  reciprocal of 1 plus the interior-height power sum over every path, and
  division by the finite cardinality is exactly the requested average.
  The right side inlines the documented solution 1/4040.

  The path-class definition and the final corpus statement are unproved $a
  declarations; this database contains no $p proof declaration.
$)

$c P20B4V $.

p20b4-paths-syntax $a class P20B4V $.

${
  $d j s $.

  p20b4-paths-definition $a |- P20B4V =
    {
      s e. ( ZZ ^m ( 0 ... ; ; ; 4 0 4 0 ) ) |
      (
        (
          ( s ` 0 ) = 0
          /\
          ( s ` ; ; ; 4 0 4 0 ) = 0
        )
        /\
        A. j e. ( 1 ... ; ; ; 4 0 4 0 )
          ( abs ` ( ( s ` j ) - ( s ` ( j - 1 ) ) ) ) = 1
      )
    }
  $.
$}

${
  $d j s $.

  putnambench-putnam-2020-b4 $a |-
    (
      (
        sum_ s e. P20B4V
          (
            1
            /
            (
              1
              +
              sum_ j e. ( 1 ... ; ; ; 4 0 3 9 )
                ( 3 ^ ( s ` j ) )
            )
          )
      )
      /
      ( # ` P20B4V )
    )
    =
    ( 1 / ; ; ; 4 0 4 0 )
  $.
$}
