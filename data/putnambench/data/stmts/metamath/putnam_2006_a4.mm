$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2006_a4: the average number of local maxima, including the
  one-sided endpoint cases, among permutations of a finite integer interval
  is (n + 1) / 3. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For n > 1, the interval 1 ... n is the problem's set S, and the base of
  its symmetric group is exactly the set of all permutations of S. For each
  permutation p, the restricted class contains precisely its local-maximum
  positions: at 1 only the right comparison is required, at n only the left
  comparison is required, and at every interior position both are required.

  Its finite cardinality is therefore the local-maximum count. Summing that
  count over the symmetric group and dividing by the group's cardinality is
  the requested average. Shifting positions and values down by one gives the
  Fin n formulation in the Lean and Isabelle sources. The final declaration
  is the single unproved $a corpus statement; this database contains no $p
  proof declaration.
$)

${
  $d k n p $.

  putnambench-putnam-2006-a4 $a |- A. n e. NN
    (
      1 < n
      ->
      (
        (
          sum_ p e. ( Base ` ( SymGrp ` ( 1 ... n ) ) )
            (
              #
              `
              {
                k e. ( 1 ... n )
                |
                (
                  (
                    k = 1
                    \/
                    ( p ` ( k - 1 ) ) < ( p ` k )
                  )
                  /\
                  (
                    k = n
                    \/
                    ( p ` ( k + 1 ) ) < ( p ` k )
                  )
                )
              }
            )
        )
        /
        (
          #
          `
          ( Base ` ( SymGrp ` ( 1 ... n ) ) )
        )
      )
      =
      ( ( n + 1 ) / 3 )
    )
  $.
$}
