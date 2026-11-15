$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2014_a6: the largest size of two indexed families of real square
  matrices whose cross-products have a zero diagonal entry exactly for
  distinct indices is n^n. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For positive n and k, P14A6Feasible n k says that there are two k-term
  families of real n-by-n matrices such that, for every pair of family
  indices i and j, the product M_i N_j has some zero diagonal entry if and
  only if i and j are distinct.

  The carriers 0 ..^ n and 0 ..^ k are the canonical n-element and k-element
  finite ordinals. Base ` ((0 ..^ n) Mat RRfld) is the full real n-by-n
  matrix carrier, and its ring multiplication is ordinary matrix
  multiplication. Thus the existential matrix families and the diagonal
  witness remain quantified exactly as in the source.

  The final conjunction states feasibility at n^n and an upper bound of n^n
  for every positive feasible k, which is bidirectionally equivalent to the
  source largest-value formulation after expanding kex and the stated
  solution. All declarations are unproved $a statement encodings; this
  database contains no $p proof declaration.
$)

$c P14A6Feasible $.

p14a6-feasible-syntax $a wff ( P14A6Feasible n k ) $.

${
  $d M N i j k n p $.

  p14a6-feasible-definition $a |- (
    ( P14A6Feasible n k )
    <->
    E. M e.
      (
        ( Base ` ( ( 0 ..^ n ) Mat RRfld ) )
        ^m
        ( 0 ..^ k )
      )
      E. N e.
        (
          ( Base ` ( ( 0 ..^ n ) Mat RRfld ) )
          ^m
          ( 0 ..^ k )
        )
        A. i e. ( 0 ..^ k )
          A. j e. ( 0 ..^ k )
            (
              E. p e. ( 0 ..^ n )
                (
                  (
                    (
                      ( M ` i )
                      ( .r ` ( ( 0 ..^ n ) Mat RRfld ) )
                      ( N ` j )
                    )
                    `
                    <. p , p >.
                  )
                  =
                  0
                )
              <->
              i =/= j
            )
  ) $.
$}

${
  $d k n $.

  putnambench-putnam-2014-a6 $a |- A. n e. NN
    (
      ( P14A6Feasible n ( n ^ n ) )
      /\
      A. k e. NN
        (
          ( P14A6Feasible n k )
          ->
          k <_ ( n ^ n )
        )
    )
  $.
$}
