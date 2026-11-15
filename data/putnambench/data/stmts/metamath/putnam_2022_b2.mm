$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2022_b2: the positive cardinalities of finite subsets of real
  three-space equal to their set of pairwise cross products are exactly
  1 and 7. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P22B2I3 is the three-element coordinate interval {0,1,2}, P22B2R3 is the
  corresponding real coordinate space, and P22B2Cross is the ordinary
  coordinate cross product.
  The restricted class in the final assertion is therefore exactly
  { v cross w | v in S and w in S }.

  Quantification over n in NN0 together with the explicit positivity
  conjunct preserves the source statement for every natural number.
  The finite set S and both cross-product inputs remain internally
  existentially quantified. All declarations are unproved $a statement
  or definition encodings; this database contains no $p proof.
$)

$c P22B2I3 P22B2R3 P22B2Cross $.

p22b2-index-syntax $a class P22B2I3 $.
p22b2-space-syntax $a class P22B2R3 $.
p22b2-cross-syntax $a class ( P22B2Cross v w ) $.

p22b2-index-definition $a |- P22B2I3 = ( 0 ... 2 ) $.

p22b2-space-definition $a |- P22B2R3 = ( RR ^m P22B2I3 ) $.

${
  $d k v w $.

  p22b2-cross-definition $a |- (
    P22B2Cross v w
  ) = (
    k e. P22B2I3 |->
      if (
        k = 0 ,
        (
          ( ( v ` 1 ) x. ( w ` 2 ) )
          -
          ( ( v ` 2 ) x. ( w ` 1 ) )
        ) ,
        if (
          k = 1 ,
          (
            ( ( v ` 2 ) x. ( w ` 0 ) )
            -
            ( ( v ` 0 ) x. ( w ` 2 ) )
          ) ,
          (
            ( ( v ` 0 ) x. ( w ` 1 ) )
            -
            ( ( v ` 1 ) x. ( w ` 0 ) )
          )
        )
      )
  ) $.
$}

${
  $d n s u v w $.

  putnambench-putnam-2022-b2 $a |- A. n e. NN0
    (
      (
        0 < n
        /\
        E. s e. Fin
          (
            s C_ P22B2R3
            /\
            (
              ( # ` s ) = n
              /\
              s =
                {
                  u e. P22B2R3 |
                    E. v e. s E. w e. s
                      u = ( P22B2Cross v w )
                }
            )
          )
      )
      <->
      (
        n = 1
        \/
        n = 7
      )
    )
  $.
$}
