$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1969_b2: a finite group is not the union of two proper subgroups,
  while the corresponding three-subgroup assertion is false. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  For a natural number N, P69B2CoverProperty N quantifies over every finite
  SetMM group G and every family H of subgroups indexed by 0,...,N-1. If
  every H ` i is proper, U. ran H is required to differ from Base ` G.
  Since each family member is a subgroup, its union is already contained in
  the carrier, so this inequality is equivalent to the source's strict-subset
  conclusion. The final declaration states the resolved answer P(2) and not
  P(3). It is the single unproved $a corpus statement, and this database
  contains no $p proof statement.
$)

$c P69B2CoverProperty $.

p69b2-cover-property-syntax $a wff ( P69B2CoverProperty N ) $.

${
  $d G H N i $.

  p69b2-cover-property-definition $a |- (
    ( P69B2CoverProperty N )
    <->
    (
      N e. NN0
      /\
      A. G
        (
          (
            G e. Grp
            /\
            ( Base ` G ) e. Fin
          )
          ->
          A. H e. ( ( SubGrp ` G ) ^m ( 0 ..^ N ) )
            (
              A. i e. ( 0 ..^ N )
                ( H ` i ) =/= ( Base ` G )
              ->
              U. ran H =/= ( Base ` G )
            )
        )
    )
  ) $.
$}

putnambench-putnam-1969-b2 $a |- (
  ( P69B2CoverProperty 2 )
  /\
  -. ( P69B2CoverProperty 3 )
) $.
