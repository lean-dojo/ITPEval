$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2010_b2: the least possible distance AB among noncollinear
  integer-coordinate planar triples whose three pairwise distances are
  integers is 3. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P10B2I is the two-coordinate index set, P10B2R2 is the full real
  coordinate plane, P10B2Dist is ordinary Euclidean distance, and
  P10B2Noncol is determinant noncollinearity. P10B2Good A B C states that
  A, B, and C have integer coordinates, are noncollinear, and have all
  three pairwise distances in ZZ.

  The final conjunction is the explicit IsLeast characterization from the
  sources: an admissible triple attains AB = 3, and every admissible triple
  has AB at least 3. All witnesses remain internally quantified. Every
  declaration below is an unproved $a statement, not a proof.
$)

$c P10B2I P10B2R2 P10B2Dist P10B2Noncol P10B2Good $.

p10b2-index-syntax $a class P10B2I $.
p10b2-plane-syntax $a class P10B2R2 $.
p10b2-distance-syntax $a class ( P10B2Dist A B ) $.
p10b2-noncollinear-syntax $a wff ( P10B2Noncol A B C ) $.
p10b2-good-syntax $a wff ( P10B2Good A B C ) $.

p10b2-index-definition $a |- P10B2I = ( 1 ... 2 ) $.

p10b2-plane-definition $a |- P10B2R2 = ( RR ^m P10B2I ) $.

${
  $d A B j $.

  p10b2-distance-definition $a |- (
    P10B2Dist A B
  ) = (
    sqrt
    `
    (
      sum_ j e. P10B2I
        ( ( ( A ` j ) - ( B ` j ) ) ^ 2 )
    )
  ) $.
$}

p10b2-noncollinear-definition $a |- (
  ( P10B2Noncol A B C )
  <->
  (
    (
      ( ( B ` 1 ) - ( A ` 1 ) )
      x.
      ( ( C ` 2 ) - ( A ` 2 ) )
    )
    =/=
    (
      ( ( B ` 2 ) - ( A ` 2 ) )
      x.
      ( ( C ` 1 ) - ( A ` 1 ) )
    )
  )
) $.

p10b2-good-definition $a |- (
  ( P10B2Good A B C )
  <->
  (
    (
      A e. ( ZZ ^m P10B2I )
      /\
      (
        B e. ( ZZ ^m P10B2I )
        /\
        C e. ( ZZ ^m P10B2I )
      )
    )
    /\
    (
      ( P10B2Noncol A B C )
      /\
      (
        ( P10B2Dist A B ) e. ZZ
        /\
        (
          ( P10B2Dist A C ) e. ZZ
          /\
          ( P10B2Dist B C ) e. ZZ
        )
      )
    )
  )
) $.

${
  $d a b c $.

  putnambench-putnam-2010-b2 $a |- (
    E. a E. b E. c
      (
        ( P10B2Good a b c )
        /\
        ( P10B2Dist a b ) = 3
      )
    /\
    A. a A. b A. c
      (
        ( P10B2Good a b c )
        ->
        3 <_ ( P10B2Dist a b )
      )
  ) $.
$}
