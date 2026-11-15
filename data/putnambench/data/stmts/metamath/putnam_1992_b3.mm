$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1992_b3: the Lebesgue area of the real-plane parameters for which
  the recursively defined real sequence converges. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  P92B3Index is the two-coordinate index set {0,1}, and P92B3Plane is the
  full real plane represented as real-valued functions on that set.
  P92B3Converges A P says that the NN0-indexed real sequence assigned by A
  to P has an internally existential real limit. P92B3Region A is exactly
  the set of plane parameters satisfying that convergence predicate, and
  P92B3Area A is its two-dimensional Lebesgue measure via set.mm's voln.

  The final assertion substitutes the resolved area 4 + pi, universally
  quantifies the arbitrary sequence family, and retains the complete source
  recurrence as its antecedent. Every declaration is an unproved $a
  statement, and this database contains no $p proof declaration.
$)

$c P92B3Index P92B3Plane P92B3Converges P92B3Region P92B3Area $.

p92b3-index-syntax $a class P92B3Index $.
p92b3-plane-syntax $a class P92B3Plane $.
p92b3-converges-syntax $a wff ( P92B3Converges A P ) $.
p92b3-region-syntax $a class ( P92B3Region A ) $.
p92b3-area-syntax $a class ( P92B3Area A ) $.

p92b3-index-definition $a |- P92B3Index = ( 0 ... 1 ) $.

p92b3-plane-definition $a |- P92B3Plane = ( RR ^m P92B3Index ) $.

${
  $d A P l n $.

  p92b3-converges-definition $a |- (
    ( P92B3Converges A P )
    <->
    E. l e. RR
      (
        n e. NN0 |->
          ( ( A ` P ) ` n )
      )
      ~~>
      l
  ) $.
$}

${
  $d A p $.

  p92b3-region-definition $a |- (
    P92B3Region A
  ) = {
    p e. P92B3Plane |
      ( P92B3Converges A p )
  } $.
$}

p92b3-area-definition $a |- (
  P92B3Area A
) = (
  ( voln ` P92B3Index )
  `
  ( P92B3Region A )
) $.

${
  $d a n p $.

  putnambench-putnam-1992-b3 $a |-
    A. a e. ( ( RR ^m NN0 ) ^m P92B3Plane )
      (
        A. p e. P92B3Plane
          (
            ( ( a ` p ) ` 0 ) = ( p ` 0 )
            /\
            A. n e. NN0
              ( ( a ` p ) ` ( n + 1 ) )
              =
              (
                (
                  ( ( ( a ` p ) ` n ) ^ 2 )
                  +
                  ( ( p ` 1 ) ^ 2 )
                )
                /
                2
              )
          )
        ->
        ( 4 + _pi ) = ( P92B3Area a )
      )
  $.
$}
