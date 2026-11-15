$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1988_a4: every three-coloring of the real Euclidean plane has a
  monochromatic pair at unit distance, while some nine-coloring has no such
  pair. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P88A4R2 is the full real coordinate plane and P88A4Dist is its ordinary
  Euclidean distance. The finite carriers 1 ... 3 and 1 ... 9 differ from
  Fin 3 and Fin 9 only by a bijective relabeling; since the statement observes
  colors only through equality, this preserves each coloring proposition.

  The source solution pair is (True, False). Thus its two biconditionals are
  equivalently represented by the three-color proposition conjoined with the
  negation of the nine-color proposition. Every coloring remains universally
  quantified over all total functions on the plane, and both point witnesses
  remain internal. The final declaration is a single unproved $a statement.
$)

$c P88A4I P88A4R2 P88A4Dist $.

p88a4-index-syntax $a class P88A4I $.
p88a4-plane-syntax $a class P88A4R2 $.
p88a4-distance-syntax $a class ( P88A4Dist A B ) $.

p88a4-index-definition $a |- P88A4I = ( 1 ... 2 ) $.

p88a4-plane-definition $a |- P88A4R2 = ( RR ^m P88A4I ) $.

${
  $d A B k $.

  p88a4-distance-definition $a |- (
    P88A4Dist A B
  ) = (
    sqrt
    `
    (
      sum_ k e. P88A4I
        ( ( ( A ` k ) - ( B ` k ) ) ^ 2 )
    )
  ) $.
$}

${
  $d C p q $.

  putnambench-putnam-1988-a4 $a |- (
    A. C e. ( ( 1 ... 3 ) ^m P88A4R2 )
      E. p e. P88A4R2 E. q e. P88A4R2
        (
          ( C ` p ) = ( C ` q )
          /\
          ( P88A4Dist p q ) = 1
        )
    /\
    -.
      A. C e. ( ( 1 ... 9 ) ^m P88A4R2 )
        E. p e. P88A4R2 E. q e. P88A4R2
          (
            ( C ` p ) = ( C ` q )
            /\
            ( P88A4Dist p q ) = 1
          )
  ) $.
$}
