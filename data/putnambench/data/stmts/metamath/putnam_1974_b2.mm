$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1974_b2: a continuously differentiable real function whose
  squared derivative plus cubed value tends to zero at positive infinity
  has both its value and derivative tend to zero. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The variable y ranges over total real-valued functions on the reals.
  Membership in ( ( C^n ` RR ) ` 1 ) is set.mm's native assertion of global
  continuous differentiability through order one, and
  ( ( RR Dn y ) ` 1 ) is its real derivative. The relation ~~>r expresses
  convergence at positive infinity for real-indexed functions.

  Thus the antecedent and both conjuncts of the conclusion are direct
  target-native renderings of the three source limits. The final declaration
  is the single unproved $a corpus statement; this database contains no $p
  proof statement.
$)

${
  $d x y $.

  putnambench-putnam-1974-b2 $a |- A. y e. ( RR ^m RR )
    (
      (
        y e. ( ( C^n ` RR ) ` 1 )
        /\
        (
          x e. RR |->
            (
              ( ( ( ( RR Dn y ) ` 1 ) ` x ) ^ 2 )
              +
              ( ( y ` x ) ^ 3 )
            )
        )
        ~~>r
        0
      )
      ->
      (
        (
          x e. RR |->
            ( y ` x )
        )
        ~~>r
        0
        /\
        (
          x e. RR |->
            ( ( ( RR Dn y ) ` 1 ) ` x )
        )
        ~~>r
        0
      )
    )
  $.
$}
