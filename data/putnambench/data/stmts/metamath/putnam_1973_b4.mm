$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1973_b4: an inequality between unit-interval integrals of a
  continuously differentiable real function, together with an identity
  function attaining equality. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P73B4Hprop unfolds the source predicate on total real-valued functions:
  global continuous differentiability through order one, derivative strictly
  positive and at most one at every real argument, and value zero at zero.
  P73B4Solution is the identity function, the equality example specified by
  the source annotations and the Rocq definition.

  The binder S. A B _d x is set.mm's Lebesgue integral over A. Thus the two
  displayed integrals are exactly over the closed unit interval. Unfolding
  P73B4Hprop and P73B4Solution gives the same hypotheses, main inequality,
  admissible equality example, and exact equality required by the sources.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

$c P73B4Hprop P73B4Solution $.

p73b4-hprop-syntax $a wff ( P73B4Hprop F ) $.
p73b4-solution-syntax $a class P73B4Solution $.

${
  $d F x $.

  p73b4-hprop-definition $a |- (
    ( P73B4Hprop F )
    <->
    (
      F e. ( RR ^m RR )
      /\
      (
        F e. ( ( C^n ` RR ) ` 1 )
        /\
        (
          A. x e. RR
            (
              0 < ( ( ( RR Dn F ) ` 1 ) ` x )
              /\
              ( ( ( RR Dn F ) ` 1 ) ` x ) <_ 1
            )
          /\
          ( F ` 0 ) = 0
        )
      )
    )
  ) $.
$}

p73b4-solution-definition $a |- P73B4Solution =
  ( x e. RR |-> x ) $.

${
  $d F x $.

  putnambench-putnam-1973-b4 $a |- A. F e. ( RR ^m RR )
    (
      ( P73B4Hprop F )
      ->
      (
        (
          S. ( 0 [,] 1 )
            ( ( F ` x ) ^ 3 )
            _d x
        )
        <_
        (
          (
            S. ( 0 [,] 1 )
              ( F ` x )
              _d x
          )
          ^ 2
        )
        /\
        (
          ( P73B4Hprop P73B4Solution )
          /\
          (
            (
              S. ( 0 [,] 1 )
                ( P73B4Solution ` x )
                _d x
            )
            ^ 2
          )
          =
          S. ( 0 [,] 1 )
            ( ( P73B4Solution ` x ) ^ 3 )
            _d x
        )
      )
    )
  $.
$}
