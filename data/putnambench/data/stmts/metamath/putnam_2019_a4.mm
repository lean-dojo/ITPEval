$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2019_a4: a nonzero continuous real-valued function on real
  three-space has zero surface integral over every unit sphere, giving a
  negative answer to the stated uniqueness question. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  P19A4R3 is real Euclidean three-space indexed by the three-element ordinal,
  and P19A4Dist is its Euclidean distance. P19A4Continuous expands continuity
  in the Euclidean metric.

  P19A4SpherePoint C t p is the point on the unit sphere centered at C with
  azimuth t and polar angle p. P19A4SurfaceIntegral uses the standard
  spherical parametrization and its sin(p) surface-area factor. For continuous
  F, the iterated real Lebesgue integral is exactly the integral against
  two-dimensional Hausdorff measure on the unit sphere; the parametrization's
  repetitions occur only on measure-zero boundary sets.

  The final existential is the negation of the universal zero conclusion in
  the source. The source predicate P is inlined using P_def, and its annotated
  solution False turns the displayed biconditional into this counterexample
  statement. The final declaration is the single unproved $a corpus statement;
  this database contains no $p proof declaration.
$)

$c P19A4R3 P19A4Dist P19A4Continuous P19A4SpherePoint
   P19A4SurfaceIntegral $.

p19a4-space-syntax $a class P19A4R3 $.
p19a4-distance-syntax $a class ( P19A4Dist A B ) $.
p19a4-continuous-syntax $a wff ( P19A4Continuous F ) $.
p19a4-sphere-point-syntax $a class ( P19A4SpherePoint C t p ) $.
p19a4-surface-integral-syntax $a class ( P19A4SurfaceIntegral F C ) $.

p19a4-space-definition $a |- P19A4R3 = ( RR ^m 3 ) $.

${
  $d A B k $.

  p19a4-distance-definition $a |- (
    P19A4Dist A B
  ) = (
    sqrt
    `
    (
      sum_ k e. 3
        ( ( ( A ` k ) - ( B ` k ) ) ^ 2 )
    )
  ) $.
$}

${
  $d F A B d e $.

  p19a4-continuous-definition $a |- (
    ( P19A4Continuous F )
    <->
    A. A e. P19A4R3 A. e e. RR
      (
        0 < e
        ->
        E. d e. RR
          (
            0 < d
            /\
            A. B e. P19A4R3
              (
                ( P19A4Dist A B ) < d
                ->
                (
                  abs
                  `
                  (
                    ( F ` A )
                    -
                    ( F ` B )
                  )
                )
                < e
              )
          )
      )
  ) $.
$}

${
  $d C k p t $.

  p19a4-sphere-point-definition $a |- (
    P19A4SpherePoint C t p
  ) = (
    k e. 3 |->
      if (
        k = 0 ,
        (
          ( C ` 0 )
          +
          (
            ( sin ` p )
            x.
            ( cos ` t )
          )
        ) ,
        if (
          k = 1 ,
          (
            ( C ` 1 )
            +
            (
              ( sin ` p )
              x.
              ( sin ` t )
            )
          ) ,
          (
            ( C ` 2 )
            +
            ( cos ` p )
          )
        )
      )
  ) $.
$}

${
  $d F C p t $.

  p19a4-surface-integral-definition $a |- (
    P19A4SurfaceIntegral F C
  ) = (
    S. ( 0 [,] ( 2 x. _pi ) )
      (
        S. ( 0 [,] _pi )
          (
            (
              F
              `
              ( P19A4SpherePoint C t p )
            )
            x.
            ( sin ` p )
          )
          _d p
      )
      _d t
  ) $.
$}

${
  $d F C X $.

  putnambench-putnam-2019-a4 $a |-
    E. F e. ( RR ^m P19A4R3 )
      (
        (
          ( P19A4Continuous F )
          /\
          A. C e. P19A4R3
            ( P19A4SurfaceIntegral F C ) = 0
        )
        /\
        E. X e. P19A4R3
          ( F ` X ) =/= 0
      )
  $.
$}
