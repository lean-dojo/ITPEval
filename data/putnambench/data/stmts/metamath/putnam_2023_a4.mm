$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2023_a4: integer linear combinations of the twelve unit vectors
  from the origin to the vertices of a regular icosahedron are dense in
  real Euclidean three-space. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P23A4I3 and P23A4I12 are the finite coordinate sets corresponding to Fin 3
  and Fin 12. P23A4R3 is real coordinate three-space. P23A4Coords is the
  exact ordered list of the twelve unnormalized icosahedron vertices from the
  Lean source, with golden ratio P23A4Phi; division by P23A4Scale normalizes
  them.

  P23A4Orth says that a real 3-by-3 matrix has orthonormal rows, which in
  finite dimension is equivalent to the source's real linear isometric
  equivalence. P23A4Apply is its action on a vector. Thus the existential
  matrix in the hypothesis preserves the source's internally existential
  isometry and its equation with the normalized vertex family.

  P23A4LinComb and P23A4Dist expand the finite integer linear combination
  and Euclidean norm coordinatewise. The final declaration retains the
  arbitrary vertex family, target vector, positive real epsilon, and
  internally existential integer coefficient family. Every declaration is
  an unproved $a statement encoding; this database contains no $p proof.
$)

$c P23A4I3 P23A4I12 P23A4R3 P23A4Phi P23A4Scale P23A4Coords P23A4Orth
   P23A4Apply P23A4LinComb P23A4Dist $.

p23a4-coordinate-index-syntax $a class P23A4I3 $.
p23a4-index-syntax $a class P23A4I12 $.
p23a4-space-syntax $a class P23A4R3 $.
p23a4-phi-syntax $a class P23A4Phi $.
p23a4-scale-syntax $a class P23A4Scale $.
p23a4-coordinates-syntax $a class P23A4Coords $.
p23a4-orthogonal-syntax $a wff ( P23A4Orth Q ) $.
p23a4-apply-syntax $a class ( P23A4Apply Q A ) $.
p23a4-linear-combination-syntax $a class ( P23A4LinComb A V ) $.
p23a4-distance-syntax $a class ( P23A4Dist A B ) $.

p23a4-coordinate-index-definition $a |- P23A4I3 = ( 0 ..^ 3 ) $.

p23a4-index-definition $a |- P23A4I12 = ( 0 ..^ ( 3 x. 4 ) ) $.

p23a4-space-definition $a |- P23A4R3 = ( RR ^m P23A4I3 ) $.

p23a4-phi-definition $a |- P23A4Phi =
  ( ( 1 + ( sqrt ` 5 ) ) / 2 ) $.

p23a4-scale-definition $a |- P23A4Scale =
  ( sqrt ` ( 1 + ( P23A4Phi ^ 2 ) ) ) $.

${
  $d i k $.

  p23a4-coordinates-definition $a |- P23A4Coords =
    (
      i e. P23A4I12 , k e. P23A4I3 |->
        if (
          i < 4 ,
          if (
            k = 0 ,
            if ( ( i = 0 \/ i = 2 ) , 1 , ( -u 1 ) ) ,
            if (
              k = 1 ,
              if (
                ( i = 0 \/ i = 1 ) ,
                P23A4Phi ,
                ( -u P23A4Phi )
              ) ,
              0
            )
          ) ,
          if (
            i < 8 ,
            if (
              k = 0 ,
              if (
                ( i = 4 \/ i = 5 ) ,
                P23A4Phi ,
                ( -u P23A4Phi )
              ) ,
              if (
                k = 1 ,
                0 ,
                if ( ( i = 4 \/ i = 6 ) , 1 , ( -u 1 ) )
              )
            ) ,
            if (
              k = 0 ,
              0 ,
              if (
                k = 1 ,
                if ( ( i = 8 \/ i = ( 8 + 2 ) ) , 1 , ( -u 1 ) ) ,
                if (
                  ( i = 8 \/ i = 9 ) ,
                  P23A4Phi ,
                  ( -u P23A4Phi )
                )
              )
            )
          )
        )
    ) $.
$}

${
  $d Q i j k $.

  p23a4-orthogonal-definition $a |- (
    ( P23A4Orth Q )
    <->
    (
      Q e. ( RR ^m ( P23A4I3 X. P23A4I3 ) )
      /\
      A. i e. P23A4I3 A. j e. P23A4I3
        (
          sum_ k e. P23A4I3
            (
              ( Q ` <. i , k >. )
              x.
              ( Q ` <. j , k >. )
            )
        )
        =
        if ( i = j , 1 , 0 )
    )
  ) $.
$}

${
  $d A Q i j $.

  p23a4-apply-definition $a |- (
    P23A4Apply Q A
  ) = (
    i e. P23A4I3 |->
      sum_ j e. P23A4I3
        (
          ( Q ` <. i , j >. )
          x.
          ( A ` j )
        )
  ) $.
$}

${
  $d A V i k $.

  p23a4-linear-combination-definition $a |- (
    P23A4LinComb A V
  ) = (
    k e. P23A4I3 |->
      sum_ i e. P23A4I12
        (
          ( A ` i )
          x.
          ( ( V ` i ) ` k )
        )
  ) $.
$}

${
  $d A B k $.

  p23a4-distance-definition $a |- (
    P23A4Dist A B
  ) = (
    sqrt
    `
    (
      sum_ k e. P23A4I3
        ( ( ( A ` k ) - ( B ` k ) ) ^ 2 )
    )
  ) $.
$}

${
  $d a e i k q v w $.

  putnambench-putnam-2023-a4 $a |-
    A. v e. ( P23A4R3 ^m P23A4I12 )
      (
        E. q
          (
            ( P23A4Orth q )
            /\
            A. i e. P23A4I12
              (
                P23A4Apply q ( v ` i )
              ) = (
                k e. P23A4I3 |->
                  (
                    ( P23A4Coords ` <. i , k >. )
                    /
                    P23A4Scale
                  )
              )
          )
        ->
        A. w e. P23A4R3 A. e e. RR
          (
            0 < e
            ->
            E. a e. ( ZZ ^m P23A4I12 )
              (
                P23A4Dist
                  ( P23A4LinComb a v )
                  w
              ) < e
          )
      )
  $.
$}
