$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2021_a3: positive integers N for which the sphere
  x^2 + y^2 + z^2 = N contains an integer-coordinate regular tetrahedron
  are exactly the integers 3 times a positive square. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  P21A3R3 is real coordinate three-space, P21A3NormSq is squared
  Euclidean norm, P21A3Dist is ordinary Euclidean distance, and
  P21A3Sphere N is the sphere whose squared radius is N.

  P21A3Tetra N retains the source's four internally existential vertices
  and positive common side length. Membership in ZZ ^m 3 is exactly the
  integer-coordinate condition, while membership in P21A3Sphere N is the
  equation x^2 + y^2 + z^2 = N.

  The final biconditional explicitly instantiates the solution set described
  in the ground-truth comments as { 3 * m^2 | m is a positive natural }.
  Every declaration is an unproved $a statement encoding; this database
  contains no $p proof statement.
$)

$c P21A3R3 P21A3NormSq P21A3Dist P21A3Sphere P21A3Tetra $.

p21a3-space-syntax $a class P21A3R3 $.
p21a3-norm-square-syntax $a class ( P21A3NormSq A ) $.
p21a3-distance-syntax $a class ( P21A3Dist A B ) $.
p21a3-sphere-syntax $a class ( P21A3Sphere N ) $.
p21a3-tetrahedron-syntax $a wff ( P21A3Tetra N ) $.

p21a3-space-definition $a |- P21A3R3 = ( RR ^m 3 ) $.

${
  $d A k $.

  p21a3-norm-square-definition $a |- (
    P21A3NormSq A
  ) = (
    sum_ k e. 3
      ( ( A ` k ) ^ 2 )
  ) $.
$}

${
  $d A B k $.

  p21a3-distance-definition $a |- (
    P21A3Dist A B
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
  $d N P $.

  p21a3-sphere-definition $a |- (
    P21A3Sphere N
  ) = {
    P e. P21A3R3 |
      ( P21A3NormSq P ) = N
  } $.
$}

${
  $d A B C D N s $.

  p21a3-tetrahedron-definition $a |- (
    ( P21A3Tetra N )
    <->
    E. A e. ( ( P21A3Sphere N ) i^i ( ZZ ^m 3 ) )
      E. B e. ( ( P21A3Sphere N ) i^i ( ZZ ^m 3 ) )
        E. C e. ( ( P21A3Sphere N ) i^i ( ZZ ^m 3 ) )
          E. D e. ( ( P21A3Sphere N ) i^i ( ZZ ^m 3 ) )
            E. s e. RR
              (
                0 < s
                /\
                (
                  ( P21A3Dist A B ) = s
                  /\
                  (
                    ( P21A3Dist A C ) = s
                    /\
                    (
                      ( P21A3Dist A D ) = s
                      /\
                      (
                        ( P21A3Dist B C ) = s
                        /\
                        (
                          ( P21A3Dist B D ) = s
                          /\
                          ( P21A3Dist C D ) = s
                        )
                      )
                    )
                  )
                )
              )
  ) $.
$}

${
  $d N m $.

  putnambench-putnam-2021-a3 $a |- A. N e. NN0
    (
      (
        0 < N
        /\
        ( P21A3Tetra N )
      )
      <->
      E. m e. NN0
        (
          0 < m
          /\
          N = ( 3 x. ( m ^ 2 ) )
        )
    )
  $.
$}
