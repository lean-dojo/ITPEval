$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2013_a5: area-definite real coefficients for triangles in the
  Euclidean plane remain area definite in Euclidean three-space. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  P13A5R2 and P13A5R3 are the full real coordinate spaces indexed by
  1 ... 2 and 1 ... 3. P13A5Area2 is the absolute determinant divided by
  two. P13A5Cross is the cross product of B - A and C - A, and P13A5Area3
  is half its Euclidean norm. These are exactly the planar Lebesgue area and
  the two-dimensional Hausdorff measure, respectively, of the convex hull
  of the three points.

  For each m in NN0, 0 ..^ m is Fin m. The coefficient map ranges over all
  real-valued functions on its full triple product; the ordered-triple
  representation is canonically equivalent to the source's curried map.
  The two point maps range over every configuration in the corresponding
  Euclidean space. The three finite sums use the source condition i < j < k,
  so values of the coefficient map on other triples are immaterial exactly
  as in the source.

  Thus the final implication directly expands the source predicates
  areadef2 and areadef3, without externalizing any witness or restricting
  any arbitrary function. The final declaration is the single unproved $a
  corpus statement; this database contains no $p proof declaration.
$)

$c P13A5I2 P13A5I3 P13A5R2 P13A5R3 $.
$c P13A5Cross P13A5Area2 P13A5Area3 $.

p13a5-index2-syntax $a class P13A5I2 $.
p13a5-index3-syntax $a class P13A5I3 $.
p13a5-plane-syntax $a class P13A5R2 $.
p13a5-space-syntax $a class P13A5R3 $.
p13a5-cross-syntax $a class ( P13A5Cross A B C ) $.
p13a5-area2-syntax $a class ( P13A5Area2 A B C ) $.
p13a5-area3-syntax $a class ( P13A5Area3 A B C ) $.

p13a5-index2-definition $a |- P13A5I2 = ( 1 ... 2 ) $.
p13a5-index3-definition $a |- P13A5I3 = ( 1 ... 3 ) $.
p13a5-plane-definition $a |- P13A5R2 = ( RR ^m P13A5I2 ) $.
p13a5-space-definition $a |- P13A5R3 = ( RR ^m P13A5I3 ) $.

p13a5-area2-definition $a |- (
  P13A5Area2 A B C
) = (
  ( 1 / 2 )
  x.
  (
    abs
    `
    (
      (
        ( ( B ` 1 ) - ( A ` 1 ) )
        x.
        ( ( C ` 2 ) - ( A ` 2 ) )
      )
      -
      (
        ( ( B ` 2 ) - ( A ` 2 ) )
        x.
        ( ( C ` 1 ) - ( A ` 1 ) )
      )
    )
  )
) $.

${
  $d A B C r $.

  p13a5-cross-definition $a |- (
    P13A5Cross A B C
  ) = (
    r e. P13A5I3 |->
      if (
        r = 1 ,
        (
          (
            ( ( B ` 2 ) - ( A ` 2 ) )
            x.
            ( ( C ` 3 ) - ( A ` 3 ) )
          )
          -
          (
            ( ( B ` 3 ) - ( A ` 3 ) )
            x.
            ( ( C ` 2 ) - ( A ` 2 ) )
          )
        ) ,
        if (
          r = 2 ,
          (
            (
              ( ( B ` 3 ) - ( A ` 3 ) )
              x.
              ( ( C ` 1 ) - ( A ` 1 ) )
            )
            -
            (
              ( ( B ` 1 ) - ( A ` 1 ) )
              x.
              ( ( C ` 3 ) - ( A ` 3 ) )
            )
          ) ,
          (
            (
              ( ( B ` 1 ) - ( A ` 1 ) )
              x.
              ( ( C ` 2 ) - ( A ` 2 ) )
            )
            -
            (
              ( ( B ` 2 ) - ( A ` 2 ) )
              x.
              ( ( C ` 1 ) - ( A ` 1 ) )
            )
          )
        )
      )
  ) $.
$}

${
  $d A B C r $.

  p13a5-area3-definition $a |- (
    P13A5Area3 A B C
  ) = (
    ( 1 / 2 )
    x.
    (
      sqrt
      `
      (
        sum_ r e. P13A5I3
          ( ( ( P13A5Cross A B C ) ` r ) ^ 2 )
      )
    )
  ) $.
$}

${
  $d P Q a i j k m $.

  putnambench-putnam-2013-a5 $a |- A. m e. NN0
    (
      3 <_ m
      ->
      A. a e.
        (
          RR
          ^m
          (
            ( ( 0 ..^ m ) X. ( 0 ..^ m ) )
            X.
            ( 0 ..^ m )
          )
        )
        (
          A. P e. ( P13A5R2 ^m ( 0 ..^ m ) )
            0
            <_
            (
              sum_ i e. ( 0 ..^ m )
                sum_ j e. ( 0 ..^ m )
                  sum_ k e. ( 0 ..^ m )
                    if (
                      (
                        i < j
                        /\
                        j < k
                      ) ,
                      (
                        ( a ` <. i , j , k >. )
                        x.
                        (
                          P13A5Area2
                          ( P ` i )
                          ( P ` j )
                          ( P ` k )
                        )
                      ) ,
                      0
                    )
            )
          ->
          A. Q e. ( P13A5R3 ^m ( 0 ..^ m ) )
            0
            <_
            (
              sum_ i e. ( 0 ..^ m )
                sum_ j e. ( 0 ..^ m )
                  sum_ k e. ( 0 ..^ m )
                    if (
                      (
                        i < j
                        /\
                        j < k
                      ) ,
                      (
                        ( a ` <. i , j , k >. )
                        x.
                        (
                          P13A5Area3
                          ( Q ` i )
                          ( Q ` j )
                          ( Q ` k )
                        )
                      ) ,
                      0
                    )
            )
        )
    )
  $.
$}
