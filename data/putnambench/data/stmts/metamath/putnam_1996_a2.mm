$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1996_a2: the midpoint locus determined by circles of radii 1 and 3
  whose centers are 10 units apart is the closed annulus of radii 1 and 2
  centered at the midpoint of the circle centers. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P96A2I is the two-coordinate index set, P96A2R2 is the full real
  Euclidean plane, P96A2Dist is coordinate Euclidean distance, and P96A2Mid
  is coordinatewise midpoint.

  Circle membership and the source solution set are inlined definitionally
  in the final assertion. Both centers remain universally quantified over
  the real plane, and the points on the two circles remain internal
  existential witnesses. The final declaration is the single unproved $a
  corpus statement; this database contains no $p proof statement.
$)

$c P96A2I P96A2R2 P96A2Dist P96A2Mid $.

p96a2-index-syntax $a class P96A2I $.
p96a2-plane-syntax $a class P96A2R2 $.
p96a2-distance-syntax $a class ( P96A2Dist A B ) $.
p96a2-midpoint-syntax $a class ( P96A2Mid A B ) $.

p96a2-index-definition $a |- P96A2I = ( 1 ... 2 ) $.

p96a2-plane-definition $a |- P96A2R2 = ( RR ^m P96A2I ) $.

${
  $d A B j $.

  p96a2-distance-definition $a |- (
    P96A2Dist A B
  ) = (
    sqrt
    `
    (
      sum_ j e. P96A2I
        ( ( ( A ` j ) - ( B ` j ) ) ^ 2 )
    )
  ) $.

  p96a2-midpoint-definition $a |- (
    P96A2Mid A B
  ) = (
    j e. P96A2I |->
      (
        ( ( A ` j ) + ( B ` j ) )
        /
        2
      )
  ) $.
$}

${
  $d M O P X Y $.

  putnambench-putnam-1996-a2 $a |-
    A. O e. P96A2R2
    A. P e. P96A2R2
      (
        ( P96A2Dist O P ) = ; 1 0
        ->
        {
          M e. P96A2R2 |
          E. X e. P96A2R2 E. Y e. P96A2R2
            (
              (
                ( P96A2Dist X O ) = 1
                /\
                ( P96A2Dist Y P ) = 3
              )
              /\
              M = ( P96A2Mid X Y )
            )
        }
        =
        {
          M e. P96A2R2 |
          (
            1 <_ ( P96A2Dist M ( P96A2Mid O P ) )
            /\
            ( P96A2Dist M ( P96A2Mid O P ) ) <_ 2
          )
        }
      )
  $.
$}
