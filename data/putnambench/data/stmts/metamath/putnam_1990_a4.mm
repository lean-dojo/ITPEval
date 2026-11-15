$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1990_a4: the minimum number of irrational-distance paper punches
  needed to remove every point of the real Euclidean plane is three. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  P90A4R2 is the real coordinate plane and P90A4Dist is its Euclidean
  distance. A punch centered at P removes exactly the points Q for which
  P90A4Dist(P,Q) is not rational.

  The first conjunct gives an internal three-point set of punch centers
  covering the whole plane. The second says that every finite center set
  with the same coverage property has natural cardinality at least three.
  Together these are equivalent to the source least-cardinality statement
  with the annotated solution value 3. All declarations are unproved $a
  statement encodings; this database contains no $p proof statement.
$)

$c P90A4I P90A4R2 P90A4Dist $.

p90a4-index-syntax $a class P90A4I $.
p90a4-plane-syntax $a class P90A4R2 $.
p90a4-distance-syntax $a class ( P90A4Dist A B ) $.

p90a4-index-definition $a |- P90A4I = ( 1 ... 2 ) $.

p90a4-plane-definition $a |- P90A4R2 = ( RR ^m P90A4I ) $.

${
  $d A B k $.

  p90a4-distance-definition $a |- (
    P90A4Dist A B
  ) = (
    sqrt
    `
    (
      sum_ k e. P90A4I
        ( ( ( A ` k ) - ( B ` k ) ) ^ 2 )
    )
  ) $.
$}

${
  $d P Q S n $.

  putnambench-putnam-1990-a4 $a |- (
    E. S
      (
        (
          S C_ P90A4R2
          /\
          ( # ` S ) = 3
        )
        /\
        A. Q e. P90A4R2
          E. P e. S
            ( P90A4Dist P Q ) e/ QQ
      )
    /\
    A. n e. NN0
      A. S
        (
          (
            (
              S C_ P90A4R2
              /\
              ( # ` S ) = n
            )
            /\
            A. Q e. P90A4R2
              E. P e. S
                ( P90A4Dist P Q ) e/ QQ
          )
          ->
          3 <_ n
        )
  ) $.
$}
