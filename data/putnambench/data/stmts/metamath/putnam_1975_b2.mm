$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1975_b2: a countable family of open slabs in real three-space
  whose positive thicknesses have convergent partial sums cannot cover the
  whole space. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P75B2R3 is real coordinate three-space indexed by 1 ... 3, P75B2Dot is
  its standard inner product, and P75B2Norm is the Euclidean norm.
  P75B2Slab A b d is the open slab of points x satisfying
  b < A dot x < b + d.

  N, O, and D range over arbitrary natural-indexed sequences of normals,
  offsets, and thicknesses. The existential real L together with set.mm's
  real-sequence convergence relation states convergence of the thickness
  partial sums over 0 ..^ n, exactly the source Finset.range n sums.
  Inlining the source's definitionally fixed slab function leaves an
  equivalent statement. The final declaration is the single unproved $a
  corpus statement; this database contains no $p proof statement.
$)

$c P75B2R3 P75B2Dot P75B2Norm P75B2Slab $.

p75b2-space-syntax $a class P75B2R3 $.
p75b2-dot-syntax $a class ( P75B2Dot A B ) $.
p75b2-norm-syntax $a class ( P75B2Norm A ) $.
p75b2-slab-syntax $a class ( P75B2Slab A B C ) $.

p75b2-space-definition $a |- P75B2R3 = ( RR ^m ( 1 ... 3 ) ) $.

${
  $d A B j $.

  p75b2-dot-definition $a |- (
    P75B2Dot A B
  ) = (
    sum_ j e. ( 1 ... 3 )
      ( ( A ` j ) x. ( B ` j ) )
  ) $.
$}

${
  $d A j $.

  p75b2-norm-definition $a |- (
    P75B2Norm A
  ) = (
    sqrt
    `
    (
      sum_ j e. ( 1 ... 3 )
        ( ( A ` j ) ^ 2 )
    )
  ) $.
$}

${
  $d A b d x $.

  p75b2-slab-definition $a |- (
    P75B2Slab A b d
  ) = {
    x e. P75B2R3 |
      (
        b < ( P75B2Dot A x )
        /\
        ( P75B2Dot A x ) < ( b + d )
      )
  } $.
$}

${
  $d D L N O i j n $.

  putnambench-putnam-1975-b2 $a |-
    A. N e. ( P75B2R3 ^m NN0 )
    A. O e. ( RR ^m NN0 )
    A. D e. ( RR ^m NN0 )
      (
        (
          A. i e. NN0
            ( P75B2Norm ( N ` i ) ) = 1
          /\
          (
            A. i e. NN0 0 < ( D ` i )
            /\
            E. L e. RR
              (
                n e. NN0 |->
                  sum_ j e. ( 0 ..^ n )
                    ( D ` j )
              )
              ~~>
              L
          )
        )
        ->
        P75B2R3 =/=
          U_ i e. NN0
            ( P75B2Slab ( N ` i ) ( O ` i ) ( D ` i ) )
      )
  $.
$}
