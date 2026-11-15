$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1992_b6: a cardinality bound for a set of real square matrices
  satisfying signed-product closure and commutation conditions. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  For positive n, P92B6Index n is the n-element carrier corresponding to
  Fin n, and P92B6Matrices n is the full set of real n-by-n matrices.
  P92B6Identity n and P92B6Neg n are respectively the identity matrix and
  pointwise additive negation, while P92B6Mul n is SetMM's real matrix
  multiplication on this carrier.

  Negating the biconditional in the second hypothesis says that exactly one
  of AB and (-A)B belongs to M. The remaining hypotheses retain the source
  commute-or-anticommute alternatives and the internal anticommuting witness.
  SetMM's cardinality is infinite on infinite sets, so its finite upper bound
  by n^2 is equivalent to the source extended-cardinality conclusion.
  Every declaration is an unproved $a statement encoding; this database
  contains no $p proof declaration.
$)

$c
  P92B6Index P92B6Matrices P92B6Identity P92B6Neg P92B6Mul
$.

p92b6-index-syntax $a class P92B6Index $.
p92b6-matrices-syntax $a class P92B6Matrices $.
p92b6-identity-syntax $a class P92B6Identity $.
p92b6-neg-syntax $a class P92B6Neg $.
p92b6-mul-syntax $a class P92B6Mul $.

${
  p92b6-index-definition $a |- P92B6Index =
    ( n e. NN |-> ( 0 ..^ n ) )
  $.
$}

${
  p92b6-matrices-definition $a |- P92B6Matrices =
    ( n e. NN |->
      (
        RR
        ^m
        (
          ( P92B6Index ` n )
          X.
          ( P92B6Index ` n )
        )
      )
    )
  $.
$}

${
  $d i j n $.

  p92b6-identity-definition $a |- P92B6Identity =
    ( n e. NN |->
      (
        i e. ( P92B6Index ` n ) ,
        j e. ( P92B6Index ` n ) |->
          if ( i = j , 1 , 0 )
      )
    )
  $.
$}

${
  $d A i j n $.

  p92b6-neg-definition $a |- P92B6Neg =
    ( n e. NN |->
      (
        A e. ( P92B6Matrices ` n ) |->
          (
            i e. ( P92B6Index ` n ) ,
            j e. ( P92B6Index ` n ) |->
              ( -u ( A ` <. i , j >. ) )
          )
      )
    )
  $.
$}

${
  p92b6-mul-definition $a |- P92B6Mul =
    ( n e. NN |->
      (
        RRfld
        maMul
        <.
          ( P92B6Index ` n ) ,
          ( P92B6Index ` n ) ,
          ( P92B6Index ` n )
        >.
      )
    )
  $.
$}

${
  $d A B M n $.

  putnambench-putnam-1992-b6 $a |-
    A. n e. NN
      A. M e. ~P ( P92B6Matrices ` n )
        (
          (
            ( P92B6Identity ` n ) e. M
            /\
            (
              A. A e. M
                A. B e. M
                  -.
                  (
                    (
                      A
                      ( P92B6Mul ` n )
                      B
                    )
                    e. M
                    <->
                    (
                      (
                        ( P92B6Neg ` n )
                        ` A
                      )
                      ( P92B6Mul ` n )
                      B
                    )
                    e. M
                  )
              /\
              (
                A. A e. M
                  A. B e. M
                    (
                      (
                        A
                        ( P92B6Mul ` n )
                        B
                      )
                      =
                      (
                        B
                        ( P92B6Mul ` n )
                        A
                      )
                      \/
                      (
                        A
                        ( P92B6Mul ` n )
                        B
                      )
                      =
                      (
                        (
                          ( P92B6Neg ` n )
                          ` B
                        )
                        ( P92B6Mul ` n )
                        A
                      )
                    )
                /\
                A. A e. M
                  (
                    A =/= ( P92B6Identity ` n )
                    ->
                    E. B e. M
                      (
                        A
                        ( P92B6Mul ` n )
                        B
                      )
                      =
                      (
                        (
                          ( P92B6Neg ` n )
                          ` B
                        )
                        ( P92B6Mul ` n )
                        A
                      )
                  )
              )
            )
          )
          ->
          ( # ` M ) <_ ( n ^ 2 )
        )
  $.
$}
