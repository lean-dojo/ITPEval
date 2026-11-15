$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2017_b1: two distinct affine lines in the real plane intersect
  exactly when every nonzero real dilation about every point off both lines
  maps some point of the first line to a point of the second. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  P17B1I is the two-coordinate index set and P17B1R2 is the full real plane.
  P17B1Line L says, exactly as in the source definition of its class "lines",
  that L has a base point u and a nonzero direction v and consists of all
  points u + t v for real t. The coordinate disjunction is equivalent to
  v being nonzero because v is a function on {1,2}.

  P17B1Scale P A B r is the coordinatewise equation B - P = r(A - P).
  Hence the final biconditional preserves the arbitrary lines, their
  distinctness, the nonempty-intersection condition, every nonzero real
  scalar, every point off both lines, and the internally existential points
  on the two lines. All assertions are unproved $a statement encodings; this
  database contains no $p proof statement.
$)

$c P17B1I P17B1R2 P17B1Line P17B1Scale $.

p17b1-index-syntax $a class P17B1I $.
p17b1-plane-syntax $a class P17B1R2 $.
p17b1-line-syntax $a wff ( P17B1Line L ) $.
p17b1-scale-syntax $a wff ( P17B1Scale P A B r ) $.

p17b1-index-definition $a |- P17B1I = ( 1 ... 2 ) $.

p17b1-plane-definition $a |- P17B1R2 = ( RR ^m P17B1I ) $.

${
  $d L i p t u v $.

  p17b1-line-definition $a |- (
    ( P17B1Line L )
    <->
    E. u e. P17B1R2 E. v e. P17B1R2
      (
        (
          ( v ` 1 ) =/= 0
          \/
          ( v ` 2 ) =/= 0
        )
        /\
        L = {
          p e. P17B1R2 |
          E. t e. RR
            p =
              (
                i e. P17B1I |->
                  (
                    ( u ` i )
                    +
                    ( t x. ( v ` i ) )
                  )
              )
        }
      )
  ) $.
$}

${
  $d A B P i r $.

  p17b1-scale-definition $a |- (
    ( P17B1Scale P A B r )
    <->
    A. i e. P17B1I
      (
        ( ( B ` i ) - ( P ` i ) )
        =
        (
          r
          x.
          ( ( A ` i ) - ( P ` i ) )
        )
      )
  ) $.
$}

${
  $d A B L M P r $.

  putnambench-putnam-2017-b1 $a |-
    A. L A. M
      (
        (
          (
            ( P17B1Line L )
            /\
            ( P17B1Line M )
          )
          /\
          L =/= M
        )
        ->
        (
          ( L i^i M ) =/= (/)
          <->
          A. r e. RR
            (
              r =/= 0
              ->
              A. P e. P17B1R2
                (
                  (
                    -. P e. L
                    /\
                    -. P e. M
                  )
                  ->
                  E. A e. L E. B e. M
                    ( P17B1Scale P A B r )
                )
            )
        )
      )
  $.
$}
