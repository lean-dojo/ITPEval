$(
  Statement-only formalization of Thousand Theorems corpus artifact Q3527215
  (thousand-theorems__metamath__Q3527215), "Hilbert projection theorem":
  in an arbitrary real inner-product space, every nonempty complete convex
  subset contains, for each ambient point, a point attaining the infimum of
  the norm distance. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  ` W ` is an arbitrary real pre-Hilbert space; no completeness assumption is
  placed on the ambient space.  For ` K C_ ( Base ` W ) `, membership of the
  induced metric structure ` W |`s K ` in ` CMetSp ` says exactly that ` K `
  is complete in the inherited metric.  The predicate below is the usual
  real convexity condition.
$)

$c Q3527215Convex $.

q3527215-convex-syntax $a
  wff ( Q3527215Convex W K )
$.

${
  $d K W t x y $.

  q3527215-convex-definition $a
    |- (
      ( Q3527215Convex W K )
      <->
      A. x e. K A. y e. K A. t e. ( 0 [,] 1 )
        (
          (
            ( t ( .s ` W ) x )
            ( +g ` W )
            ( ( 1 - t ) ( .s ` W ) y )
          )
          e. K
        )
    )
  $.
$}

$(
  The displayed infimum is taken over the norm distances from ` u ` to all
  points of ` K `.  The minimizing point ` v ` remains an internal
  existential witness, as in the source statement.
$)

${
  $d K W u v w $.

  thousand-theorems-metamath-Q3527215 $a
    |- A. W
      (
        ( W e. CPreHil /\ ( Scalar ` W ) = RRfld )
        ->
        A. K e. ~P ( Base ` W )
          (
            (
              K =/= (/)
              /\
              ( ( W |`s K ) e. CMetSp /\ ( Q3527215Convex W K ) )
            )
            ->
            A. u e. ( Base ` W )
              E. v e. K
                (
                  ( ( norm ` W ) ` ( u ( -g ` W ) v ) )
                  =
                  inf
                    (
                      ran
                        (
                          w e. K |->
                            ( ( norm ` W ) ` ( u ( -g ` W ) w ) )
                        )
                      ,
                      RR
                      ,
                      <
                    )
                )
          )
      )
  $.
$}
