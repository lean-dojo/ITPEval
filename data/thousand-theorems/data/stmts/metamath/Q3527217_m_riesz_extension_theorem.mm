$(
  Statement-only formalization of Thousand Theorems corpus artifact Q3527217
  (thousand-theorems__metamath__Q3527217), "M. Riesz extension theorem": a
  real-linear functional defined on a subspace, nonnegative on its
  intersection with a pointed convex cone and satisfying the stated
  cofinality condition, extends to a real-linear functional on the whole
  space that is nonnegative on the cone. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q3527217PointedCone V s states that V is a real vector space and s is a
  pointed cone in V: s contains zero and is closed under addition and
  multiplication by every nonnegative real scalar.

  Mathlib's partial linear map f : E ->l.[RR] RR is represented by its domain
  p in LSubSp(V) together with
  f in ((V |`s p) LMHom (ringLMod ` RRfld)). This is the defining data of the
  bundled source object, so universally quantifying p and f preserves the
  source quantification. The dense hypothesis is rendered verbatim as
  every y in V admitting x in p with x + y in s. The extending functional g
  remains internally existentially quantified.

  The final declaration is the single unproved corpus $a statement. The
  preceding $a declarations are syntax and a faithful definition, and this
  database contains no $p proof statement.
$)

$c Q3527217PointedCone $.

q3527217-pointed-cone-syntax
  $a wff ( Q3527217PointedCone V s ) $.

${
  $d V s a x y $.

  q3527217-pointed-cone-definition $a |- (
    ( Q3527217PointedCone V s )
    <->
    (
      V e. LVec
      /\
      ( Scalar ` V ) = RRfld
      /\
      s C_ ( Base ` V )
      /\
      ( 0g ` V ) e. s
      /\
      A. x e. s
        A. y e. s
          ( x ( +g ` V ) y ) e. s
      /\
      A. a e. RR
        (
          0 <_ a
          ->
          A. x e. s
            ( a ( .s ` V ) x ) e. s
        )
    )
  ) $.
$}

${
  $d V f g p s x y $.

  thousand-theorems-q3527217-m-riesz-extension $a |-
    A. V
      A. s
        (
          ( Q3527217PointedCone V s )
          ->
          A. p e. ( LSubSp ` V )
            A. f
              (
                (
                  f e.
                    (
                      ( V |`s p )
                      LMHom
                      ( ringLMod ` RRfld )
                    )
                  /\
                  A. x e. p
                    (
                      x e. s
                      ->
                      0 <_ ( f ` x )
                    )
                  /\
                  A. y e. ( Base ` V )
                    E. x e. p
                      ( x ( +g ` V ) y ) e. s
                )
                ->
                E. g
                  (
                    g e.
                      (
                        V
                        LMHom
                        ( ringLMod ` RRfld )
                      )
                    /\
                    A. x e. p
                      ( g ` x ) = ( f ` x )
                    /\
                    A. x e. s
                      0 <_ ( g ` x )
                  )
              )
        )
  $.
$}
