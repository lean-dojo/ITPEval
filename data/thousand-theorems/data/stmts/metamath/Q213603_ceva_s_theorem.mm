$(
  Statement-only formalization of Thousand Theorems corpus artifact Q213603
  (thousand-theorems__metamath__Q213603), "Ceva's theorem": over an arbitrary
  normed field, three concurrent cevians of an affine-independent triangle
  satisfy the product-of-distance-ratios form of Ceva's theorem. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  K ranges over bundled SetMM normed fields and W over arbitrary normed vector
  spaces with scalar field K. Choosing any affine origin identifies the
  source's normed affine torsor with Base ` W while preserving affine lines
  and distances. Conversely, Base ` W is itself such a torsor. Although the
  source initially gives W a seminorm, its metric torsor structure makes that
  seminorm definite, so this presentation does not strengthen the domain.

  Q213603Line K W A B X says that X is an arbitrary K-affine combination of
  A and B. Q213603Dist W A B is the norm of B minus A.
  Q213603Noncol K W A B C says that A, B, C are affine-independent: A and B
  are distinct and C is not on their affine line. Thus A, B, C present exactly
  the source object Affine.Triangle K P.

  X, Y, and Z are the source function p at indices 0, 1, and 2, respectively,
  and P is p'. The three inequalities are precisely the nonzero-denominator
  assumptions. The final $a declaration is the single unproved corpus
  statement; all preceding $a declarations are syntax or faithful
  definitions, and this file adds no $p proof statement.
$)

$c Q213603Line Q213603Dist Q213603Noncol $.

q213603-line-syntax $a wff ( Q213603Line K W A B X ) $.
q213603-distance-syntax $a class ( Q213603Dist W A B ) $.
q213603-noncollinear-syntax
  $a wff ( Q213603Noncol K W A B C ) $.

${
  $d A B K W X x $.

  q213603-line-definition $a |- (
    ( Q213603Line K W A B X )
    <->
    E. x e. ( Base ` K )
      X
      =
      (
        ( x ( .s ` W ) A )
        ( +g ` W )
        (
          (
            ( 1r ` K )
            ( +g ` K )
            ( ( -g ` K ) ` x )
          )
          ( .s ` W )
          B
        )
      )
  ) $.
$}

q213603-distance-definition $a |- (
  Q213603Dist W A B
) = (
  ( norm ` W )
  `
  (
    B
    ( +g ` W )
    ( ( -g ` W ) ` A )
  )
) $.

q213603-noncollinear-definition $a |- (
  ( Q213603Noncol K W A B C )
  <->
  (
    A =/= B
    /\
    -. ( Q213603Line K W A B C )
  )
) $.

${
  $d A B C K P W X Y Z $.

  thousand-theorems-q213603-ceva-s-theorem $a |-
    A. K e. ( NrmRing i^i Field )
      A. W e. { w e. NrmVec | ( Scalar ` w ) = K }
        A. A e. ( Base ` W )
          A. B e. ( Base ` W )
            A. C e. ( Base ` W )
              A. X e. ( Base ` W )
                A. Y e. ( Base ` W )
                  A. Z e. ( Base ` W )
                    A. P e. ( Base ` W )
                      (
                        (
                          ( Q213603Noncol K W A B C )
                          /\
                          X =/= C
                          /\
                          Y =/= A
                          /\
                          Z =/= B
                          /\
                          ( Q213603Line K W B C X )
                          /\
                          ( Q213603Line K W C A Y )
                          /\
                          ( Q213603Line K W A B Z )
                          /\
                          ( Q213603Line K W A X P )
                          /\
                          ( Q213603Line K W B Y P )
                          /\
                          ( Q213603Line K W C Z P )
                        )
                        ->
                        (
                          (
                            (
                              ( Q213603Dist W B X )
                              /
                              ( Q213603Dist W X C )
                            )
                            x.
                            (
                              ( Q213603Dist W C Y )
                              /
                              ( Q213603Dist W Y A )
                            )
                          )
                          x.
                          (
                            ( Q213603Dist W A Z )
                            /
                            ( Q213603Dist W Z B )
                          )
                        )
                        =
                        1
                      )
  $.
$}
