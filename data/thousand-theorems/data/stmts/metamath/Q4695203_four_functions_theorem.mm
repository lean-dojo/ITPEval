$(
  Statement-only formalization of Thousand Theorems corpus artifact Q4695203
  (thousand-theorems__metamath__Q4695203), "Four functions theorem": the
  Ahlswede-Daykin inequality for four nonnegative functions on an arbitrary
  distributive lattice, valued in an ordered commutative semiring. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  Q4695203Codomain R expands the source assumptions CommSemiring, LinearOrder,
  IsStrictOrderedRing, and ExistsAddOfLE. CSRing supplies the commutative
  semiring. Membership in oMnd supplies the total order and additive
  monotonicity; the next clause is the order-reflection field of
  IsOrderedCancelAddMonoid. The remaining clauses state zero <= one,
  nontriviality, strict monotonicity of multiplication by positive elements
  on both sides, and the existence of an additive difference whenever a <= b.
  Strict inequalities are rendered definitionally as <= together with
  inequality in the bundled partial order.

  Q4695203Infs K S T and Q4695203Sups K S T are respectively the finite-set
  images {a meet b | a in S, b in T} and {a join b | a in S, b in T}.
  SetMM's gsum is the finite commutative-monoid sum. The final declaration is
  the single unproved $a corpus statement; all earlier $a declarations are
  syntax or explicit definitions, and this database contains no $p proof
  statement.
$)

$c Q4695203Codomain Q4695203Infs Q4695203Sups $.

q4695203-codomain-syntax $a wff ( Q4695203Codomain R ) $.
q4695203-infs-syntax $a class ( Q4695203Infs K S T ) $.
q4695203-sups-syntax $a class ( Q4695203Sups K S T ) $.

${
  $d R a b c $.

  q4695203-codomain-definition $a |- (
    ( Q4695203Codomain R )
    <->
    (
      R e. CSRing
      /\
      (
        R e. oMnd
        /\
        (
          A. a e. ( Base ` R ) A. b e. ( Base ` R )
            A. c e. ( Base ` R )
              (
                (
                  ( a ( +g ` R ) b )
                  ( le ` R )
                  ( a ( +g ` R ) c )
                )
                ->
                b ( le ` R ) c
              )
          /\
          (
            ( 0g ` R ) ( le ` R ) ( 1r ` R )
            /\
            (
              E. a e. ( Base ` R ) E. b e. ( Base ` R ) a =/= b
              /\
              (
                A. a e. ( Base ` R ) A. b e. ( Base ` R )
                  A. c e. ( Base ` R )
                    (
                      (
                        (
                          ( ( 0g ` R ) ( le ` R ) a /\ ( 0g ` R ) =/= a )
                          /\
                          ( b ( le ` R ) c /\ b =/= c )
                        )
                        ->
                        (
                          ( a ( .r ` R ) b )
                            ( le ` R )
                          ( a ( .r ` R ) c )
                          /\
                          ( a ( .r ` R ) b ) =/= ( a ( .r ` R ) c )
                        )
                      )
                    )
                /\
                (
                  A. a e. ( Base ` R ) A. b e. ( Base ` R )
                    A. c e. ( Base ` R )
                      (
                        (
                          (
                            ( ( 0g ` R ) ( le ` R ) c /\ ( 0g ` R ) =/= c )
                            /\
                            ( a ( le ` R ) b /\ a =/= b )
                          )
                          ->
                          (
                            ( a ( .r ` R ) c )
                              ( le ` R )
                            ( b ( .r ` R ) c )
                            /\
                            ( a ( .r ` R ) c ) =/= ( b ( .r ` R ) c )
                          )
                        )
                      )
                  /\
                  A. a e. ( Base ` R ) A. b e. ( Base ` R )
                    (
                      a ( le ` R ) b
                      ->
                      E. c e. ( Base ` R )
                        b = ( a ( +g ` R ) c )
                    )
                )
              )
            )
          )
        )
      )
    )
  ) $.
$}

${
  $d K S T a b x $.

  q4695203-infs-definition $a |- ( Q4695203Infs K S T ) =
    {
      x e. ( Base ` K ) |
        E. a e. S E. b e. T
          x = ( a ( meet ` K ) b )
    }
  $.
$}

${
  $d K S T a b x $.

  q4695203-sups-definition $a |- ( Q4695203Sups K S T ) =
    {
      x e. ( Base ` K ) |
        E. a e. S E. b e. T
          x = ( a ( join ` K ) b )
    }
  $.
$}

${
  $d K R F G H I S T a b $.

  thousand-theorems-q4695203-four-functions-theorem $a |-
    A. K A. R
      (
        (
          K e. DLat
          /\
          ( Q4695203Codomain R )
        )
        ->
        A. F e. ( ( Base ` R ) ^m ( Base ` K ) )
          A. G e. ( ( Base ` R ) ^m ( Base ` K ) )
            A. H e. ( ( Base ` R ) ^m ( Base ` K ) )
              A. I e. ( ( Base ` R ) ^m ( Base ` K ) )
                A. S e. Fin A. T e. Fin
                  (
                    (
                      (
                        S C_ ( Base ` K )
                        /\
                        T C_ ( Base ` K )
                      )
                      /\
                      (
                        A. a e. ( Base ` K )
                          (
                            (
                              ( 0g ` R ) ( le ` R ) ( F ` a )
                              /\
                              ( 0g ` R ) ( le ` R ) ( G ` a )
                            )
                            /\
                            (
                              ( 0g ` R ) ( le ` R ) ( H ` a )
                              /\
                              ( 0g ` R ) ( le ` R ) ( I ` a )
                            )
                          )
                        /\
                        A. a e. ( Base ` K ) A. b e. ( Base ` K )
                          (
                            (
                              ( F ` a )
                              ( .r ` R )
                              ( G ` b )
                            )
                            ( le ` R )
                            (
                              ( H ` ( a ( meet ` K ) b ) )
                              ( .r ` R )
                              ( I ` ( a ( join ` K ) b ) )
                            )
                          )
                      )
                    )
                    ->
                    (
                      (
                        R gsum ( a e. S |-> ( F ` a ) )
                      )
                      ( .r ` R )
                      (
                        R gsum ( a e. T |-> ( G ` a ) )
                      )
                    )
                    ( le ` R )
                    (
                      (
                        R gsum
                          (
                            a e. ( Q4695203Infs K S T ) |->
                              ( H ` a )
                          )
                      )
                      ( .r ` R )
                      (
                        R gsum
                          (
                            a e. ( Q4695203Sups K S T ) |->
                              ( I ` a )
                          )
                      )
                    )
                  )
      )
  $.
$}
