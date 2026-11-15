$(
  Statement-only formalization of Thousand Theorems corpus artifact Q476776
  (thousand-theorems__metamath__Q476776), "Solutions of a general quartic
  equation": characterization of the four roots of a quartic over an
  arbitrary field in which 2 is invertible, using a root of its cubic
  resolvent and specified square roots. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  K ranges over bundled SetMM fields and all lowercase variables range over
  Base ` K. Q476776Nat is the natural-number cast N |-> N * 1 in K;
  Q476776Pow is natural power in the multiplicative monoid of K. The
  remaining abbreviations are exactly the field operations.

  Nonvanishing of Q476776Nat K 2 is equivalent, in a field, to the source
  assumption Invertible (2 : K). The hypotheses retain the definitions of
  p, q, and r, nonvanishing of a and q, the cubic resolvent equation for u,
  and the three square-root equations for s, v, and w. The final $a
  declaration is the single unproved corpus statement; there is no $p proof
  statement.
$)

$c Q476776Add Q476776Mul Q476776Neg Q476776Sub Q476776Div $.
$c Q476776Nat Q476776Pow $.

q476776-add-syntax $a class ( Q476776Add K X Y ) $.
q476776-mul-syntax $a class ( Q476776Mul K X Y ) $.
q476776-neg-syntax $a class ( Q476776Neg K X ) $.
q476776-sub-syntax $a class ( Q476776Sub K X Y ) $.
q476776-div-syntax $a class ( Q476776Div K X Y ) $.
q476776-nat-syntax $a class ( Q476776Nat K N ) $.
q476776-pow-syntax $a class ( Q476776Pow K X N ) $.

q476776-add-definition $a |- ( Q476776Add K X Y ) =
  ( X ( +g ` K ) Y ) $.

q476776-mul-definition $a |- ( Q476776Mul K X Y ) =
  ( X ( .r ` K ) Y ) $.

q476776-neg-definition $a |- ( Q476776Neg K X ) =
  ( ( -g ` K ) ` X ) $.

q476776-sub-definition $a |- ( Q476776Sub K X Y ) =
  ( Q476776Add K X ( Q476776Neg K Y ) ) $.

q476776-div-definition $a |- ( Q476776Div K X Y ) =
  ( X ( /r ` K ) Y ) $.

q476776-nat-definition $a |- ( Q476776Nat K N ) =
  ( N ( .g ` K ) ( 1r ` K ) ) $.

q476776-pow-definition $a |- ( Q476776Pow K X N ) =
  ( N ( .g ` ( mulGrp ` K ) ) X ) $.

${
  $d K a b c d e p q r s u v w x $.

  thousand-theorems-q476776-quartic-eq-zero-iff $a |-
    A. K e. Field
      A. a e. ( Base ` K )
        A. b e. ( Base ` K )
          A. c e. ( Base ` K )
            A. d e. ( Base ` K )
              A. e e. ( Base ` K )
                A. p e. ( Base ` K )
                  A. q e. ( Base ` K )
                    A. r e. ( Base ` K )
                      A. s e. ( Base ` K )
                        A. u e. ( Base ` K )
                          A. v e. ( Base ` K )
                            A. w e. ( Base ` K )
                              A. x e. ( Base ` K )
                                (
                                  (
                                    ( Q476776Nat K 2 ) =/= ( 0g ` K )
                                    /\
                                    a =/= ( 0g ` K )
                                    /\
                                    p =
                                    (
                                      Q476776Div K
                                      (
                                        Q476776Sub K
                                        (
                                          Q476776Mul K
                                          (
                                            Q476776Mul K
                                            ( Q476776Nat K 8 )
                                            a
                                          )
                                          c
                                        )
                                        (
                                          Q476776Mul K
                                          ( Q476776Nat K 3 )
                                          ( Q476776Pow K b 2 )
                                        )
                                      )
                                      (
                                        Q476776Mul K
                                        ( Q476776Nat K 8 )
                                        ( Q476776Pow K a 2 )
                                      )
                                    )
                                    /\
                                    q =
                                    (
                                      Q476776Div K
                                      (
                                        Q476776Add K
                                        (
                                          Q476776Sub K
                                          ( Q476776Pow K b 3 )
                                          (
                                            Q476776Mul K
                                            (
                                              Q476776Mul K
                                              (
                                                Q476776Mul K
                                                ( Q476776Nat K 4 )
                                                a
                                              )
                                              b
                                            )
                                            c
                                          )
                                        )
                                        (
                                          Q476776Mul K
                                          (
                                            Q476776Mul K
                                            ( Q476776Nat K 8 )
                                            ( Q476776Pow K a 2 )
                                          )
                                          d
                                        )
                                      )
                                      (
                                        Q476776Mul K
                                        ( Q476776Nat K 8 )
                                        ( Q476776Pow K a 3 )
                                      )
                                    )
                                    /\
                                    q =/= ( 0g ` K )
                                    /\
                                    r =
                                    (
                                      Q476776Div K
                                      (
                                        Q476776Sub K
                                        (
                                          Q476776Sub K
                                          (
                                            Q476776Add K
                                            (
                                              Q476776Mul K
                                              (
                                                Q476776Mul K
                                                (
                                                  Q476776Mul K
                                                  (
                                                    Q476776Pow K
                                                    ( Q476776Nat K 2 )
                                                    4
                                                  )
                                                  a
                                                )
                                                ( Q476776Pow K b 2 )
                                              )
                                              c
                                            )
                                            (
                                              Q476776Mul K
                                              (
                                                Q476776Mul K
                                                (
                                                  Q476776Pow K
                                                  ( Q476776Nat K 2 )
                                                  8
                                                )
                                                ( Q476776Pow K a 3 )
                                              )
                                              e
                                            )
                                          )
                                          (
                                            Q476776Mul K
                                            ( Q476776Nat K 3 )
                                            ( Q476776Pow K b 4 )
                                          )
                                        )
                                        (
                                          Q476776Mul K
                                          (
                                            Q476776Mul K
                                            (
                                              Q476776Mul K
                                              (
                                                Q476776Pow K
                                                ( Q476776Nat K 2 )
                                                6
                                              )
                                              ( Q476776Pow K a 2 )
                                            )
                                            b
                                          )
                                          d
                                        )
                                      )
                                      (
                                        Q476776Mul K
                                        (
                                          Q476776Pow K
                                          ( Q476776Nat K 2 )
                                          8
                                        )
                                        ( Q476776Pow K a 4 )
                                      )
                                    )
                                    /\
                                    (
                                      Q476776Sub K
                                      (
                                        Q476776Add K
                                        (
                                          Q476776Sub K
                                          (
                                            Q476776Sub K
                                            ( Q476776Pow K u 3 )
                                            (
                                              Q476776Mul K p
                                              ( Q476776Pow K u 2 )
                                            )
                                          )
                                          (
                                            Q476776Mul K
                                            (
                                              Q476776Mul K
                                              ( Q476776Nat K 4 )
                                              r
                                            )
                                            u
                                          )
                                        )
                                        (
                                          Q476776Mul K
                                          (
                                            Q476776Mul K
                                            ( Q476776Nat K 4 )
                                            p
                                          )
                                          r
                                        )
                                      )
                                      ( Q476776Pow K q 2 )
                                    )
                                    =
                                    ( 0g ` K )
                                    /\
                                    ( Q476776Pow K s 2 ) =
                                    ( Q476776Sub K u p )
                                    /\
                                    ( Q476776Pow K v 2 ) =
                                    (
                                      Q476776Sub K
                                      (
                                        Q476776Mul K
                                        ( Q476776Nat K 4 )
                                        ( Q476776Pow K s 2 )
                                      )
                                      (
                                        Q476776Mul K
                                        ( Q476776Nat K 8 )
                                        (
                                          Q476776Sub K
                                          u
                                          ( Q476776Div K q s )
                                        )
                                      )
                                    )
                                    /\
                                    ( Q476776Pow K w 2 ) =
                                    (
                                      Q476776Sub K
                                      (
                                        Q476776Mul K
                                        ( Q476776Nat K 4 )
                                        ( Q476776Pow K s 2 )
                                      )
                                      (
                                        Q476776Mul K
                                        ( Q476776Nat K 8 )
                                        (
                                          Q476776Add K
                                          u
                                          ( Q476776Div K q s )
                                        )
                                      )
                                    )
                                  )
                                  ->
                                  (
                                    (
                                      Q476776Add K
                                      (
                                        Q476776Add K
                                        (
                                          Q476776Add K
                                          (
                                            Q476776Add K
                                            (
                                              Q476776Mul K a
                                              ( Q476776Pow K x 4 )
                                            )
                                            (
                                              Q476776Mul K b
                                              ( Q476776Pow K x 3 )
                                            )
                                          )
                                          (
                                            Q476776Mul K c
                                            ( Q476776Pow K x 2 )
                                          )
                                        )
                                        ( Q476776Mul K d x )
                                      )
                                      e
                                    )
                                    =
                                    ( 0g ` K )
                                    <->
                                    (
                                      x =
                                      (
                                        Q476776Sub K
                                        (
                                          Q476776Div K
                                          (
                                            Q476776Sub K
                                            (
                                              Q476776Mul K
                                              ( Q476776Neg K
                                                ( Q476776Nat K 2 ) )
                                              s
                                            )
                                            v
                                          )
                                          ( Q476776Nat K 4 )
                                        )
                                        (
                                          Q476776Div K
                                          b
                                          (
                                            Q476776Mul K
                                            ( Q476776Nat K 4 )
                                            a
                                          )
                                        )
                                      )
                                      \/
                                      x =
                                      (
                                        Q476776Sub K
                                        (
                                          Q476776Div K
                                          (
                                            Q476776Add K
                                            (
                                              Q476776Mul K
                                              ( Q476776Neg K
                                                ( Q476776Nat K 2 ) )
                                              s
                                            )
                                            v
                                          )
                                          ( Q476776Nat K 4 )
                                        )
                                        (
                                          Q476776Div K
                                          b
                                          (
                                            Q476776Mul K
                                            ( Q476776Nat K 4 )
                                            a
                                          )
                                        )
                                      )
                                      \/
                                      x =
                                      (
                                        Q476776Sub K
                                        (
                                          Q476776Div K
                                          (
                                            Q476776Sub K
                                            (
                                              Q476776Mul K
                                              ( Q476776Nat K 2 )
                                              s
                                            )
                                            w
                                          )
                                          ( Q476776Nat K 4 )
                                        )
                                        (
                                          Q476776Div K
                                          b
                                          (
                                            Q476776Mul K
                                            ( Q476776Nat K 4 )
                                            a
                                          )
                                        )
                                      )
                                      \/
                                      x =
                                      (
                                        Q476776Sub K
                                        (
                                          Q476776Div K
                                          (
                                            Q476776Add K
                                            (
                                              Q476776Mul K
                                              ( Q476776Nat K 2 )
                                              s
                                            )
                                            w
                                          )
                                          ( Q476776Nat K 4 )
                                        )
                                        (
                                          Q476776Div K
                                          b
                                          (
                                            Q476776Mul K
                                            ( Q476776Nat K 4 )
                                            a
                                          )
                                        )
                                      )
                                    )
                                  )
                                )
  $.
$}
