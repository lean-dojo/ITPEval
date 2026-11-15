$(
  Statement-only formalization of Thousand Theorems corpus artifact Q203565
  (thousand-theorems__metamath__Q203565), "Solutions of a general cubic
  equation": Cardano's characterization of the three roots of a cubic over an
  arbitrary field in which 2 and 3 are invertible. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  K ranges over bundled SetMM fields and all lowercase variables range over
  Base ` K. Q203565Nat is the natural-number cast N |-> N * 1 in K;
  Q203565Pow is the natural power in the multiplicative monoid of K. The
  remaining abbreviations are exactly the field operations.

  Nonvanishing of Q203565Nat K 2 and Q203565Nat K 3 is equivalent to the
  source assumptions Invertible (2 : K) and Invertible (3 : K). For a cube
  root of unity in a field, w ^ 3 = 1 together with w =/= 1 is equivalent to
  IsPrimitiveRoot w 3. The final $a declaration is the single unproved corpus
  statement; there is no $p proof statement.
$)

$c Q203565Add Q203565Mul Q203565Neg Q203565Sub Q203565Div $.
$c Q203565Nat Q203565Pow $.

q203565-add-syntax $a class ( Q203565Add K X Y ) $.
q203565-mul-syntax $a class ( Q203565Mul K X Y ) $.
q203565-neg-syntax $a class ( Q203565Neg K X ) $.
q203565-sub-syntax $a class ( Q203565Sub K X Y ) $.
q203565-div-syntax $a class ( Q203565Div K X Y ) $.
q203565-nat-syntax $a class ( Q203565Nat K N ) $.
q203565-pow-syntax $a class ( Q203565Pow K X N ) $.

q203565-add-definition $a |- ( Q203565Add K X Y ) =
  ( X ( +g ` K ) Y ) $.

q203565-mul-definition $a |- ( Q203565Mul K X Y ) =
  ( X ( .r ` K ) Y ) $.

q203565-neg-definition $a |- ( Q203565Neg K X ) =
  ( ( invg ` K ) ` X ) $.

q203565-sub-definition $a |- ( Q203565Sub K X Y ) =
  ( Q203565Add K X ( Q203565Neg K Y ) ) $.

q203565-div-definition $a |- ( Q203565Div K X Y ) =
  ( X ( /r ` K ) Y ) $.

q203565-nat-definition $a |- ( Q203565Nat K N ) =
  ( N ( .g ` K ) ( 1r ` K ) ) $.

q203565-pow-definition $a |- ( Q203565Pow K X N ) =
  ( N ( .g ` ( mulGrp ` K ) ) X ) $.

${
  $d K a b c d p q r s t w x $.

  thousand-theorems-q203565-cubic-eq-zero-iff $a |-
    A. K e. Field
      A. a e. ( Base ` K )
        A. b e. ( Base ` K )
          A. c e. ( Base ` K )
            A. d e. ( Base ` K )
              A. p e. ( Base ` K )
                A. q e. ( Base ` K )
                  A. r e. ( Base ` K )
                    A. s e. ( Base ` K )
                      A. t e. ( Base ` K )
                        A. w e. ( Base ` K )
                          A. x e. ( Base ` K )
                            (
                              (
                                ( Q203565Nat K 2 ) =/= ( 0g ` K )
                                /\
                                ( Q203565Nat K 3 ) =/= ( 0g ` K )
                                /\
                                a =/= ( 0g ` K )
                                /\
                                (
                                  ( Q203565Pow K w 3 ) = ( 1r ` K )
                                  /\
                                  w =/= ( 1r ` K )
                                )
                                /\
                                p =
                                (
                                  Q203565Div K
                                  (
                                    Q203565Sub K
                                    (
                                      Q203565Mul K
                                      ( Q203565Mul K
                                        ( Q203565Nat K 3 ) a )
                                      c
                                    )
                                    ( Q203565Pow K b 2 )
                                  )
                                  (
                                    Q203565Mul K
                                    ( Q203565Nat K 9 )
                                    ( Q203565Pow K a 2 )
                                  )
                                )
                                /\
                                p =/= ( 0g ` K )
                                /\
                                q =
                                (
                                  Q203565Div K
                                  (
                                    Q203565Sub K
                                    (
                                      Q203565Sub K
                                      (
                                        Q203565Mul K
                                        (
                                          Q203565Mul K
                                          (
                                            Q203565Mul K
                                            ( Q203565Nat K 9 )
                                            a
                                          )
                                          b
                                        )
                                        c
                                      )
                                      (
                                        Q203565Mul K
                                        ( Q203565Nat K 2 )
                                        ( Q203565Pow K b 3 )
                                      )
                                    )
                                    (
                                      Q203565Mul K
                                      (
                                        Q203565Mul K
                                        (
                                          Q203565Pow K
                                          ( Q203565Nat K 3 )
                                          3
                                        )
                                        ( Q203565Pow K a 2 )
                                      )
                                      d
                                    )
                                  )
                                  (
                                    Q203565Mul K
                                    (
                                      Q203565Mul K
                                      ( Q203565Nat K 2 )
                                      (
                                        Q203565Pow K
                                        ( Q203565Nat K 3 )
                                        3
                                      )
                                    )
                                    ( Q203565Pow K a 3 )
                                  )
                                )
                                /\
                                ( Q203565Pow K r 2 ) =
                                (
                                  Q203565Add K
                                  ( Q203565Pow K q 2 )
                                  ( Q203565Pow K p 3 )
                                )
                                /\
                                ( Q203565Pow K s 3 ) =
                                ( Q203565Add K q r )
                                /\
                                ( Q203565Mul K t s ) = p
                              )
                              ->
                              (
                                (
                                  Q203565Add K
                                  (
                                    Q203565Add K
                                    (
                                      Q203565Add K
                                      (
                                        Q203565Mul K a
                                        ( Q203565Pow K x 3 )
                                      )
                                      (
                                        Q203565Mul K b
                                        ( Q203565Pow K x 2 )
                                      )
                                    )
                                    ( Q203565Mul K c x )
                                  )
                                  d
                                )
                                =
                                ( 0g ` K )
                                <->
                                (
                                  x =
                                  (
                                    Q203565Sub K
                                    ( Q203565Sub K s t )
                                    (
                                      Q203565Div K b
                                      (
                                        Q203565Mul K
                                        ( Q203565Nat K 3 )
                                        a
                                      )
                                    )
                                  )
                                  \/
                                  x =
                                  (
                                    Q203565Sub K
                                    (
                                      Q203565Sub K
                                      ( Q203565Mul K s w )
                                      (
                                        Q203565Mul K t
                                        ( Q203565Pow K w 2 )
                                      )
                                    )
                                    (
                                      Q203565Div K b
                                      (
                                        Q203565Mul K
                                        ( Q203565Nat K 3 )
                                        a
                                      )
                                    )
                                  )
                                  \/
                                  x =
                                  (
                                    Q203565Sub K
                                    (
                                      Q203565Sub K
                                      (
                                        Q203565Mul K s
                                        ( Q203565Pow K w 2 )
                                      )
                                      ( Q203565Mul K t w )
                                    )
                                    (
                                      Q203565Div K b
                                      (
                                        Q203565Mul K
                                        ( Q203565Nat K 3 )
                                        a
                                      )
                                    )
                                  )
                                )
                              )
                            )
  $.
$}
