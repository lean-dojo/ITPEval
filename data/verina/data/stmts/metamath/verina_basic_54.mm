$(
  Statement-only formalization of the VERINA corpus artifact
  verina_basic_54 (verina__metamath__verina_basic_54), catalog title
  CanyonSearch: the exact recursive two-pointer search of two nonempty
  nondecreasing integer arrays returns their attained minimum pairwise
  absolute difference. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number length, w ` i is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete index set.

  VERINAB54ToList is Array.toList, extensionally the identity on this finite
  word representation. VERINAB54GetBang reproduces Lean Array.get! on integer
  arrays, including its inhabited default value zero outside the array.
  VERINAB54NatAbs is Lean Int.natAbs on integers, VERINAB54NatMin is natural
  minimum, and VERINAB54NatSub is truncated natural subtraction.
  VERINAB54PairwiseLE is exactly List.Pairwise (fun x y => x <= y), expressed
  over every earlier/later index pair. VERINAB54Pre preserves the two
  nonemptiness and two nondecreasing-order assumptions.

  VERINAB54AuxGraph is the exact deterministic operational graph of
  canyonSearchAux for every pair of typed arrays and every natural m, n, and
  d. Its trace length uses the source termination measure
  (a.size + b.size - m) - n. Each active transition computes the same
  absolute difference and minimum update, then increments m exactly when
  a[m]! <= b[n]! and increments n otherwise. Once either index is out of
  bounds the trace is absorbing, which has the same returned d as the source
  base case. An active transition strictly decreases the source measure, so
  the final trace value is exactly the recursive helper result.
  VERINAB54Aux selects that unique result.

  VERINAB54CanyonSearch preserves the source initial comparison and invokes
  the helper at m = n = 0. VERINAB54Post is the conjunction of the nested
  Array.any assertion that the result is attained by some pair and the nested
  Array.all assertion that it is no greater than every pairwise absolute
  difference. The proof-valued precondition arguments to the implementation
  and postcondition are computationally and propositionally unused beyond the
  explicit precondition antecedent in the final correctness assertion. Every
  earlier $a is syntax or a faithful definition required by this rendering,
  and this database has no $p declaration.
$)

$c
  VERINAB54NatSub VERINAB54NatAbs VERINAB54NatMin
  VERINAB54ToList VERINAB54GetBang
  VERINAB54PairwiseLE VERINAB54Pre
  VERINAB54AuxGraph VERINAB54Aux
  VERINAB54CanyonSearch VERINAB54Post
$.

verinab54-nat-sub-syntax
  $a class ( VERINAB54NatSub A B ) $.
verinab54-nat-abs-syntax
  $a class ( VERINAB54NatAbs A ) $.
verinab54-nat-min-syntax
  $a class ( VERINAB54NatMin A B ) $.
verinab54-to-list-syntax
  $a class ( VERINAB54ToList A ) $.
verinab54-get-bang-syntax
  $a class ( VERINAB54GetBang A B ) $.
verinab54-pairwise-le-syntax
  $a wff ( VERINAB54PairwiseLE A ) $.
verinab54-precondition-syntax
  $a wff ( VERINAB54Pre A B ) $.
verinab54-aux-graph-syntax
  $a wff ( VERINAB54AuxGraph A B C D E F ) $.
verinab54-aux-syntax
  $a class ( VERINAB54Aux A B C D E ) $.
verinab54-program-syntax
  $a class ( VERINAB54CanyonSearch A B ) $.
verinab54-postcondition-syntax
  $a wff ( VERINAB54Post A B C ) $.

verinab54-nat-sub-definition $a |- (
  VERINAB54NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab54-nat-abs-definition $a |- (
  VERINAB54NatAbs A
) = (
  abs ` A
) $.

verinab54-nat-min-definition $a |- (
  VERINAB54NatMin A B
) = if (
  A < B ,
  A ,
  B
) $.

verinab54-to-list-definition $a |- (
  VERINAB54ToList A
) = A $.

verinab54-get-bang-definition $a |- (
  VERINAB54GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d i j A $.

  verinab54-pairwise-le-definition $a |- (
    VERINAB54PairwiseLE A
  ) <-> (
    A e. Word ZZ
    /\
    A. i e. ( 0 ..^ ( # ` A ) )
      A. j e. ( 0 ..^ ( # ` A ) )
        (
          i < j
          ->
          ( A ` i ) <_ ( A ` j )
        )
  ) $.
$}

verinab54-precondition-definition $a |- (
  VERINAB54Pre A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. Word ZZ
  )
  /\
  (
    (
      0 < ( # ` A )
      /\
      0 < ( # ` B )
    )
    /\
    (
      ( VERINAB54PairwiseLE ( VERINAB54ToList A ) )
      /\
      ( VERINAB54PairwiseLE ( VERINAB54ToList B ) )
    )
  )
) $.

${
  $d k p q r A B C D E F $.

  verinab54-aux-graph-definition $a |- (
    VERINAB54AuxGraph A B C D E F
  ) <-> (
    (
      (
        (
          (
            A e. Word ZZ
            /\
            B e. Word ZZ
          )
          /\
          (
            C e. NN0
            /\
            D e. NN0
          )
        )
        /\
        E e. NN0
      )
      /\
      F e. NN0
    )
    /\
    E. p e. Word NN0
      E. q e. Word NN0
        E. r e. Word NN0
          (
            (
              (
                (
                  ( # ` p ) = (
                    (
                      VERINAB54NatSub
                        (
                          VERINAB54NatSub
                            ( ( # ` A ) + ( # ` B ) )
                            C
                        )
                        D
                    ) + 1
                  )
                  /\
                  ( # ` q ) = ( # ` p )
                )
                /\
                ( # ` r ) = ( # ` p )
              )
              /\
              (
                (
                  ( p ` 0 ) = C
                  /\
                  ( q ` 0 ) = D
                )
                /\
                ( r ` 0 ) = E
              )
            )
            /\
            (
              A. k e. (
                0 ..^ (
                  VERINAB54NatSub
                    (
                      VERINAB54NatSub
                        ( ( # ` A ) + ( # ` B ) )
                        C
                    )
                    D
                )
              )
                (
                  (
                    p ` ( k + 1 )
                  ) = if (
                    (
                      ( p ` k ) < ( # ` A )
                      /\
                      ( q ` k ) < ( # ` B )
                    )
                    ,
                    if (
                      (
                        VERINAB54GetBang A ( p ` k )
                      ) <_ (
                        VERINAB54GetBang B ( q ` k )
                      )
                      ,
                      ( ( p ` k ) + 1 )
                      ,
                      ( p ` k )
                    )
                    ,
                    ( p ` k )
                  )
                  /\
                  (
                    (
                      q ` ( k + 1 )
                    ) = if (
                      (
                        ( p ` k ) < ( # ` A )
                        /\
                        ( q ` k ) < ( # ` B )
                      )
                      ,
                      if (
                        (
                          VERINAB54GetBang A ( p ` k )
                        ) <_ (
                          VERINAB54GetBang B ( q ` k )
                        )
                        ,
                        ( q ` k )
                        ,
                        ( ( q ` k ) + 1 )
                      )
                      ,
                      ( q ` k )
                    )
                    /\
                    (
                      r ` ( k + 1 )
                    ) = if (
                      (
                        ( p ` k ) < ( # ` A )
                        /\
                        ( q ` k ) < ( # ` B )
                      )
                      ,
                      (
                        VERINAB54NatMin
                          (
                            VERINAB54NatAbs
                              (
                                (
                                  VERINAB54GetBang A ( p ` k )
                                )
                                -
                                (
                                  VERINAB54GetBang B ( q ` k )
                                )
                              )
                          )
                          ( r ` k )
                      )
                      ,
                      ( r ` k )
                    )
                  )
                )
              /\
              F = (
                r ` (
                  VERINAB54NatSub
                    (
                      VERINAB54NatSub
                        ( ( # ` A ) + ( # ` B ) )
                        C
                    )
                    D
                )
              )
            )
          )
  ) $.
$}

${
  $d y A B C D E $.

  verinab54-aux-definition $a |- (
    VERINAB54Aux A B C D E
  ) = (
    iota_ y e. NN0
      ( VERINAB54AuxGraph A B C D E y )
  ) $.
$}

verinab54-program-definition $a |- (
  VERINAB54CanyonSearch A B
) = (
  VERINAB54Aux
    A
    B
    0
    0
    if (
      (
        VERINAB54GetBang A 0
      ) < (
        VERINAB54GetBang B 0
      )
      ,
      (
        VERINAB54NatAbs
          (
            ( VERINAB54GetBang B 0 )
            -
            ( VERINAB54GetBang A 0 )
          )
      )
      ,
      (
        VERINAB54NatAbs
          (
            ( VERINAB54GetBang A 0 )
            -
            ( VERINAB54GetBang B 0 )
          )
      )
    )
) $.

${
  $d i j A B C $.

  verinab54-postcondition-definition $a |- (
    VERINAB54Post A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. Word ZZ
      )
      /\
      C e. NN0
    )
    /\
    (
      E. i e. ( 0 ..^ ( # ` A ) )
        E. j e. ( 0 ..^ ( # ` B ) )
          C = (
            VERINAB54NatAbs
              ( ( A ` i ) - ( B ` j ) )
          )
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        A. j e. ( 0 ..^ ( # ` B ) )
          C <_ (
            VERINAB54NatAbs
              ( ( A ` i ) - ( B ` j ) )
          )
    )
  ) $.
$}

verina-basic-54-canyon-search $a |- A. a e. Word ZZ
  A. b e. Word ZZ
    (
      ( VERINAB54Pre a b )
      ->
      (
        VERINAB54Post
          a
          b
          ( VERINAB54CanyonSearch a b )
      )
    )
$.
