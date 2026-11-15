$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_69
  (verina__metamath__verina_basic_69), catalog title LinearSearch: the exact
  recursive linear search of a finite integer array containing a target
  returns the target's first index. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number length, w ` i is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete valid-index set.

  VERINAB69GetBang reproduces Lean Array.get! on integer arrays, including
  its inhabited default value zero outside the array. VERINAB69NatSub is
  truncated natural subtraction.

  VERINAB69AuxGraph is the exact deterministic graph of linearSearchAux.
  Its witness p is the number of consecutive failed comparisons beginning
  at the supplied natural index n. It is bounded by a.size - n. Every one of
  those p positions differs from the target. If p is smaller than the bound,
  the next array entry equals the target and the result is n + p; otherwise
  p equals the bound and the result is zero. These are exactly the recursive
  match, recursive increment, and exhausted-array branches, including the
  source behavior when n is already out of bounds. VERINAB69Aux selects the
  unique graph result, so the helper admits no extra outputs.

  VERINAB69Pre is the source precondition that the target occurs at a valid
  array index. VERINAB69LinearSearch is exactly the executable source call
  linearSearchAux a e 0. VERINAB69Post states that the returned natural is a
  valid target index and every smaller natural index has a different value.
  The proof-valued precondition arguments to the implementation and
  postcondition are computationally and propositionally unused beyond the
  explicit precondition antecedent in the final correctness assertion. Every
  earlier $a is syntax or a faithful definition required by this rendering,
  and this database has no $p declaration.
$)

$c
  VERINAB69NatSub VERINAB69GetBang
  VERINAB69AuxGraph VERINAB69Aux
  VERINAB69Pre VERINAB69LinearSearch VERINAB69Post
$.

verinab69-nat-sub-syntax
  $a class ( VERINAB69NatSub A B ) $.
verinab69-get-bang-syntax
  $a class ( VERINAB69GetBang A B ) $.
verinab69-aux-graph-syntax
  $a wff ( VERINAB69AuxGraph A B C D ) $.
verinab69-aux-syntax
  $a class ( VERINAB69Aux A B C ) $.
verinab69-precondition-syntax
  $a wff ( VERINAB69Pre A B ) $.
verinab69-program-syntax
  $a class ( VERINAB69LinearSearch A B ) $.
verinab69-postcondition-syntax
  $a wff ( VERINAB69Post A B C ) $.

verinab69-nat-sub-definition $a |- (
  VERINAB69NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab69-get-bang-definition $a |- (
  VERINAB69GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d j p A B C D $.

  verinab69-aux-graph-definition $a |- (
    VERINAB69AuxGraph A B C D
  ) <-> (
    (
      (
        (
          A e. Word ZZ
          /\
          B e. ZZ
        )
        /\
        C e. NN0
      )
      /\
      D e. NN0
    )
    /\
    E. p e. NN0
      (
        p <_ (
          VERINAB69NatSub
            ( # ` A )
            C
        )
        /\
        (
          A. j e. ( 0 ..^ p )
            (
              VERINAB69GetBang
                A
                ( C + j )
            ) =/= B
          /\
          (
            (
              p < (
                VERINAB69NatSub
                  ( # ` A )
                  C
              )
              /\
              (
                (
                  VERINAB69GetBang
                    A
                    ( C + p )
                ) = B
                /\
                D = ( C + p )
              )
            )
            \/
            (
              p = (
                VERINAB69NatSub
                  ( # ` A )
                  C
              )
              /\
              D = 0
            )
          )
        )
      )
  ) $.
$}

${
  $d y A B C $.

  verinab69-aux-definition $a |- (
    VERINAB69Aux A B C
  ) = (
    iota_ y e. NN0
      ( VERINAB69AuxGraph A B C y )
  ) $.
$}

${
  $d i A B $.

  verinab69-precondition-definition $a |- (
    VERINAB69Pre A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. ZZ
    )
    /\
    E. i e. ( 0 ..^ ( # ` A ) )
      ( VERINAB69GetBang A i ) = B
  ) $.
$}

verinab69-program-definition $a |- (
  VERINAB69LinearSearch A B
) = (
  VERINAB69Aux A B 0
) $.

${
  $d k A B C $.

  verinab69-postcondition-definition $a |- (
    VERINAB69Post A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. ZZ
      )
      /\
      C e. NN0
    )
    /\
    (
      C < ( # ` A )
      /\
      (
        ( VERINAB69GetBang A C ) = B
        /\
        A. k e. NN0
          (
            k < C
            ->
            ( VERINAB69GetBang A k ) =/= B
          )
      )
    )
  ) $.
$}

verina-basic-69-linear-search $a |- A. a e. Word ZZ
  A. e e. ZZ
    (
      ( VERINAB69Pre a e )
      ->
      (
        VERINAB69Post
          a
          e
          ( VERINAB69LinearSearch a e )
      )
    )
$.
