$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_24
  (verina__metamath__verina_basic_24), catalog title firstEvenOddDifference:
  the exact executable left-to-right scan of a finite integer array returns
  its first even entry minus its first odd entry under the stated existence
  precondition and satisfies the first-occurrence contract. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number length, w ` i is zero-based lookup,
  ran w is its collection of entries, and 0 ..^ ( # ` w ) is its complete
  valid-index set. The Boolean domain is represented by { 0 , 1 }, with
  false = 0 and true = 1.

  VERINAB24IsEven and VERINAB24IsOdd are exactly the source Boolean helpers
  n % 2 == 0 and n % 2 != 0. SetMM integer remainder modulo positive two
  agrees with Lean's nonnegative integer remainder. VERINAB24GetBang
  reproduces Lean Array.get! on integer arrays, including its inhabited
  default value zero outside the array.

  VERINAB24None, VERINAB24Some, and VERINAB24OptionNat give a disjoint tagged
  representation of Option Nat. VERINAB24UpdateEven and
  VERINAB24UpdateOdd reproduce the two source let-bindings: an absent index is
  replaced by the current index exactly when the current entry has the
  requested parity, while an already present index is retained.

  VERINAB24LoopGraph is the least relation closed under the exact three
  branches of findFirstEvenOdd. At or beyond the array length it returns zero.
  At a valid index it performs both updates and immediately returns the
  get!-indexed even value minus the get!-indexed odd value when both updated
  options are present. Otherwise it recurses at the successor index with the
  updated options. VERINAB24Loop selects the unique integer output of this
  deterministic finite recursion, and VERINAB24FirstEvenOddDifference invokes
  it at index zero with both options absent, exactly as the source executable
  implementation does.

  VERINAB24Pre preserves the source size-greater-than-one condition and the
  existence of an even and an odd array entry. Quantification over ran w is
  equivalent to the source Array membership quantification, including
  duplicate entries. VERINAB24Post preserves the two natural indices, bounds,
  parity tests, returned integer difference, and both universal
  first-occurrence clauses. The proof-valued precondition argument has no
  computational effect and is represented by the explicit antecedent in the
  final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c
  VERINAB24IsEven VERINAB24IsOdd VERINAB24GetBang
  VERINAB24None VERINAB24Some VERINAB24OptionNat
  VERINAB24UpdateEven VERINAB24UpdateOdd
  VERINAB24LoopGraph VERINAB24Loop
  VERINAB24Pre VERINAB24FirstEvenOddDifference VERINAB24Post
$.

verinab24-is-even-syntax
  $a class ( VERINAB24IsEven A ) $.
verinab24-is-odd-syntax
  $a class ( VERINAB24IsOdd A ) $.
verinab24-get-bang-syntax
  $a class ( VERINAB24GetBang A B ) $.
verinab24-none-syntax
  $a class VERINAB24None $.
verinab24-some-syntax
  $a class ( VERINAB24Some A ) $.
verinab24-option-nat-syntax
  $a class VERINAB24OptionNat $.
verinab24-update-even-syntax
  $a class ( VERINAB24UpdateEven A B C ) $.
verinab24-update-odd-syntax
  $a class ( VERINAB24UpdateOdd A B C ) $.
verinab24-loop-graph-syntax
  $a wff ( VERINAB24LoopGraph A B C D E ) $.
verinab24-loop-syntax
  $a class ( VERINAB24Loop A B C D ) $.
verinab24-precondition-syntax
  $a wff ( VERINAB24Pre A ) $.
verinab24-program-syntax
  $a class ( VERINAB24FirstEvenOddDifference A ) $.
verinab24-postcondition-syntax
  $a wff ( VERINAB24Post A B ) $.

verinab24-is-even-definition $a |- (
  VERINAB24IsEven A
) = if (
  ( A mod 2 ) = 0 ,
  1 ,
  0
) $.

verinab24-is-odd-definition $a |- (
  VERINAB24IsOdd A
) = if (
  ( A mod 2 ) =/= 0 ,
  1 ,
  0
) $.

verinab24-get-bang-definition $a |- (
  VERINAB24GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

verinab24-none-definition $a |- VERINAB24None = (/) $.

verinab24-some-definition $a |- (
  VERINAB24Some A
) = <. 1 , A >. $.

${
  $d x y $.

  verinab24-option-nat-definition $a |- VERINAB24OptionNat =
    { x |
      (
        x = VERINAB24None
        \/
        E. y e. NN0 x = ( VERINAB24Some y )
      )
    } $.
$}

verinab24-update-even-definition $a |- (
  VERINAB24UpdateEven A B C
) = if (
  (
    B = VERINAB24None
    /\
    ( VERINAB24IsEven C ) = 1
  ) ,
  ( VERINAB24Some A ) ,
  B
) $.

verinab24-update-odd-definition $a |- (
  VERINAB24UpdateOdd A B C
) = if (
  (
    B = VERINAB24None
    /\
    ( VERINAB24IsOdd C ) = 1
  ) ,
  ( VERINAB24Some A ) ,
  B
) $.

${
  $d
    R A B C D E
    w i p q r s e o y
  $.

  verinab24-loop-graph-definition $a |- (
    VERINAB24LoopGraph A B C D E
  ) <-> (
    (
      (
        (
          (
            A e. Word ZZ
            /\
            B e. NN0
          )
          /\
          C e. VERINAB24OptionNat
        )
        /\
        D e. VERINAB24OptionNat
      )
      /\
      E e. ZZ
    )
    /\
    A. R
      (
        (
          (
            A. w e. Word ZZ
              A. i e. NN0
                A. p e. VERINAB24OptionNat
                  A. q e. VERINAB24OptionNat
                    (
                      -. i < ( # ` w )
                      ->
                      <.
                        <.
                          <.
                            <. w , i >.
                            ,
                            p
                          >.
                          ,
                          q
                        >.
                        ,
                        0
                      >. e. R
                    )
            /\
            A. w e. Word ZZ
              A. i e. NN0
                A. p e. VERINAB24OptionNat
                  A. q e. VERINAB24OptionNat
                    A. r e. VERINAB24OptionNat
                      A. s e. VERINAB24OptionNat
                        A. e e. NN0
                          A. o e. NN0
                            (
                              (
                                (
                                  (
                                    i < ( # ` w )
                                    /\
                                    r = (
                                      VERINAB24UpdateEven
                                        i
                                        p
                                        ( VERINAB24GetBang w i )
                                    )
                                  )
                                  /\
                                  s = (
                                    VERINAB24UpdateOdd
                                      i
                                      q
                                      ( VERINAB24GetBang w i )
                                  )
                                )
                                /\
                                r = ( VERINAB24Some e )
                              )
                              /\
                              s = ( VERINAB24Some o )
                              ->
                              <.
                                <.
                                  <.
                                    <. w , i >.
                                    ,
                                    p
                                  >.
                                  ,
                                  q
                                >.
                                ,
                                (
                                  ( VERINAB24GetBang w e )
                                  -
                                  ( VERINAB24GetBang w o )
                                )
                              >. e. R
                            )
          )
          /\
          A. w e. Word ZZ
            A. i e. NN0
              A. p e. VERINAB24OptionNat
                A. q e. VERINAB24OptionNat
                  A. r e. VERINAB24OptionNat
                    A. s e. VERINAB24OptionNat
                      A. y e. ZZ
                        (
                          (
                            (
                              (
                                i < ( # ` w )
                                /\
                                r = (
                                  VERINAB24UpdateEven
                                    i
                                    p
                                    ( VERINAB24GetBang w i )
                                )
                              )
                              /\
                              s = (
                                VERINAB24UpdateOdd
                                  i
                                  q
                                  ( VERINAB24GetBang w i )
                              )
                            )
                            /\
                            -.
                            E. e e. NN0
                              E. o e. NN0
                                (
                                  r = ( VERINAB24Some e )
                                  /\
                                  s = ( VERINAB24Some o )
                                )
                          )
                          /\
                          <.
                            <.
                              <.
                                <. w , ( i + 1 ) >.
                                ,
                                r
                              >.
                              ,
                              s
                            >.
                            ,
                            y
                          >. e. R
                          ->
                          <.
                            <.
                              <.
                                <. w , i >.
                                ,
                                p
                              >.
                              ,
                              q
                            >.
                            ,
                            y
                          >. e. R
                        )
        )
        ->
        <.
          <.
            <.
              <. A , B >.
              ,
              C
            >.
            ,
            D
          >.
          ,
          E
        >. e. R
      )
  ) $.
$}

${
  $d y A B C D $.

  verinab24-loop-definition $a |- (
    VERINAB24Loop A B C D
  ) = (
    iota_ y e. ZZ
      ( VERINAB24LoopGraph A B C D y )
  ) $.
$}

${
  $d x y A $.

  verinab24-precondition-definition $a |- (
    VERINAB24Pre A
  ) <-> (
    (
      A e. Word ZZ
      /\
      1 < ( # ` A )
    )
    /\
    (
      E. x e. ran A
        ( VERINAB24IsEven x ) = 1
      /\
      E. y e. ran A
        ( VERINAB24IsOdd y ) = 1
    )
  ) $.
$}

verinab24-program-definition $a |- (
  VERINAB24FirstEvenOddDifference A
) = (
  VERINAB24Loop
    A
    0
    VERINAB24None
    VERINAB24None
) $.

${
  $d i j k A B $.

  verinab24-postcondition-definition $a |- (
    VERINAB24Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. ZZ
    )
    /\
    E. i e. NN0
      E. j e. NN0
        (
          (
            i < ( # ` A )
            /\
            j < ( # ` A )
          )
          /\
          (
            (
              ( VERINAB24IsEven ( VERINAB24GetBang A i ) ) = 1
              /\
              ( VERINAB24IsOdd ( VERINAB24GetBang A j ) ) = 1
            )
            /\
            (
              B = (
                ( VERINAB24GetBang A i )
                -
                ( VERINAB24GetBang A j )
              )
              /\
              (
                A. k e. NN0
                  (
                    k < i
                    ->
                    (
                      VERINAB24IsOdd
                        ( VERINAB24GetBang A k )
                    ) = 1
                  )
                /\
                A. k e. NN0
                  (
                    k < j
                    ->
                    (
                      VERINAB24IsEven
                        ( VERINAB24GetBang A k )
                    ) = 1
                  )
              )
            )
          )
        )
  ) $.
$}

verina-basic-24-first-even-odd-difference $a |- A. w e. Word ZZ
  (
    ( VERINAB24Pre w )
    ->
    (
      VERINAB24Post
        w
        ( VERINAB24FirstEvenOddDifference w )
    )
  )
$.
