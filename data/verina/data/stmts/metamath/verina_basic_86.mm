$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_86
  (verina__metamath__verina_basic_86), catalog title rotate: the exact
  executable recursive integer-array program rotates an arbitrary finite
  array to the left by a nonnegative integer offset and satisfies its
  size-and-modular-index correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number size, w ` i is zero-based lookup, and
  0 ..^ n is the complete set of natural indices below n. Natural values
  embed into ZZ identically, exactly representing Int.ofNat.

  VERINAB86NatSub is Lean's truncated natural subtraction.
  VERINAB86GetBang reproduces Array.get! on integer arrays, including its
  inhabited default value zero outside the array. VERINAB86SetBangGraph and
  its iota-selected function reproduce Array.set!, including unchanged-array
  behavior at an out-of-range index. VERINAB86ConstArray is exactly
  Array.mkArray for an integer value.

  VERINAB86IntMod is Lean Int.emod on all integer inputs: modulus zero returns
  the dividend, and a nonzero divisor uses its positive magnitude.
  VERINAB86Adjusted preserves the source let-bound negative-remainder
  adjustment, and VERINAB86ToNat is Lean Int.toNat, returning zero on
  negative integers.

  VERINAB86AuxGraph is the exact finite execution trace of rotateAux for every
  typed input array, integer offset, natural starting index and length, and
  integer-array accumulator. Its trace has max(len - i, 0) transitions.
  Transition k computes the source modular index from i + k and offset,
  performs the negative-result adjustment and Int.toNat conversion, reads a
  with get!, and applies set! at i + k to the current accumulator.
  VERINAB86Aux selects the unique final accumulator fixed by this trace and
  therefore admits no result beyond the source computation.

  VERINAB86Pre preserves the nonnegative-offset precondition.
  VERINAB86Rotate sets len to a.size, selects a[0]! when len is positive and
  zero otherwise, allocates Array.mkArray len with that value, and invokes
  the exact auxiliary computation at index zero. VERINAB86Post preserves the
  result-size equation and the universal get!-equation with the source's
  unadjusted Int.toNat of the Euclidean remainder. The proof-valued
  precondition arguments to the implementation and postcondition have no
  computational or propositional effect beyond the explicit antecedent in
  the final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c
  VERINAB86NatSub VERINAB86GetBang
  VERINAB86SetBangGraph VERINAB86SetBang
  VERINAB86ConstArrayGraph VERINAB86ConstArray
  VERINAB86IntMod VERINAB86Adjusted VERINAB86ToNat
  VERINAB86AuxGraph VERINAB86Aux
  VERINAB86Pre VERINAB86Rotate VERINAB86Post
$.

verinab86-nat-sub-syntax
  $a class ( VERINAB86NatSub A B ) $.
verinab86-get-bang-syntax
  $a class ( VERINAB86GetBang A B ) $.
verinab86-set-bang-graph-syntax
  $a wff ( VERINAB86SetBangGraph A B C D ) $.
verinab86-set-bang-syntax
  $a class ( VERINAB86SetBang A B C ) $.
verinab86-const-array-graph-syntax
  $a wff ( VERINAB86ConstArrayGraph A B C ) $.
verinab86-const-array-syntax
  $a class ( VERINAB86ConstArray A B ) $.
verinab86-int-mod-syntax
  $a class ( VERINAB86IntMod A B ) $.
verinab86-adjusted-syntax
  $a class ( VERINAB86Adjusted A B ) $.
verinab86-to-nat-syntax
  $a class ( VERINAB86ToNat A ) $.
verinab86-aux-graph-syntax
  $a wff ( VERINAB86AuxGraph A B C D E F ) $.
verinab86-aux-syntax
  $a class ( VERINAB86Aux A B C D E ) $.
verinab86-precondition-syntax
  $a wff ( VERINAB86Pre A B ) $.
verinab86-program-syntax
  $a class ( VERINAB86Rotate A B ) $.
verinab86-postcondition-syntax
  $a wff ( VERINAB86Post A B C ) $.

verinab86-nat-sub-definition $a |- (
  VERINAB86NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab86-get-bang-definition $a |- (
  VERINAB86GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d k A B C D $.

  verinab86-set-bang-graph-definition $a |- (
    VERINAB86SetBangGraph A B C D
  ) <-> (
    (
      (
        (
          A e. Word ZZ
          /\
          B e. NN0
        )
        /\
        C e. ZZ
      )
      /\
      D e. Word ZZ
    )
    /\
    (
      ( # ` D ) = ( # ` A )
      /\
      A. k e. ( 0 ..^ ( # ` A ) )
        ( D ` k ) = if (
          k = B ,
          C ,
          ( A ` k )
        )
    )
  ) $.
$}

${
  $d y A B C $.

  verinab86-set-bang-definition $a |- (
    VERINAB86SetBang A B C
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB86SetBangGraph A B C y )
  ) $.
$}

${
  $d k A B C $.

  verinab86-const-array-graph-definition $a |- (
    VERINAB86ConstArrayGraph A B C
  ) <-> (
    (
      (
        A e. NN0
        /\
        B e. ZZ
      )
      /\
      C e. Word ZZ
    )
    /\
    (
      ( # ` C ) = A
      /\
      A. k e. ( 0 ..^ A )
        ( C ` k ) = B
    )
  ) $.
$}

${
  $d y A B $.

  verinab86-const-array-definition $a |- (
    VERINAB86ConstArray A B
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB86ConstArrayGraph A B y )
  ) $.
$}

verinab86-int-mod-definition $a |- (
  VERINAB86IntMod A B
) = if (
  B = 0 ,
  A ,
  ( A mod ( abs ` B ) )
) $.

verinab86-adjusted-definition $a |- (
  VERINAB86Adjusted A B
) = if (
  ( VERINAB86IntMod A B ) < 0 ,
  ( ( VERINAB86IntMod A B ) + B ) ,
  ( VERINAB86IntMod A B )
) $.

verinab86-to-nat-definition $a |- (
  VERINAB86ToNat A
) = if (
  A < 0 ,
  0 ,
  A
) $.

${
  $d k t A B C D E F $.

  verinab86-aux-graph-definition $a |- (
    VERINAB86AuxGraph A B C D E F
  ) <-> (
    (
      (
        (
          (
            A e. Word ZZ
            /\
            B e. ZZ
          )
          /\
          (
            C e. NN0
            /\
            D e. NN0
          )
        )
        /\
        E e. Word ZZ
      )
      /\
      F e. Word ZZ
    )
    /\
    E. t e. Word ( Word ZZ )
      (
        (
          ( # ` t ) = (
            ( VERINAB86NatSub D C ) + 1
          )
          /\
          ( t ` 0 ) = E
        )
        /\
        (
          A. k e. (
            0 ..^ ( VERINAB86NatSub D C )
          )
            (
              t ` ( k + 1 )
            ) = (
              VERINAB86SetBang
                ( t ` k )
                ( C + k )
                (
                  VERINAB86GetBang
                    A
                    (
                      VERINAB86ToNat
                        (
                          VERINAB86Adjusted
                            ( ( C + k ) + B )
                            D
                        )
                    )
                )
            )
          /\
          F = (
            t ` ( VERINAB86NatSub D C )
          )
        )
      )
  ) $.
$}

${
  $d y A B C D E $.

  verinab86-aux-definition $a |- (
    VERINAB86Aux A B C D E
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB86AuxGraph A B C D E y )
  ) $.
$}

verinab86-precondition-definition $a |- (
  VERINAB86Pre A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. ZZ
  )
  /\
  0 <_ B
) $.

verinab86-program-definition $a |- (
  VERINAB86Rotate A B
) = (
  VERINAB86Aux
    A
    B
    0
    ( # ` A )
    (
      VERINAB86ConstArray
        ( # ` A )
        if (
          0 < ( # ` A ) ,
          ( VERINAB86GetBang A 0 ) ,
          0
        )
    )
) $.

${
  $d i A B C $.

  verinab86-postcondition-definition $a |- (
    VERINAB86Post A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. ZZ
      )
      /\
      C e. Word ZZ
    )
    /\
    (
      ( # ` C ) = ( # ` A )
      /\
      A. i e. NN0
        (
          i < ( # ` A )
          ->
          (
            VERINAB86GetBang C i
          ) = (
            VERINAB86GetBang
              A
              (
                VERINAB86ToNat
                  (
                    VERINAB86IntMod
                      ( i + B )
                      ( # ` A )
                  )
              )
          )
        )
    )
  ) $.
$}

verina-basic-86-rotate $a |- A. a e. Word ZZ
  A. o e. ZZ
    (
      ( VERINAB86Pre a o )
      ->
      (
        VERINAB86Post
          a
          o
          ( VERINAB86Rotate a o )
      )
    )
$.
