$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_70
  (verina__metamath__verina_basic_70), catalog title LinearSearch3: the exact
  executable left-to-right search of a finite integer array under an arbitrary
  Boolean predicate returns its first satisfying index. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains,
  Word ZZ is exactly the type of arbitrary finite integer arrays, and
  { 0 , 1 } ^m ZZ is the full type of predicates Int -> Bool, with false = 0
  and true = 1. For a word a, # ` a is its natural-number size, a ` i is
  zero-based lookup, and 0 ..^ n is the set of natural indices below n.

  VERINAB70GetBang reproduces Lean Array.get! on integer arrays, including
  its inhabited default value zero outside the array. VERINAB70NatSub is
  truncated natural subtraction.

  VERINAB70LoopGraph is the exact deterministic graph of the source local
  recursive loop. Its witness p is the number of consecutive false predicate
  results beginning at the supplied natural index n, bounded by a.size - n.
  If p is smaller than that bound, the predicate is true at n + p and the
  result is n + p. If p equals the bound, the scan is exhausted and the result
  is zero. These are exactly the source true, recursive n + 1, and
  out-of-bounds branches, including starts at or beyond the array size.
  VERINAB70Loop selects the unique graph result.

  VERINAB70Pre is the source precondition that the predicate is true at some
  valid array index. VERINAB70LinearSearch3 is exactly the executable source
  call loop 0. VERINAB70Post states that the result is a valid index where the
  predicate is true and that the predicate is false at every smaller natural
  index. The proof-valued precondition arguments to the implementation and
  postcondition are computationally and propositionally unused beyond the
  explicit precondition antecedent in the final correctness assertion. Every
  earlier $a is syntax or a faithful definition required by this rendering,
  and this database has no $p declaration.
$)

$c
  VERINAB70NatSub VERINAB70GetBang
  VERINAB70LoopGraph VERINAB70Loop
  VERINAB70Pre VERINAB70LinearSearch3 VERINAB70Post
$.

verinab70-nat-sub-syntax
  $a class ( VERINAB70NatSub A B ) $.
verinab70-get-bang-syntax
  $a class ( VERINAB70GetBang A B ) $.
verinab70-loop-graph-syntax
  $a wff ( VERINAB70LoopGraph A B C D ) $.
verinab70-loop-syntax
  $a class ( VERINAB70Loop A B C ) $.
verinab70-precondition-syntax
  $a wff ( VERINAB70Pre A B ) $.
verinab70-program-syntax
  $a class ( VERINAB70LinearSearch3 A B ) $.
verinab70-postcondition-syntax
  $a wff ( VERINAB70Post A B C ) $.

verinab70-nat-sub-definition $a |- (
  VERINAB70NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab70-get-bang-definition $a |- (
  VERINAB70GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d j p A B C D $.

  verinab70-loop-graph-definition $a |- (
    VERINAB70LoopGraph A B C D
  ) <-> (
    (
      (
        (
          A e. Word ZZ
          /\
          B e. ( { 0 , 1 } ^m ZZ )
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
          VERINAB70NatSub
            ( # ` A )
            C
        )
        /\
        (
          A. j e. ( 0 ..^ p )
            (
              B
              `
              (
                VERINAB70GetBang
                  A
                  ( C + j )
              )
            ) = 0
          /\
          (
            (
              p < (
                VERINAB70NatSub
                  ( # ` A )
                  C
              )
              /\
              (
                (
                  B
                  `
                  (
                    VERINAB70GetBang
                      A
                      ( C + p )
                  )
                ) = 1
                /\
                D = ( C + p )
              )
            )
            \/
            (
              p = (
                VERINAB70NatSub
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

  verinab70-loop-definition $a |- (
    VERINAB70Loop A B C
  ) = (
    iota_ y e. NN0
      ( VERINAB70LoopGraph A B C y )
  ) $.
$}

${
  $d i A B $.

  verinab70-precondition-definition $a |- (
    VERINAB70Pre A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. ( { 0 , 1 } ^m ZZ )
    )
    /\
    E. i e. ( 0 ..^ ( # ` A ) )
      (
        B
        `
        ( VERINAB70GetBang A i )
      ) = 1
  ) $.
$}

verinab70-program-definition $a |- (
  VERINAB70LinearSearch3 A B
) = (
  VERINAB70Loop A B 0
) $.

${
  $d k A B C $.

  verinab70-postcondition-definition $a |- (
    VERINAB70Post A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. ( { 0 , 1 } ^m ZZ )
      )
      /\
      C e. NN0
    )
    /\
    (
      C < ( # ` A )
      /\
      (
        (
          B
          `
          ( VERINAB70GetBang A C )
        ) = 1
        /\
        A. k e. NN0
          (
            k < C
            ->
            (
              B
              `
              ( VERINAB70GetBang A k )
            ) = 0
          )
      )
    )
  ) $.
$}

verina-basic-70-linear-search3 $a |- A. a e. Word ZZ
  A. p e. ( { 0 , 1 } ^m ZZ )
    (
      ( VERINAB70Pre a p )
      ->
      (
        VERINAB70Post
          a
          p
          ( VERINAB70LinearSearch3 a p )
      )
    )
$.
