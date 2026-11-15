$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_19
  (verina__metamath__verina_basic_19), catalog title isSorted: the exact
  executable indexed Boolean scan returns true precisely when every adjacent
  pair of an arbitrary finite integer array is in non-decreasing order, with
  its unconditional correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number length, w ` i is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete valid-index set. The Boolean domain is
  represented by { 0 , 1 }, with false = 0 and true = 1.

  VERINAB19MapIdxGraph exactly reproduces the source Array.mapIdx. Its output
  has the same length as the input; at each valid index i it tests i + 1
  against the input size, returns the Boolean decision of the integer
  comparison w[i] <= w[i + 1] when that successor is valid, and returns true
  at the final index. VERINAB19MapIdx selects the unique Boolean word fixed by
  that graph.

  VERINAB19AllId is exactly Array.all id on a Boolean word: it returns true
  precisely when every entry is true, including vacuous truth on the empty
  word. VERINAB19IsSorted preserves the source size-at-most-one true branch
  and otherwise applies that all scan to the exact mapIdx result. Thus the
  executable output is fixed independently of the postcondition and admits
  no additional results.

  VERINAB19NatSub is Lean's truncated natural subtraction. VERINAB19Pre is the
  source True precondition on typed Array Int inputs. VERINAB19Post preserves
  the source universal natural index, proof-guarded bound i < a.size - 1,
  adjacent integer comparison, and equivalence with the Boolean result. The
  proof-valued precondition argument is computationally and propositionally
  unused and is represented by the explicit antecedent in the final
  correctness assertion. Every earlier $a is syntax or a faithful definition
  required by this rendering, and this database has no $p declaration.
$)

$c
  VERINAB19NatSub
  VERINAB19MapIdxGraph VERINAB19MapIdx VERINAB19AllId
  VERINAB19Pre VERINAB19IsSorted VERINAB19Post
$.

verinab19-nat-sub-syntax
  $a class ( VERINAB19NatSub A B ) $.
verinab19-map-idx-graph-syntax
  $a wff ( VERINAB19MapIdxGraph A B ) $.
verinab19-map-idx-syntax
  $a class ( VERINAB19MapIdx A ) $.
verinab19-all-id-syntax
  $a class ( VERINAB19AllId A ) $.
verinab19-precondition-syntax
  $a wff ( VERINAB19Pre A ) $.
verinab19-program-syntax
  $a class ( VERINAB19IsSorted A ) $.
verinab19-postcondition-syntax
  $a wff ( VERINAB19Post A B ) $.

verinab19-nat-sub-definition $a |- (
  VERINAB19NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

${
  $d i A B $.

  verinab19-map-idx-graph-definition $a |- (
    VERINAB19MapIdxGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word { 0 , 1 }
    )
    /\
    (
      ( # ` B ) = ( # ` A )
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        (
          B ` i
        ) = if (
          ( i + 1 ) < ( # ` A ) ,
          if (
            ( A ` i ) <_ ( A ` ( i + 1 ) ) ,
            1 ,
            0
          ) ,
          1
        )
    )
  ) $.
$}

${
  $d y A $.

  verinab19-map-idx-definition $a |- (
    VERINAB19MapIdx A
  ) = (
    iota_ y e. Word { 0 , 1 }
      ( VERINAB19MapIdxGraph A y )
  ) $.
$}

${
  $d i A $.

  verinab19-all-id-definition $a |- (
    VERINAB19AllId A
  ) = if (
    (
      A e. Word { 0 , 1 }
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        ( A ` i ) = 1
    ) ,
    1 ,
    0
  ) $.
$}

verinab19-precondition-definition $a |- (
  VERINAB19Pre A
) <-> (
  A e. Word ZZ
) $.

verinab19-program-definition $a |- (
  VERINAB19IsSorted A
) = if (
  ( # ` A ) <_ 1 ,
  1 ,
  (
    VERINAB19AllId
      ( VERINAB19MapIdx A )
  )
) $.

${
  $d i A B $.

  verinab19-postcondition-definition $a |- (
    VERINAB19Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. { 0 , 1 }
    )
    /\
    (
      A. i e. NN0
        (
          i < ( VERINAB19NatSub ( # ` A ) 1 )
          ->
          ( A ` i ) <_ ( A ` ( i + 1 ) )
        )
      <->
      B = 1
    )
  ) $.
$}

verina-basic-19-is-sorted $a |- A. w e. Word ZZ
  (
    ( VERINAB19Pre w )
    ->
    (
      VERINAB19Post
        w
        ( VERINAB19IsSorted w )
    )
  )
$.
