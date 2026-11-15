$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_70 (verina__metamath__verina_advanced_70), catalog title
  semiOrderedPermutation: the exact finite-list program computes the minimum
  adjacent-swap count that moves 1 first and the list length last in a
  permutation of 1 through that length, together with its full precondition
  and arithmetic postcondition. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer lists. For a word
  w, # ` w is its natural-number length, w ` i is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete index set. Natural values in integer
  expressions use the canonical inclusion NN0 C_ ZZ, exactly as Lean's
  Int.ofNat coercions do here.

  VERINA70IdxOfGraph characterizes List.idxOf exactly: its result is the
  least index containing the requested integer, or the word length if the
  integer is absent. VERINA70IdxOf selects that unique result.
  VERINA70NatSub is Lean's truncated natural subtraction.

  VERINA70Pre preserves all source clauses: positive length, List.Nodup, and
  every integer entry between one and the integer coercion of the length.
  Under those clauses the word is precisely a permutation of 1 through its
  length, but the definition retains the source clauses themselves.

  VERINA70EndPosition, VERINA70DistanceOne, VERINA70DistanceLast, and
  VERINA70TotalMoves reproduce the source let-bound computations. In
  particular, both subtractions are truncated natural subtraction and the
  overlap adjustment is made exactly when the index of 1 is greater than the
  index of the length. VERINA70SemiOrderedPermutation is therefore the exact
  executable result, canonically embedded in ZZ, and is fixed independently
  of the postcondition.

  VERINA70Post is the source conditional integer equation using the same two
  idxOf computations. The proof-valued precondition arguments to the program
  and postcondition are computationally and propositionally unused, so they
  are represented by the explicit antecedent of the final correctness
  assertion. Every earlier $a is syntax or a faithful definition required by
  this rendering, and this database has no $p declaration.
$)

$c
  VERINA70IdxOfGraph VERINA70IdxOf
  VERINA70NatSub
  VERINA70Pre
  VERINA70EndPosition
  VERINA70DistanceOne VERINA70DistanceLast VERINA70TotalMoves
  VERINA70SemiOrderedPermutation
  VERINA70Post
$.

verina70-idx-of-graph-syntax
  $a wff ( VERINA70IdxOfGraph A B C ) $.
verina70-idx-of-syntax
  $a class ( VERINA70IdxOf A B ) $.
verina70-nat-sub-syntax
  $a class ( VERINA70NatSub A B ) $.
verina70-precondition-syntax
  $a wff ( VERINA70Pre A ) $.
verina70-end-position-syntax
  $a class ( VERINA70EndPosition A ) $.
verina70-distance-one-syntax
  $a class ( VERINA70DistanceOne A ) $.
verina70-distance-last-syntax
  $a class ( VERINA70DistanceLast A ) $.
verina70-total-moves-syntax
  $a class ( VERINA70TotalMoves A ) $.
verina70-program-syntax
  $a class ( VERINA70SemiOrderedPermutation A ) $.
verina70-postcondition-syntax
  $a wff ( VERINA70Post A B ) $.

${
  $d j A B C $.

  verina70-idx-of-graph-definition $a |- (
    VERINA70IdxOfGraph A B C
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
      C <_ ( # ` A )
      /\
      (
        A. j e. ( 0 ..^ C )
          ( A ` j ) =/= B
        /\
        (
          C < ( # ` A )
          ->
          ( A ` C ) = B
        )
      )
    )
  ) $.
$}

${
  $d y A B $.

  verina70-idx-of-definition $a |- (
    VERINA70IdxOf A B
  ) = (
    iota_ y e. NN0
      ( VERINA70IdxOfGraph A B y )
  ) $.
$}

verina70-nat-sub-definition $a |- (
  VERINA70NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

${
  $d i j A $.

  verina70-precondition-definition $a |- (
    VERINA70Pre A
  ) <-> (
    (
      A e. Word ZZ
      /\
      0 < ( # ` A )
    )
    /\
    (
      A. i e. ( 0 ..^ ( # ` A ) )
        A. j e. ( 0 ..^ ( # ` A ) )
          (
            i < j
            ->
            ( A ` i ) =/= ( A ` j )
          )
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        (
          1 <_ ( A ` i )
          /\
          ( A ` i ) <_ ( # ` A )
        )
    )
  ) $.
$}

verina70-end-position-definition $a |- (
  VERINA70EndPosition A
) = (
  VERINA70NatSub ( # ` A ) 1
) $.

verina70-distance-one-definition $a |- (
  VERINA70DistanceOne A
) = if (
  ( VERINA70IdxOf A 1 ) =/= 0 ,
  ( VERINA70IdxOf A 1 ) ,
  0
) $.

verina70-distance-last-definition $a |- (
  VERINA70DistanceLast A
) = if (
  (
    VERINA70IdxOf A ( # ` A )
  ) =/= (
    VERINA70EndPosition A
  ) ,
  (
    VERINA70NatSub
      ( VERINA70EndPosition A )
      ( VERINA70IdxOf A ( # ` A ) )
  ) ,
  0
) $.

verina70-total-moves-definition $a |- (
  VERINA70TotalMoves A
) = (
  ( VERINA70DistanceOne A )
  +
  ( VERINA70DistanceLast A )
) $.

verina70-program-definition $a |- (
  VERINA70SemiOrderedPermutation A
) = if (
  (
    VERINA70IdxOf A ( # ` A )
  ) < (
    VERINA70IdxOf A 1
  ) ,
  (
    VERINA70NatSub
      ( VERINA70TotalMoves A )
      1
  ) ,
  ( VERINA70TotalMoves A )
) $.

verina70-postcondition-definition $a |- (
  VERINA70Post A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. ZZ
  )
  /\
  (
    (
      (
        VERINA70IdxOf A ( # ` A )
      ) < (
        VERINA70IdxOf A 1
      )
      ->
      (
        (
          ( VERINA70IdxOf A 1 )
          +
          ( # ` A )
        ) = (
          (
            B + 2
          ) + (
            VERINA70IdxOf A ( # ` A )
          )
        )
      )
    )
    /\
    (
      -. (
        (
          VERINA70IdxOf A ( # ` A )
        ) < (
          VERINA70IdxOf A 1
        )
      )
      ->
      (
        (
          ( VERINA70IdxOf A 1 )
          +
          ( # ` A )
        ) = (
          (
            B + 1
          ) + (
            VERINA70IdxOf A ( # ` A )
          )
        )
      )
    )
  )
) $.

verina-advanced-70-semi-ordered-permutation
  $a |- A. w e. Word ZZ
    (
      ( VERINA70Pre w )
      ->
      (
        VERINA70Post
          w
          ( VERINA70SemiOrderedPermutation w )
      )
    )
  $.
