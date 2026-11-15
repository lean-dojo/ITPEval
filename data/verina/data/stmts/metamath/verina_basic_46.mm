$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_46
  (verina__metamath__verina_basic_46), catalog title lastPosition: the exact
  executable full scan of a nondecreasing finite integer array returns the
  last target index, or integer -1 when the target is absent, and satisfies
  its complete correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays and their
  toList conversions. For a word w, # ` w is its natural-number length,
  w ` i is zero-based lookup, and 0 ..^ ( # ` w ) is its complete valid-index
  set.

  VERINAB46GetBang reproduces Lean Array.get! on integer arrays, including
  its inhabited default value zero outside the array, and VERINAB46ToNat is
  Lean Int.toNat.

  VERINAB46LoopGraph is the exact computation of the source local loop for
  every typed array, target, natural starting index, and integer accumulator.
  If the remaining suffix contains the target, its result is the unique
  greatest matching valid index in that suffix. If the suffix contains no
  target, it returns the accumulator unchanged. This is precisely the effect
  of scanning every remaining index, replacing pos exactly at matches, and
  stopping at the array size. VERINAB46Loop selects the unique integer fixed
  by this graph, and VERINAB46LastPosition invokes it at index zero with
  accumulator -1. Thus the executable result is fixed independently of the
  postcondition and the graph admits no extra outputs, including on unsorted
  typed arrays.

  VERINAB46PairwiseLE is exactly List.Pairwise with integer <=, expressed over
  every earlier/later index pair. VERINAB46Pre preserves that sortedness
  precondition. VERINAB46Post preserves all three source conjuncts: the
  result is -1 or nonnegative; a nonnegative result is an in-bounds target
  index with no later target occurrence; and -1 means no valid array index
  contains the target. The source drop (result.toNat + 1) followed by all
  inequality is represented by quantifying exactly the valid indices at or
  after that offset. The proof-valued precondition arguments are
  computationally and propositionally unused beyond the explicit antecedent
  in the final correctness assertion. Every earlier $a is syntax or a
  faithful definition required by this rendering, and this database has no
  $p declaration.
$)

$c
  VERINAB46GetBang VERINAB46ToNat
  VERINAB46PairwiseLE VERINAB46Pre
  VERINAB46LoopGraph VERINAB46Loop
  VERINAB46LastPosition VERINAB46Post
$.

verinab46-get-bang-syntax
  $a class ( VERINAB46GetBang A B ) $.
verinab46-to-nat-syntax
  $a class ( VERINAB46ToNat A ) $.
verinab46-pairwise-le-syntax
  $a wff ( VERINAB46PairwiseLE A ) $.
verinab46-precondition-syntax
  $a wff ( VERINAB46Pre A B ) $.
verinab46-loop-graph-syntax
  $a wff ( VERINAB46LoopGraph A B C D E ) $.
verinab46-loop-syntax
  $a class ( VERINAB46Loop A B C D ) $.
verinab46-program-syntax
  $a class ( VERINAB46LastPosition A B ) $.
verinab46-postcondition-syntax
  $a wff ( VERINAB46Post A B C ) $.

verinab46-get-bang-definition $a |- (
  VERINAB46GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

verinab46-to-nat-definition $a |- (
  VERINAB46ToNat A
) = if (
  A < 0 ,
  0 ,
  A
) $.

${
  $d i j A $.

  verinab46-pairwise-le-definition $a |- (
    VERINAB46PairwiseLE A
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

verinab46-precondition-definition $a |- (
  VERINAB46Pre A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. ZZ
  )
  /\
  ( VERINAB46PairwiseLE A )
) $.

${
  $d j A B C D E $.

  verinab46-loop-graph-definition $a |- (
    VERINAB46LoopGraph A B C D E
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
      (
        D e. ZZ
        /\
        E e. ZZ
      )
    )
    /\
    (
      (
        (
          E e. NN0
          /\
          C <_ E
        )
        /\
        (
          E < ( # ` A )
          /\
          ( A ` E ) = B
        )
        /\
        A. j e. ( 0 ..^ ( # ` A ) )
          (
            E < j
            ->
            ( A ` j ) =/= B
          )
      )
      \/
      (
        (
          A. j e. ( 0 ..^ ( # ` A ) )
            (
              C <_ j
              ->
              ( A ` j ) =/= B
            )
        )
        /\
        E = D
      )
    )
  ) $.
$}

${
  $d y A B C D $.

  verinab46-loop-definition $a |- (
    VERINAB46Loop A B C D
  ) = (
    iota_ y e. ZZ
      ( VERINAB46LoopGraph A B C D y )
  ) $.
$}

verinab46-program-definition $a |- (
  VERINAB46LastPosition A B
) = (
  VERINAB46Loop A B 0 ( -u 1 )
) $.

${
  $d i A B C $.

  verinab46-postcondition-definition $a |- (
    VERINAB46Post A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. ZZ
      )
      /\
      C e. ZZ
    )
    /\
    (
      (
        C = ( -u 1 )
        \/
        0 <_ C
      )
      /\
      (
        (
          0 <_ C
          ->
          (
            ( VERINAB46ToNat C ) < ( # ` A )
            /\
            (
              VERINAB46GetBang A ( VERINAB46ToNat C )
            ) = B
            /\
            A. i e. ( 0 ..^ ( # ` A ) )
              (
                ( ( VERINAB46ToNat C ) + 1 ) <_ i
                ->
                ( A ` i ) =/= B
              )
          )
        )
        /\
        (
          C = ( -u 1 )
          ->
          A. i e. ( 0 ..^ ( # ` A ) )
            ( A ` i ) =/= B
        )
      )
    )
  ) $.
$}

verina-basic-46-last-position
  $a |- A. w e. Word ZZ
    A. t e. ZZ
      (
        ( VERINAB46Pre w t )
        ->
        (
          VERINAB46Post
            w
            t
            ( VERINAB46LastPosition w t )
        )
      )
  $.
