$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_64 (verina__metamath__verina_advanced_64), catalog title
  removeElement: the exact recursive natural-list program removes every
  occurrence of a target while preserving the order of all remaining
  elements, together with its indexed filter correctness contract. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain, and Word NN0 is exactly the
  type of arbitrary finite natural-number lists. For a word w, # ` w is its
  natural-number length, w ` i is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete index set.

  VERINA64ConsGraph and VERINA64Cons are exact list cons.
  VERINA64HelperGraph records the complete deterministic right-recursive
  execution of the source-local helper. Its trace entry at index i is the
  result on the suffix beginning at i, the terminal entry is the empty word,
  and each earlier entry either omits a matching head or conses a nonmatching
  head onto the already-computed suffix result. VERINA64Helper selects its
  unique output, and VERINA64RemoveElement is the source public executable
  implementation. Its result is therefore fixed independently of the
  postcondition.

  VERINA64FilterGraph retains exactly the non-target input positions in
  strictly increasing order, including repeated values, and VERINA64Filter
  is the corresponding stable List.filter computation used by the source
  postcondition. VERINA64None, VERINA64Some, VERINA64OptionNat, and
  VERINA64GetOption reproduce List.get? on natural-number lists.

  VERINA64Pre is the source True precondition on typed inputs.
  VERINA64Post expands result.zipIdx.all over every result index: the filtered
  input lookup must be some value equal to the result entry, and the two words
  must have equal lengths. This is exactly the source indexed comparison and
  length conjunction. The proof-valued precondition argument is
  computationally and propositionally unused and is represented by the
  explicit antecedent of the final correctness assertion. Every earlier $a
  is syntax or a faithful definition, and this database has no $p declaration.
$)

$c
  VERINA64ConsGraph VERINA64Cons
  VERINA64HelperGraph VERINA64Helper VERINA64RemoveElement
  VERINA64FilterGraph VERINA64Filter
  VERINA64None VERINA64Some VERINA64OptionNat VERINA64GetOption
  VERINA64Pre VERINA64Post
$.

verina64-cons-graph-syntax
  $a wff ( VERINA64ConsGraph A B C ) $.
verina64-cons-syntax
  $a class ( VERINA64Cons A B ) $.
verina64-helper-graph-syntax
  $a wff ( VERINA64HelperGraph A B C ) $.
verina64-helper-syntax
  $a class ( VERINA64Helper A B ) $.
verina64-program-syntax
  $a class ( VERINA64RemoveElement A B ) $.
verina64-filter-graph-syntax
  $a wff ( VERINA64FilterGraph A B C ) $.
verina64-filter-syntax
  $a class ( VERINA64Filter A B ) $.
verina64-none-syntax
  $a class VERINA64None $.
verina64-some-syntax
  $a class ( VERINA64Some A ) $.
verina64-option-nat-syntax
  $a class VERINA64OptionNat $.
verina64-get-option-syntax
  $a class ( VERINA64GetOption A B ) $.
verina64-precondition-syntax
  $a wff ( VERINA64Pre A B ) $.
verina64-postcondition-syntax
  $a wff ( VERINA64Post A B C ) $.

${
  $d j A B C $.

  verina64-cons-graph-definition $a |- (
    VERINA64ConsGraph A B C
  ) <-> (
    (
      (
        A e. NN0
        /\
        B e. Word NN0
      )
      /\
      C e. Word NN0
    )
    /\
    (
      ( # ` C ) = ( ( # ` B ) + 1 )
      /\
      (
        ( C ` 0 ) = A
        /\
        A. j e. ( 0 ..^ ( # ` B ) )
          ( C ` ( j + 1 ) ) = ( B ` j )
      )
    )
  ) $.
$}

${
  $d y A B $.

  verina64-cons-definition $a |- (
    VERINA64Cons A B
  ) = (
    iota_ y e. Word NN0
      ( VERINA64ConsGraph A B y )
  ) $.
$}

${
  $d i t A B C $.

  verina64-helper-graph-definition $a |- (
    VERINA64HelperGraph A B C
  ) <-> (
    (
      (
        A e. Word NN0
        /\
        B e. NN0
      )
      /\
      C e. Word NN0
    )
    /\
    E. t e. Word ( Word NN0 )
      (
        (
          ( # ` t ) = ( ( # ` A ) + 1 )
          /\
          ( t ` ( # ` A ) ) = (/)
        )
        /\
        (
          A. i e. ( 0 ..^ ( # ` A ) )
            (
              t ` i
            ) = if (
              ( A ` i ) = B ,
              ( t ` ( i + 1 ) ) ,
              (
                VERINA64Cons
                  ( A ` i )
                  ( t ` ( i + 1 ) )
              )
            )
          /\
          C = ( t ` 0 )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verina64-helper-definition $a |- (
    VERINA64Helper A B
  ) = (
    iota_ y e. Word NN0
      ( VERINA64HelperGraph A B y )
  ) $.
$}

verina64-program-definition $a |- (
  VERINA64RemoveElement A B
) = (
  VERINA64Helper A B
) $.

${
  $d i j k p A B C $.

  verina64-filter-graph-definition $a |- (
    VERINA64FilterGraph A B C
  ) <-> (
    (
      (
        A e. Word NN0
        /\
        B e. NN0
      )
      /\
      C e. Word NN0
    )
    /\
    E. p e. Word NN0
      (
        ( # ` p ) = ( # ` C )
        /\
        (
          A. j e. ( 0 ..^ ( # ` C ) )
            (
              (
                ( p ` j ) < ( # ` A )
                /\
                ( A ` ( p ` j ) ) =/= B
              )
              /\
              ( C ` j ) = ( A ` ( p ` j ) )
            )
          /\
          (
            A. j e. ( 0 ..^ ( # ` C ) )
              A. k e. ( 0 ..^ ( # ` C ) )
                (
                  j < k
                  ->
                  ( p ` j ) < ( p ` k )
                )
            /\
            A. i e. ( 0 ..^ ( # ` A ) )
              (
                ( A ` i ) =/= B
                ->
                E. j e. ( 0 ..^ ( # ` C ) )
                  ( p ` j ) = i
              )
          )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verina64-filter-definition $a |- (
    VERINA64Filter A B
  ) = (
    iota_ y e. Word NN0
      ( VERINA64FilterGraph A B y )
  ) $.
$}

verina64-none-definition $a |- VERINA64None = (/) $.

verina64-some-definition $a |- (
  VERINA64Some A
) = <. 1 , A >. $.

${
  $d x y $.

  verina64-option-nat-definition $a |- VERINA64OptionNat =
    { x |
      (
        x = VERINA64None
        \/
        E. y e. NN0
          x = ( VERINA64Some y )
      )
    } $.
$}

verina64-get-option-definition $a |- (
  VERINA64GetOption A B
) = if (
  B < ( # ` A ) ,
  ( VERINA64Some ( A ` B ) ) ,
  VERINA64None
) $.

verina64-precondition-definition $a |- (
  VERINA64Pre A B
) <-> (
  A e. Word NN0
  /\
  B e. NN0
) $.

${
  $d i A B C $.

  verina64-postcondition-definition $a |- (
    VERINA64Post A B C
  ) <-> (
    (
      (
        A e. Word NN0
        /\
        B e. NN0
      )
      /\
      C e. Word NN0
    )
    /\
    (
      A. i e. ( 0 ..^ ( # ` C ) )
        (
          VERINA64GetOption
            ( VERINA64Filter A B )
            i
        ) = (
          VERINA64Some ( C ` i )
        )
      /\
      ( # ` C ) = ( # ` ( VERINA64Filter A B ) )
    )
  ) $.
$}

verina-advanced-64-remove-element $a |-
  A. w e. Word NN0
    A. n e. NN0
      (
        ( VERINA64Pre w n )
        ->
        (
          VERINA64Post
            w
            n
            ( VERINA64RemoveElement w n )
        )
      )
$.
