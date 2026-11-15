$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_77
  (verina__metamath__verina_basic_77), catalog title modify_array_element:
  the exact nested natural-number array program updates one selected inner
  element and satisfies the complete size-and-unchanged-entry correctness
  contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain, Word NN0 is exactly the type
  of arbitrary finite natural-number arrays, and Word ( Word NN0 ) is exactly
  the type of arbitrary finite arrays of such arrays. For a word w, # ` w is
  its natural-number size, w ` k is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete valid-index set.

  VERINAB77OuterGetBang and VERINAB77InnerGetBang reproduce Lean Array.get!
  at the two array levels, with the correct inhabited defaults: the empty
  natural-number array and zero, respectively. VERINAB77InnerSetBangGraph and
  VERINAB77OuterSetBangGraph uniquely characterize Array.set! by preserving
  the input length and replacing precisely the designated in-range entry;
  when the index is out of range, the array is unchanged. Their iota-selected
  functions therefore admit no extra outputs.

  VERINAB77UpdateInner is the source updateInner helper exactly.
  VERINAB77ModifyArrayElement first reads the selected inner array, applies
  UpdateInner at index2 with val, and writes that exact inner result back at
  index1. Thus the executable implementation is fixed independently of the
  postcondition.

  VERINAB77Pre preserves both source bounds together with all input types.
  VERINAB77Post preserves the outer size, selected-inner size, every
  nonselected outer entry, every nonselected entry of the selected inner
  array, and the new selected value. The source proof-valued precondition
  arguments have no computational effect and are not inspected by the
  postcondition, so the final correctness assertion represents them by its
  explicit precondition antecedent. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c
  VERINAB77OuterGetBang VERINAB77InnerGetBang
  VERINAB77InnerSetBangGraph VERINAB77InnerSetBang VERINAB77UpdateInner
  VERINAB77OuterSetBangGraph VERINAB77OuterSetBang
  VERINAB77Pre VERINAB77ModifyArrayElement VERINAB77Post
$.

verinab77-outer-get-bang-syntax
  $a class ( VERINAB77OuterGetBang A B ) $.
verinab77-inner-get-bang-syntax
  $a class ( VERINAB77InnerGetBang A B ) $.
verinab77-inner-set-bang-graph-syntax
  $a wff ( VERINAB77InnerSetBangGraph A B C D ) $.
verinab77-inner-set-bang-syntax
  $a class ( VERINAB77InnerSetBang A B C ) $.
verinab77-update-inner-syntax
  $a class ( VERINAB77UpdateInner A B C ) $.
verinab77-outer-set-bang-graph-syntax
  $a wff ( VERINAB77OuterSetBangGraph A B C D ) $.
verinab77-outer-set-bang-syntax
  $a class ( VERINAB77OuterSetBang A B C ) $.
verinab77-precondition-syntax
  $a wff ( VERINAB77Pre A B C D ) $.
verinab77-program-syntax
  $a class ( VERINAB77ModifyArrayElement A B C D ) $.
verinab77-postcondition-syntax
  $a wff ( VERINAB77Post A B C D E ) $.

verinab77-outer-get-bang-definition $a |- (
  VERINAB77OuterGetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  (/)
) $.

verinab77-inner-get-bang-definition $a |- (
  VERINAB77InnerGetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d i A B C D $.

  verinab77-inner-set-bang-graph-definition $a |- (
    VERINAB77InnerSetBangGraph A B C D
  ) <-> (
    (
      (
        (
          A e. Word NN0
          /\
          B e. NN0
        )
        /\
        C e. NN0
      )
      /\
      D e. Word NN0
    )
    /\
    (
      ( # ` D ) = ( # ` A )
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        ( D ` i ) = if (
          i = B ,
          C ,
          ( A ` i )
        )
    )
  ) $.
$}

${
  $d y A B C $.

  verinab77-inner-set-bang-definition $a |- (
    VERINAB77InnerSetBang A B C
  ) = (
    iota_ y e. Word NN0
      ( VERINAB77InnerSetBangGraph A B C y )
  ) $.
$}

verinab77-update-inner-definition $a |- (
  VERINAB77UpdateInner A B C
) = (
  VERINAB77InnerSetBang A B C
) $.

${
  $d i A B C D $.

  verinab77-outer-set-bang-graph-definition $a |- (
    VERINAB77OuterSetBangGraph A B C D
  ) <-> (
    (
      (
        (
          A e. Word ( Word NN0 )
          /\
          B e. NN0
        )
        /\
        C e. Word NN0
      )
      /\
      D e. Word ( Word NN0 )
    )
    /\
    (
      ( # ` D ) = ( # ` A )
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        ( D ` i ) = if (
          i = B ,
          C ,
          ( A ` i )
        )
    )
  ) $.
$}

${
  $d y A B C $.

  verinab77-outer-set-bang-definition $a |- (
    VERINAB77OuterSetBang A B C
  ) = (
    iota_ y e. Word ( Word NN0 )
      ( VERINAB77OuterSetBangGraph A B C y )
  ) $.
$}

verinab77-precondition-definition $a |- (
  VERINAB77Pre A B C D
) <-> (
  (
    (
      (
        A e. Word ( Word NN0 )
        /\
        B e. NN0
      )
      /\
      C e. NN0
    )
    /\
    D e. NN0
  )
  /\
  (
    B < ( # ` A )
    /\
    C < (
      # ` ( VERINAB77OuterGetBang A B )
    )
  )
) $.

verinab77-program-definition $a |- (
  VERINAB77ModifyArrayElement A B C D
) = (
  VERINAB77OuterSetBang
    A
    B
    (
      VERINAB77UpdateInner
        ( VERINAB77OuterGetBang A B )
        C
        D
    )
) $.

${
  $d i j A B C D E $.

  verinab77-postcondition-definition $a |- (
    VERINAB77Post A B C D E
  ) <-> (
    (
      (
        (
          (
            A e. Word ( Word NN0 )
            /\
            B e. NN0
          )
          /\
          C e. NN0
        )
        /\
        D e. NN0
      )
      /\
      E e. Word ( Word NN0 )
    )
    /\
    (
      ( # ` E ) = ( # ` A )
      /\
      (
        (
          # ` ( VERINAB77OuterGetBang E B )
        ) = (
          # ` ( VERINAB77OuterGetBang A B )
        )
        /\
        (
          A. i e. NN0
            (
              i < ( # ` A )
              ->
              (
                i =/= B
                ->
                (
                  VERINAB77OuterGetBang E i
                ) = (
                  VERINAB77OuterGetBang A i
                )
              )
            )
          /\
          (
            A. j e. NN0
              (
                j < (
                  # ` ( VERINAB77OuterGetBang A B )
                )
                ->
                (
                  j =/= C
                  ->
                  (
                    VERINAB77InnerGetBang
                      ( VERINAB77OuterGetBang E B )
                      j
                  ) = (
                    VERINAB77InnerGetBang
                      ( VERINAB77OuterGetBang A B )
                      j
                  )
                )
              )
            /\
            (
              VERINAB77InnerGetBang
                ( VERINAB77OuterGetBang E B )
                C
            ) = D
          )
        )
      )
    )
  ) $.
$}

verina-basic-77-modify-array-element $a |-
  A. a e. Word ( Word NN0 )
    A. i e. NN0
      A. j e. NN0
        A. v e. NN0
          (
            ( VERINAB77Pre a i j v )
            ->
            (
              VERINAB77Post
                a
                i
                j
                v
                ( VERINAB77ModifyArrayElement a i j v )
            )
          )
$.
