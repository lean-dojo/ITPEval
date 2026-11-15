$(
  Statement-only formalization of the VERINA corpus artifact
  verina_basic_103 (verina__metamath__verina_basic_103), catalog title
  UpdateElements: the exact integer-array program increments index four by
  three and then sets index seven to 516, preserving the array length and all
  other entries under the source size precondition. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number length, w ` i is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete index set.

  VERINAB103GetBang reproduces Lean Array.get! on integer arrays, including
  its default value zero outside the array. VERINAB103SetBangGraph and its
  iota-selected function reproduce Array.set!, including unchanged-array
  behavior at an out-of-range index. VERINAB103UpdateElements composes the
  source updates in order: index four receives the original get!-value plus
  three, then index seven receives 516.

  VERINAB103Pre is the input type and source requirement that the array have
  at least eight entries. VERINAB103Post preserves the source size, updated
  entries, and universal unchanged-entry clause. The proof-valued precondition
  arguments have no computational effect and the postcondition does not
  inspect them, so the final correctness assertion represents them by its
  explicit precondition antecedent. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c
  VERINAB103GetBang
  VERINAB103SetBangGraph VERINAB103SetBang
  VERINAB103UpdateElements VERINAB103Pre VERINAB103Post
$.

verinab103-get-bang-syntax
  $a class ( VERINAB103GetBang A B ) $.
verinab103-set-bang-graph-syntax
  $a wff ( VERINAB103SetBangGraph A B C D ) $.
verinab103-set-bang-syntax
  $a class ( VERINAB103SetBang A B C ) $.
verinab103-program-syntax
  $a class ( VERINAB103UpdateElements A ) $.
verinab103-precondition-syntax
  $a wff ( VERINAB103Pre A ) $.
verinab103-postcondition-syntax
  $a wff ( VERINAB103Post A B ) $.

verinab103-get-bang-definition $a |- (
  VERINAB103GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d i A B C D $.

  verinab103-set-bang-graph-definition $a |- (
    VERINAB103SetBangGraph A B C D
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

  verinab103-set-bang-definition $a |- (
    VERINAB103SetBang A B C
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB103SetBangGraph A B C y )
  ) $.
$}

verinab103-program-definition $a |- (
  VERINAB103UpdateElements A
) = (
  VERINAB103SetBang
    (
      VERINAB103SetBang
        A
        4
        ( ( VERINAB103GetBang A 4 ) + 3 )
    )
    7
    ; ; 5 1 6
) $.

verinab103-precondition-definition $a |- (
  VERINAB103Pre A
) <-> (
  A e. Word ZZ
  /\
  8 <_ ( # ` A )
) $.

${
  $d i A B $.

  verinab103-postcondition-definition $a |- (
    VERINAB103Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      ( # ` B ) = ( # ` A )
      /\
      (
        ( VERINAB103GetBang B 4 )
        =
        ( ( VERINAB103GetBang A 4 ) + 3 )
      )
      /\
      (
        ( VERINAB103GetBang B 7 ) = ; ; 5 1 6
        /\
        A. i e. NN0
          (
            (
              (
                i < ( # ` A )
                /\
                i =/= 4
              )
              /\
              i =/= 7
            )
            ->
            (
              ( VERINAB103GetBang B i )
              =
              ( VERINAB103GetBang A i )
            )
          )
      )
    )
  ) $.
$}

verina-basic-103-update-elements $a |- A. w e. Word ZZ
  (
    ( VERINAB103Pre w )
    ->
    (
      VERINAB103Post
        w
        ( VERINAB103UpdateElements w )
    )
  )
$.
