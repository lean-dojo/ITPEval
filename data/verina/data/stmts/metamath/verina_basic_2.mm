$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_2
  (verina__metamath__verina_basic_2), catalog title findSmallest: the exact
  executable minimum scan returns none for an empty natural-number array and
  otherwise returns an element no greater than any array entry. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain, and Word NN0 is exactly the
  type of arbitrary finite natural-number arrays after the source s.toList
  conversion. For a word w, # ` w is its length, w ` k is zero-based lookup,
  and 0 ..^ ( # ` w ) is its complete index set.

  VERINAB2None and VERINAB2Some give a disjoint tagged representation of
  Option Nat. VERINAB2MinStep is one exact executable scan step: none becomes
  some of the current entry, while some c becomes some of the smaller of c
  and the current entry. VERINAB2MinGraph records every option state of this
  left-to-right scan, beginning with none, so it characterizes List.min?
  exactly on every finite natural-number list. VERINAB2ListMin selects its
  unique graph output, and VERINAB2FindSmallest is the source executable
  implementation after Array.toList.

  VERINAB2Pre is the source True precondition together with the Array Nat
  input type. VERINAB2Post is the exact source match: none requires the empty
  list; some r requires membership and r <= every list element. The
  proof-valued precondition argument is computationally and propositionally
  unused and is represented by the explicit precondition antecedent in the
  final correctness statement. Every earlier $a is syntax or a faithful
  definition, and this database has no $p declaration.
$)

$c
  VERINAB2None VERINAB2Some VERINAB2OptionNat
  VERINAB2MinStep VERINAB2MinGraph VERINAB2ListMin
  VERINAB2Pre VERINAB2FindSmallest VERINAB2Post
$.

verinab2-none-syntax
  $a class VERINAB2None $.
verinab2-some-syntax
  $a class ( VERINAB2Some A ) $.
verinab2-option-nat-syntax
  $a class VERINAB2OptionNat $.
verinab2-min-step-syntax
  $a wff ( VERINAB2MinStep A B C ) $.
verinab2-min-graph-syntax
  $a wff ( VERINAB2MinGraph A B ) $.
verinab2-list-min-syntax
  $a class ( VERINAB2ListMin A ) $.
verinab2-precondition-syntax
  $a wff ( VERINAB2Pre A ) $.
verinab2-find-smallest-syntax
  $a class ( VERINAB2FindSmallest A ) $.
verinab2-postcondition-syntax
  $a wff ( VERINAB2Post A B ) $.

verinab2-none-definition $a |- VERINAB2None = (/) $.

verinab2-some-definition $a |- (
  VERINAB2Some A
) = <. 1 , A >. $.

${
  $d x y $.

  verinab2-option-nat-definition $a |- VERINAB2OptionNat =
    { x |
      (
        x = VERINAB2None
        \/
        E. y e. NN0 x = ( VERINAB2Some y )
      )
    } $.
$}

${
  $d c A B C $.

  verinab2-min-step-definition $a |- (
    VERINAB2MinStep A B C
  ) <-> (
    (
      (
        A e. NN0
        /\
        B e. VERINAB2OptionNat
      )
      /\
      C e. VERINAB2OptionNat
    )
    /\
    (
      (
        B = VERINAB2None
        /\
        C = ( VERINAB2Some A )
      )
      \/
      E. c e. NN0
        (
          B = ( VERINAB2Some c )
          /\
          C = (
            VERINAB2Some
              if ( A < c , A , c )
          )
        )
    )
  ) $.
$}

${
  $d k t A B $.

  verinab2-min-graph-definition $a |- (
    VERINAB2MinGraph A B
  ) <-> (
    (
      A e. Word NN0
      /\
      B e. VERINAB2OptionNat
    )
    /\
    E. t e. Word VERINAB2OptionNat
      (
        (
          ( # ` t ) = ( ( # ` A ) + 1 )
          /\
          ( t ` 0 ) = VERINAB2None
        )
        /\
        (
          A. k e. ( 0 ..^ ( # ` A ) )
            (
              VERINAB2MinStep
                ( A ` k )
                ( t ` k )
                ( t ` ( k + 1 ) )
            )
          /\
          B = ( t ` ( # ` A ) )
        )
      )
  ) $.
$}

${
  $d y A $.

  verinab2-list-min-definition $a |- (
    VERINAB2ListMin A
  ) = (
    iota_ y e. VERINAB2OptionNat
      ( VERINAB2MinGraph A y )
  ) $.
$}

verinab2-precondition-definition $a |- (
  VERINAB2Pre A
) <-> (
  A e. Word NN0
) $.

verinab2-find-smallest-definition $a |- (
  VERINAB2FindSmallest A
) = (
  VERINAB2ListMin A
) $.

${
  $d i j r A B $.

  verinab2-postcondition-definition $a |- (
    VERINAB2Post A B
  ) <-> (
    (
      A e. Word NN0
      /\
      B e. VERINAB2OptionNat
    )
    /\
    (
      (
        B = VERINAB2None
        /\
        A = (/)
      )
      \/
      E. r e. NN0
        (
          B = ( VERINAB2Some r )
          /\
          (
            E. i e. ( 0 ..^ ( # ` A ) )
              ( A ` i ) = r
            /\
            A. j e. ( 0 ..^ ( # ` A ) )
              r <_ ( A ` j )
          )
        )
    )
  ) $.
$}

verina-basic-2-find-smallest $a |- A. w e. Word NN0
  (
    ( VERINAB2Pre w )
    ->
    (
      VERINAB2Post
        w
        ( VERINAB2FindSmallest w )
    )
  )
$.
