$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_22 (verina__metamath__verina_advanced_22), catalog title
  isPeakValley: an executable scan decides whether an arbitrary finite
  integer list strictly increases and then strictly decreases, with both
  phases nonempty, together with its Boolean correctness contract. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, Word ZZ is exactly the type of
  arbitrary finite integer lists, and { 0 , 1 } represents Bool with false
  = 0 and true = 1. For a word w, # ` w is its length, w ` k is zero-based
  lookup, and 0 ..^ ( # ` w ) is its complete index set.

  VERINA22State is the pair (increasing, startedDecreasing) used by the
  source local aux function. VERINA22Continue is exactly a recursive branch:
  a strict increase continues only before decreasing has started and sets
  increasing to true, while a strict decrease continues only after an
  increase and sets startedDecreasing to true. VERINA22Stop is exactly
  either the short-list base case, returning the conjunction of the two
  state bits, or an equal/out-of-order comparison that returns false.
  VERINA22AuxGraph records the complete finite execution trace, and
  VERINA22Aux selects its unique Boolean result. VERINA22IsPeakValley starts
  that executable helper with both state bits false.

  VERINA22PeakAt is the predicate used by the source List.range filter.
  VERINA22ValidPeaksGraph retains exactly those indices, in increasing range
  order, and VERINA22ValidPeaks is therefore the exact filtered list.
  VERINA22Pre is the source True precondition together with the List Int
  input type. VERINA22Post reproduces both implications involving nonempty
  validPeaks and zero validPeaks length. The proof-valued precondition
  argument is computationally unused and is omitted from the target
  function. The final $a declaration is the source correctness proposition.
  Every earlier $a is syntax or a faithful definition, and this database
  has no $p declaration.
$)

$c
  VERINA22State
  VERINA22Continue VERINA22Stop
  VERINA22AuxGraph VERINA22Aux
  VERINA22Pre VERINA22IsPeakValley
  VERINA22PeakAt
  VERINA22ValidPeaksGraph VERINA22ValidPeaks
  VERINA22Post
$.

verina22-state-syntax
  $a class VERINA22State $.
verina22-continue-syntax
  $a wff ( VERINA22Continue A B C D ) $.
verina22-stop-syntax
  $a wff ( VERINA22Stop A B C D ) $.
verina22-aux-graph-syntax
  $a wff ( VERINA22AuxGraph A B C ) $.
verina22-aux-syntax
  $a class ( VERINA22Aux A B ) $.
verina22-precondition-syntax
  $a wff ( VERINA22Pre A ) $.
verina22-is-peak-valley-syntax
  $a class ( VERINA22IsPeakValley A ) $.
verina22-peak-at-syntax
  $a wff ( VERINA22PeakAt A B ) $.
verina22-valid-peaks-graph-syntax
  $a wff ( VERINA22ValidPeaksGraph A B ) $.
verina22-valid-peaks-syntax
  $a class ( VERINA22ValidPeaks A ) $.
verina22-postcondition-syntax
  $a wff ( VERINA22Post A B ) $.

verina22-state-definition $a |- VERINA22State = (
  { 0 , 1 } X. { 0 , 1 }
) $.

verina22-continue-definition $a |- (
  VERINA22Continue A B C D
) <-> (
  (
    (
      A e. Word ZZ
      /\
      B e. NN0
    )
    /\
    (
      C e. VERINA22State
      /\
      D e. VERINA22State
    )
  )
  /\
  (
    ( B + 1 ) < ( # ` A )
    /\
    (
      (
        (
          ( A ` B ) < ( A ` ( B + 1 ) )
          /\
          ( 2nd ` C ) = 0
        )
        /\
        D = <. 1 , 0 >.
      )
      \/
      (
        (
          ( A ` B ) > ( A ` ( B + 1 ) )
          /\
          ( 1st ` C ) = 1
        )
        /\
        D = <. 1 , 1 >.
      )
    )
  )
) $.

verina22-stop-definition $a |- (
  VERINA22Stop A B C D
) <-> (
  (
    (
      A e. Word ZZ
      /\
      B e. NN0
    )
    /\
    (
      C e. VERINA22State
      /\
      D e. { 0 , 1 }
    )
  )
  /\
  (
    (
      (
        ( # ` A ) <_ ( B + 1 )
        /\
        (
          ( 1st ` C ) = 1
          /\
          ( 2nd ` C ) = 1
        )
      )
      /\
      D = 1
    )
    \/
    (
      (
        ( # ` A ) <_ ( B + 1 )
        /\
        (
          ( 1st ` C ) = 0
          \/
          ( 2nd ` C ) = 0
        )
      )
      /\
      D = 0
    )
    \/
    (
      (
        ( B + 1 ) < ( # ` A )
        /\
        (
          ( A ` B ) = ( A ` ( B + 1 ) )
          \/
          (
            ( A ` B ) < ( A ` ( B + 1 ) )
            /\
            ( 2nd ` C ) = 1
          )
          \/
          (
            ( A ` B ) > ( A ` ( B + 1 ) )
            /\
            ( 1st ` C ) = 0
          )
        )
      )
      /\
      D = 0
    )
  )
) $.

${
  $d i k t A B C $.

  verina22-aux-graph-definition $a |- (
    VERINA22AuxGraph A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. VERINA22State
      )
      /\
      C e. { 0 , 1 }
    )
    /\
    E. k e. NN0 E. t e. Word VERINA22State
      (
        (
          ( # ` t ) = ( k + 1 )
          /\
          ( t ` 0 ) = B
        )
        /\
        (
          A. i e. ( 0 ..^ k )
            (
              VERINA22Continue
                A
                i
                ( t ` i )
                ( t ` ( i + 1 ) )
            )
          /\
          (
            VERINA22Stop
              A
              k
              ( t ` k )
              C
          )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verina22-aux-definition $a |- (
    VERINA22Aux A B
  ) = (
    iota_ y e. { 0 , 1 }
      ( VERINA22AuxGraph A B y )
  ) $.
$}

verina22-precondition-definition $a |- (
  VERINA22Pre A
) <-> (
  A e. Word ZZ
) $.

verina22-is-peak-valley-definition $a |- (
  VERINA22IsPeakValley A
) = (
  VERINA22Aux A <. 0 , 0 >.
) $.

${
  $d i A B $.

  verina22-peak-at-definition $a |- (
    VERINA22PeakAt A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. ( 0 ..^ ( # ` A ) )
    )
    /\
    (
      (
        1 <_ B
        /\
        B < ( ( # ` A ) - 1 )
      )
      /\
      (
        A. i e. ( 0 ..^ B )
          ( A ` i ) < ( A ` ( i + 1 ) )
        /\
        A. i e. (
          0 ..^ ( ( ( # ` A ) - 1 ) - B )
        )
          (
            A ` ( B + i )
          ) > (
            A ` ( ( B + i ) + 1 )
          )
      )
    )
  ) $.
$}

${
  $d i j p A B $.

  verina22-valid-peaks-graph-definition $a |- (
    VERINA22ValidPeaksGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word NN0
    )
    /\
    (
      (
        A. i e. ( 0 ..^ ( # ` B ) )
          ( VERINA22PeakAt A ( B ` i ) )
        /\
        A. i e. ( 0 ..^ ( # ` B ) )
          A. j e. ( 0 ..^ ( # ` B ) )
            (
              i < j
              ->
              ( B ` i ) < ( B ` j )
            )
      )
      /\
      A. p e. ( 0 ..^ ( # ` A ) )
        (
          ( VERINA22PeakAt A p )
          ->
          E. i e. ( 0 ..^ ( # ` B ) )
            ( B ` i ) = p
        )
    )
  ) $.
$}

${
  $d y A $.

  verina22-valid-peaks-definition $a |- (
    VERINA22ValidPeaks A
  ) = (
    iota_ y e. Word NN0
      ( VERINA22ValidPeaksGraph A y )
  ) $.
$}

verina22-postcondition-definition $a |- (
  VERINA22Post A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. { 0 , 1 }
  )
  /\
  (
    (
      ( VERINA22ValidPeaks A ) =/= (/)
      ->
      B = 1
    )
    /\
    (
      ( # ` ( VERINA22ValidPeaks A ) ) = 0
      ->
      B = 0
    )
  )
) $.

verina-advanced-22-is-peak-valley
  $a |- A. w e. Word ZZ
    (
      ( VERINA22Pre w )
      ->
      (
        VERINA22Post
          w
          ( VERINA22IsPeakValley w )
      )
    )
  $.
