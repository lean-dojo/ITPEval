$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_36 (verina__metamath__verina_advanced_36), catalog title
  majorityElement: the exact Boyer-Moore-style candidate and counter scan
  returns a natural number occurring more than half the length of an
  arbitrary nonempty finite natural-number list that has a majority element.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain, and Word NN0 is exactly the
  type of arbitrary finite natural-number lists. For a word w, # ` w is its
  natural-number length, w ` k is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete index set.

  VERINA36CountOccurrences is the source countOccurrences recursion,
  extensionally represented by the number of input positions equal to the
  target. VERINA36None, VERINA36Some, and VERINA36OptionNat give a disjoint
  tagged encoding of Option Nat.

  VERINA36FindStep is exactly one nonempty-list branch of findCandidate. With
  no candidate it installs the current input and count one. With some
  candidate, equality increments the count; inequality replaces the
  candidate at count zero, and otherwise decrements the count while retaining
  the candidate. VERINA36FindCandidateGraph records the option and count
  before and after every input entry and applies the source empty-list return:
  the final candidate value, or zero for none. This gives the exact helper
  computation for arbitrary typed list, initial candidate, and initial count.
  VERINA36FindCandidate selects its unique output, and
  VERINA36MajorityElement calls it with none and zero exactly as the source
  executable implementation does.

  VERINA36Pre is exactly positive length together with List.any of a value
  whose occurrence count exceeds floor(length / 2). VERINA36Post is exactly
  that same strict count bound for the returned result. The proof-valued
  precondition argument is computationally and propositionally unused and is
  omitted from the target function and postcondition. The final $a
  declaration is the source correctness proposition. Every earlier $a is
  syntax or a faithful definition, and this database has no $p declaration.
$)

$c
  VERINA36CountOccurrences
  VERINA36None VERINA36Some VERINA36OptionNat
  VERINA36FindStep
  VERINA36FindCandidateGraph VERINA36FindCandidate
  VERINA36MajorityElement
  VERINA36Pre VERINA36Post
$.

verina36-count-occurrences-syntax
  $a class ( VERINA36CountOccurrences A B ) $.
verina36-none-syntax
  $a class VERINA36None $.
verina36-some-syntax
  $a class ( VERINA36Some A ) $.
verina36-option-nat-syntax
  $a class VERINA36OptionNat $.
verina36-find-step-syntax
  $a wff ( VERINA36FindStep A B C D E ) $.
verina36-find-candidate-graph-syntax
  $a wff ( VERINA36FindCandidateGraph A B C D ) $.
verina36-find-candidate-syntax
  $a class ( VERINA36FindCandidate A B C ) $.
verina36-majority-element-syntax
  $a class ( VERINA36MajorityElement A ) $.
verina36-precondition-syntax
  $a wff ( VERINA36Pre A ) $.
verina36-postcondition-syntax
  $a wff ( VERINA36Post A B ) $.

${
  $d k A B $.

  verina36-count-occurrences-definition $a |- (
    VERINA36CountOccurrences A B
  ) = (
    # ` {
      k e. ( 0 ..^ ( # ` B ) )
      |
      ( B ` k ) = A
    }
  ) $.
$}

verina36-none-definition $a |- VERINA36None = (/) $.

verina36-some-definition $a |- (
  VERINA36Some A
) = <. 1 , A >. $.

${
  $d x y $.

  verina36-option-nat-definition $a |- VERINA36OptionNat =
    { x |
      (
        x = VERINA36None
        \/
        E. y e. NN0 x = ( VERINA36Some y )
      )
    } $.
$}

${
  $d c A B C D E $.

  verina36-find-step-definition $a |- (
    VERINA36FindStep A B C D E
  ) <-> (
    (
      (
        (
          (
            A e. NN0
            /\
            B e. VERINA36OptionNat
          )
          /\
          C e. NN0
        )
        /\
        D e. VERINA36OptionNat
      )
      /\
      E e. NN0
    )
    /\
    (
      (
        B = VERINA36None
        /\
        (
          D = ( VERINA36Some A )
          /\
          E = 1
        )
      )
      \/
      E. c e. NN0
        (
          B = ( VERINA36Some c )
          /\
          (
            (
              A = c
              /\
              (
                D = ( VERINA36Some c )
                /\
                E = ( C + 1 )
              )
            )
            \/
            (
              (
                A =/= c
                /\
                C = 0
              )
              /\
              (
                D = ( VERINA36Some A )
                /\
                E = 1
              )
            )
            \/
            (
              (
                A =/= c
                /\
                C =/= 0
              )
              /\
              (
                D = ( VERINA36Some c )
                /\
                E = ( C - 1 )
              )
            )
          )
        )
    )
  ) $.
$}

${
  $d c k o q A B C D $.

  verina36-find-candidate-graph-definition $a |- (
    VERINA36FindCandidateGraph A B C D
  ) <-> (
    (
      (
        (
          A e. Word NN0
          /\
          B e. VERINA36OptionNat
        )
        /\
        C e. NN0
      )
      /\
      D e. NN0
    )
    /\
    E. o e. Word VERINA36OptionNat
      E. q e. Word NN0
        (
          (
            (
              ( # ` o ) = ( ( # ` A ) + 1 )
              /\
              ( # ` q ) = ( ( # ` A ) + 1 )
            )
            /\
            (
              ( o ` 0 ) = B
              /\
              ( q ` 0 ) = C
            )
          )
          /\
          (
            A. k e. ( 0 ..^ ( # ` A ) )
              (
                VERINA36FindStep
                  ( A ` k )
                  ( o ` k )
                  ( q ` k )
                  ( o ` ( k + 1 ) )
                  ( q ` ( k + 1 ) )
              )
            /\
            (
              (
                ( o ` ( # ` A ) ) = VERINA36None
                /\
                D = 0
              )
              \/
              E. c e. NN0
                (
                  ( o ` ( # ` A ) ) = ( VERINA36Some c )
                  /\
                  D = c
                )
            )
          )
        )
  ) $.
$}

${
  $d y A B C $.

  verina36-find-candidate-definition $a |- (
    VERINA36FindCandidate A B C
  ) = (
    iota_ y e. NN0
      ( VERINA36FindCandidateGraph A B C y )
  ) $.
$}

verina36-majority-element-definition $a |- (
  VERINA36MajorityElement A
) = (
  VERINA36FindCandidate A VERINA36None 0
) $.

${
  $d i A $.

  verina36-precondition-definition $a |- (
    VERINA36Pre A
  ) <-> (
    (
      A e. Word NN0
      /\
      0 < ( # ` A )
    )
    /\
    E. i e. ( 0 ..^ ( # ` A ) )
      (
        |_ ` ( ( # ` A ) / 2 )
      ) < (
        VERINA36CountOccurrences
          ( A ` i )
          A
      )
  ) $.
$}

verina36-postcondition-definition $a |- (
  VERINA36Post A B
) <-> (
  (
    A e. Word NN0
    /\
    B e. NN0
  )
  /\
  (
    |_ ` ( ( # ` A ) / 2 )
  ) < (
    VERINA36CountOccurrences B A
  )
) $.

verina-advanced-36-majority-element
  $a |- A. w e. Word NN0
    (
      ( VERINA36Pre w )
      ->
      (
        VERINA36Post
          w
          ( VERINA36MajorityElement w )
      )
    )
  $.
