$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/there_and_back_again_Palindrome_palindrome_recqtvc: the recursive
  palindrome-checking verification condition for arbitrary finite lists,
  including the success postcondition and propagation of a mismatching
  symmetric pair through the nested list cases. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  D is the source's arbitrary inhabited element type, represented by a
  nonempty set. Word D is exactly the full type of arbitrary finite
  zero-based lists over D. C is the source equality predicate, represented
  by a total Boolean-valued function on D X. D; its essential hypothesis is
  the complete source specification that it returns true exactly on equal
  elements.

  NTP4VCPal is the source integer-indexed palindrome predicate.
  NTP4VCMismatch is its displayed existential counterexample. Every indexed
  access occurs under the source bounds, and each use has the corresponding
  source length bound, so Word application is exactly the source option
  lookup at those indices.

  NTP4VCOutcome is the normal recursive postcondition: an internally
  quantified consumed prefix has the required length, the original list is
  that prefix appended to the returned suffix, and the inspected prefix is
  palindromic. NTP4VCO1Case, NTP4VCOneCase, NTP4VCManyCase, and
  NTP4VCNonemptyCase expand the source list matches into exhaustive empty
  and internally quantified head-tail cases. No match witness or recursive
  result is moved to an external parameter.

  Expanding the definitions gives the original Why3 verification condition
  and the agreeing Lean, Rocq, and Isabelle exports. Every auxiliary $a
  below is syntax or a faithful definitional abbreviation. The final $a
  declaration is Metamath's native unproved statement encoding; this
  database contains no $p declaration.
$)

$c
  NTP4VCPal NTP4VCMismatch NTP4VCOutcome NTP4VCO1Case
  NTP4VCOneCase NTP4VCManyCase NTP4VCNonemptyCase NTP4VCMain
$.

ntp4vc-pal-syntax
  $a wff ( NTP4VCPal A B ) $.
ntp4vc-mismatch-syntax
  $a wff ( NTP4VCMismatch A B ) $.
ntp4vc-outcome-syntax
  $a wff ( NTP4VCOutcome A B C D ) $.
ntp4vc-o1-case-syntax
  $a wff ( NTP4VCO1Case A B C D E F ) $.
ntp4vc-one-case-syntax
  $a wff ( NTP4VCOneCase A B C ) $.
ntp4vc-many-case-syntax
  $a wff ( NTP4VCManyCase A B C D E ) $.
ntp4vc-nonempty-case-syntax
  $a wff ( NTP4VCNonemptyCase A B C D ) $.
ntp4vc-main-syntax
  $a wff ( NTP4VCMain A B C D ) $.

${
  $d i A B $.

  ntp4vc-pal-definition $a |- (
    NTP4VCPal A B
  ) <-> (
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < B
        )
        ->
        ( A ` i ) = ( A ` ( ( B - 1 ) - i ) )
      )
  ) $.
$}

${
  $d i A B $.

  ntp4vc-mismatch-definition $a |- (
    NTP4VCMismatch A B
  ) <-> (
    E. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < B
        )
        /\
        ( A ` i ) =/= ( A ` ( ( B - 1 ) - i ) )
      )
  ) $.
$}

${
  $d w A B C D $.

  ntp4vc-outcome-definition $a |- (
    NTP4VCOutcome A B C D
  ) <-> (
    (
      E. w e. Word D
        (
          ( # ` w ) = ( # ` A )
          /\
          B = ( w ++ C )
        )
    )
    /\
    ( NTP4VCPal B ( # ` A ) )
  ) $.
$}

${
  $d h t A B C D E F $.

  $(
    A is the original y, B is the original x, C is x's head,
    D is the recursive result o1, E is the equality function, and F is the
    element carrier. The empty o1 branch is false, so this internal
    nonempty decomposition is exactly the source match on o1.
  $)
  ntp4vc-o1-case-definition $a |- (
    NTP4VCO1Case A B C D E F
  ) <-> (
    E. h e. F E. t e. Word F
      (
        D = ( <" h "> ++ t )
        /\
        (
          (
            ( E ` <. C , h >. ) = 1
            <->
            C = h
          )
          ->
          (
            (
              ( E ` <. C , h >. ) = 1
              /\
              ( NTP4VCOutcome A B t F )
            )
            \/
            (
              ( E ` <. C , h >. ) =/= 1
              /\
              ( NTP4VCMismatch B ( # ` A ) )
            )
          )
        )
      )
  ) $.
$}

${
  $d h t A B C $.

  $(
    A is the one-element y, B is x, and C is the element carrier.
    The source empty-x branch is false.
  $)
  ntp4vc-one-case-definition $a |- (
    NTP4VCOneCase A B C
  ) <-> (
    E. h e. C E. t e. Word C
      (
        B = ( <" h "> ++ t )
        /\
        ( NTP4VCOutcome A B t C )
      )
  ) $.
$}

${
  $d h o t A B C D E $.

  $(
    A is the original y, B is the original x, C is the tail after the
    first two y elements, D is the equality function, and E is the carrier.
    The source empty-x branch is false. The repeated inner match on x is
    retained as the definitional tail equality t = t.
  $)
  ntp4vc-many-case-definition $a |- (
    NTP4VCManyCase A B C D E
  ) <-> (
    E. h e. E E. t e. Word E
      (
        B = ( <" h "> ++ t )
        /\
        (
          (
            (
              t = t
              /\
              ( # ` C ) <_ ( # ` t )
            )
            /\
            A. o e. Word E
              (
                ( NTP4VCOutcome C t o E )
                ->
                ( NTP4VCO1Case A B h o D E )
              )
          )
          /\
          (
            ( NTP4VCMismatch t ( # ` C ) )
            ->
            ( NTP4VCMismatch B ( # ` A ) )
          )
        )
      )
  ) $.
$}

${
  $d h k s t A B C D $.

  $(
    A is y, B is x, C is the equality function, and D is the carrier.
    h,t are y's first head and tail; k,s are the second head and remaining
    tail in the at-least-two-element branch.
  $)
  ntp4vc-nonempty-case-definition $a |- (
    NTP4VCNonemptyCase A B C D
  ) <-> (
    E. h e. D E. t e. Word D
      (
        A = ( <" h "> ++ t )
        /\
        (
          (
            t = (/)
            /\
            ( NTP4VCOneCase A B D )
          )
          \/
          E. k e. D E. s e. Word D
            (
              t = ( <" k "> ++ s )
              /\
              ( NTP4VCManyCase A B s C D )
            )
        )
      )
  ) $.
$}

ntp4vc-main-definition $a |- (
  NTP4VCMain A B C D
) <-> (
  (
    A = (/)
    /\
    ( NTP4VCOutcome A B B D )
  )
  \/
  ( NTP4VCNonemptyCase A B C D )
) $.

${
  $d u v A B C D $.

  $( Source declarations: A=y, B=x, C=eq, and D=elt. $)
  ntp4vc-element-carrier-nonempty $e |- D =/= (/) $.
  ntp4vc-y-word $e |- A e. Word D $.
  ntp4vc-x-word $e |- B e. Word D $.
  ntp4vc-equality-function $e |- C e. ( 2 ^m ( D X. D ) ) $.

  ntp4vc-equality-specification $e |- A. u e. D A. v e. D
    (
      ( C ` <. u , v >. ) = 1
      <->
      u = v
    ) $.

  $( Source assumption fact0. $)
  ntp4vc-fact0 $e |- ( # ` A ) <_ ( # ` B ) $.

  ntp4vc-pearl-there-and-back-again-palindrome-palindrome-rec-vc
    $a |- ( NTP4VCMain A B C D ) $.
$}
