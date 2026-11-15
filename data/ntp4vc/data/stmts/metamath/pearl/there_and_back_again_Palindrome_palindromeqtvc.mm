$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/there_and_back_again_Palindrome_palindromeqtvc: the palindrome
  verification condition for arbitrary finite lists, including its
  length bound, preservation of the palindrome predicate, and rejection
  from a mismatching symmetric pair. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  D is the source's arbitrary inhabited element type, represented by a
  nonempty set. Word D is exactly the full type of arbitrary finite
  zero-based lists over D.

  NTP4VCPal is the source integer-indexed palindrome predicate.
  NTP4VCMismatch is its displayed existential counterexample. Every indexed
  access occurs under the source bounds; those bounds also put the reflected
  index in range, so Word application is exactly the source option lookup.
  NTP4VCSplit retains both the universally quantified suffix and the
  internally existentially quantified prefix from the source statement.

  Expanding the definitions gives the original verification condition and
  the agreeing Lean, Rocq, and Isabelle exports: the reflexive length bound,
  the universally quantified implication preserving palindromicity, and the
  implication from a symmetric mismatch to non-palindromicity. Every
  auxiliary $a below is syntax or a faithful definitional abbreviation. The
  final $a declaration is Metamath's native unproved statement encoding; this
  database contains no $p declaration.
$)

$c NTP4VCPal NTP4VCMismatch NTP4VCSplit NTP4VCMain $.

ntp4vc-pal-syntax
  $a wff ( NTP4VCPal A B ) $.
ntp4vc-mismatch-syntax
  $a wff ( NTP4VCMismatch A B ) $.
ntp4vc-split-syntax
  $a wff ( NTP4VCSplit A B C ) $.
ntp4vc-main-syntax
  $a wff ( NTP4VCMain A B ) $.

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
  $d w A B C $.

  ntp4vc-split-definition $a |- (
    NTP4VCSplit A B C
  ) <-> (
    E. w e. Word C
      (
        ( # ` w ) = ( # ` A )
        /\
        A = ( w ++ B )
      )
  ) $.
$}

${
  $d o A B $.

  ntp4vc-main-definition $a |- (
    NTP4VCMain A B
  ) <-> (
    ( # ` A ) <_ ( # ` A )
    /\
    (
      A. o e. Word B
        (
          (
            ( NTP4VCSplit A o B )
            /\
            ( NTP4VCPal A ( # ` A ) )
          )
          ->
          ( NTP4VCPal A ( # ` A ) )
        )
      /\
      (
        ( NTP4VCMismatch A ( # ` A ) )
        ->
        -. ( NTP4VCPal A ( # ` A ) )
      )
    )
  ) $.
$}

${
  $( Source declarations: A=x and B=elt. $)
  ntp4vc-element-carrier-nonempty $e |- B =/= (/) $.
  ntp4vc-x-word $e |- A e. Word B $.

  ntp4vc-pearl-there-and-back-again-palindrome-palindrome-vc
    $a |- ( NTP4VCMain A B ) $.
$}
