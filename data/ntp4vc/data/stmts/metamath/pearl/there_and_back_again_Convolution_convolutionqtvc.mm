$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/there_and_back_again_Convolution_convolutionqtvc: the top-level
  symbolic-convolution verification condition for equal-length arbitrary
  finite lists, relating a consumed prefix of the second list to the first
  list paired with the reversed second list. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  U is the source's arbitrary inhabited element type, represented by a
  nonempty set. Word U and Word ( U X. U ) are exactly the full types of
  arbitrary finite zero-based lists of elements and ordered pairs.

  NTP4VCReverse is exact finite-list reversal. NTP4VCZipEq forms the
  pointwise pair word with the length of its first argument. It occurs only
  where the two input lengths are equal: from fact0 in the conclusion and
  from the internal prefix-length equality in the premise. Thus it is exactly
  Why3 combine and the Lean, Rocq, and Isabelle zip operations at every use.

  The source result list C and suffix D remain universally quantified. The
  consumed prefix w remains existentially quantified inside the implication
  premise, preserving its source scope. Every auxiliary $a below is syntax or
  a faithful definitional abbreviation. The final $a declaration is
  Metamath's native unproved statement encoding; this database contains no
  $p declaration.
$)

$c NTP4VCReverse NTP4VCZipEq $.

ntp4vc-reverse-syntax
  $a class ( NTP4VCReverse A ) $.
ntp4vc-zip-equal-syntax
  $a class ( NTP4VCZipEq A B ) $.

${
  $d i A $.

  ntp4vc-reverse-definition $a |- (
    NTP4VCReverse A
  ) = (
    i e. ( 0 ..^ ( # ` A ) ) |->
      ( A ` ( ( ( # ` A ) - 1 ) - i ) )
  ) $.
$}

${
  $d i A B $.

  ntp4vc-zip-equal-definition $a |- (
    NTP4VCZipEq A B
  ) = (
    i e. ( 0 ..^ ( # ` A ) ) |->
      <. ( A ` i ) , ( B ` i ) >.
  ) $.
$}

${
  $d w C D A B U $.

  $( Source arbitrary inhabited carrier alpha and theorem parameters x, y. $)
  ntp4vc-element-carrier-nonempty $e |- U =/= (/) $.
  ntp4vc-x-word $e |- A e. Word U $.
  ntp4vc-y-word $e |- B e. Word U $.

  $( Source assumption fact0. $)
  ntp4vc-fact0 $e |- ( # ` A ) = ( # ` B ) $.

  ntp4vc-pearl-there-and-back-again-convolution-convolution-vc
    $a |- (
      ( # ` A ) <_ ( # ` B )
      /\
      A. C e. Word ( U X. U ) A. D e. Word U
        (
          (
            E. w e. Word U
              (
                B = ( w ++ D )
                /\
                (
                  ( # ` w ) = ( # ` A )
                  /\
                  C = (
                    NTP4VCZipEq A ( NTP4VCReverse w )
                  )
                )
              )
          )
          ->
          C = (
            NTP4VCZipEq A ( NTP4VCReverse B )
          )
        )
    ) $.
$}
