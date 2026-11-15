$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/there_and_back_again_Convolution_convolution_recqtvc: the recursive
  symbolic-convolution verification condition requires a sufficiently long
  second list, establishes that the recursive remainder is nonempty, and
  reconstructs the paired result using a reversed consumed prefix. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  U is the arbitrary inhabited source carrier alpha, represented by a
  nonempty set. Word U and Word ( U X. U ) are exactly the full types of
  arbitrary finite zero-based lists of elements and pairs, respectively.

  NTP4VCReverse is exact finite-list reversal. NTP4VCZipEq forms the
  pointwise pair word with the length of its first argument; every occurrence
  is guarded inside NTP4VCPost by equality of the two input lengths, where it
  is exactly Why3 combine and Lean/Rocq/Isabelle zip.

  NTP4VCPost is the recursive function's source postcondition. The source
  list matches are expanded into exhaustive empty and internally quantified
  head-tail cases. NTP4VCNonempty preserves the internal witnesses for the
  required nonempty recursive remainder. NTP4VCConsObligation and
  NTP4VCConsResult only name the two displayed nonempty-match subformulas;
  no match witness is moved to an external parameter.

  Expanding these definitions gives the original Why3 verification condition
  and the agreeing Lean, Rocq, and Isabelle exports. Every auxiliary $a below
  is syntax or a faithful definitional abbreviation. The final $a declaration
  is Metamath's native unproved statement encoding; this database contains no
  $p declaration.
$)

$c
  NTP4VCReverse NTP4VCZipEq NTP4VCPost NTP4VCNonempty
  NTP4VCConsObligation NTP4VCConsResult
$.

ntp4vc-reverse-syntax
  $a class ( NTP4VCReverse A ) $.
ntp4vc-zip-equal-syntax
  $a class ( NTP4VCZipEq A B ) $.
ntp4vc-post-syntax
  $a wff ( NTP4VCPost A B C D E ) $.
ntp4vc-nonempty-syntax
  $a wff ( NTP4VCNonempty A B ) $.
ntp4vc-cons-obligation-syntax
  $a wff ( NTP4VCConsObligation A B C ) $.
ntp4vc-cons-result-syntax
  $a wff ( NTP4VCConsResult A B C D E ) $.

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
  $d w A B C D E $.

  ntp4vc-post-definition $a |- (
    NTP4VCPost A B C D E
  ) <-> (
    E. w e. Word E
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
  ) $.
$}

${
  $d h t A B $.

  ntp4vc-nonempty-definition $a |- (
    NTP4VCNonempty A B
  ) <-> (
    E. h e. B E. t e. Word B
      A = ( <" h "> ++ t )
  ) $.
$}

${
  $d r s t x A B C $.

  ntp4vc-cons-obligation-definition $a |- (
    NTP4VCConsObligation A B C
  ) <-> (
    E. x e. C E. t e. Word C
      (
        A = ( <" x "> ++ t )
        /\
        (
          (
            t = t
            /\
            ( # ` t ) <_ ( # ` B )
          )
          /\
          A. r e. Word ( C X. C ) A. s e. Word C
            (
              ( NTP4VCPost t B r s C )
              ->
              ( NTP4VCNonempty s C )
            )
        )
      )
  ) $.
$}

${
  $d h q s t u x A B C D E $.

  ntp4vc-cons-result-definition $a |- (
    NTP4VCConsResult A B C D E
  ) <-> (
    E. x e. E E. t e. Word E
      (
        A = ( <" x "> ++ t )
        /\
        E. q e. Word ( E X. E ) E. s e. Word E
          (
            ( NTP4VCPost t B q s E )
            /\
            E. h e. E E. u e. Word E
              (
                s = ( <" h "> ++ u )
                /\
                (
                  C = ( <" <. x , h >. "> ++ q )
                  /\
                  D = u
                )
              )
          )
      )
  ) $.
$}

${
  $d r s A B U $.

  $( Source arbitrary inhabited carrier alpha and theorem parameters x, y. $)
  ntp4vc-element-carrier-nonempty $e |- U =/= (/) $.
  ntp4vc-x-word $e |- A e. Word U $.
  ntp4vc-y-word $e |- B e. Word U $.

  $( Source assumption fact0. $)
  ntp4vc-fact0 $e |- ( # ` A ) <_ ( # ` B ) $.

  ntp4vc-pearl-there-and-back-again-convolution-convolution-rec-vc
    $a |- (
      (
        A = (/)
        \/
        ( NTP4VCConsObligation A B U )
      )
      /\
      A. r e. Word ( U X. U ) A. s e. Word U
        (
          (
            (
              A = (/)
              /\
              (
                r = (/)
                /\
                s = B
              )
            )
            \/
            ( NTP4VCConsResult A B r s U )
          )
          ->
          ( NTP4VCPost A B r s U )
        )
    ) $.
$}
