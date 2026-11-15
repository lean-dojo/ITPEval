$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/dyck_Check_is_dyckqtvc: the Dyck-word checking verification
  condition characterizes acceptance from the unique Dyck prefix whose
  suffix does not begin with a left parenthesis, and rejects a word when no
  such decomposition exists. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Parentheses are represented exactly by SetMM's two-element carrier 2, with
  L = 0 and R = 1. Thus Word 2 is precisely the source type of arbitrary
  finite parenthesis lists. NTP4VCWrap p s is the source Dyck constructor
  L :: (p ++ R :: s).

  D is exactly the source inductive predicate dyck, represented as a subset
  of Word 2. Empty-word closure, constructor closure, and the displayed
  structural-induction principle characterize D as the least constructor-
  closed subset, excluding both missing Dyck words and extraneous words.

  NTP4VCFall and NTP4VCUnique directly encode the source fall predicate and
  uniqueness of its decomposition. NTP4VCResultCase expands the source match
  on o1, with Booleans represented exactly by 2, false = 0, and true = 1.
  NTP4VCNoFall directly encodes absence of any fall decomposition. Source
  list matches are expanded into exhaustive empty and nonempty word cases;
  wildcard heads retain their full carrier 2. Every word and Boolean
  quantifier remains at its source scope. Proposition equality in the Lean
  and Rocq sources is rendered by its bidirectional logical equivalent, as
  made explicit by the Isabelle ground truth. The final $a declaration is
  Metamath's native unproved statement encoding; this database contains no
  $p proof declaration.
$)

$c
  NTP4VCWrap NTP4VCFall NTP4VCUnique
  NTP4VCResultCase NTP4VCNoFall
$.

ntp4vc-wrap-syntax
  $a class ( NTP4VCWrap A B ) $.
ntp4vc-fall-syntax
  $a wff ( NTP4VCFall A B C ) $.
ntp4vc-unique-syntax
  $a wff ( NTP4VCUnique A B C D ) $.
ntp4vc-result-case-syntax
  $a wff ( NTP4VCResultCase A B ) $.
ntp4vc-no-fall-syntax
  $a wff ( NTP4VCNoFall A B ) $.

ntp4vc-wrap-definition $a |- (
  NTP4VCWrap A B
) = (
  <" 0 "> ++ ( A ++ ( <" 1 "> ++ B ) )
) $.

${
  $d t A B C $.

  ntp4vc-fall-definition $a |- (
    ( NTP4VCFall A B C )
    <->
    (
      A e. C
      /\
      (
        B = (/)
        \/
        E. t e. Word 2
          B = ( <" 1 "> ++ t )
      )
    )
  ) $.
$}

${
  $d p s A B C D $.

  ntp4vc-unique-definition $a |- (
    ( NTP4VCUnique A B C D )
    <->
    A. p e. Word 2 A. s e. Word 2
      (
        (
          A = ( p ++ s )
          /\
          ( NTP4VCFall p s D )
        )
        ->
        (
          p = B
          /\
          s = C
        )
      )
  ) $.
$}

${
  $d h t A B $.

  ntp4vc-result-case-definition $a |- (
    ( NTP4VCResultCase A B )
    <->
    (
      (
        A = (/)
        /\
        B = 1
      )
      \/
      E. h e. 2 E. t e. Word 2
        (
          A = ( <" h "> ++ t )
          /\
          B = 0
        )
    )
  ) $.
$}

${
  $d p s A B $.

  ntp4vc-no-fall-definition $a |- (
    ( NTP4VCNoFall A B )
    <->
    A. p e. Word 2 A. s e. Word 2
      (
        A = ( p ++ s )
        ->
        -. ( NTP4VCFall p s B )
      )
  ) $.
$}

${
  $d p q r s A B D $.

  $( Exact least fixed-point presentation of the source dyck predicate. $)
  ntp4vc-dyck-subset $e |- D C_ Word 2 $.

  ntp4vc-dyck-empty $e |- (/) e. D $.

  ntp4vc-dyck-constructor $e |- A. p e. D A. s e. D
    ( NTP4VCWrap p s ) e. D $.

  ntp4vc-dyck-structural-induction $e |- A. q e. ~P D
    (
      (
        (/) e. q
        /\
        A. p e. D A. s e. D
          (
            (
              p e. q
              /\
              s e. q
            )
            ->
            ( NTP4VCWrap p s ) e. q
          )
      )
      ->
      q = D
    ) $.

  $( Source theorem parameters A=w and B=o2. $)
  ntp4vc-w-word $e |- A e. Word 2 $.
  ntp4vc-o2-word $e |- B e. Word 2 $.

  ntp4vc-pearl-dyck-check-is-dyck-vc $a |- (
    (
      A. p e. Word 2
        (
          (
            A = ( B ++ p )
            /\
            (
              ( NTP4VCFall B p D )
              /\
              ( NTP4VCUnique A B p D )
            )
          )
          ->
          A. r e. 2
            (
              ( NTP4VCResultCase p r )
              ->
              (
                r = 1
                <->
                A e. D
              )
            )
        )
    )
    /\
    (
      ( NTP4VCNoFall A D )
      ->
      -. A e. D
    )
  ) $.
$}
