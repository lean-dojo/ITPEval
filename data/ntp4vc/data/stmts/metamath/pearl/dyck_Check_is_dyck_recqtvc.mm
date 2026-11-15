$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/dyck_Check_is_dyck_recqtvc: the recursive Dyck-word checking
  verification condition preserves progress, identifies unique Dyck prefixes
  whose suffix does not begin with a left parenthesis, and propagates failure
  when no such decomposition exists. This file contains no proof.
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

  NTP4VCFall, NTP4VCUnique, and NTP4VCNoFall directly encode the source fall
  predicate, uniqueness of a fall decomposition, and absence of any fall
  decomposition. NTP4VCInner, NTP4VCO1Case, NTP4VCOuter, and NTP4VCBase only
  name subformulas of the verification condition. Source list matches are
  expanded into exhaustive empty, L-headed, and R-headed word cases; wildcard
  heads retain their full carrier 2. All prefix and suffix quantifiers range
  over arbitrary Word 2 values at their original scopes. The final $a
  declaration is Metamath's native unproved statement encoding; this database
  contains no $p proof declaration.
$)

$c
  NTP4VCWrap NTP4VCFall NTP4VCUnique NTP4VCNoFall
  NTP4VCInner NTP4VCO1Case NTP4VCOuter NTP4VCBase
$.

ntp4vc-wrap-syntax
  $a class ( NTP4VCWrap A B ) $.
ntp4vc-fall-syntax
  $a wff ( NTP4VCFall A B C ) $.
ntp4vc-unique-syntax
  $a wff ( NTP4VCUnique A B C D ) $.
ntp4vc-no-fall-syntax
  $a wff ( NTP4VCNoFall A B ) $.
ntp4vc-inner-syntax
  $a wff ( NTP4VCInner A B C D ) $.
ntp4vc-o1-case-syntax
  $a wff ( NTP4VCO1Case A B C D ) $.
ntp4vc-outer-syntax
  $a wff ( NTP4VCOuter A B C ) $.
ntp4vc-base-syntax
  $a wff ( NTP4VCBase A B ) $.

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
  $d p s A B C D $.

  $(
    A=w, B=p0, C=w1, and D is the source dyck predicate.
    The p and s binders are respectively the source p1 and w2.
  $)
  ntp4vc-inner-definition $a |- (
    ( NTP4VCInner A B C D )
    <->
    A. p e. Word 2
      (
        (
          A. s e. Word 2
            (
              (
                C = ( p ++ s )
                /\
                (
                  ( NTP4VCFall p s D )
                  /\
                  ( NTP4VCUnique C p s D )
                )
              )
              ->
              (
                A = ( ( NTP4VCWrap B p ) ++ s )
                /\
                (
                  ( NTP4VCFall ( NTP4VCWrap B p ) s D )
                  /\
                  (
                    NTP4VCUnique
                      A ( NTP4VCWrap B p ) s D
                  )
                )
              )
            )
        )
        /\
        (
          ( NTP4VCNoFall C D )
          ->
          ( NTP4VCNoFall A D )
        )
      )
  ) $.
$}

${
  $d h t A B C D $.

  $(
    A=w, B=p0, C=o1, and D is the source dyck predicate.
    The nonempty case binds the wildcard head h and tail t.
  $)
  ntp4vc-o1-case-definition $a |- (
    ( NTP4VCO1Case A B C D )
    <->
    (
      (
        C = (/)
        /\
        ( NTP4VCNoFall A D )
      )
      \/
      E. h e. 2 E. t e. Word 2
        (
          C = ( <" h "> ++ t )
          /\
          (
            (
              0 <_ ( # ` A )
              /\
              ( # ` t ) < ( # ` A )
            )
            /\
            ( NTP4VCInner A B t D )
          )
        )
    )
  ) $.
$}

${
  $d p s A B C $.

  $(
    A=w, B=w0, and C is the source dyck predicate. The p and s binders
    are respectively the source p0 and o1.
  $)
  ntp4vc-outer-definition $a |- (
    ( NTP4VCOuter A B C )
    <->
    (
      (
        0 <_ ( # ` A )
        /\
        ( # ` B ) < ( # ` A )
      )
      /\
      A. p e. Word 2
        (
          (
            A. s e. Word 2
              (
                (
                  B = ( p ++ s )
                  /\
                  (
                    ( NTP4VCFall p s C )
                    /\
                    ( NTP4VCUnique B p s C )
                  )
                )
                ->
                ( NTP4VCO1Case A p s C )
              )
          )
          /\
          (
            ( NTP4VCNoFall B C )
            ->
            ( NTP4VCNoFall A C )
          )
        )
    )
  ) $.
$}

ntp4vc-base-definition $a |- (
  ( NTP4VCBase A B )
  <->
  (
    A = ( (/) ++ A )
    /\
    (
      ( NTP4VCFall (/) A B )
      /\
      ( NTP4VCUnique A (/) A B )
    )
  )
) $.

${
  $d p q s t A D $.

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

  $( Source theorem parameter A=w. $)
  ntp4vc-w-word $e |- A e. Word 2 $.

  ntp4vc-pearl-dyck-check-is-dyck-rec-vc $a |- (
    (
      E. t e. Word 2
        (
          A = ( <" 0 "> ++ t )
          /\
          ( NTP4VCOuter A t D )
        )
    )
    \/
    (
      (
        A = (/)
        \/
        E. t e. Word 2
          A = ( <" 1 "> ++ t )
      )
      /\
      ( NTP4VCBase A D )
    )
  ) $.
$}
