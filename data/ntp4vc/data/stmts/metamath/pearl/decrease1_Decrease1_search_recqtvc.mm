$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/decrease1_Decrease1_search_recqtvc: the recursive-search verification
  condition preserves the invariant that successive integer-list entries may
  decrease by at most one, proves progress of each recursive call, and carries
  the first-zero search postcondition back to the original index. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  Integer lists are represented exactly by SetMM words over ZZ, hence by
  arbitrary finite zero-based sequences of integers. NTP4VCToNat is the
  source conversion from integers to naturals, and NTP4VCAt is the source
  totalized list lookup with integer default 0.

  NTP4VCDecrease1 directly expands the source decrease1 predicate.
  NTP4VCProgress is the recursive-call variant decrease together with the
  preserved decrease1 predicate and nonnegative next index.
  NTP4VCSearchPost is exactly the source result alternative: either -1 and no
  zero in the remaining suffix, or the first zero at a returned in-bounds
  index. NTP4VCBody and NTP4VCResultCase substitute the let-bound o1 and o2
  values and render proposition-valued source conditionals as exhaustive
  guarded disjunctions. Splitting the typed parameters and the two theorem
  assumptions into scoped essential hypotheses is bidirectionally equivalent
  to the source curried theorem. Every integer and word quantifier retains its
  full source domain. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCInBounds NTP4VCDecrease1
  NTP4VCProgress NTP4VCSearchPost NTP4VCBody NTP4VCResultCase
$.

ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B ) $.
ntp4vc-in-bounds-syntax
  $a wff ( NTP4VCInBounds A B ) $.
ntp4vc-decrease1-syntax
  $a wff ( NTP4VCDecrease1 A ) $.
ntp4vc-progress-syntax
  $a wff ( NTP4VCProgress A B C ) $.
ntp4vc-search-post-syntax
  $a wff ( NTP4VCSearchPost A B C ) $.
ntp4vc-body-syntax
  $a wff ( NTP4VCBody A B ) $.
ntp4vc-result-case-syntax
  $a wff ( NTP4VCResultCase A B C ) $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if (
  0 <_ A ,
  A ,
  0
) $.

ntp4vc-at-definition $a |- (
  NTP4VCAt A B
) = if (
  ( NTP4VCToNat B ) < ( # ` A ) ,
  ( A ` ( NTP4VCToNat B ) ) ,
  0
) $.

ntp4vc-in-bounds-definition $a |- (
  ( NTP4VCInBounds A B )
  <->
  (
    0 <_ B
    /\
    B < ( # ` A )
  )
) $.

${
  $d j A $.

  ntp4vc-decrease1-definition $a |- (
    ( NTP4VCDecrease1 A )
    <->
    A. j e. ZZ
      (
        (
          0 <_ j
          /\
          j < ( ( # ` A ) - 1 )
        )
        ->
        (
          ( ( NTP4VCAt A j ) - 1 )
          <_
          ( NTP4VCAt A ( j + 1 ) )
        )
      )
  ) $.
$}

ntp4vc-progress-definition $a |- (
  ( NTP4VCProgress A B C )
  <->
  (
    (
      0 <_ ( ( # ` A ) - B )
      /\
      (
        ( ( # ` A ) - C )
        <
        ( ( # ` A ) - B )
      )
    )
    /\
    (
      ( NTP4VCDecrease1 A )
      /\
      0 <_ C
    )
  )
) $.

${
  $d j A B C $.

  ntp4vc-search-post-definition $a |- (
    ( NTP4VCSearchPost A B C )
    <->
    (
      (
        C = ( -u 1 )
        /\
        A. j e. ZZ
          (
            (
              B <_ j
              /\
              j < ( # ` A )
            )
            ->
            ( NTP4VCAt A j ) =/= 0
          )
      )
      \/
      (
        (
          B <_ C
          /\
          C < ( # ` A )
        )
        /\
        (
          ( NTP4VCAt A C ) = 0
          /\
          A. j e. ZZ
            (
              (
                B <_ j
                /\
                j < C
              )
              ->
              ( NTP4VCAt A j ) =/= 0
            )
        )
      )
    )
  ) $.
$}

ntp4vc-body-definition $a |- (
  ( NTP4VCBody A B )
  <->
  (
    ( NTP4VCInBounds A B )
    /\
    (
      ( NTP4VCAt A B ) =/= 0
      ->
      (
        ( NTP4VCInBounds A B )
        /\
        (
          (
            0 < ( NTP4VCAt A B )
            /\
            (
              ( NTP4VCInBounds A B )
              /\
              (
                NTP4VCProgress
                  A B ( B + ( NTP4VCAt A B ) )
              )
            )
          )
          \/
          (
            -. 0 < ( NTP4VCAt A B )
            /\
            ( NTP4VCProgress A B ( B + 1 ) )
          )
        )
      )
    )
  )
) $.

ntp4vc-result-case-definition $a |- (
  ( NTP4VCResultCase A B C )
  <->
  (
    (
      B < ( # ` A )
      /\
      (
        (
          ( NTP4VCAt A B ) = 0
          /\
          C = B
        )
        \/
        (
          ( NTP4VCAt A B ) =/= 0
          /\
          (
            (
              0 < ( NTP4VCAt A B )
              /\
              (
                NTP4VCSearchPost
                  A ( B + ( NTP4VCAt A B ) ) C
              )
            )
            \/
            (
              -. 0 < ( NTP4VCAt A B )
              /\
              ( NTP4VCSearchPost A ( B + 1 ) C )
            )
          )
        )
      )
    )
    \/
    (
      -. B < ( # ` A )
      /\
      C = ( -u 1 )
    )
  )
) $.

${
  $d r A B $.

  $( Source parameters: A=a and B=i. $)

  ntp4vc-a-list $e |- A e. Word ZZ $.
  ntp4vc-i-integer $e |- B e. ZZ $.
  ntp4vc-fact0 $e |- ( NTP4VCDecrease1 A ) $.
  ntp4vc-fact1 $e |- 0 <_ B $.

  ntp4vc-pearl-decrease1-search-rec-vc $a |- (
    (
      B < ( # ` A )
      ->
      ( NTP4VCBody A B )
    )
    /\
    A. r e. ZZ
      (
        ( NTP4VCResultCase A B r )
        ->
        ( NTP4VCSearchPost A B r )
      )
  ) $.
$}
