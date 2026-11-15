$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/binary_search_Complexity_binary_searchqtvc: the binary-search
  complexity verification condition states initialization, interval
  preservation, progress, lookup, and logarithmic time-bound obligations for
  searching a sorted integer list. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Integer lists are represented exactly by SetMM words over ZZ, hence by
  arbitrary finite zero-based sequences of integers. NTP4VCToNat is the
  source conversion from integers to naturals, and NTP4VCAt is the source
  totalized list lookup with integer default 0.

  NTP4VCTDiv2 is truncating integer division by 2. This is the Why3 division
  operation rendered as Lean Int.tdiv and Isabelle cdiv; every occurrence in
  the verification condition has the fixed positive divisor 2.
  NTP4VCF directly expands f n = if n = 0 then 0 else 1 + log2 n.
  The arbitrary total integer function C represents log2, and its complete
  recursive defining law is retained as a scoped essential hypothesis.

  NTP4VCExcluded, NTP4VCAllAbsent, and NTP4VCInvariant directly expand the
  source quantified exclusion property, whole-list absence property, and
  loop invariant. NTP4VCStep expands both source proposition-valued if
  expressions as exhaustive guarded disjunctions and substitutes the
  let-bound midpoint definition. Splitting the typed theorem parameters,
  sortedness assumption, and log2 defining law into scoped essential
  hypotheses is bidirectionally equivalent to the source theorem context.
  Every list and integer quantifier retains its full source domain. The final
  declaration is Metamath's native unproved $a statement encoding; this
  database contains no $p proof declaration.
$)

$c
  NTP4VCToNat NTP4VCTDiv2 NTP4VCAt NTP4VCF NTP4VCMid
  NTP4VCExcluded NTP4VCAllAbsent NTP4VCInvariant NTP4VCStep
$.

ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-tdiv2-syntax $a class ( NTP4VCTDiv2 A ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B ) $.
ntp4vc-f-syntax $a class ( NTP4VCF A B ) $.
ntp4vc-mid-syntax $a class ( NTP4VCMid A B ) $.

ntp4vc-excluded-syntax
  $a wff ( NTP4VCExcluded A B C D ) $.
ntp4vc-all-absent-syntax
  $a wff ( NTP4VCAllAbsent A B ) $.
ntp4vc-invariant-syntax
  $a wff ( NTP4VCInvariant A B C D E F ) $.
ntp4vc-step-syntax
  $a wff ( NTP4VCStep A B C D E F ) $.

ntp4vc-to-nat-definition $a |- (
  NTP4VCToNat A
) = if (
  0 < A ,
  A ,
  0
) $.

ntp4vc-tdiv2-definition $a |- (
  NTP4VCTDiv2 A
) = if (
  A < 0 ,
  ( |^ ` ( A / 2 ) ) ,
  ( |_ ` ( A / 2 ) )
) $.

ntp4vc-at-definition $a |- (
  NTP4VCAt A B
) = if (
  ( NTP4VCToNat B ) < ( # ` A ) ,
  ( A ` ( NTP4VCToNat B ) ) ,
  0
) $.

ntp4vc-f-definition $a |- (
  NTP4VCF A B
) = if (
  B = 0 ,
  0 ,
  ( 1 + ( A ` B ) )
) $.

ntp4vc-mid-definition $a |- (
  NTP4VCMid A B
) = (
  B + ( NTP4VCTDiv2 ( A - B ) )
) $.

${
  $d i A B C D $.

  ntp4vc-excluded-definition $a |- (
    ( NTP4VCExcluded A B C D )
    <->
    A. i e. ZZ
      (
        (
          (
            0 <_ i
            /\
            i < C
          )
          \/
          (
            D <_ i
            /\
            i < ( # ` A )
          )
        )
        ->
        ( NTP4VCAt A i ) =/= B
      )
  ) $.
$}

${
  $d i A B $.

  ntp4vc-all-absent-definition $a |- (
    ( NTP4VCAllAbsent A B )
    <->
    A. i e. ZZ
      (
        (
          0 <_ i
          /\
          i < ( # ` A )
        )
        ->
        ( NTP4VCAt A i ) =/= B
      )
  ) $.
$}

ntp4vc-invariant-definition $a |- (
  ( NTP4VCInvariant A B C D E F )
  <->
  (
    (
      0 <_ E
      /\
      (
        E <_ D
        /\
        D <_ ( # ` A )
      )
    )
    /\
    (
      ( NTP4VCExcluded A B E D )
      /\
      (
        ( ( F - 0 ) + ( NTP4VCF C ( D - E ) ) )
        <_
        ( NTP4VCF C ( # ` A ) )
      )
    )
  )
) $.

ntp4vc-step-definition $a |- (
  ( NTP4VCStep A B C D E F )
  <->
  (
    (
      E < D
      /\
      (
        2 =/= 0
        /\
        (
          (
            0 <_ ( NTP4VCMid D E )
            /\
            ( NTP4VCMid D E ) < ( # ` A )
          )
          /\
          (
            (
              ( NTP4VCAt A ( NTP4VCMid D E ) ) < B
              /\
              (
                (
                  0 <_ ( D - E )
                  /\
                  (
                    D - ( ( NTP4VCMid D E ) + 1 )
                  )
                  <
                  ( D - E )
                )
                /\
                (
                  NTP4VCInvariant
                    A B C D ( ( NTP4VCMid D E ) + 1 ) ( F + 1 )
                )
              )
            )
            \/
            (
              -. ( NTP4VCAt A ( NTP4VCMid D E ) ) < B
              /\
              (
                (
                  0 <_ ( NTP4VCMid D E )
                  /\
                  ( NTP4VCMid D E ) < ( # ` A )
                )
                /\
                (
                  (
                    B < ( NTP4VCAt A ( NTP4VCMid D E ) )
                    /\
                    (
                      (
                        0 <_ ( D - E )
                        /\
                        (
                          ( NTP4VCMid D E ) - E
                        )
                        <
                        ( D - E )
                      )
                      /\
                      (
                        NTP4VCInvariant
                          A B C ( NTP4VCMid D E ) E ( F + 1 )
                      )
                    )
                  )
                  \/
                  (
                    -. B < ( NTP4VCAt A ( NTP4VCMid D E ) )
                    /\
                    (
                      (
                        (
                          (
                            0 <_ ( NTP4VCMid D E )
                            /\
                            ( NTP4VCMid D E ) < ( # ` A )
                          )
                          /\
                          ( NTP4VCAt A ( NTP4VCMid D E ) ) = B
                        )
                        \/
                        (
                          ( NTP4VCMid D E ) = -u 1
                          /\
                          ( NTP4VCAllAbsent A B )
                        )
                      )
                      /\
                      (
                        ( F - 0 )
                        <_
                        ( NTP4VCF C ( # ` A ) )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    \/
    (
      -. E < D
      /\
      (
        (
          (
            (
              0 <_ -u 1
              /\
              -u 1 < ( # ` A )
            )
            /\
            ( NTP4VCAt A ( -u 1 ) ) = B
          )
          \/
          ( NTP4VCAllAbsent A B )
        )
        /\
        (
          ( F - 0 )
          <_
          ( NTP4VCF C ( # ` A ) )
        )
      )
    )
  )
) $.

${
  $d h i j k l n A B C $.

  $( Source parameters: A=a, B=v, and C=log2. $)

  ntp4vc-a-list $e |- A e. Word ZZ $.
  ntp4vc-v-integer $e |- B e. ZZ $.
  ntp4vc-log2-function $e |- C e. ( ZZ ^m ZZ ) $.

  ntp4vc-log2-definition $e |- A. n e. ZZ
    (
      (
        n <_ 1
        /\
        ( C ` n ) = 0
      )
      \/
      (
        -. n <_ 1
        /\
        (
          ( C ` n )
          =
          ( 1 + ( C ` ( NTP4VCTDiv2 n ) ) )
        )
      )
    ) $.

  ntp4vc-sorted $e |- A. i e. ZZ
    A. j e. ZZ
      (
        (
          0 <_ i
          /\
          (
            i <_ j
            /\
            j < ( # ` A )
          )
        )
        ->
        ( NTP4VCAt A i ) <_ ( NTP4VCAt A j )
      ) $.

  ntp4vc-pearl-binary-search-complexity-vc $a |- (
    ( NTP4VCInvariant A B C ( # ` A ) 0 0 )
    /\
    A. h e. ZZ
      A. l e. ZZ
        A. k e. ZZ
          (
            ( NTP4VCInvariant A B C h l k )
            ->
            ( NTP4VCStep A B C h l k )
          )
  ) $.
$}
