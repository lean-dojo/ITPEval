$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/verifythis_2017_odd_even_sort_rearranging_Top_my_swapqtvc: swapping
  an earlier larger entry with a later smaller entry in an integer array
  preserves the exchange relation and strictly decreases the weighted
  entropy sum. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Source integer arrays are represented exactly by arbitrary finite SetMM
  words over ZZ. NTP4VCToNat is the source Int.toNat conversion, NTP4VCAt is
  totalized list lookup with the inhabited integer default zero, and
  NTP4VCSet is List.set at the converted index. NTP4VCExchange states that
  the second word is exactly the first word with the two selected entries
  exchanged.

  NTP4VCEntropy is the source half-open sum from zero to the array length.
  Its summand directly unfolds aux and the source axiom identifying
  aux_closure with aux. The final assertion retains the generated universal
  quantifier over every same-length exchange result and its repeated exchange
  conjunct. All arrays and integers retain their full source domains.

  Every declaration below is syntax, a faithful definition, or Metamath's
  native unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

$c
  NTP4VCToNat NTP4VCAt NTP4VCSet NTP4VCExchange NTP4VCEntropy
$.

ntp4vc-to-nat-syntax $a class ( NTP4VCToNat A ) $.
ntp4vc-at-syntax $a class ( NTP4VCAt A B ) $.
ntp4vc-set-syntax $a class ( NTP4VCSet A B C ) $.
ntp4vc-exchange-syntax $a wff ( NTP4VCExchange A B C D ) $.
ntp4vc-entropy-syntax $a class ( NTP4VCEntropy A B ) $.

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

${
  $d k A B C $.

  ntp4vc-set-definition $a |- (
    NTP4VCSet A B C
  ) = (
    k e. ( 0 ..^ ( # ` A ) ) |->
      if (
        k = ( NTP4VCToNat B ) ,
        C ,
        ( A ` k )
      )
  ) $.
$}

ntp4vc-exchange-definition $a |- (
  NTP4VCExchange A B C D
) <-> (
  B
  =
  (
    NTP4VCSet
      ( NTP4VCSet A C ( NTP4VCAt A D ) )
      D
      ( NTP4VCAt A C )
  )
) $.

${
  $d k A B $.

  ntp4vc-entropy-definition $a |- (
    NTP4VCEntropy A B
  ) = (
    sum_ k e. ( 0 ..^ ( # ` A ) )
      (
        k
        x.
        (
          B
          -
          ( NTP4VCAt A k )
        )
      )
  ) $.
$}

${
  $d x A B C D $.

  $( Source parameters: A=a, B=j, C=i, D=m, and x ranges over a1. $)

  ntp4vc-array-parameter
    $e |- A e. ( Word ZZ ) $.
  ntp4vc-j-parameter
    $e |- B e. ZZ $.
  ntp4vc-i-parameter
    $e |- C e. ZZ $.
  ntp4vc-m-parameter
    $e |- D e. ZZ $.

  ntp4vc-fact0
    $e |- ( NTP4VCAt A B ) < ( NTP4VCAt A C ) $.
  ntp4vc-fact1
    $e |- 0 <_ C $.
  ntp4vc-fact2
    $e |- C < B $.
  ntp4vc-fact3
    $e |- B < ( # ` A ) $.

  ntp4vc-pearl-verifythis-2017-odd-even-sort-my-swap-vc $a |- (
    0 <_ C
    /\
    (
      C < ( # ` A )
      /\
      (
        0 <_ B
        /\
        (
          B < ( # ` A )
          /\
          A. x e. ( Word ZZ )
            (
              ( # ` x ) = ( # ` A )
              ->
              (
                ( NTP4VCExchange A x C B )
                ->
                (
                  ( NTP4VCExchange A x C B )
                  /\
                  ( NTP4VCEntropy x D )
                  <
                  ( NTP4VCEntropy A D )
                )
              )
            )
        )
      )
    )
  ) $.
$}
