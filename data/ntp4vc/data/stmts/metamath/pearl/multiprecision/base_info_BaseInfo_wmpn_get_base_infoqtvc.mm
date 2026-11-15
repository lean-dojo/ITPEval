$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/multiprecision/base_info_BaseInfo_wmpn_get_base_infoqtvc:
  the verification condition for constructing invariant-bearing
  multiprecision base information by growing an integer power within exact
  unsigned 32- and 64-bit bounds. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Unsigned words are represented exactly by their complete bounded integer
  carriers. A base-information record is represented by the nested ordered
  pair <base,<exponent,power>>, restricted to the source record invariant.
  Thus its base remains an arbitrary integer, while its exponent and power
  retain their exact 32- and 64-bit types.

  NTP4VCQuotient is floor((2^64-1)/base), the Euclidean quotient used by the
  source for the positive input base. NTP4VCGrowth and NTP4VCExit encode the
  two branches of the loop condition. NTP4VCLoop preserves the universally
  quantified loop state and invariant, and NTP4VCQuotientBody preserves the
  local quotient binding and its scope. Proposition-valued conditionals are
  expanded into equivalent exhaustive guarded implications.

  The final declaration is Metamath's native unproved $a statement encoding;
  this database contains no $p proof declaration.
$)

$c
  NTP4VCWord32 NTP4VCWord64 NTP4VCBaseInfo
  NTP4VCBase NTP4VCExponent NTP4VCPower NTP4VCQuotient
  NTP4VCGrowth NTP4VCExit NTP4VCLoop NTP4VCQuotientBody
$.

ntp4vc-word32-syntax $a class NTP4VCWord32 $.
ntp4vc-word64-syntax $a class NTP4VCWord64 $.
ntp4vc-base-info-syntax $a class NTP4VCBaseInfo $.
ntp4vc-base-syntax $a class ( NTP4VCBase A ) $.
ntp4vc-exponent-syntax $a class ( NTP4VCExponent A ) $.
ntp4vc-power-syntax $a class ( NTP4VCPower A ) $.
ntp4vc-quotient-syntax $a class ( NTP4VCQuotient A ) $.
ntp4vc-growth-syntax $a wff ( NTP4VCGrowth A B C D ) $.
ntp4vc-exit-syntax $a wff ( NTP4VCExit A B C ) $.
ntp4vc-loop-syntax $a wff ( NTP4VCLoop A B C D ) $.
ntp4vc-quotient-body-syntax $a wff ( NTP4VCQuotientBody A ) $.

ntp4vc-word32-definition $a |- NTP4VCWord32 =
  ( 0 ... ( ( 2 ^ ; 3 2 ) - 1 ) ) $.

ntp4vc-word64-definition $a |- NTP4VCWord64 =
  ( 0 ... ( ( 2 ^ ; 6 4 ) - 1 ) ) $.

ntp4vc-base-definition $a |- ( NTP4VCBase A ) =
  ( 1st ` A ) $.

ntp4vc-exponent-definition $a |- ( NTP4VCExponent A ) =
  ( 1st ` ( 2nd ` A ) ) $.

ntp4vc-power-definition $a |- ( NTP4VCPower A ) =
  ( 2nd ` ( 2nd ` A ) ) $.

ntp4vc-base-info-definition $a |- NTP4VCBaseInfo =
  { r e. ( ZZ X. ( NTP4VCWord32 X. NTP4VCWord64 ) ) |
    (
      (
        2 <_ ( NTP4VCBase r )
        /\
        ( NTP4VCBase r ) <_ ; 2 5 6
      )
      /\
      (
        (
          ( NTP4VCPower r ) < ( 2 ^ ; 6 4 )
          /\
          ( 2 ^ ; 6 4 )
            <_ ( ( NTP4VCPower r ) x. ( NTP4VCBase r ) )
        )
        /\
        (
          (
            7 <_ ( NTP4VCExponent r )
            /\
            ( NTP4VCExponent r ) <_ ; 6 3
          )
          /\
          ( NTP4VCPower r ) =
            ( ( NTP4VCBase r ) ^ ( NTP4VCExponent r ) )
        )
      )
    )
  } $.

ntp4vc-quotient-definition $a |- ( NTP4VCQuotient A ) =
  ( |_ ` ( ( ( 2 ^ ; 6 4 ) - 1 ) / A ) ) $.

${
  $d o A $.  $d o B $.  $d o C $.  $d o D $.
  $d n A $.  $d n B $.  $d n C $.  $d n D $.  $d n o $.

  ntp4vc-growth-definition $a |- (
    NTP4VCGrowth A B C D
  ) <-> (
    ( D x. A ) e. NTP4VCWord64
    /\
    A. o e. NTP4VCWord64
      (
        o = ( D x. A )
        ->
        (
          ( C + 1 ) e. NTP4VCWord32
          /\
          A. n e. NTP4VCWord32
            (
              n = ( C + 1 )
              ->
              (
                (
                  (
                    0 <_ ( B - D )
                    /\
                    ( B - o ) < ( B - D )
                  )
                  /\
                  ( A ^ n ) = o
                )
                /\
                (
                  1 <_ n
                  /\
                  n <_ ; 6 4
                )
              )
            )
        )
      )
  ) $.
$}

${
  $d q A $.  $d q B $.  $d q C $.
  $d r A $.  $d r B $.  $d r C $.  $d r q $.

  ntp4vc-exit-definition $a |- (
    NTP4VCExit A B C
  ) <-> (
    A. q e. NTP4VCWord64
      (
        q = A
        ->
        (
          (
            2 <_ q
            /\
            q <_ ; 2 5 6
          )
          /\
          (
            (
              C < ( 2 ^ ; 6 4 )
              /\
              ( 2 ^ ; 6 4 ) <_ ( C x. q )
            )
            /\
            (
              (
                (
                  7 <_ B
                  /\
                  B <_ ; 6 3
                )
                /\
                C = ( q ^ B )
              )
              /\
              A. r e. NTP4VCBaseInfo
                (
                  (
                    ( NTP4VCBase r ) = q
                    /\
                    (
                      ( NTP4VCExponent r ) = B
                      /\
                      ( NTP4VCPower r ) = C
                    )
                  )
                  ->
                  ( NTP4VCBase r ) = A
                )
            )
          )
        )
      )
  ) $.
$}

ntp4vc-loop-definition $a |- (
  NTP4VCLoop A B C D
) <-> (
  (
    (
      ( A ^ C ) = D
      /\
      (
        1 <_ C
        /\
        C <_ ; 6 4
      )
    )
    ->
    (
      (
        D <_ B
        ->
        ( NTP4VCGrowth A B C D )
      )
      /\
      (
        -. D <_ B
        ->
        ( NTP4VCExit A C D )
      )
    )
  )
) $.

${
  $d m A $.  $d x A $.  $d p A $.
  $d x m $.  $d p m $.  $d p x $.

  ntp4vc-quotient-body-definition $a |- (
    NTP4VCQuotientBody A
  ) <-> (
    A. m e. NTP4VCWord64
      (
        m = ( NTP4VCQuotient A )
        ->
        (
          (
            ( A ^ 1 ) = A
            /\
            (
              1 <_ 1
              /\
              1 <_ ; 6 4
            )
          )
          /\
          A. x e. NTP4VCWord32
            A. p e. NTP4VCWord64
              ( NTP4VCLoop A m x p )
        )
      )
  ) $.
$}

${
  $( Source theorem parameter A=b1, represented by its unsigned value. $)
  ntp4vc-b1-word64 $e |- A e. NTP4VCWord64 $.
  ntp4vc-fact0 $e |- 2 <_ A $.
  ntp4vc-fact1 $e |- A <_ ; 2 5 6 $.

  ntp4vc-pearl-multiprecision-base-info-get-base-info-vc $a |- (
    A =/= 0
    /\
    (
      ( NTP4VCQuotient A ) e. NTP4VCWord64
      /\
      ( NTP4VCQuotientBody A )
    )
  ) $.
$}
