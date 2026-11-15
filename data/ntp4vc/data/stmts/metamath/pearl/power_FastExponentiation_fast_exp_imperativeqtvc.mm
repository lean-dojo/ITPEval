$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/power_FastExponentiation_fast_exp_imperativeqtvc: the imperative fast
  exponentiation verification condition establishes loop initialization,
  invariant preservation, descent, and the final integer-power result. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain. Under the loop invariant
  premise 0 <= e, Why3's computer division by the positive integer 2 is the
  floor of e / 2, its computer remainder is SetMM's e mod 2, and every power
  exponent displayed below is nonnegative. Thus SetMM's integer power agrees
  with the source int.Power operation on every constrained occurrence.

  The two proposition-valued conditionals are expanded into exhaustive
  guarded disjunctions. This is bidirectionally equivalent to the source
  nested if-expression and preserves the universal quantifier over all
  integer loop states e, p, and r. The repeated nonzero-divisor, invariant,
  descent, nonnegativity, and power equations remain explicit.

  The pinned Why3 source and the Lean and Isabelle exports use division in
  the updated exponent. The Rocq export instead places remainder in those
  positions and quotient in the parity test; that export discrepancy is not
  used here. The declaration below is Metamath's native unproved $a statement
  encoding; this database contains no artifact-level $p proof declaration.
$)

${
  $d e p $.  $d e r $.  $d p r $.
  $d e A $.  $d e B $.
  $d p A $.  $d p B $.
  $d r A $.  $d r B $.

  $( Source theorem parameters: A=n and B=x. $)

  ntp4vc-n-integer $e |- A e. ZZ $.
  ntp4vc-x-integer $e |- B e. ZZ $.
  ntp4vc-n-nonnegative $e |- 0 <_ A $.

  ntp4vc-pearl-power-fast-exponentiation-fast-exp-imperative-vc $a |- (
    0 <_ A
    /\
    (
      ( 1 x. ( B ^ A ) ) = ( B ^ A )
      /\
      A. e e. ZZ A. p e. ZZ A. r e. ZZ
        (
          (
            0 <_ e
            /\
            ( r x. ( p ^ e ) ) = ( B ^ A )
          )
          ->
          (
            (
              0 < e
              /\
              (
                2 =/= 0
                /\
                (
                  (
                    ( e mod 2 ) = 1
                    /\
                    (
                      2 =/= 0
                      /\
                      (
                        (
                          0 <_ e
                          /\
                          ( |_ ` ( e / 2 ) ) < e
                        )
                        /\
                        (
                          0 <_ ( |_ ` ( e / 2 ) )
                          /\
                          (
                            ( r x. p )
                            x.
                            (
                              ( p x. p )
                              ^
                              ( |_ ` ( e / 2 ) )
                            )
                          )
                          =
                          ( B ^ A )
                        )
                      )
                    )
                  )
                  \/
                  (
                    -. ( ( e mod 2 ) = 1 )
                    /\
                    (
                      2 =/= 0
                      /\
                      (
                        (
                          0 <_ e
                          /\
                          ( |_ ` ( e / 2 ) ) < e
                        )
                        /\
                        (
                          0 <_ ( |_ ` ( e / 2 ) )
                          /\
                          (
                            r
                            x.
                            (
                              ( p x. p )
                              ^
                              ( |_ ` ( e / 2 ) )
                            )
                          )
                          =
                          ( B ^ A )
                        )
                      )
                    )
                  )
                )
              )
            )
            \/
            (
              -. ( 0 < e )
              /\
              r = ( B ^ A )
            )
          )
        )
    )
  ) $.
$}
