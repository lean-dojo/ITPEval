$(
  Statement-only formalization of the Logipedia corpus artifact
  sigma_pi.exp_pi_bc (logipedia__metamath__sigma_pi.exp_pi_bc), catalog
  title "sigma_pi.exp_pi_bc": a natural power times a finite product of
  shifted natural-valued function values equals the product obtained by
  multiplying every factor by the power's base. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 and ( NN0 ^m NN0 ) preserve the source natural-number and total-function
  domains. The term if ( b <_ c , c - b , 0 ) is exactly the source truncated
  subtraction c minus b. The always-true source bigop with base one and
  multiplication is the SetMM product over the half-open interval beginning
  at zero. SetMM addition, multiplication, exponentiation, application, and
  equality directly encode the remaining source operations. The final
  declaration is an unproved $a statement encoding; this database contains
  no $p proof declaration.
$)

${
  $d a b c f i $.

  logipedia-sigma-pi-exp-pi-bc $a |-
    A. a e. NN0
      A. b e. NN0
        A. c e. NN0
          A. f e. ( NN0 ^m NN0 )
            (
              (
                (
                  a
                  ^
                  if (
                    b <_ c ,
                    ( c - b ) ,
                    0
                  )
                )
                x.
                (
                  prod_ i e.
                    (
                      0
                      ..^
                      if (
                        b <_ c ,
                        ( c - b ) ,
                        0
                      )
                    )
                    ( f ` ( i + b ) )
                )
              )
              =
              (
                prod_ i e.
                  (
                    0
                    ..^
                    if (
                      b <_ c ,
                      ( c - b ) ,
                      0
                    )
                  )
                  ( a x. ( f ` ( i + b ) ) )
              )
            )
  $.
$}
