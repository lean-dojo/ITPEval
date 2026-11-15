$(
  Statement-only formalization of the Logipedia corpus artifact
  sigma_pi.exp_pi_l (logipedia__metamath__sigma_pi.exp_pi_l), catalog title
  "sigma_pi.exp_pi_l": a natural power times a finite product of
  natural-valued function values equals the product obtained by multiplying
  every factor by the power's base. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 and ( NN0 ^m NN0 ) preserve the source natural-number and total-function
  domains. The always-true source bigop with base one and multiplication is
  exactly the SetMM product over the half-open interval of indices below n.
  SetMM multiplication, exponentiation, application, and equality directly
  encode the remaining source operations. The final declaration is an
  unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

${
  $d a f i n $.

  logipedia-sigma-pi-exp-pi-l $a |-
    A. n e. NN0
      A. a e. NN0
        A. f e. ( NN0 ^m NN0 )
          (
            (
              ( a ^ n )
              x.
              (
                prod_ i e. ( 0 ..^ n )
                  ( f ` i )
              )
            )
            =
            (
              prod_ i e. ( 0 ..^ n )
                ( a x. ( f ` i ) )
            )
          )
  $.
$}
