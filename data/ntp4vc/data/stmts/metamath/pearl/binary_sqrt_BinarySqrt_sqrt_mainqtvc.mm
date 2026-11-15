$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/binary_sqrt_BinarySqrt_sqrt_mainqtvc: the binary-square-root
  initialization verification condition repeats the nonnegativity of the
  real radicand and positivity of the real tolerance, together with integer
  reflexivity at one and the real multiplicative identity at one.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's RR and ZZ are the full real-number and integer domains. The source
  coercion real_of_int 1 is the same canonical number 1 in RR, so the final
  equality is represented exactly as eps = 1 times eps. Splitting the two
  typed theorem parameters and assumptions into scoped essential hypotheses
  is bidirectionally equivalent to the source curried theorem. Every source
  conjunct, including both repeated assumptions and the integer inequality
  1 <= 1, remains explicit. The final declaration is Metamath's native
  unproved $a statement encoding; this database contains no $p declaration.
$)

${
  $d A B $.

  $( Source parameters: A=r and B=eps. $)

  ntp4vc-r-real $e |- A e. RR $.
  ntp4vc-eps-real $e |- B e. RR $.

  ntp4vc-r-nonnegative $e |- 0 <_ A $.
  ntp4vc-eps-positive $e |- 0 < B $.

  ntp4vc-pearl-binary-sqrt-main-vc $a |- (
    0 <_ A
    /\
    (
      0 < B
      /\
      (
        1 <_ 1
        /\
        B = ( 1 x. B )
      )
    )
  ) $.
$}
