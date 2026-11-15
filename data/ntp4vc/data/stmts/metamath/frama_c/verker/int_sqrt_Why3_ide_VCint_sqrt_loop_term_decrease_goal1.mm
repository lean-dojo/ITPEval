$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/verker/int_sqrt_Why3_ide_VCint_sqrt_loop_term_decrease_goal1:
  the integer-square-root loop termination condition states that shifting a
  nonzero unsigned 64-bit integer right by two gives a strictly smaller
  integer, under the generated integer-range assumptions. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  NTP4VCUint64 directly expands the source definition to the integer interval
  from zero inclusive to 18446744073709551616 exclusive. NTP4VCTDiv is
  truncating integer division toward zero.

  On the source assumption that A is unsigned, A is nonnegative. The imported
  Cbits laws lsr_1 and lsr_add therefore identify lsr(A,2) with two successive
  truncating divisions by two; the intermediate quotient is also
  nonnegative. NTP4VCLsr2 is exactly that equivalent expression, so the
  source let-bound x is expanded without restricting the integer domain.

  The source implication chain is split into scoped essential hypotheses for
  the arbitrary displayed integers A=i_1 and B=i. Every original assumption,
  including the unsigned-64 condition on the shifted value, is retained. The
  final declaration is Metamath's native unproved $a statement encoding; this
  database contains no $p declaration.
$)

$c
  NTP4VCUint64Limit NTP4VCTDiv NTP4VCLsr2 NTP4VCUint64
$.

ntp4vc-uint64-limit-class $a class NTP4VCUint64Limit $.
ntp4vc-tdiv-class $a class ( NTP4VCTDiv A B ) $.
ntp4vc-lsr2-class $a class ( NTP4VCLsr2 A ) $.
ntp4vc-uint64-syntax $a wff ( NTP4VCUint64 A ) $.

ntp4vc-uint64-limit-def $a |- NTP4VCUint64Limit =
  ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
  1 8 4 4 6 7 4 4 0 7 3 7 0 9 5 5 1 6 1 6 $.

ntp4vc-tdiv-def $a |- ( NTP4VCTDiv A B ) =
  if (
    A < 0 ,
    ( |^ ` ( A / B ) ) ,
    ( |_ ` ( A / B ) )
  ) $.

ntp4vc-lsr2-def $a |- ( NTP4VCLsr2 A ) =
  ( NTP4VCTDiv ( NTP4VCTDiv A 2 ) 2 ) $.

ntp4vc-uint64-def $a |- ( ( NTP4VCUint64 A ) <->
  ( 0 <_ A /\ A < NTP4VCUint64Limit )
) $.

${
  $d A B $.

  $( Source parameters A=i_1 and B=i. $)

  ntp4vc-i1-integer $e |- A e. ZZ $.
  ntp4vc-i-integer $e |- B e. ZZ $.

  ntp4vc-i1-nonzero $e |- A =/= 0 $.
  ntp4vc-two-le-i $e |- 2 <_ B $.
  ntp4vc-i-uint64 $e |- ( NTP4VCUint64 B ) $.
  ntp4vc-i1-uint64 $e |- ( NTP4VCUint64 A ) $.
  ntp4vc-shifted-i1-uint64 $e |- (
    NTP4VCUint64 ( NTP4VCLsr2 A )
  ) $.

  ntp4vc-int-sqrt-loop-term-decrease-goal1 $a |- (
    ( NTP4VCLsr2 A ) < A
  ) $.
$}
