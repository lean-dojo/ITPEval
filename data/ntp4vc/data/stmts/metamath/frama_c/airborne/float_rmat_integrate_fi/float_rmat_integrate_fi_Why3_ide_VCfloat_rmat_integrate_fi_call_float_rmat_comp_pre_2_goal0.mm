$(
  Statement-only formalization of the NTP4VC corpus artifact
  frama_c/airborne/float_rmat_integrate_fi/float_rmat_integrate_fi_Why3_ide_VCfloat_rmat_integrate_fi_call_float_rmat_comp_pre_2_goal0:
  under the generated region, linked-allocation, and input-rate validity
  conditions, a writable nine-real matrix memory block satisfies the readable
  validity precondition required by floating-point matrix composition. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  The source address structure is represented exactly by ZZ X. ZZ, with its
  base and offset given by 1st and 2nd. T is the arbitrary integer allocation
  map, F is the arbitrary real-valued memory, G is the arbitrary source region
  map, and membership of T in the arbitrary predicate extension L represents
  the source linked predicate.

  At the positive lengths used here, valid_rw and valid_rd are expanded into
  their exact base, offset, and allocation-bound conjuncts. In the imported
  source theory is_float32 is definitionally True and is_finite32 is asserted
  for every real. Thus the three is_float32 assumptions and all finite-value
  conjuncts in p_rvalid_floatrates and p_rvalid_floatrmat disappear by
  bidirectional logical equivalence. Splitting the remaining conjunctions into
  essential hypotheses is likewise equivalent.

  The final declaration is Metamath's native unproved $a statement encoding;
  this file contains no local $p proof declaration. Its imported set.mm
  dependency contains the standard library proofs.
$)

$c NTP4VCAddr NTP4VCBase NTP4VCOffset $.

ntp4vc-addr-class $a class NTP4VCAddr $.
ntp4vc-base-class $a class ( NTP4VCBase A ) $.
ntp4vc-offset-class $a class ( NTP4VCOffset A ) $.

ntp4vc-addr-def $a |- NTP4VCAddr = ( ZZ X. ZZ ) $.
ntp4vc-base-def $a |- ( NTP4VCBase A ) = ( 1st ` A ) $.
ntp4vc-offset-def $a |- ( NTP4VCOffset A ) = ( 2nd ` A ) $.

${
  $d A B F G L T $.

  ntp4vc-output-address $e |- A e. NTP4VCAddr $.
  ntp4vc-rates-address $e |- B e. NTP4VCAddr $.
  ntp4vc-allocation-map $e |- T e. ( ZZ ^m ZZ ) $.
  ntp4vc-real-memory $e |- F e. ( RR ^m NTP4VCAddr ) $.
  ntp4vc-region-map $e |- G e. ( ZZ ^m ZZ ) $.
  ntp4vc-linked-predicate $e |- L C_ ( ZZ ^m ZZ ) $.

  ntp4vc-output-region $e |- (
    ( G ` ( NTP4VCBase A ) ) <_ 0
  ) $.

  ntp4vc-rates-region $e |- (
    ( G ` ( NTP4VCBase B ) ) <_ 0
  ) $.

  ntp4vc-linked-allocation $e |- T e. L $.

  ntp4vc-output-positive-base $e |- 0 < ( NTP4VCBase A ) $.
  ntp4vc-output-nonnegative-offset $e |- (
    0 <_ ( NTP4VCOffset A )
  ) $.
  ntp4vc-output-valid-end $e |- (
    ( ( NTP4VCOffset A ) + 9 ) <_ ( T ` ( NTP4VCBase A ) )
  ) $.

  ntp4vc-rates-nonzero-base $e |- ( NTP4VCBase B ) =/= 0 $.
  ntp4vc-rates-nonnegative-offset $e |- (
    0 <_ ( NTP4VCOffset B )
  ) $.
  ntp4vc-rates-valid-end $e |- (
    ( ( NTP4VCOffset B ) + 3 ) <_ ( T ` ( NTP4VCBase B ) )
  ) $.

  ntp4vc-float-rmat-integrate-fi-call-float-rmat-comp-pre-2-goal0
    $a |- (
      ( NTP4VCBase A ) =/= 0
      /\
      (
        0 <_ ( NTP4VCOffset A )
        /\
        ( ( NTP4VCOffset A ) + 9 ) <_ ( T ` ( NTP4VCBase A ) )
      )
    ) $.
$}
