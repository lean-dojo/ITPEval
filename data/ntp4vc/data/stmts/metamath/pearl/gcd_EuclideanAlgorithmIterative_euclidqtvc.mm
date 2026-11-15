$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/gcd_EuclideanAlgorithmIterative_euclidqtvc: the iterative Euclidean
  algorithm verification condition preserves nonnegativity and the integer
  greatest common divisor across a remainder step. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain, and its gcd operator is the
  canonical nonnegative greatest common divisor on integers. In the pinned
  Why3 module EuclideanAlgorithmIterative, the loop assignment v <- u % v
  uses the mach.int.Int remainder. The selected VC quantifies the loop states
  v and u over all integers, and its invariant antecedent gives u >= 0 and
  v >= 0. In the active branch v != 0, hence v > 0, so SetMM's u mod v is
  exactly the source remainder on every state where its value is constrained.

  The scoped integer and nonnegativity hypotheses preserve the source
  parameters u0 and v0. Expanding the proposition-valued conditional into
  two exhaustive guarded cases is bidirectionally equivalent to the original
  Why3 conditional and preserves its universal quantifier scope.

  The secondary Lean and Isabelle exports also render the Euclidean remainder.
  The secondary Rocq export instead places Z.quot, the integer quotient, in
  those positions; under the reviewed canonical resolution this is an export
  defect and does not override the pinned Why3 goal. The declaration below is
  Metamath's native unproved $a statement encoding; this database has no
  artifact-level $p proof declaration.
$)

${
  $d u v $.
  $d u A $.  $d u B $.
  $d v A $.  $d v B $.

  $( Source parameters: A=u0 and B=v0; set variables v and u are loop states. $)

  ntp4vc-u0-integer $e |- A e. ZZ $.
  ntp4vc-v0-integer $e |- B e. ZZ $.
  ntp4vc-fact0 $e |- 0 <_ A $.
  ntp4vc-fact1 $e |- 0 <_ B $.

  ntp4vc-pearl-gcd-euclidean-algorithm-iterative-vc $a |- (
    0 <_ A
    /\
    (
      0 <_ B
      /\
      A. v e. ZZ A. u e. ZZ
        (
          (
            (
              0 <_ u
              /\
              0 <_ v
            )
            /\
            ( u gcd v ) = ( A gcd B )
          )
          ->
          (
            (
              v =/= 0
              /\
              (
                v =/= 0
                /\
                (
                  (
                    0 <_ v
                    /\
                    ( u mod v ) < v
                  )
                  /\
                  (
                    (
                      0 <_ v
                      /\
                      0 <_ ( u mod v )
                    )
                    /\
                    ( v gcd ( u mod v ) ) = ( A gcd B )
                  )
                )
              )
            )
            \/
            (
              -. v =/= 0
              /\
              u = ( A gcd B )
            )
          )
        )
    )
  ) $.
$}
