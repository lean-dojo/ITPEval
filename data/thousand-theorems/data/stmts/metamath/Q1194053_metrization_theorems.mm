$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1194053
  (thousand-theorems__metamath__Q1194053), "Metrization theorems":
  Urysohn's metrization theorem says that every T3 second-countable topology
  on an arbitrary carrier is induced by a genuine metric. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's Reg and Kol2 predicates jointly express the T3 assumption:
  regularity together with the T0 separation property. For a regular topology,
  SetMM also proves that Kol2 is equivalent to Hausdorff separation. The 2ndc
  predicate is second countability, and U. j is the full carrier of topology j.

  The conclusion retains the internal existential witness: d is a genuine
  real-valued metric on the entire carrier U. j, and MetOpen d is required to
  equal the given topology j. Thus it directly expresses existence of a metric
  space structure generating the original topology.

  The final declaration is the single unproved corpus $a statement. This
  database contains no $p proof statement.
$)

${
  $d d j $.

  thousand-theorems-q1194053-metrization $a |-
    A. j
      (
        (
          (
            j e. Reg
            /\
            j e. Kol2
          )
          /\
          j e. 2ndc
        )
        ->
        E. d e. ( Met ` U. j )
          j = ( MetOpen ` d )
      )
  $.
$}
