$(
  Statement-only formalization of "Law of Quadratic Reciprocity" from Hundred
  Theorems item 007: for distinct odd primes, the product of the two Legendre
  symbols is minus one raised to the product of their half-predecessors. This
  file contains no proof.
$)

$[ library/set.mm $]

$(
  The included set.mm library defines the natural primes, the Legendre symbol
  /L, integer arithmetic, and exponentiation. Membership in Prime \ { 2 }
  states that each modulus is an odd prime. Metamath assertion variables are
  schematic, so P and Q are universally quantified subject to the displayed
  assumptions. The declaration below is an unproved $a statement.
$)

hundred-theorems-007-quadratic-reciprocity $a
  |- ( ( P e. ( Prime \ { 2 } ) /\ Q e. ( Prime \ { 2 } ) /\ P =/= Q ) ->
       ( ( P /L Q ) x. ( Q /L P ) ) =
       ( -u 1 ^ ( ( ( P - 1 ) / 2 ) x. ( ( Q - 1 ) / 2 ) ) ) )
$.
