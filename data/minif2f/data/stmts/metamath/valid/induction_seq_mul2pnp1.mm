$(
  @{
    @d N x $@
    @d U n y $@
    @d U x y $@
    @d ph x y $@
    induction-seq-mul2pnp1.0 @e |- ( ph -> N e. NN0 ) $@
    induction-seq-mul2pnp1.1 @e |- ( ph -> ( U ` 0 ) = 0 ) $@
    induction-seq-mul2pnp1.2 @e |- ( ph -> A. n e. NN0 ( U ` ( n + 1 ) ) = ( ( 2 
  x. ( U ` n ) ) + ( n + 1 ) ) ) $@
    @( (Contributed by Stanislas Polu, 13-Oct-2020.) @)
    induction-seq-mul2pnp1 @p |- ( ph -> ( U ` N ) = ( ( 2 ^ ( N + 1 ) ) - ( N + 
  2 ) ) ) @=
      ? @.
  @}
$)
