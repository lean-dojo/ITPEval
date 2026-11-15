$(
  @{
    @d N k x $@
    @d k y x $@
    @d ph x y $@
    induction-sum-odd.0 @e |- ( ph -> N e. NN ) $@
    @( (Contributed by Stanislas Polu, 14-Oct-2020.) @)
    induction-sum-odd @p |- ( ph -> sum_ k e. ( 1 ... N ) ( ( 2 x. k ) - 1 ) = ( 
  N ^ 2 ) ) @=
      ? @.
  @}
$)
