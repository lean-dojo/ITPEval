$(
  @{
    imo-1981-p6.0 @e |- ( ph -> F : ( NN0 X. NN0 ) --> NN0 ) $@
    imo-1981-p6.1 @e |- ( ph -> A. y e. NN0 ( 0 F y ) = ( y + 1 ) ) $@
    imo-1981-p6.2 @e |- ( ph -> A. x e. NN0 ( ( x + 1 ) F 0 ) = ( x F 1 ) ) $@
    imo-1981-p6.3 @e |- ( ph -> A. x e. NN0 A. y e. NN0 ( ( x + 1 ) F ( y + 1 ) ) = ( x F ( ( x + 1 ) F y ) ) ) $@
    @( (Contributed by Kunhao Zheng, 9-Aug-2021.) @)
    imo-1981-p6 @p |- ( ph -> A. y e. NN0 ( 4 F ( y + 1 ) ) = ( ( 2 ^ ( ( 4 F y ) + 3 ) ) - 3 ) ) @=
      ? @.
  @}
$)
