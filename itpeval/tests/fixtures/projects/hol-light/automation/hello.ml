let itpeval_target = prove
  (`(!x:A. R x ==> S x) /\ R (a:A) ==> S a /\ R a`,
   ASM_MESON_TAC []);;
