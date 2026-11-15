(* Statement-only formalization of miniF2F valid problem amc12a_2003_p24. *)
let statement =
  `(?a b:real.
      &1 < b /\ b <= a /\
      ln (a / b) / ln a + ln (b / a) / ln b = &0) /\
   (!a b:real.
      &1 < b /\ b <= a
      ==> ln (a / b) / ln a + ln (b / a) / ln b <= &0)`;;
