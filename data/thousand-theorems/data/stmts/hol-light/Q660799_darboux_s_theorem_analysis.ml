(*
  Statement-only formalization of Thousand Theorems corpus artifact Q660799,
  "Darboux's theorem (analysis)": intermediate-value properties of derivatives
  on real intervals, including ordered-connected and convex image formulations.
  This file contains no proof.
*)

let Q660799_DARBOUX_S_THEOREM_ANALYSIS =
 `let closed_interval =
      \(a:real) (b:real) (x:real). a <= x /\ x <= b in
  let open_interval =
      \(a:real) (b:real) (x:real). a < x /\ x < b in
  let has_derivative_within =
      \(f:real->real) (d:real) (s:real->bool) (x:real).
        !epsilon:real.
          &0 < epsilon
          ==> ?delta:real.
                &0 < delta /\
                !y:real.
                  y IN s /\
                  &0 < abs(y - x) /\
                  abs(y - x) < delta
                  ==> abs((f y - f x) / (y - x) - d) < epsilon in
  let has_derivative_at =
      \(f:real->real) (d:real) (x:real).
        !epsilon:real.
          &0 < epsilon
          ==> ?delta:real.
                &0 < delta /\
                !y:real.
                  &0 < abs(y - x) /\
                  abs(y - x) < delta
                  ==> abs((f y - f x) / (y - x) - d) < epsilon in
  let real_derivative_within =
      \(f:real->real) (s:real->bool) (x:real).
        @d:real. has_derivative_within f d s x in
  let real_derivative =
      \(f:real->real) (x:real).
        @d:real. has_derivative_at f d x in
  let ord_connected =
      \(s:real->bool).
        !a b c:real.
          a IN s /\ b IN s /\ a <= c /\ c <= b ==> c IN s in
  let convex_real =
      \(s:real->bool).
        !x y u v:real.
          x IN s /\ y IN s /\
          &0 <= u /\ &0 <= v /\ u + v = &1
          ==> u * x + v * y IN s in
  ((!f df:real->real. !a b m:real.
      a <= b /\
      (!x:real.
         closed_interval a b x
         ==> has_derivative_within f (df x)
               (closed_interval a b) x) /\
      df a < m /\ m < df b
      ==> ?c:real.
            open_interval a b c /\ df c = m) /\
   (!f df:real->real. !a b m:real.
      a <= b /\
      (!x:real.
         closed_interval a b x
         ==> has_derivative_within f (df x)
               (closed_interval a b) x) /\
      m < df a /\ df b < m
      ==> ?c:real.
            open_interval a b c /\ df c = m) /\
   (!s:real->bool. !f df:real->real.
      ord_connected s /\
      (!x:real.
         x IN s
         ==> has_derivative_within f (df x) s x)
      ==> ord_connected (IMAGE df s)) /\
   (!s:real->bool. !f:real->real.
      ord_connected s /\
      (!x:real.
         x IN s
         ==> ?d:real. has_derivative_within f d s x)
      ==> ord_connected (IMAGE (real_derivative_within f s) s)) /\
   (!s:real->bool. !f:real->real.
      ord_connected s /\
      (!x:real.
         x IN s
         ==> ?d:real. has_derivative_at f d x)
      ==> ord_connected (IMAGE (real_derivative f) s)) /\
   (!s:real->bool. !f df:real->real.
      convex_real s /\
      (!x:real.
         x IN s
         ==> has_derivative_within f (df x) s x)
      ==> convex_real (IMAGE df s)) /\
   (!s:real->bool. !f:real->real.
      convex_real s /\
      (!x:real.
         x IN s
         ==> ?d:real. has_derivative_within f d s x)
      ==> convex_real (IMAGE (real_derivative_within f s) s)) /\
   (!s:real->bool. !f:real->real.
      convex_real s /\
      (!x:real.
         x IN s
         ==> ?d:real. has_derivative_at f d x)
      ==> convex_real (IMAGE (real_derivative f) s)) /\
   (!f df:real->real. !a b m:real.
      a <= b /\
      (!x:real.
         closed_interval a b x
         ==> has_derivative_within f (df x)
               (closed_interval a b) x) /\
      df a <= m /\ m <= df b
      ==> ?c:real.
            closed_interval a b c /\ df c = m) /\
   (!f df:real->real. !a b m:real.
      a <= b /\
      (!x:real.
         closed_interval a b x
         ==> has_derivative_within f (df x)
               (closed_interval a b) x) /\
      df a <= m /\ m <= df b
      ==> ?c:real.
            closed_interval a b c /\ df c = m))`;;
