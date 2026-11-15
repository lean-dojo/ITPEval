(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q765987, "Heine–Cantor theorem": every continuous function from a compact
  uniform space to an arbitrary uniform space is uniformly continuous. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory;

val q765987_pair_carrier_def = new_definition (
  "q765987_pair_carrier_def",
  ``q765987_pair_carrier (carrier : 'a set) =
      {p : 'a # 'a | FST p IN carrier /\ SND p IN carrier}``);

val q765987_uniform_space_def = new_definition (
  "q765987_uniform_space_def",
  ``q765987_uniform_space
      (carrier : 'a set) (entourages : (('a # 'a) set) set) <=>
      q765987_pair_carrier carrier IN entourages /\
      (!u.
        u IN entourages
        ==>
        u SUBSET q765987_pair_carrier carrier) /\
      (!u v.
        u IN entourages /\ v IN entourages
        ==>
        u INTER v IN entourages) /\
      (!u v.
        u IN entourages /\
        u SUBSET v /\
        v SUBSET q765987_pair_carrier carrier
        ==>
        v IN entourages) /\
      (!u.
        u IN entourages
        ==>
        !x. x IN carrier ==> (x,x) IN u) /\
      (!u.
        u IN entourages
        ==>
        {p | (SND p,FST p) IN u} IN entourages) /\
      (!u.
        u IN entourages
        ==>
        ?v.
          v IN entourages /\
          !x z.
            x IN carrier /\
            z IN carrier /\
            (?y.
              y IN carrier /\
              (x,y) IN v /\
              (y,z) IN v)
            ==>
            (x,z) IN u)``);

val q765987_uniform_open_def = new_definition (
  "q765987_uniform_open_def",
  ``q765987_uniform_open
      (carrier : 'a set)
      (entourages : (('a # 'a) set) set)
      (s : 'a set) <=>
      s SUBSET carrier /\
      !x.
        x IN s
        ==>
        ?u.
          u IN entourages /\
          !y. (x,y) IN u ==> y IN s``);

val q765987_compact_space_def = new_definition (
  "q765987_compact_space_def",
  ``q765987_compact_space
      (carrier : 'a set)
      (entourages : (('a # 'a) set) set) <=>
      !cover : ('a set) set.
        (!s.
          s IN cover
          ==>
          q765987_uniform_open carrier entourages s) /\
        carrier SUBSET BIGUNION cover
        ==>
        ?subcover : ('a set) set.
          FINITE subcover /\
          subcover SUBSET cover /\
          carrier SUBSET BIGUNION subcover``);

val q765987_continuous_def = new_definition (
  "q765987_continuous_def",
  ``q765987_continuous
      (source_carrier : 'a set)
      (source_entourages : (('a # 'a) set) set)
      (target_carrier : 'b set)
      (target_entourages : (('b # 'b) set) set)
      (f : 'a -> 'b) <=>
      (!x. x IN source_carrier ==> f x IN target_carrier) /\
      !s.
        q765987_uniform_open target_carrier target_entourages s
        ==>
        q765987_uniform_open source_carrier source_entourages
          {x | x IN source_carrier /\ f x IN s}``);

val q765987_uniformly_continuous_def = new_definition (
  "q765987_uniformly_continuous_def",
  ``q765987_uniformly_continuous
      (source_carrier : 'a set)
      (source_entourages : (('a # 'a) set) set)
      (target_carrier : 'b set)
      (target_entourages : (('b # 'b) set) set)
      (f : 'a -> 'b) <=>
      (!x. x IN source_carrier ==> f x IN target_carrier) /\
      !v.
        v IN target_entourages
        ==>
        {p |
          FST p IN source_carrier /\
          SND p IN source_carrier /\
          (f (FST p),f (SND p)) IN v}
        IN source_entourages``);

val CompactSpace_uniformContinuous_of_continuous =
  ``!(source_carrier : 'a set)
      (source_entourages : (('a # 'a) set) set)
      (target_carrier : 'b set)
      (target_entourages : (('b # 'b) set) set)
      (f : 'a -> 'b).
      q765987_uniform_space source_carrier source_entourages /\
      q765987_uniform_space target_carrier target_entourages /\
      q765987_compact_space source_carrier source_entourages /\
      q765987_continuous
        source_carrier source_entourages
        target_carrier target_entourages f
      ==>
      q765987_uniformly_continuous
        source_carrier source_entourages
        target_carrier target_entourages f``;
