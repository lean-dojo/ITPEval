(* Statement-only formalization of VERINA corpus artifact verina_advanced_47,
   catalog title "mergeIntervals": insertion-sort computation followed by a
   deterministic merge of overlapping integer intervals, together with its
   coverage, non-overlap, endpoint, and no-spurious-merge correctness
   contract. This file contains no proof. *)

From Stdlib Require Import Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition mergeIntervals_precond
    (intervals : list (Z * Z)) : Prop :=
  forallb
    (fun interval =>
      Z.leb (fst interval) (snd interval))
    intervals = true.

Fixpoint mergeIntervals_insert
    (x : Z * Z)
    (sorted : list (Z * Z)) : list (Z * Z) :=
  match sorted with
  | [] => [x]
  | y :: ys =>
      if Z.leb (fst x) (fst y)
      then x :: sorted
      else y :: mergeIntervals_insert x ys
  end.

Fixpoint mergeIntervals_sort
    (intervals : list (Z * Z)) : list (Z * Z) :=
  match intervals with
  | [] => []
  | x :: xs =>
      mergeIntervals_insert x (mergeIntervals_sort xs)
  end.

Fixpoint mergeIntervals_merge
    (intervals accumulator : list (Z * Z))
    {struct intervals} : list (Z * Z) :=
  match intervals with
  | [] => rev accumulator
  | (start, finish) :: rest =>
      match accumulator with
      | [] =>
          mergeIntervals_merge rest [(start, finish)]
      | (previousStart, previousFinish) :: accumulatorTail =>
          if Z.leb start previousFinish
          then
            mergeIntervals_merge
              rest
              ((previousStart, Z.max previousFinish finish) ::
                accumulatorTail)
          else
            mergeIntervals_merge
              rest
              ((start, finish) ::
                (previousStart, previousFinish) ::
                accumulatorTail)
      end
  end.

Definition mergeIntervals
    (intervals : list (Z * Z))
    (_h_precond : mergeIntervals_precond intervals) :
    list (Z * Z) :=
  mergeIntervals_merge (mergeIntervals_sort intervals) [].

Definition mergeIntervals_covered
    (intervals result : list (Z * Z)) : bool :=
  forallb
    (fun interval =>
      existsb
        (fun resultInterval =>
          andb
            (Z.leb (fst resultInterval) (fst interval))
            (Z.leb (snd interval) (snd resultInterval)))
        result)
    intervals.

Fixpoint mergeIntervals_noOverlap
    (intervals : list (Z * Z)) : bool :=
  match intervals with
  | [] => true
  | [_] => true
  | (_, finish1) :: ((start2, finish2) :: rest as tail) =>
      andb
        (Z.ltb finish1 start2)
        (mergeIntervals_noOverlap tail)
  end.

Definition mergeIntervals_resultBounded
    (intervals result : list (Z * Z)) : bool :=
  forallb
    (fun resultInterval =>
      andb
        (existsb
          (fun interval =>
            Z.eqb (fst interval) (fst resultInterval))
          intervals)
        (existsb
          (fun interval =>
            Z.eqb (snd interval) (snd resultInterval))
          intervals))
    result.

Definition mergeIntervals_noSpuriousMerge
    (intervals result : list (Z * Z)) : bool :=
  forallb
    (fun resultInterval =>
      let resultStart := fst resultInterval in
      let resultFinish := snd resultInterval in
      forallb
        (fun interval =>
          let start := fst interval in
          orb
            (Z.eqb start resultStart)
            (existsb
              (fun earlierInterval =>
                andb
                  (Z.leb resultStart (fst earlierInterval))
                  (andb
                    (Z.leb (snd earlierInterval) resultFinish)
                    (andb
                      (Z.ltb (fst earlierInterval) start)
                      (Z.leb start (snd earlierInterval)))))
              intervals))
        (filter
          (fun interval =>
            andb
              (Z.leb resultStart (fst interval))
              (Z.leb (snd interval) resultFinish))
          intervals))
    result.

Definition mergeIntervals_postcond
    (intervals result : list (Z * Z))
    (_h_precond : mergeIntervals_precond intervals) : Prop :=
  mergeIntervals_covered intervals result = true /\
  mergeIntervals_noOverlap result = true /\
  mergeIntervals_resultBounded intervals result = true /\
  mergeIntervals_noSpuriousMerge intervals result = true.

Theorem mergeIntervals_spec_satisfied
    (intervals : list (Z * Z))
    (h_precond : mergeIntervals_precond intervals) :
  mergeIntervals_postcond
    intervals
    (mergeIntervals intervals h_precond)
    h_precond.
Admitted.
