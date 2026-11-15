;; Statement-only formalization of thousand-theorems corpus artifact Q5171652,
;; "Corners theorem": a sufficiently dense finite subset of an initial square
;; of natural-number pairs contains a nontrivial additive corner, with the
;; explicit triangle-removal bound from the source. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The Lean statement quantifies epsilon over the reals. For this universal
;; finite-density statement, exact positive rationals give a bidirectionally
;; equivalent formulation. The real theorem immediately implies its rational
;; restriction. Conversely, a counterexample has
;;
;;   epsilon <= |A| / n^2 <= 1.
;;
;; If epsilon is rational, retain it. Otherwise the first inequality is strict,
;; so density of Q supplies a rational q with
;; epsilon < q <= |A| / n^2. On 0 < epsilon <= 1, the expanded
;; cornersTheoremBound(epsilon/9) is nonincreasing: its ceil and floor indices
;; are nonincreasing, the regularity bound is therefore nonincreasing, and both
;; branches of triangleRemovalBound(epsilon/81) are nondecreasing. Replacing
;; epsilon by q thus preserves the bound and density hypotheses. Hence a real
;; counterexample exists exactly when a rational counterexample exists.

;; These predicates are the exact Nat.ceil and Nat.floor characterizations
;; occurring in triangleRemovalBound and SzemerediRegularity.bound.

(defun q5171652-ceil-four-over-p (x k)
  (and
   (rationalp x)
   (< 0 x)
   (natp k)
   (< 0 k)
   (< (* (- k 1) x) 4)
   (<= 4 (* k x))))

(defun q5171652-floor-four-over-fifth-power-p
    (fifth-power value)
  (and
   (rationalp fifth-power)
   (< 0 fifth-power)
   (natp value)
   (<= (* value fifth-power) 4)
   (< 4 (* (+ value 1) fifth-power))))

(defun q5171652-floor-log-four-p
    (fifth-power value)
  (and
   (rationalp fifth-power)
   (< 0 fifth-power)
   (natp value)
   (if (zp value)
       (< 100 (* 4 fifth-power))
     (and
      (<= (* (expt 4 value) fifth-power) 100)
      (< 100 (* (expt 4 (+ value 1)) fifth-power))))))

(defun q5171652-step-bound (value)
  (* value (expt 4 value)))

(defun q5171652-iterate-step-bound (value count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      value
    (q5171652-iterate-step-bound
     (q5171652-step-bound value)
     (- count 1))))

(defun q5171652-regularity-bound
    (ceil-value floor-iterate floor-log)
  (let* ((initial
          (max 7
               (max ceil-value (+ floor-log 1))))
         (iterated
          (q5171652-iterate-step-bound
           initial floor-iterate)))
    (* iterated (expt 16 iterated))))

(defun q5171652-triangle-removal-bound
    (epsilon ceil-value floor-iterate floor-log)
  (let* ((x (/ epsilon 81))
         (regularity-bound
          (q5171652-regularity-bound
           ceil-value floor-iterate floor-log))
         (first-branch
          (/ 1 (* 2 (expt ceil-value 3))))
         (positive-factor
          (- 1 (/ (min 1 x) 4)))
         (small-quotient
          (/ x (* 16 regularity-bound)))
         (second-branch
          (* positive-factor
             (expt small-quotient 3))))
    (min first-branch second-branch)))

;; Expanding cornersTheoremBound(epsilon/9) makes x = epsilon/81 in
;; triangleRemovalBound. For its positive value t,
;;
;;   floor((27*t)^-1) + 1 <= n  iff  1 < 27*n*t.

(defun q5171652-bound-data-p
    (epsilon n ceil-value floor-iterate floor-log)
  (let* ((x (/ epsilon 81))
         (delta (/ x 8))
         (fifth-power (expt delta 5))
         (triangle-bound
          (q5171652-triangle-removal-bound
           epsilon ceil-value floor-iterate floor-log)))
    (and
     (q5171652-ceil-four-over-p x ceil-value)
     (q5171652-floor-four-over-fifth-power-p
      fifth-power floor-iterate)
     (q5171652-floor-log-four-p
      fifth-power floor-log)
     (< 1 (* 27 n triangle-bound)))))

(defun-sk q5171652-source-bound-at-most-p (epsilon n)
  (exists (ceil-value floor-iterate floor-log)
    (q5171652-bound-data-p
     epsilon n ceil-value floor-iterate floor-log)))

;; Duplicate-free proper lists of natural pairs represent exactly Finset
;; (Nat x Nat). The recursive membership tests below are therefore invariant
;; under list order and preserve the source finite-set semantics.

(defun q5171652-natural-pair-p (pair)
  (and
   (consp pair)
   (natp (car pair))
   (natp (cdr pair))))

(defun q5171652-finite-pair-set-p (set)
  (if (consp set)
      (and
       (q5171652-natural-pair-p (car set))
       (not (member-equal (car set) (cdr set)))
       (q5171652-finite-pair-set-p (cdr set)))
    (equal set nil)))

(defun q5171652-in-initial-square-p (set n)
  (if (consp set)
      (and
       (< (caar set) n)
       (< (cdar set) n)
       (q5171652-in-initial-square-p
        (cdr set) n))
    (equal set nil)))

;; FIRST = (x1,y1), SECOND = (x1,y2), and THIRD = (x2,y1). The additive
;; equation and x1 != x2 are exactly Mathlib's nontrivial corner condition.

(defun q5171652-corner-third-p (first second third)
  (and
   (equal (car first) (car second))
   (equal (cdr first) (cdr third))
   (equal (+ (car first) (cdr second))
          (+ (car third) (cdr first)))
   (not (equal (car first) (car third)))))

(defun q5171652-corner-with-first-second-p
    (first second remaining)
  (if (consp remaining)
      (or
       (q5171652-corner-third-p
        first second (car remaining))
       (q5171652-corner-with-first-second-p
        first second (cdr remaining)))
    nil))

(defun q5171652-corner-with-first-p
    (first set remaining-seconds)
  (if (consp remaining-seconds)
      (or
       (q5171652-corner-with-first-second-p
        first (car remaining-seconds) set)
       (q5171652-corner-with-first-p
        first set (cdr remaining-seconds)))
    nil))

(defun q5171652-has-nontrivial-corner-p
    (set remaining-firsts)
  (if (consp remaining-firsts)
      (or
       (q5171652-corner-with-first-p
        (car remaining-firsts) set set)
       (q5171652-has-nontrivial-corner-p
        set (cdr remaining-firsts)))
    nil))

(defun q5171652-density-at-least-p
    (epsilon n set)
  (<= (* epsilon n n) (len set)))

(defun thousand-theorems-q5171652-corners-theorem-nat-statement
    (epsilon n set)
  (implies
   (and
    (rationalp epsilon)
    (< 0 epsilon)
    (natp n)
    (q5171652-finite-pair-set-p set)
    (q5171652-in-initial-square-p set n)
    (q5171652-source-bound-at-most-p epsilon n)
    (q5171652-density-at-least-p epsilon n set))
   (q5171652-has-nontrivial-corner-p set set)))

(value-triple :itpeval-statement-checked)
:q
