;; Statement-only formalization of VERINA corpus artifact verina_basic_23,
;; catalog title "differenceMinMax": a deterministic nonempty integer-array
;; scan returns the maximum element minus the minimum element, with correctness
;; stated against independent minimum and maximum folds. This file contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements are arbitrary integers.

(defun verina-basic-23-int-array-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (integerp (car a))
       (verina-basic-23-int-array-p (cdr a)))
    (equal a nil)))

;; The source precondition a.size > 0 is exactly list nonemptiness.

(defun verina-basic-23-difference-min-max-precond (a)
  (< 0 (len a)))

;; The source local loop starts after the first element and carries the
;; smallest and largest values seen so far. Structural recursion over the
;; remaining suffix is the exact list representation of its increasing index.

(defun verina-basic-23-difference-min-max-loop
    (remaining min-value max-value)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (let* ((x (car remaining))
             (new-min
              (if (< x min-value)
                  x
                min-value))
             (new-max
              (if (> x max-value)
                  x
                max-value)))
        (verina-basic-23-difference-min-max-loop
         (cdr remaining)
         new-min
         new-max))
    (- max-value min-value)))

;; The proof-valued precondition argument is computationally irrelevant and is
;; erased. On every source-valid input this initializes from a[0] and scans
;; exactly the entries at indices 1 through a.size - 1. The empty branch is
;; unreachable under the source precondition.

(defun verina-basic-23-difference-min-max (a)
  (if (consp a)
      (verina-basic-23-difference-min-max-loop
       (cdr a)
       (car a)
       (car a))
    0))

;; These two recursions independently reproduce the source Array.foldl
;; computations over the full array, including its first element.

(defun verina-basic-23-min-fold (remaining accumulator)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (let ((x (car remaining)))
        (verina-basic-23-min-fold
         (cdr remaining)
         (if (< x accumulator)
             x
           accumulator)))
    accumulator))

(defun verina-basic-23-max-fold (remaining accumulator)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (let ((x (car remaining)))
        (verina-basic-23-max-fold
         (cdr remaining)
         (if (> x accumulator)
             x
           accumulator)))
    accumulator))

;; The source postcondition states result + folded minimum = folded maximum.
;; Its proof-valued precondition argument is unused and is erased.

(defun verina-basic-23-difference-min-max-postcond
    (a result)
  (and
   (verina-basic-23-int-array-p a)
   (integerp result)
   (equal
    (+ result
       (verina-basic-23-min-fold a (car a)))
    (verina-basic-23-max-fold a (car a)))))

;; This predicate is the unproved final correctness proposition. It preserves
;; the arbitrary Array Int input and nonempty precondition, and applies the
;; complete postcondition to the exact executable result.

(defun-sk
    verina-basic-23-difference-min-max-spec-satisfied-statement
    ()
  (forall (a)
    (implies
     (and
      (verina-basic-23-int-array-p a)
      (verina-basic-23-difference-min-max-precond a))
     (verina-basic-23-difference-min-max-postcond
      a
      (verina-basic-23-difference-min-max a)))))

(value-triple :itpeval-statement-checked)
:q
