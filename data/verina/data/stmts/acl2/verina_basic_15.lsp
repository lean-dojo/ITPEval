;; Statement-only formalization of VERINA corpus artifact verina_basic_15,
;; catalog title "containsConsecutiveNumbers": a deterministic integer-array
;; program returns true exactly when some entry plus one equals the following
;; entry. This file contains no proof.

(in-package "ACL2")

;; ACL2 true lists of integers represent exactly the finite Array Int inputs.

(defun verina-basic-15-int-array-p (a)
  (if (consp a)
      (and
       (integerp (car a))
       (verina-basic-15-int-array-p (cdr a)))
    (equal a nil)))

;; The source precondition is True. The Array Int binder domain remains
;; explicit in the final correctness statement.

(defun verina-basic-15-contains-consecutive-numbers-precond (a)
  (declare (ignore a))
  t)

;; This adjacent-pair recursion is exactly the source mapIdx/any computation.
;; Arrays of size at most one return false; otherwise each in-bounds pair is
;; tested in increasing index order. The proof-valued precondition argument is
;; computationally irrelevant and is erased.

(defun verina-basic-15-contains-consecutive-numbers (a)
  (if (and
       (consp a)
       (consp (cdr a)))
      (if (equal
           (+ (car a) 1)
           (car (cdr a)))
          t
        (verina-basic-15-contains-consecutive-numbers
         (cdr a)))
    nil))

(defun verina-basic-15-bool-p (result)
  (or
   (equal result t)
   (equal result nil)))

;; Lean Nat subtraction truncates at zero.

(defun verina-basic-15-nat-sub (left right)
  (nfix (- left right)))

;; This preserves the source postcondition's existential Nat index and its
;; exact bound i < a.size - 1. Under that bound, both NTH accesses correspond
;; to the source's in-bounds getElem! operations.

(defun-sk verina-basic-15-has-consecutive-numbers-p (a)
  (exists (i)
    (and
     (natp i)
     (< i
        (verina-basic-15-nat-sub
         (len a)
         1))
     (equal
      (+ (nth i a) 1)
      (nth (+ i 1) a)))))

(defun verina-basic-15-contains-consecutive-numbers-postcond
    (a result)
  (and
   (verina-basic-15-int-array-p a)
   (verina-basic-15-bool-p result)
   (iff
    (verina-basic-15-has-consecutive-numbers-p a)
    result)))

;; This predicate is the unproved final correctness proposition. It preserves
;; the arbitrary finite Array Int input and True precondition, and applies the
;; complete postcondition to the exact executable result.

(defun-sk
    verina-basic-15-contains-consecutive-numbers-spec-satisfied-statement
    ()
  (forall (a)
    (implies
     (and
      (verina-basic-15-int-array-p a)
      (verina-basic-15-contains-consecutive-numbers-precond a))
     (verina-basic-15-contains-consecutive-numbers-postcond
      a
      (verina-basic-15-contains-consecutive-numbers a)))))

(value-triple :itpeval-statement-checked)
:q
