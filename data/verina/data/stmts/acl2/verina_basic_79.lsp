;; Statement-only formalization of VERINA corpus artifact verina_basic_79,
;; catalog title "onlineMax": a deterministic integer-array scan computes the
;; maximum among the first x entries and then returns the first later index
;; whose value is larger, or the final index if none exists. This file contains
;; no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-79-int-array-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (integerp (car a))
       (verina-basic-79-int-array-p (cdr a)))
    (equal a nil)))

;; Array.get! on Array Int returns the in-bounds entry and the inhabited
;; integer default zero outside the array.

(defun verina-basic-79-nth-default-zero (index a)
  (if (and
       (natp index)
       (< index (len a)))
      (nth index a)
    0))

;; This is Lean natural-number subtraction.

(defun verina-basic-79-nat-sub (left right)
  (nfix (- (nfix left) (nfix right))))

;; The source precondition is a.size > 0, x > 0, and x < a.size.

(defun verina-basic-79-online-max-precond (a x)
  (and
   (< 0 (len a))
   (< 0 x)
   (< x (len a))))

;; REMAINING is exactly x - i for source-natural arguments. Each recursive
;; step compares a[i]! with BEST, updates the accumulator on a strict increase,
;; and advances i. Thus this loop is the source findBest recursion with its
;; termination distance made explicit.

(defun verina-basic-79-find-best-loop
    (a index remaining best)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      best
    (let* ((entry
            (verina-basic-79-nth-default-zero index a))
           (new-best
            (if (> entry best)
                entry
              best)))
      (verina-basic-79-find-best-loop
       a
       (+ index 1)
       (- remaining 1)
       new-best))))

(defun verina-basic-79-find-best (a x i best)
  (verina-basic-79-find-best-loop
   a
   (nfix i)
   (verina-basic-79-nat-sub x i)
   best))

;; REMAINING is exactly a.size - i for source-natural i. The first entry
;; strictly larger than M is returned immediately; exhausting the suffix
;; returns a.size - 1. This is the complete deterministic findP computation.

(defun verina-basic-79-find-p-loop
    (a m index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (verina-basic-79-nat-sub (len a) 1)
    (if (>
         (verina-basic-79-nth-default-zero index a)
         m)
        index
      (verina-basic-79-find-p-loop
       a
       m
       (+ index 1)
       (- remaining 1)))))

(defun verina-basic-79-find-p (a x m i)
  (declare (ignore x))
  (verina-basic-79-find-p-loop
   a
   m
   (nfix i)
   (verina-basic-79-nat-sub (len a) i)))

;; Int x Nat is represented bijectively by a cons whose car is the integer
;; component and whose cdr is the natural component.

(defun verina-basic-79-int-nat-pair-p (result)
  (and
   (consp result)
   (integerp (car result))
   (natp (cdr result))))

;; The proof-valued precondition argument is computationally irrelevant and is
;; erased. These local bindings and helper calls are exactly the Lean onlineMax
;; implementation.

(defun verina-basic-79-online-max (a x)
  (let* ((best
          (verina-basic-79-nth-default-zero 0 a))
         (m
          (verina-basic-79-find-best a x 1 best))
         (p
          (verina-basic-79-find-p a x m x)))
    (cons m p)))

;; These predicates preserve the source postcondition's existential and
;; universal Nat binders with their exact bounds.

(defun-sk verina-basic-79-prefix-at-most-p (a x m)
  (forall (i)
    (implies
     (and
      (natp i)
      (< i x))
     (<=
      (verina-basic-79-nth-default-zero i a)
      m))))

(defun-sk verina-basic-79-prefix-attains-p (a x m)
  (exists (i)
    (and
     (natp i)
     (< i x)
     (equal
      (verina-basic-79-nth-default-zero i a)
      m))))

(defun-sk verina-basic-79-between-at-most-p (a x p m)
  (forall (i)
    (implies
     (and
      (natp i)
      (<= x i)
      (< i p))
     (<=
      (verina-basic-79-nth-default-zero i a)
      m))))

(defun-sk verina-basic-79-suffix-at-most-p (a x m)
  (forall (i)
    (implies
     (and
      (natp i)
      (<= x i)
      (< i (len a)))
     (<=
      (verina-basic-79-nth-default-zero i a)
      m))))

;; This is the complete source postcondition after destructuring RESULT as
;; (m, p). Its proof-valued precondition argument is unused and is erased.

(defun verina-basic-79-online-max-postcond
    (a x result)
  (and
   (verina-basic-79-int-array-p a)
   (natp x)
   (verina-basic-79-int-nat-pair-p result)
   (let ((m (car result))
         (p (cdr result)))
     (and
      (<= x p)
      (< p (len a))
      (verina-basic-79-prefix-at-most-p a x m)
      (verina-basic-79-prefix-attains-p a x m)
      (verina-basic-79-between-at-most-p a x p m)
      (or
       (>
        (verina-basic-79-nth-default-zero p a)
        m)
       (and
        (equal
         p
         (verina-basic-79-nat-sub (len a) 1))
        (verina-basic-79-suffix-at-most-p
         a
         x
         m)))))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over the complete Array Int and Nat domains, assumes exactly the source
;; precondition, and applies the complete postcondition to the exact executable
;; result.

(defun-sk
    verina-basic-79-online-max-spec-satisfied-statement
    ()
  (forall (a x)
    (implies
     (and
      (verina-basic-79-int-array-p a)
      (natp x)
      (verina-basic-79-online-max-precond a x))
     (verina-basic-79-online-max-postcond
      a
      x
      (verina-basic-79-online-max a x)))))

(value-triple :itpeval-statement-checked)
:q
