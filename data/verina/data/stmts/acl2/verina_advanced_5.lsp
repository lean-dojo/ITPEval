;; Statement-only formalization of VERINA corpus artifact verina_advanced_5,
;; "addTwoNumbers": two canonical nonempty reverse-order decimal digit lists
;; are added by a deterministic carry recursion, with the resulting digit
;; list's arithmetic and canonical-form correctness contract. This file
;; contains no proof.

(in-package "ACL2")

;; Lean's List Nat domain is represented by proper ACL2 lists of naturals.

(defun verina-advanced-5-nat-listp (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (natp (car xs))
       (verina-advanced-5-nat-listp (cdr xs)))
    (equal xs nil)))

;; This is the source little-endian decimal evaluation:
;; listToNat (d :: ds) = d + 10 * listToNat ds.

(defun verina-advanced-5-list-to-nat (digits)
  (declare (xargs :measure (acl2-count digits)))
  (if (consp digits)
      (+
       (car digits)
       (* 10
          (verina-advanced-5-list-to-nat
           (cdr digits))))
    0))

;; List.getLast! on List Nat returns zero on the empty list. The precondition
;; only uses it on nonempty lists, but the total default behavior is retained.

(defun verina-advanced-5-get-last-default-zero (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (if (consp (cdr xs))
          (verina-advanced-5-get-last-default-zero
           (cdr xs))
        (car xs))
    0))

(defun verina-advanced-5-decimal-digit-listp (digits)
  (declare (xargs :measure (acl2-count digits)))
  (if (consp digits)
      (and
       (natp (car digits))
       (< (car digits) 10)
       (verina-advanced-5-decimal-digit-listp
        (cdr digits)))
    (equal digits nil)))

;; Besides making the implicit List Nat binder domains explicit, this is the
;; exact source precondition: both lists are nonempty decimal digit lists and
;; have no most-significant zero unless the represented number is zero.

(defun verina-advanced-5-add-two-numbers-precond (l1 l2)
  (and
   (verina-advanced-5-nat-listp l1)
   (verina-advanced-5-nat-listp l2)
   (consp l1)
   (consp l2)
   (verina-advanced-5-decimal-digit-listp l1)
   (verina-advanced-5-decimal-digit-listp l2)
   (or
    (not
     (equal
      (verina-advanced-5-get-last-default-zero l1)
      0))
    (equal l1 (list 0)))
   (or
    (not
     (equal
      (verina-advanced-5-get-last-default-zero l2)
      0))
    (equal l2 (list 0)))))

;; Exact operational translation of the source local addAux. Every recursive
;; call removes one input digit, and the final carry is emitted precisely when
;; it is nonzero.

(defun verina-advanced-5-add-aux (l1 l2 carry)
  (declare
   (xargs
    :measure
    (+
     (acl2-count l1)
     (acl2-count l2))))
  (cond
   ((and (consp l1) (consp l2))
    (let ((sum
           (+
            (car l1)
            (car l2)
            carry)))
      (cons
       (mod sum 10)
       (verina-advanced-5-add-aux
        (cdr l1)
        (cdr l2)
        (floor sum 10)))))
   ((consp l1)
    (let ((sum (+ (car l1) carry)))
      (cons
       (mod sum 10)
       (verina-advanced-5-add-aux
        (cdr l1)
        nil
        (floor sum 10)))))
   ((consp l2)
    (let ((sum (+ (car l2) carry)))
      (cons
       (mod sum 10)
       (verina-advanced-5-add-aux
        nil
        (cdr l2)
        (floor sum 10)))))
   ((equal carry 0)
    nil)
   (t
    (list carry))))

;; The source proof-valued precondition argument is computationally erased.
;; The final statement below supplies that same precondition explicitly.

(defun verina-advanced-5-add-two-numbers (l1 l2)
  (verina-advanced-5-add-aux l1 l2 0))

;; This is the full source postcondition, including the implicit result type:
;; numeric equality, decimal digits, and no most-significant zero except for
;; the uniquely specified zero-plus-zero result.

(defun verina-advanced-5-add-two-numbers-postcond
    (l1 l2 result)
  (and
   (verina-advanced-5-nat-listp l1)
   (verina-advanced-5-nat-listp l2)
   (verina-advanced-5-nat-listp result)
   (equal
    (verina-advanced-5-list-to-nat result)
    (+
     (verina-advanced-5-list-to-nat l1)
     (verina-advanced-5-list-to-nat l2)))
   (verina-advanced-5-decimal-digit-listp result)
   (or
    (not
     (equal
      (verina-advanced-5-get-last-default-zero result)
      0))
    (and
     (equal l1 (list 0))
     (equal l2 (list 0))
     (equal result (list 0))))))

;; This predicate is the unproved final correctness proposition connecting
;; the complete precondition and postcondition to the exact executable result.

(defun
    verina-advanced-5-add-two-numbers-spec-satisfied-statement
    (l1 l2)
  (implies
   (verina-advanced-5-add-two-numbers-precond l1 l2)
   (verina-advanced-5-add-two-numbers-postcond
    l1
    l2
    (verina-advanced-5-add-two-numbers l1 l2))))

(value-triple :itpeval-statement-checked)
:q
