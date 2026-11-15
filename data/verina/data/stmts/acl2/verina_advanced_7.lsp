;; Statement-only formalization of VERINA corpus artifact verina_advanced_7,
;; "binaryToDecimal": a deterministic positional-power recursion converts a
;; big-endian list of binary natural-number digits to its decimal value, with
;; its fold-based natural-number correctness contract. This file contains no
;; proof.

(in-package "ACL2")

;; Lean's List Nat domain is represented by proper ACL2 lists of naturals.

(defun verina-advanced-7-nat-listp (digits)
  (declare (xargs :measure (acl2-count digits)))
  (if (consp digits)
      (and
       (natp (car digits))
       (verina-advanced-7-nat-listp (cdr digits)))
    (equal digits nil)))

;; This is digits.all (fun d => d = 0 or d = 1), with the source List Nat
;; binder domain made explicit.

(defun verina-advanced-7-binary-to-decimal-precond (digits)
  (declare (xargs :measure (acl2-count digits)))
  (if (consp digits)
      (and
       (natp (car digits))
       (or
        (equal (car digits) 0)
        (equal (car digits) 1))
       (verina-advanced-7-binary-to-decimal-precond
        (cdr digits)))
    (equal digits nil)))

;; Exact operational translation of the source local helper:
;; helper (first :: rest) = first * 2^(length rest) + helper rest.

(defun verina-advanced-7-binary-to-decimal-helper (digits)
  (declare (xargs :measure (acl2-count digits)))
  (if (consp digits)
      (+
       (*
        (car digits)
        (expt 2 (len (cdr digits))))
       (verina-advanced-7-binary-to-decimal-helper
        (cdr digits)))
    0))

;; The proof-valued precondition argument is computationally irrelevant, so
;; the executable function is precisely the helper applied to the input.

(defun verina-advanced-7-binary-to-decimal (digits)
  (verina-advanced-7-binary-to-decimal-helper digits))

;; This tail recursion is exactly
;; List.foldl (fun acc bit => acc * 2 + bit) 0 digits.

(defun verina-advanced-7-binary-foldl
    (remaining accumulator)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (verina-advanced-7-binary-foldl
       (cdr remaining)
       (+
        (* accumulator 2)
        (car remaining)))
    accumulator))

;; NFIX of an integer difference is Lean's truncated Nat subtraction on
;; natural-number operands.

(defun verina-advanced-7-nat-sub (left right)
  (if (and (natp left) (natp right))
      (nfix (- left right))
    0))

;; This preserves both subtraction-equals-zero conjuncts from the source
;; postcondition rather than replacing them textually by equality.

(defun verina-advanced-7-binary-to-decimal-postcond
    (digits result)
  (let ((folded-value
         (verina-advanced-7-binary-foldl digits 0)))
    (and
     (verina-advanced-7-nat-listp digits)
     (natp result)
     (equal
      (verina-advanced-7-nat-sub
       result
       folded-value)
      0)
     (equal
      (verina-advanced-7-nat-sub
       folded-value
       result)
      0))))

;; This predicate is the unproved final correctness proposition connecting the
;; complete precondition and postcondition to the exact executable result.

(defun
    verina-advanced-7-binary-to-decimal-spec-satisfied-statement
    (digits)
  (implies
   (verina-advanced-7-binary-to-decimal-precond digits)
   (verina-advanced-7-binary-to-decimal-postcond
    digits
    (verina-advanced-7-binary-to-decimal digits))))

(value-triple :itpeval-statement-checked)
:q
