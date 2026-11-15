;; Statement-only formalization of VERINA corpus artifact verina_basic_31,
;; catalog title "toUppercase": a deterministic Unicode-string program maps
;; ASCII lowercase letters to uppercase and leaves every other character
;; unchanged. This file contains no proof.

(in-package "ACL2")

;; A Lean String is represented bijectively by its finite list of Unicode
;; scalar values. This preserves the complete Char domain rather than
;; restricting strings to ACL2's host character set.

(defun verina-basic-31-unicode-scalar-p (c)
  (and
   (natp c)
   (or
    (< c 55296)
    (and
     (< 57343 c)
     (< c 1114112)))))

(defun verina-basic-31-string-p (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (and
       (verina-basic-31-unicode-scalar-p (car s))
       (verina-basic-31-string-p (cdr s)))
    (equal s nil)))

;; This is the source Boolean test 'a' <= c && c <= 'z', expressed through
;; the corresponding Unicode scalar values.

(defun verina-basic-31-is-lower-case (c)
  (and
   (<= 97 c)
   (<= c 122)))

;; NFIX of an integer difference is Lean natural-number subtraction on Nat.

(defun verina-basic-31-nat-sub (left right)
  (if (and
       (natp left)
       (natp right))
      (nfix (- left right))
    0))

;; The modulo result is below 128 and hence is already a valid argument to
;; Char.ofNat. Thus this exactly preserves shiftMinus32 on every source Char.

(defun verina-basic-31-shift-minus-32 (c)
  (mod
   (verina-basic-31-nat-sub c 32)
   128))

;; The source precondition is True. The String binder domain remains explicit
;; in the final correctness proposition.

(defun verina-basic-31-to-uppercase-precond (s)
  (declare (ignore s))
  t)

;; This structural recursion is exactly the source map over String.toList.
;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased in the target implementation.

(defun verina-basic-31-to-uppercase (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (cons
       (if (verina-basic-31-is-lower-case (car s))
           (verina-basic-31-shift-minus-32 (car s))
         (car s))
       (verina-basic-31-to-uppercase (cdr s)))
    nil))

;; Given the postcondition's equal-length equation, this aligned scan is
;; equivalent to its bounded universal quantifier over every string index.

(defun verina-basic-31-pointwise-uppercase-p (s result)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (and
       (consp result)
       (implies
        (verina-basic-31-is-lower-case (car s))
        (equal
         (car result)
         (verina-basic-31-shift-minus-32 (car s))))
       (implies
        (not (verina-basic-31-is-lower-case (car s)))
        (equal
         (car result)
         (car s)))
       (verina-basic-31-pointwise-uppercase-p
        (cdr s)
        (cdr result)))
    (equal s nil)))

;; This is the complete source postcondition: both values are Strings, their
;; lengths agree, lowercase characters are shifted, and all others are fixed.

(defun verina-basic-31-to-uppercase-postcond (s result)
  (and
   (verina-basic-31-string-p s)
   (verina-basic-31-string-p result)
   (equal (len result) (len s))
   (verina-basic-31-pointwise-uppercase-p
    s
    result)))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over the complete Unicode-string domain, applies the True precondition, and
;; connects the full postcondition to the exact executable result.

(defun-sk verina-basic-31-to-uppercase-spec-satisfied-statement ()
  (forall (s)
    (implies
     (and
      (verina-basic-31-string-p s)
      (verina-basic-31-to-uppercase-precond s))
     (verina-basic-31-to-uppercase-postcond
      s
      (verina-basic-31-to-uppercase s)))))

(value-triple :itpeval-statement-checked)
:q
