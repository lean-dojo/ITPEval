;; Statement-only formalization of VERINA corpus artifact verina_advanced_65,
;; "reverseString": a deterministic tail-recursive program reverses the
;; Unicode characters of a string while preserving its length. This file
;; contains no proof.

(in-package "ACL2")

;; A Lean String is canonically represented by its finite list of Unicode
;; scalar values. This preserves the full Char domain rather than restricting
;; strings to ACL2's host character set.

(defun verina-advanced-65-unicode-scalar-p (c)
  (and
   (natp c)
   (or
    (< c 55296)
    (and
     (< 57343 c)
     (< c 1114112)))))

(defun verina-advanced-65-string-p (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (and
       (verina-advanced-65-unicode-scalar-p (car s))
       (verina-advanced-65-string-p (cdr s)))
    (equal s nil)))

;; The source precondition is True. The String binder domain is explicit in
;; the final correctness statement.

(defun verina-advanced-65-reverse-string-precond (s)
  (declare (ignore s))
  t)

;; This is the source-local reverseAux definition: each unprocessed head is
;; pushed onto the accumulator before recurring on the tail.

(defun verina-advanced-65-reverse-aux (chars acc)
  (declare (xargs :measure (acl2-count chars)))
  (if (consp chars)
      (verina-advanced-65-reverse-aux
       (cdr chars)
       (cons (car chars) acc))
    acc))

;; Under the canonical representation, String.toList and String.mk are the
;; identity conversions between the represented string and its character
;; list. The proof-valued True precondition argument is computationally
;; irrelevant.

(defun verina-advanced-65-reverse-string (s)
  (verina-advanced-65-reverse-aux s nil))

(defun verina-advanced-65-reverse-string-postcond
    (s result)
  (and
   (verina-advanced-65-string-p s)
   (verina-advanced-65-string-p result)
   (equal (len result) (len s))
   (equal result (reverse s))))

;; This predicate is the unproved final correctness proposition connecting
;; the complete precondition and postcondition to the exact executable result.

(defun
    verina-advanced-65-reverse-string-spec-satisfied-statement
    (s)
  (implies
   (and
    (verina-advanced-65-string-p s)
    (verina-advanced-65-reverse-string-precond s))
   (verina-advanced-65-reverse-string-postcond
    s
    (verina-advanced-65-reverse-string s))))

(value-triple :itpeval-statement-checked)
:q
