;; Statement-only formalization of VERINA corpus artifact verina_basic_73,
;; catalog title "Match": a deterministic Unicode-string matcher accepts
;; equal-length inputs exactly when every pattern character equals the
;; corresponding input character or is the wildcard '?'. This file contains
;; no proof.

(in-package "ACL2")

;; A Lean String is represented bijectively by its finite list of Unicode
;; scalar values. This preserves the complete Lean Char domain rather than
;; restricting strings to ACL2's host character set.

(defun verina-basic-73-unicode-scalar-p (c)
  (and
   (natp c)
   (or
    (< c 55296)
    (and
     (< 57343 c)
     (< c 1114112)))))

(defun verina-basic-73-string-p (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (and
       (verina-basic-73-unicode-scalar-p (car s))
       (verina-basic-73-string-p (cdr s)))
    (equal s nil)))

;; This is exactly the source precondition on the two typed String inputs.

(defun verina-basic-73-match-precond (s p)
  (equal (len s) (len p)))

;; The source loop scans from index zero and stops at the first position whose
;; characters differ and whose pattern character is not '?', Unicode scalar
;; value 63. Passing the unscanned suffixes is an equivalent recursive state:
;; under the equal-length precondition, each CAR is precisely get! at the
;; current source index, and consuming both suffixes increments that index.

(defun verina-basic-73-match-loop (s-tail p-tail)
  (declare (xargs :measure (acl2-count s-tail)))
  (if (consp s-tail)
      (if (and
           (not (equal (car s-tail) (car p-tail)))
           (not (equal (car p-tail) 63)))
          nil
        (verina-basic-73-match-loop
         (cdr s-tail)
         (cdr p-tail)))
    t))

;; The proof-valued precondition argument is computationally irrelevant and is
;; erased. This applies the exact executable loop to both complete strings.

(defun verina-basic-73-match (s p)
  (verina-basic-73-match-loop s p))

;; List.get! returns the indexed character when present and Unicode NUL outside
;; the list. Every observation in the postcondition is in bounds for S, and
;; the precondition gives the same bound for P.

(defun verina-basic-73-char-at (index chars)
  (if (and
       (natp index)
       (< index (len chars)))
      (nth index chars)
    0))

;; This is the source postcondition's universal Nat quantifier over all valid
;; input-string indices.

(defun-sk verina-basic-73-every-index-matches-p (s p)
  (forall (index)
    (implies
     (and
      (natp index)
      (< index (len s)))
     (or
      (equal
       (verina-basic-73-char-at index s)
       (verina-basic-73-char-at index p))
      (equal
       (verina-basic-73-char-at index p)
       63)))))

;; This preserves the complete typed postcondition: RESULT is true if and only
;; if every source position either agrees with the pattern or has wildcard
;; '?' in the pattern. The proof-valued precondition argument is unused and
;; therefore erased.

(defun verina-basic-73-match-postcond (s p result)
  (and
   (verina-basic-73-string-p s)
   (verina-basic-73-string-p p)
   (booleanp result)
   (iff
    (equal result t)
    (verina-basic-73-every-index-matches-p s p))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every pair of Unicode strings satisfying exactly the source
;; equal-length precondition and applies the complete postcondition to the
;; exact executable result.

(defun-sk verina-basic-73-match-spec-satisfied-statement ()
  (forall (s p)
    (implies
     (and
      (verina-basic-73-string-p s)
      (verina-basic-73-string-p p)
      (verina-basic-73-match-precond s p))
     (verina-basic-73-match-postcond
      s
      p
      (verina-basic-73-match s p)))))

(value-triple :itpeval-statement-checked)
:q
