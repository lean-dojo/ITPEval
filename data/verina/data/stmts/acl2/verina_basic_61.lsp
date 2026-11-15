;; Statement-only formalization of VERINA corpus artifact verina_basic_61,
;; catalog title "allDigits": a deterministic Unicode-string program returns
;; true exactly when every character is an ASCII decimal digit. This file
;; contains no proof.

(in-package "ACL2")

;; A Lean String is canonically represented by its finite list of Unicode
;; scalar values. This preserves the complete Lean Char domain rather than
;; restricting strings to ACL2's host character set.

(defun verina-basic-61-unicode-scalar-p (c)
  (and
   (natp c)
   (or
    (< c 55296)
    (and
     (< 57343 c)
     (< c 1114112)))))

(defun verina-basic-61-string-p (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (and
       (verina-basic-61-unicode-scalar-p (car s))
       (verina-basic-61-string-p (cdr s)))
    (equal s nil)))

;; Unicode scalar values 48 and 57 are '0' and '9'. This Boolean predicate is
;; exactly the source isDigit helper on the represented Char domain.

(defun verina-basic-61-is-digit (c)
  (and
   (verina-basic-61-unicode-scalar-p c)
   (<= 48 c)
   (<= c 57)))

;; The source precondition is True. The String binder domain remains explicit
;; in the final correctness proposition.

(defun verina-basic-61-all-digits-precond (s)
  (declare (ignore s))
  t)

;; An iterator state is represented by the unprocessed suffix of the source
;; string. Empty means atEnd; otherwise curr is the head and next is the tail.
;; The recursion therefore preserves the source's short-circuit computation.

(defun verina-basic-61-all-digits-loop (remaining)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (if (not (verina-basic-61-is-digit (car remaining)))
          nil
        (verina-basic-61-all-digits-loop (cdr remaining)))
    t))

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. The initial iterator over S is its complete character list.

(defun verina-basic-61-all-digits (s)
  (verina-basic-61-all-digits-loop s))

;; This is the postcondition's universal quantifier over every character in
;; String.toList, which is the represented list itself.

(defun-sk verina-basic-61-every-character-is-digit-p (s)
  (forall (c)
    (implies
     (member-equal c s)
     (verina-basic-61-is-digit c))))

(defun verina-basic-61-bool-p (result)
  (or
   (equal result t)
   (equal result nil)))

;; This is the complete source postcondition: RESULT is true if and only if
;; every character of S satisfies the source isDigit helper.

(defun verina-basic-61-all-digits-postcond (s result)
  (and
   (verina-basic-61-string-p s)
   (verina-basic-61-bool-p result)
   (iff
    (equal result t)
    (verina-basic-61-every-character-is-digit-p s))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every Lean String, assumes exactly the source True precondition, and
;; applies the complete postcondition to the exact executable result.

(defun-sk verina-basic-61-all-digits-spec-satisfied-statement ()
  (forall (s)
    (implies
     (and
      (verina-basic-61-string-p s)
      (verina-basic-61-all-digits-precond s))
     (verina-basic-61-all-digits-postcond
      s
      (verina-basic-61-all-digits s)))))

(value-triple :itpeval-statement-checked)
:q
