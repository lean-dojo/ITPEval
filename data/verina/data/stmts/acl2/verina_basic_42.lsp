;; Statement-only formalization of VERINA corpus artifact verina_basic_42,
;; catalog title "countDigits": a deterministic Unicode-string program counts
;; exactly the characters between '0' and '9'. This file contains no proof.

(in-package "ACL2")

;; A Lean String is canonically represented by its finite list of Unicode
;; scalar values, preserving the complete Lean Char domain.

(defun verina-basic-42-unicode-scalar-p (c)
  (and
   (natp c)
   (or
    (< c 55296)
    (and
     (< 57343 c)
     (< c 1114112)))))

(defun verina-basic-42-string-p (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (and
       (verina-basic-42-unicode-scalar-p (car s))
       (verina-basic-42-string-p (cdr s)))
    (equal s nil)))

;; Unicode scalar values 48 and 57 are '0' and '9'. This Boolean predicate is
;; the source isDigit helper on the represented Char domain.

(defun verina-basic-42-is-digit (c)
  (and
   (verina-basic-42-unicode-scalar-p c)
   (<= 48 c)
   (<= c 57)))

;; The source precondition is True. The String binder domain remains explicit
;; in the final correctness statement.

(defun verina-basic-42-count-digits-precond (s)
  (declare (ignore s))
  t)

;; Under the canonical representation, String.toList is the identity. This
;; recursion is exactly List.filter isDigit.

(defun verina-basic-42-filter-digits (chars)
  (declare (xargs :measure (acl2-count chars)))
  (if (consp chars)
      (if (verina-basic-42-is-digit (car chars))
          (cons
           (car chars)
           (verina-basic-42-filter-digits (cdr chars)))
        (verina-basic-42-filter-digits (cdr chars)))
    nil))

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. ACL2 len on the filtered character list is exactly the
;; source List.length computation.

(defun verina-basic-42-count-digits (s)
  (len (verina-basic-42-filter-digits s)))

;; Lean Nat subtraction truncates at zero.

(defun verina-basic-42-nat-sub (left right)
  (nfix (- left right)))

;; This is the complete source postcondition, including both directed
;; truncated-subtraction equalities.

(defun verina-basic-42-count-digits-postcond
    (s result)
  (let ((digit-count
         (len (verina-basic-42-filter-digits s))))
    (and
     (verina-basic-42-string-p s)
     (natp result)
     (equal
      (verina-basic-42-nat-sub result digit-count)
      0)
     (equal
      (verina-basic-42-nat-sub digit-count result)
      0))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every Lean String, applies the source's True precondition, and connects
;; the complete postcondition to the exact executable result.

(defun-sk
    verina-basic-42-count-digits-spec-satisfied-statement
    ()
  (forall (s)
    (implies
     (and
      (verina-basic-42-string-p s)
      (verina-basic-42-count-digits-precond s))
     (verina-basic-42-count-digits-postcond
      s
      (verina-basic-42-count-digits s)))))

(value-triple :itpeval-statement-checked)
:q
