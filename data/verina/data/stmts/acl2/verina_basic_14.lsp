;; Statement-only formalization of VERINA corpus artifact verina_basic_14,
;; catalog title "containsZ": a deterministic Unicode-string program returns
;; true exactly when the string contains lowercase or uppercase z. This file
;; contains no proof.

(in-package "ACL2")

;; A Lean String is canonically represented by its finite list of Unicode
;; scalar values. This preserves the full Char domain rather than restricting
;; strings to ACL2's host character set.

(defun verina-basic-14-unicode-scalar-p (c)
  (and
   (natp c)
   (or
    (< c 55296)
    (and
     (< 57343 c)
     (< c 1114112)))))

(defun verina-basic-14-string-p (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (and
       (verina-basic-14-unicode-scalar-p (car s))
       (verina-basic-14-string-p (cdr s)))
    (equal s nil)))

;; The source precondition is True. The String binder domain remains explicit
;; in the final correctness statement.

(defun verina-basic-14-contains-z-precond (s)
  (declare (ignore s))
  t)

;; Unicode scalar values 122 and 90 are respectively 'z' and 'Z'. This
;; recursion is exactly String.toList.any with the source Boolean predicate.
;; The proof-valued True precondition argument is computationally irrelevant.

(defun verina-basic-14-contains-z (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (if (or
           (equal (car s) 122)
           (equal (car s) 90))
          t
        (verina-basic-14-contains-z (cdr s)))
    nil))

(defun verina-basic-14-bool-p (result)
  (or
   (equal result t)
   (equal result nil)))

;; Structural membership in the represented character list is equivalent to
;; the source existential witness x in s.toList with x = 'z' or x = 'Z'.

(defun verina-basic-14-has-z-or-uppercase-z-p (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (or
       (equal (car s) 122)
       (equal (car s) 90)
       (verina-basic-14-has-z-or-uppercase-z-p (cdr s)))
    nil))

(defun verina-basic-14-contains-z-postcond (s result)
  (and
   (verina-basic-14-string-p s)
   (verina-basic-14-bool-p result)
   (iff
    (verina-basic-14-has-z-or-uppercase-z-p s)
    result)))

;; This predicate is the unproved final correctness proposition. It preserves
;; the arbitrary Unicode-string input and True precondition, and applies the
;; complete postcondition to the exact executable result.

(defun-sk verina-basic-14-contains-z-spec-satisfied-statement ()
  (forall (s)
    (implies
     (and
      (verina-basic-14-string-p s)
      (verina-basic-14-contains-z-precond s))
     (verina-basic-14-contains-z-postcond
      s
      (verina-basic-14-contains-z s)))))

(value-triple :itpeval-statement-checked)
:q
