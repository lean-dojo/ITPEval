;; Statement-only formalization of VERINA corpus artifact verina_basic_36,
;; catalog title "replaceWithColon": a deterministic Unicode-string program
;; replaces spaces, commas, and dots with colons while preserving length and
;; every other character. This file contains no proof.

(in-package "ACL2")

;; A Lean String is canonically represented by its finite list of Unicode
;; scalar values, preserving the complete Lean Char domain.

(defun verina-basic-36-unicode-scalar-p (c)
  (and
   (natp c)
   (or
    (< c 55296)
    (and
     (< 57343 c)
     (< c 1114112)))))

(defun verina-basic-36-string-p (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (and
       (verina-basic-36-unicode-scalar-p (car s))
       (verina-basic-36-string-p (cdr s)))
    (equal s nil)))

;; Unicode scalar values 32, 44, and 46 are space, comma, and dot.

(defun verina-basic-36-is-space-comma-dot (c)
  (or
   (equal c 32)
   (equal c 44)
   (equal c 46)))

;; The source precondition is True. The String binder domain remains explicit
;; in the final correctness statement.

(defun verina-basic-36-replace-with-colon-precond (s)
  (declare (ignore s))
  t)

;; Under the canonical representation, this structural recursion is exactly
;; String.toList, List.map with the source conditional, and String.mk. Unicode
;; scalar value 58 is colon. The proof-valued True precondition argument is
;; computationally irrelevant and is erased.

(defun verina-basic-36-replace-with-colon (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (cons
       (if (verina-basic-36-is-space-comma-dot (car s))
           58
         (car s))
       (verina-basic-36-replace-with-colon (cdr s)))
    nil))

;; List.get! is only observed at in-bounds indices in the source postcondition.
;; This total accessor supplies Unicode NUL outside that range.

(defun verina-basic-36-char-at (i chars)
  (if (and
       (natp i)
       (< i (len chars)))
      (nth i chars)
    0))

;; This preserves the universal Nat index and both conditional clauses for
;; replaced and unchanged characters.

(defun-sk verina-basic-36-correct-at-every-index-p
    (s result)
  (forall (i)
    (implies
     (and
      (natp i)
      (< i (len s)))
     (and
      (implies
       (verina-basic-36-is-space-comma-dot
        (verina-basic-36-char-at i s))
       (equal
        (verina-basic-36-char-at i result)
        58))
      (implies
       (not
        (verina-basic-36-is-space-comma-dot
         (verina-basic-36-char-at i s)))
       (equal
        (verina-basic-36-char-at i result)
        (verina-basic-36-char-at i s)))))))

(defun verina-basic-36-replace-with-colon-postcond
    (s result)
  (and
   (verina-basic-36-string-p s)
   (verina-basic-36-string-p result)
   (equal (len result) (len s))
   (verina-basic-36-correct-at-every-index-p
    s
    result)))

;; This predicate is the unproved final correctness proposition. It applies
;; the complete postcondition to the exact executable result for every typed
;; input satisfying the source's True precondition.

(defun-sk
    verina-basic-36-replace-with-colon-spec-satisfied-statement
    ()
  (forall (s)
    (implies
     (and
      (verina-basic-36-string-p s)
      (verina-basic-36-replace-with-colon-precond s))
     (verina-basic-36-replace-with-colon-postcond
      s
      (verina-basic-36-replace-with-colon s)))))

(value-triple :itpeval-statement-checked)
:q
