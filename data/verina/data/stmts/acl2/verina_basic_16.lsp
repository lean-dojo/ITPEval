;; Statement-only formalization of VERINA corpus artifact verina_basic_16,
;; catalog title "replaceChars": a deterministic Unicode-string program
;; replaces every occurrence of one character with another while preserving
;; length and all other positions. This file contains no proof.

(in-package "ACL2")

;; A Lean String is canonically represented by its finite list of Unicode
;; scalar values, preserving the complete Lean Char domain.

(defun verina-basic-16-unicode-scalar-p (c)
  (and
   (natp c)
   (or
    (< c 55296)
    (and
     (< 57343 c)
     (< c 1114112)))))

(defun verina-basic-16-string-p (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (and
       (verina-basic-16-unicode-scalar-p (car s))
       (verina-basic-16-string-p (cdr s)))
    (equal s nil)))

;; The source precondition is True. The typed input domains remain explicit
;; in the final correctness statement.

(defun verina-basic-16-replace-chars-precond
    (s old-char new-char)
  (declare (ignore s old-char new-char))
  t)

;; This structural recursion is exactly the source String.toList map followed
;; by String.mk. The proof-valued True precondition argument is computationally
;; irrelevant and is erased.

(defun verina-basic-16-replace-chars
    (s old-char new-char)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (cons
       (if (equal (car s) old-char)
           new-char
         (car s))
       (verina-basic-16-replace-chars
        (cdr s)
        old-char
        new-char))
    nil))

;; List.get! is only observed at in-bounds indices in a true postcondition.
;; This total accessor supplies Unicode NUL outside that range.

(defun verina-basic-16-char-at (i chars)
  (if (and
       (natp i)
       (< i (len chars)))
      (nth i chars)
    0))

;; This preserves the source postcondition's universal Nat index and its two
;; conditional clauses for replaced and unchanged characters.

(defun-sk verina-basic-16-correct-at-every-index-p
    (s old-char new-char result)
  (forall (i)
    (implies
     (and
      (natp i)
      (< i (len s)))
     (and
      (implies
       (equal
        (verina-basic-16-char-at i s)
        old-char)
       (equal
        (verina-basic-16-char-at i result)
        new-char))
      (implies
       (not
        (equal
         (verina-basic-16-char-at i s)
         old-char))
       (equal
        (verina-basic-16-char-at i result)
        (verina-basic-16-char-at i s)))))))

(defun verina-basic-16-replace-chars-postcond
    (s old-char new-char result)
  (and
   (verina-basic-16-string-p s)
   (verina-basic-16-unicode-scalar-p old-char)
   (verina-basic-16-unicode-scalar-p new-char)
   (verina-basic-16-string-p result)
   (equal (len result) (len s))
   (verina-basic-16-correct-at-every-index-p
    s
    old-char
    new-char
    result)))

;; This predicate is the unproved final correctness proposition. It applies
;; the complete postcondition to the exact executable result for every typed
;; input satisfying the source's True precondition.

(defun-sk
    verina-basic-16-replace-chars-spec-satisfied-statement
    ()
  (forall (s old-char new-char)
    (implies
     (and
      (verina-basic-16-string-p s)
      (verina-basic-16-unicode-scalar-p old-char)
      (verina-basic-16-unicode-scalar-p new-char)
      (verina-basic-16-replace-chars-precond
       s
       old-char
       new-char))
     (verina-basic-16-replace-chars-postcond
      s
      old-char
      new-char
      (verina-basic-16-replace-chars
       s
       old-char
       new-char)))))

(value-triple :itpeval-statement-checked)
:q
