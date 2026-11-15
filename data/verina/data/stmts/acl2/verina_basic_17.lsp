;; Statement-only formalization of VERINA corpus artifact verina_basic_17,
;; catalog title "toLowercase": a deterministic Unicode-string program maps
;; each ASCII uppercase letter to its lowercase counterpart, preserves every
;; other character, and preserves string length. This file contains no proof.

(in-package "ACL2")

;; A Lean String is canonically represented by its finite list of Unicode
;; scalar values, preserving the complete Lean Char domain.

(defun verina-basic-17-unicode-scalar-p (c)
  (and
   (natp c)
   (or
    (< c 55296)
    (and
     (< 57343 c)
     (< c 1114112)))))

(defun verina-basic-17-string-p (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (and
       (verina-basic-17-unicode-scalar-p (car s))
       (verina-basic-17-string-p (cdr s)))
    (equal s nil)))

;; These are the source isUpperCase and Char.ofNat helpers. Char.ofNat returns
;; Unicode NUL when its natural-number input is not a Unicode scalar value.

(defun verina-basic-17-is-uppercase (c)
  (and
   (<= 65 c)
   (<= c 90)))

(defun verina-basic-17-char-of-nat (n)
  (if (verina-basic-17-unicode-scalar-p n)
      n
    0))

(defun verina-basic-17-shift32 (c)
  (verina-basic-17-char-of-nat (+ c 32)))

;; The source precondition is True. The String binder domain remains explicit
;; in the final correctness statement.

(defun verina-basic-17-to-lowercase-precond (s)
  (declare (ignore s))
  t)

;; Under the canonical representation, String.toList and String.mk are the
;; identity conversions around this exact List.map computation. The
;; proof-valued True precondition argument is computationally irrelevant.

(defun verina-basic-17-to-lowercase (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (cons
       (if (verina-basic-17-is-uppercase (car s))
           (verina-basic-17-shift32 (car s))
         (car s))
       (verina-basic-17-to-lowercase (cdr s)))
    nil))

;; List.get! is total in Lean. Unicode NUL is its default character, matching
;; this accessor outside the natural in-bounds case.

(defun verina-basic-17-char-at (i chars)
  (if (and
       (natp i)
       (< i (len chars)))
      (nth i chars)
    0))

;; This preserves the postcondition's universal Nat index and both conditional
;; clauses for uppercase and non-uppercase input characters.

(defun-sk verina-basic-17-correct-at-every-index-p
    (s result)
  (forall (i)
    (implies
     (and
      (natp i)
      (< i (len s)))
     (and
      (implies
       (verina-basic-17-is-uppercase
        (verina-basic-17-char-at i s))
       (equal
        (verina-basic-17-char-at i result)
        (verina-basic-17-shift32
         (verina-basic-17-char-at i s))))
      (implies
       (not
        (verina-basic-17-is-uppercase
         (verina-basic-17-char-at i s)))
       (equal
        (verina-basic-17-char-at i result)
        (verina-basic-17-char-at i s)))))))

(defun verina-basic-17-to-lowercase-postcond
    (s result)
  (and
   (verina-basic-17-string-p s)
   (verina-basic-17-string-p result)
   (equal (len result) (len s))
   (verina-basic-17-correct-at-every-index-p
    s
    result)))

;; This predicate is the unproved final correctness proposition. It preserves
;; the arbitrary Unicode-string input and True precondition, and applies the
;; complete postcondition to the exact executable result.

(defun-sk
    verina-basic-17-to-lowercase-spec-satisfied-statement
    ()
  (forall (s)
    (implies
     (and
      (verina-basic-17-string-p s)
      (verina-basic-17-to-lowercase-precond s))
     (verina-basic-17-to-lowercase-postcond
      s
      (verina-basic-17-to-lowercase s)))))

(value-triple :itpeval-statement-checked)
:q
