;; Statement-only formalization of VERINA corpus artifact verina_advanced_67,
;; "runLengthEncode": a deterministic Unicode-string program groups consecutive
;; equal characters into positive run lengths whose decoding is the input.
;; This file contains no proof.

(in-package "ACL2")

;; A Lean String is canonically represented by its finite list of Unicode
;; scalar values. This preserves the full Char domain rather than restricting
;; strings to ACL2's host character set.

(defun verina-advanced-67-unicode-scalar-p (c)
  (and
   (natp c)
   (or
    (< c 55296)
    (and
     (< 57343 c)
     (< c 1114112)))))

(defun verina-advanced-67-string-p (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (and
       (verina-advanced-67-unicode-scalar-p (car s))
       (verina-advanced-67-string-p (cdr s)))
    (equal s nil)))

;; A Lean (Char x Nat) value is represented by the dotted pair
;; (character . count), and the result type is a proper list of such pairs.

(defun verina-advanced-67-rle-pair-p (pair)
  (and
   (consp pair)
   (verina-advanced-67-unicode-scalar-p (car pair))
   (natp (cdr pair))))

(defun verina-advanced-67-rle-list-p (pairs)
  (declare (xargs :measure (acl2-count pairs)))
  (if (consp pairs)
      (and
       (verina-advanced-67-rle-pair-p (car pairs))
       (verina-advanced-67-rle-list-p (cdr pairs)))
    (equal pairs nil)))

;; The source precondition is True. The String binder domain is explicit in
;; the final correctness statement.

(defun verina-advanced-67-run-length-encode-precond (s)
  (declare (ignore s))
  t)

;; ACC stores completed and current runs in reverse order. Each source
;; character either increments the current run or starts a new run at the
;; front. Reversing ACC at exhaustion is exactly the source encodeAux.

(defun verina-advanced-67-encode-aux (acc rest)
  (declare (xargs :measure (acl2-count rest)))
  (if (consp rest)
      (let* ((h (car rest))
             (tail (cdr rest)))
        (if (consp acc)
            (let* ((current (car acc))
                   (ch (car current))
                   (count (cdr current))
                   (acc-tail (cdr acc)))
              (if (equal ch h)
                  (verina-advanced-67-encode-aux
                   (cons (cons ch (+ count 1)) acc-tail)
                   tail)
                (verina-advanced-67-encode-aux
                 (cons
                  (cons h 1)
                  (cons (cons ch count) acc-tail))
                 tail)))
          (verina-advanced-67-encode-aux
           (list (cons h 1))
           tail)))
    (reverse acc)))

;; String.data is the represented scalar list. The proof-valued True
;; precondition argument is computationally irrelevant, so this wrapper
;; preserves the complete executable source program.

(defun verina-advanced-67-run-length-encode (s)
  (let* ((chars s)
         (encoded
          (verina-advanced-67-encode-aux nil chars)))
    encoded))

;; These definitions reproduce List.replicate, String.mk, string append, and
;; the source decodeRLE recursion on the canonical scalar-list representation.

(defun verina-advanced-67-replicate-char (count ch)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons
     ch
     (verina-advanced-67-replicate-char
      (- count 1)
      ch))))

(defun verina-advanced-67-decode-rle (pairs)
  (declare (xargs :measure (acl2-count pairs)))
  (if (consp pairs)
      (append
       (verina-advanced-67-replicate-char
        (cdr (car pairs))
        (car (car pairs)))
       (verina-advanced-67-decode-rle (cdr pairs)))
    nil))

;; These two recursions are equivalent to the source universal conditions:
;; every run count is positive, and every pair at index i has a character
;; different from the pair at index i+1 whenever i < length - 1.

(defun verina-advanced-67-all-counts-positive-p (pairs)
  (declare (xargs :measure (acl2-count pairs)))
  (if (consp pairs)
      (and
       (< 0 (cdr (car pairs)))
       (verina-advanced-67-all-counts-positive-p
        (cdr pairs)))
    t))

(defun verina-advanced-67-adjacent-characters-distinct-p
    (pairs)
  (declare (xargs :measure (acl2-count pairs)))
  (if (and (consp pairs) (consp (cdr pairs)))
      (and
       (not
        (equal
         (car (car pairs))
         (car (car (cdr pairs)))))
       (verina-advanced-67-adjacent-characters-distinct-p
        (cdr pairs)))
    t))

(defun verina-advanced-67-run-length-encode-postcond
    (s result)
  (and
   (verina-advanced-67-string-p s)
   (verina-advanced-67-rle-list-p result)
   (verina-advanced-67-all-counts-positive-p result)
   (verina-advanced-67-adjacent-characters-distinct-p result)
   (equal
    (verina-advanced-67-decode-rle result)
    s)))

;; This predicate is the unproved final correctness proposition connecting
;; the source precondition and postcondition to the exact executable result.

(defun
    verina-advanced-67-run-length-encode-spec-satisfied-statement
    (s)
  (implies
   (and
    (verina-advanced-67-string-p s)
    (verina-advanced-67-run-length-encode-precond s))
   (verina-advanced-67-run-length-encode-postcond
    s
    (verina-advanced-67-run-length-encode s))))

(value-triple :itpeval-statement-checked)
:q
