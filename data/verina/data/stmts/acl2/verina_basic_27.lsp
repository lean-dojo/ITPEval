;; Statement-only formalization of VERINA corpus artifact verina_basic_27,
;; catalog title "findFirstRepeatedChar": a deterministic Unicode-string
;; program returns the first character encountered for a second time, or none,
;; with its complete distinct-prefix correctness contract. This file contains
;; no proof.

(in-package "ACL2")

;; A Lean String is canonically represented by its finite list of Unicode
;; scalar values. This preserves the full Char domain rather than restricting
;; strings to ACL2's host character set.

(defun verina-basic-27-unicode-scalar-p (c)
  (and
   (natp c)
   (or
    (< c 55296)
    (and
     (< 57343 c)
     (< c 1114112)))))

(defun verina-basic-27-string-p (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (and
       (verina-basic-27-unicode-scalar-p (car s))
       (verina-basic-27-string-p (cdr s)))
    (equal s nil)))

;; The source precondition is True. The String binder domain remains explicit
;; in the final correctness statement.

(defun verina-basic-27-find-first-repeated-char-precond (s)
  (declare (ignore s))
  t)

;; The source HashSet Char is represented extensionally by a duplicate-free
;; list of Unicode scalar values. Membership is exact character equality, and
;; insertion preserves the represented set.

(defun verina-basic-27-seen-contains (c seen)
  (declare (xargs :measure (acl2-count seen)))
  (if (consp seen)
      (if (equal c (car seen))
          t
        (verina-basic-27-seen-contains c (cdr seen)))
    nil))

(defun verina-basic-27-seen-insert (c seen)
  (if (verina-basic-27-seen-contains c seen)
      seen
    (cons c seen)))

;; Option Char is represented by :none or the tagged pair (:some . code).

(defun verina-basic-27-option-char-p (result)
  (or
   (equal result :none)
   (and
    (consp result)
    (equal (car result) :some)
    (verina-basic-27-unicode-scalar-p (cdr result)))))

;; This structural recursion consumes the same String.toList from left to
;; right as the source index recursion. Its REMAINING list is cs.drop i, and
;; SEEN denotes exactly the source hash set after processing the earlier
;; characters. Thus it returns the same first repeated character or none.

(defun verina-basic-27-loop (remaining seen)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (let ((c (car remaining)))
        (if (verina-basic-27-seen-contains c seen)
            (cons :some c)
          (verina-basic-27-loop
           (cdr remaining)
           (verina-basic-27-seen-insert c seen))))
    :none))

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. The empty seen set and complete character sequence reproduce
;; the source implementation's initial call loop 0 Std.HashSet.empty.

(defun verina-basic-27-find-first-repeated-char (s)
  (verina-basic-27-loop s nil))

;; List.idxOf returns the first zero-based index of C and returns the list
;; length when C is absent.

(defun verina-basic-27-idx-of-aux (c remaining index)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (if (equal (car remaining) c)
          index
        (verina-basic-27-idx-of-aux
         c
         (cdr remaining)
         (+ index 1)))
    index))

(defun verina-basic-27-idx-of (c characters)
  (verina-basic-27-idx-of-aux c characters 0))

;; This is cs.zipIdx.findIdx (fun (x, i) => x = c && i != cs.idxOf c).
;; FINDIDX returns the traversed list length when no such indexed pair exists.

(defun verina-basic-27-second-index-aux
    (c remaining first-index index)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (if (and
           (equal (car remaining) c)
           (not (equal index first-index)))
          index
        (verina-basic-27-second-index-aux
         c
         (cdr remaining)
         first-index
         (+ index 1)))
    index))

(defun verina-basic-27-second-index (c characters)
  (verina-basic-27-second-index-aux
   c
   characters
   (verina-basic-27-idx-of c characters)
   0))

;; Exact recursive encodings of List.count and List.take.

(defun verina-basic-27-count-char (c characters)
  (declare (xargs :measure (acl2-count characters)))
  (if (consp characters)
      (+
       (if (equal (car characters) c) 1 0)
       (verina-basic-27-count-char c (cdr characters)))
    0))

(defun verina-basic-27-take (n characters)
  (declare (xargs :measure (acl2-count characters)))
  (if (or
       (zp n)
       (not (consp characters)))
      nil
    (cons
     (car characters)
     (verina-basic-27-take
      (- n 1)
      (cdr characters)))))

;; These predicates exactly encode List.Pairwise (fun left right => left !=
;; right): every head differs from every later element, recursively.

(defun verina-basic-27-all-different-from-p (c characters)
  (declare (xargs :measure (acl2-count characters)))
  (if (consp characters)
      (and
       (not (equal c (car characters)))
       (verina-basic-27-all-different-from-p
        c
        (cdr characters)))
    t))

(defun verina-basic-27-pairwise-distinct-p (characters)
  (declare (xargs :measure (acl2-count characters)))
  (if (consp characters)
      (and
       (verina-basic-27-all-different-from-p
        (car characters)
        (cdr characters))
       (verina-basic-27-pairwise-distinct-p
        (cdr characters)))
    t))

;; This preserves both branches of the source postcondition. For some C, the
;; second index is computed independently by the exact zipIdx/findIdx
;; predicate before taking the prefix required to be pairwise distinct.

(defun verina-basic-27-find-first-repeated-char-postcond
    (s result)
  (and
   (verina-basic-27-string-p s)
   (verina-basic-27-option-char-p result)
   (if (equal result :none)
       (verina-basic-27-pairwise-distinct-p s)
     (let* ((c (cdr result))
            (second-index
             (verina-basic-27-second-index c s)))
       (and
        (<= 2
            (verina-basic-27-count-char c s))
        (verina-basic-27-pairwise-distinct-p
         (verina-basic-27-take second-index s)))))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every Lean String, applies the source's True precondition, and connects
;; the complete postcondition to the exact executable result.

(defun-sk
    verina-basic-27-find-first-repeated-char-spec-satisfied-statement
    ()
  (forall (s)
    (implies
     (and
      (verina-basic-27-string-p s)
      (verina-basic-27-find-first-repeated-char-precond s))
     (verina-basic-27-find-first-repeated-char-postcond
      s
      (verina-basic-27-find-first-repeated-char s)))))

(value-triple :itpeval-statement-checked)
:q
