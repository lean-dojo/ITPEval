;; Statement-only formalization of thousand-theorems corpus artifact Q1566341,
;; "Hindman's theorem": for any stream in a semigroup, every finite cover of
;; its nonempty finite-product set has a cell containing the finite-product
;; set of another infinite stream. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative generic interfaces interpret semigroup structures, streams,
;; subsets, and families of subsets without enumerating their carriers or
;; replacing sets and functions by finite tables. DEFUN-SK keeps the cover
;; cell and infinite-stream witness inside the conclusion.

(defstub q1566341-carrier-member-p (semigroup value) t)
(defstub q1566341-multiply (semigroup left right) t)
(defstub q1566341-sequence-value (semigroup sequence index) t)
(defstub q1566341-set-member-p (semigroup set value) t)
(defstub q1566341-family-member-p (semigroup family set) t)

;; Semigroup structure and streams over its carrier.

(defun-sk q1566341-semigroup-laws-p (semigroup)
  (forall (x y z)
    (and
     (implies
      (and
       (q1566341-carrier-member-p semigroup x)
       (q1566341-carrier-member-p semigroup y))
      (q1566341-carrier-member-p
       semigroup
       (q1566341-multiply semigroup x y)))
     (implies
      (and
       (q1566341-carrier-member-p semigroup x)
       (q1566341-carrier-member-p semigroup y)
       (q1566341-carrier-member-p semigroup z))
      (equal
       (q1566341-multiply
        semigroup
        x
        (q1566341-multiply semigroup y z))
       (q1566341-multiply
        semigroup
        (q1566341-multiply semigroup x y)
        z))))))

(defun q1566341-semigroup-p (semigroup)
  (q1566341-semigroup-laws-p semigroup))

(defun-sk q1566341-sequence-in-carrier-p (semigroup sequence)
  (forall (index)
    (implies
     (natp index)
     (q1566341-carrier-member-p
      semigroup
      (q1566341-sequence-value
       semigroup sequence index)))))

(defun q1566341-stream-p (semigroup sequence)
  (q1566341-sequence-in-carrier-p semigroup sequence))

;; A nonempty strictly increasing list of natural indices represents a
;; nonempty finite subsequence. Its product is associated to the right;
;; associativity makes this exactly the inductive FP set in the Lean source.

(defun q1566341-increasing-index-list-p (indices)
  (if (consp indices)
      (and
       (natp (car indices))
       (if (consp (cdr indices))
           (and
            (< (car indices) (cadr indices))
            (q1566341-increasing-index-list-p (cdr indices)))
         (equal (cdr indices) nil)))
    (equal indices nil)))

(defun q1566341-finite-product (semigroup sequence indices)
  (if (consp indices)
      (if (consp (cdr indices))
          (q1566341-multiply
           semigroup
           (q1566341-sequence-value
            semigroup sequence (car indices))
           (q1566341-finite-product
            semigroup sequence (cdr indices)))
        (q1566341-sequence-value
         semigroup sequence (car indices)))
    nil))

(defun-sk q1566341-fp-member-p
    (semigroup sequence value)
  (exists (indices)
    (and
     (true-listp indices)
     (consp indices)
     (q1566341-increasing-index-list-p indices)
     (equal
      value
      (q1566341-finite-product
       semigroup sequence indices))
     (q1566341-carrier-member-p
      semigroup value))))

;; Subsets are compared extensionally on the carrier. A family is finite when
;; an internal finite list enumerates exactly its extensional members.

(defun-sk q1566341-set-equiv-p (semigroup left right)
  (forall (x)
    (implies
     (q1566341-carrier-member-p semigroup x)
     (iff
      (q1566341-set-member-p semigroup left x)
      (q1566341-set-member-p semigroup right x)))))

(defun q1566341-list-contains-equiv-set-p
    (semigroup set sets)
  (if (consp sets)
      (or
       (q1566341-set-equiv-p
        semigroup set (car sets))
       (q1566341-list-contains-equiv-set-p
        semigroup set (cdr sets)))
    nil))

(defun-sk q1566341-family-enumeration-exact-p
    (semigroup family sets)
  (forall (set)
    (iff
     (q1566341-family-member-p
      semigroup family set)
     (q1566341-list-contains-equiv-set-p
      semigroup set sets))))

(defun q1566341-family-enumeration-p
    (semigroup family sets)
  (and
   (true-listp sets)
   (q1566341-family-enumeration-exact-p
    semigroup family sets)))

(defun-sk q1566341-finite-family-p (semigroup family)
  (exists (sets)
    (q1566341-family-enumeration-p
     semigroup family sets)))

(defun-sk q1566341-family-union-member-p
    (semigroup family value)
  (exists (set)
    (and
     (q1566341-family-member-p
      semigroup family set)
     (q1566341-set-member-p
      semigroup set value))))

;; The source cover assumption FP(a) subset union(s).

(defun-sk q1566341-fp-covered-p
    (semigroup sequence family)
  (forall (value)
    (implies
     (q1566341-fp-member-p
      semigroup sequence value)
     (q1566341-family-union-member-p
      semigroup family value))))

;; The source conclusion FP(b) subset c, with both c and b existentially
;; quantified in the same scope as in FP_partition_regular.

(defun-sk q1566341-fp-subset-p
    (semigroup sequence set)
  (forall (value)
    (implies
     (q1566341-fp-member-p
      semigroup sequence value)
     (q1566341-set-member-p
      semigroup set value))))

(defun-sk q1566341-monochromatic-fp-stream-exists-p
    (semigroup family)
  (exists (set sequence)
    (and
     (q1566341-family-member-p
      semigroup family set)
     (q1566341-stream-p semigroup sequence)
     (q1566341-fp-subset-p
      semigroup sequence set))))

(defun thousand-theorems-q1566341-hindman-s-theorem-statement
    (semigroup sequence family)
  (implies
   (and
    (q1566341-semigroup-p semigroup)
    (q1566341-stream-p semigroup sequence)
    (q1566341-finite-family-p semigroup family)
    (q1566341-fp-covered-p
     semigroup sequence family))
   (q1566341-monochromatic-fp-stream-exists-p
    semigroup family)))

(value-triple :itpeval-statement-checked)
:q
