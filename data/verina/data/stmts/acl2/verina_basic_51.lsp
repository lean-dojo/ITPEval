;; Statement-only formalization of VERINA corpus artifact verina_basic_51,
;; catalog title "BinarySearch": deterministic lower-bound binary search on a
;; nondecreasing integer array returns an insertion index with every preceding
;; value below the key and every following value at least the key. This file
;; contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-51-int-array-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (integerp (car a))
       (verina-basic-51-int-array-p (cdr a)))
    (equal a nil)))

;; These predicates are exactly List.Pairwise (fun x y => x <= y): each head
;; is at most every later value, recursively for every suffix.

(defun verina-basic-51-head-at-most-all-p
    (head remaining)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (and
       (<= head (car remaining))
       (verina-basic-51-head-at-most-all-p
        head
        (cdr remaining)))
    (equal remaining nil)))

(defun verina-basic-51-pairwise-nondecreasing-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (verina-basic-51-head-at-most-all-p
        (car a)
        (cdr a))
       (verina-basic-51-pairwise-nondecreasing-p
        (cdr a)))
    (equal a nil)))

(defun verina-basic-51-binary-search-precond
    (a key)
  (declare (ignore key))
  (verina-basic-51-pairwise-nondecreasing-p a))

;; Array.get! on Array Int returns the in-bounds entry and the inhabited
;; integer default zero outside the array.

(defun verina-basic-51-array-read (index a)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      0
    (if (consp a)
        (if (zp index)
            (car a)
          (verina-basic-51-array-read
           (- index 1)
           (cdr a)))
      0)))

;; This fuel recursion evaluates binarySearchLoop. For natural LO and HI the
;; wrapper supplies HI-LO units. Whenever LO < HI, MID=floor((LO+HI)/2) makes
;; each source recursive call strictly reduce that width, so fuel cannot
;; expire before the source base case and does not change the result.

(defun verina-basic-51-binary-search-loop-fuel
    (a key lo hi fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or
       (zp fuel)
       (not (natp lo))
       (not (natp hi))
       (not (< lo hi)))
      lo
    (let* ((mid
            (floor (+ lo hi) 2))
           (mid-value
            (verina-basic-51-array-read mid a)))
      (if (< mid-value key)
          (verina-basic-51-binary-search-loop-fuel
           a
           key
           (+ mid 1)
           hi
           (- fuel 1))
        (verina-basic-51-binary-search-loop-fuel
         a
         key
         lo
         mid
         (- fuel 1))))))

(defun verina-basic-51-binary-search-loop
    (a key lo hi)
  (verina-basic-51-binary-search-loop-fuel
   a
   key
   lo
   hi
   (nfix (- hi lo))))

;; The proof-valued precondition argument is computationally irrelevant and
;; is erased. The initial interval [0, a.size) exactly reproduces the source
;; executable BinarySearch function.

(defun verina-basic-51-binary-search (a key)
  (verina-basic-51-binary-search-loop
   a
   key
   0
   (len a)))

;; These are Array.take and Array.drop at a natural count under the list
;; representation.

(defun verina-basic-51-take (count values)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (if (consp values)
        (cons
         (car values)
         (verina-basic-51-take
          (- count 1)
          (cdr values)))
      nil)))

(defun verina-basic-51-drop (count values)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      values
    (if (consp values)
        (verina-basic-51-drop
         (- count 1)
         (cdr values))
      nil)))

;; These predicates are Array.all for the two source comparisons.

(defun verina-basic-51-all-less-than-p
    (values key)
  (declare (xargs :measure (acl2-count values)))
  (if (consp values)
      (and
       (< (car values) key)
       (verina-basic-51-all-less-than-p
        (cdr values)
        key))
    (equal values nil)))

(defun verina-basic-51-all-at-least-p
    (values key)
  (declare (xargs :measure (acl2-count values)))
  (if (consp values)
      (and
       (>= (car values) key)
       (verina-basic-51-all-at-least-p
        (cdr values)
        key))
    (equal values nil)))

;; This is the complete source postcondition. The proof-valued precondition
;; argument is unused and erased.

(defun verina-basic-51-binary-search-postcond
    (a key result)
  (and
   (verina-basic-51-int-array-p a)
   (integerp key)
   (natp result)
   (<= result (len a))
   (verina-basic-51-all-less-than-p
    (verina-basic-51-take result a)
    key)
   (verina-basic-51-all-at-least-p
    (verina-basic-51-drop result a)
    key)))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every finite integer array and integer key, assumes exactly the source
;; sortedness precondition, and applies the complete postcondition to the exact
;; executable result.

(defun-sk
    verina-basic-51-binary-search-spec-satisfied-statement
    ()
  (forall (a key)
    (implies
     (and
      (verina-basic-51-int-array-p a)
      (integerp key)
      (verina-basic-51-binary-search-precond
       a
       key))
     (verina-basic-51-binary-search-postcond
      a
      key
      (verina-basic-51-binary-search a key)))))

(value-triple :itpeval-statement-checked)
:q
