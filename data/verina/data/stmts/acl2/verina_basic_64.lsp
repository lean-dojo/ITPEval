;; Statement-only formalization of VERINA corpus artifact verina_basic_64,
;; catalog title "insert": a deterministic Unicode-character array program
;; inserts the first p characters of one array at a natural position within
;; the first l characters of another array. This file contains no proof.

(in-package "ACL2")

;; Lean Array Char values are represented bijectively by proper ACL2 lists of
;; Unicode scalar values, preserving the complete Lean Char domain.

(defun verina-basic-64-unicode-scalar-p (c)
  (and
   (natp c)
   (or
    (< c 55296)
    (and
     (< 57343 c)
     (< c 1114112)))))

(defun verina-basic-64-char-array-p (array)
  (declare (xargs :measure (acl2-count array)))
  (if (consp array)
      (and
       (verina-basic-64-unicode-scalar-p (car array))
       (verina-basic-64-char-array-p (cdr array)))
    (equal array nil)))

;; This is exactly the source precondition after Array.size is represented by
;; list length.

(defun verina-basic-64-insert-precond
    (oline l nl p at-pos)
  (and
   (<= l (len oline))
   (<= p (len nl))
   (<= at-pos l)))

;; Array.get! on Array Char returns the indexed entry when present and the
;; inhabited Unicode NUL character otherwise.

(defun verina-basic-64-array-read (index array)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      0
    (if (consp array)
        (if (zp index)
            (car array)
          (verina-basic-64-array-read
           (- index 1)
           (cdr array)))
      0)))

;; Array.set! replaces an in-bounds entry and leaves the array unchanged when
;; its natural index is out of bounds.

(defun verina-basic-64-array-set
    (index value array)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      array
    (if (consp array)
        (if (zp index)
            (cons value (cdr array))
          (cons
           (car array)
           (verina-basic-64-array-set
            (- index 1)
            value
            (cdr array))))
      nil)))

;; This is Array.mkArray for the source's initial space-filled result.

(defun verina-basic-64-make-spaces (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (cons
     32
     (verina-basic-64-make-spaces (- n 1)))))

;; Each fold below traverses exactly the corresponding Array.range in
;; increasing order. REMAINING is the number of unprocessed range entries,
;; and INDEX is the current entry.

(defun verina-basic-64-copy-prefix-fold
    (result oline at-pos remaining index)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      result
    (verina-basic-64-copy-prefix-fold
     (if (< index at-pos)
         (verina-basic-64-array-set
          index
          (verina-basic-64-array-read index oline)
          result)
       result)
     oline
     at-pos
     (- remaining 1)
     (+ index 1))))

(defun verina-basic-64-insert-new-fold
    (result nl at-pos remaining index)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      result
    (verina-basic-64-insert-new-fold
     (verina-basic-64-array-set
      (+ at-pos index)
      (verina-basic-64-array-read index nl)
      result)
     nl
     at-pos
     (- remaining 1)
     (+ index 1))))

(defun verina-basic-64-copy-suffix-fold
    (result oline p at-pos remaining index)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      result
    (verina-basic-64-copy-suffix-fold
     (if (<= at-pos index)
         (verina-basic-64-array-set
          (+ index p)
          (verina-basic-64-array-read index oline)
          result)
       result)
     oline
     p
     at-pos
     (- remaining 1)
     (+ index 1))))

;; The proof-valued precondition argument is computationally irrelevant and
;; is erased. The initializer and three folds reproduce the complete source
;; program in their original order.

(defun verina-basic-64-insert
    (oline l nl p at-pos)
  (let* ((result
          (verina-basic-64-make-spaces (+ l p)))
         (result
          (verina-basic-64-copy-prefix-fold
           result
           oline
           at-pos
           l
           0))
         (result
          (verina-basic-64-insert-new-fold
           result
           nl
           at-pos
           p
           0))
         (result
          (verina-basic-64-copy-suffix-fold
           result
           oline
           p
           at-pos
           l
           0)))
    result))

;; These bounded recursions are exactly the three List.range(...).all
;; expressions in the source postcondition, starting each range at zero.

(defun verina-basic-64-inserted-segment-correct-p
    (result nl at-pos remaining index)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (and
     (equal
      (verina-basic-64-array-read
       (+ at-pos index)
       result)
      (verina-basic-64-array-read index nl))
     (verina-basic-64-inserted-segment-correct-p
      result
      nl
      at-pos
      (- remaining 1)
      (+ index 1)))))

(defun verina-basic-64-prefix-correct-p
    (result oline remaining index)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (and
     (equal
      (verina-basic-64-array-read index result)
      (verina-basic-64-array-read index oline))
     (verina-basic-64-prefix-correct-p
      result
      oline
      (- remaining 1)
      (+ index 1)))))

(defun verina-basic-64-suffix-correct-p
    (result oline at-pos p remaining index)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (and
     (equal
      (verina-basic-64-array-read
       (+ at-pos p index)
       result)
      (verina-basic-64-array-read
       (+ at-pos index)
       oline))
     (verina-basic-64-suffix-correct-p
      result
      oline
      at-pos
      p
      (- remaining 1)
      (+ index 1)))))

;; This is the complete source postcondition. The typed Array Char and Nat
;; domains are explicit; the unused proof-valued precondition argument is
;; erased.

(defun verina-basic-64-insert-postcond
    (oline l nl p at-pos result)
  (and
   (verina-basic-64-char-array-p oline)
   (natp l)
   (verina-basic-64-char-array-p nl)
   (natp p)
   (natp at-pos)
   (verina-basic-64-char-array-p result)
   (equal (len result) (+ l p))
   (verina-basic-64-inserted-segment-correct-p
    result
    nl
    at-pos
    p
    0)
   (verina-basic-64-prefix-correct-p
    result
    oline
    at-pos
    0)
   (verina-basic-64-suffix-correct-p
    result
    oline
    at-pos
    p
    (- l at-pos)
    0)))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over all finite Unicode-character arrays and natural parameters, assumes
;; exactly the source precondition, and connects the complete postcondition
;; to the exact executable result.

(defun-sk
    verina-basic-64-insert-spec-satisfied-statement
    ()
  (forall (oline l nl p at-pos)
    (implies
     (and
      (verina-basic-64-char-array-p oline)
      (natp l)
      (verina-basic-64-char-array-p nl)
      (natp p)
      (natp at-pos)
      (verina-basic-64-insert-precond
       oline
       l
       nl
       p
       at-pos))
     (verina-basic-64-insert-postcond
      oline
      l
      nl
      p
      at-pos
      (verina-basic-64-insert
       oline
       l
       nl
       p
       at-pos)))))

(value-triple :itpeval-statement-checked)
:q
