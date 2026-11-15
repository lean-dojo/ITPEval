;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/vacid_0_sparse_array_SparseArray_getqtvc: the sparse-array get
;; verification condition, preserving index bounds and agreement between the
;; conditional returned value and the abstract sparse-array value. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; Proper finite ACL2 lists represent the source's finite Why3 arrays. Values
;; range over ACL2's full object universe, preserving the arbitrary
;; polymorphic element type; index and back arrays retain integer entries.

(defun v0sa-integer-list-p (xs)
  (if (consp xs)
      (and
       (integerp (car xs))
       (v0sa-integer-list-p (cdr xs)))
    (equal xs nil)))

;; Sparse arrays are exact tagged records
;; (:V0SA-SPARSE-ARRAY values index back card default).

(defun v0sa-sparse-array-shape-p (array)
  (and
   (true-listp array)
   (equal (len array) 6)
   (equal (car array) :v0sa-sparse-array)))

(defun v0sa-values (array)
  (cadr array))

(defun v0sa-index (array)
  (caddr array))

(defun v0sa-back (array)
  (cadddr array))

(defun v0sa-card (array)
  (car (cddddr array)))

(defun v0sa-default (array)
  (cadr (cddddr array)))

;; This is the complete source type invariant. The quantified position remains
;; an internal universal quantifier over mathematical integers.

(defun-sk v0sa-index-back-invariant-p (array)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (and
       (<= 0 position)
       (< position (v0sa-card array)))
      (let ((stored-index
             (nth
              (nfix position)
              (v0sa-back array))))
        (and
         (<= 0 stored-index)
         (< stored-index
            (len (v0sa-values array)))
         (equal
          (nth
           (nfix stored-index)
           (v0sa-index array))
          position)))))))

(defun v0sa-sparse-array-p (array)
  (and
   (v0sa-sparse-array-shape-p array)
   (true-listp (v0sa-values array))
   (v0sa-integer-list-p (v0sa-index array))
   (v0sa-integer-list-p (v0sa-back array))
   (integerp (v0sa-card array))
   (<= 0 (v0sa-card array))
   (<= (v0sa-card array)
       (len (v0sa-values array)))
   (<= (len (v0sa-values array)) 1000)
   (equal
    (len (v0sa-values array))
    (len (v0sa-index array)))
   (equal
    (len (v0sa-index array))
    (len (v0sa-back array)))
   (v0sa-index-back-invariant-p array)))

(defun v0sa-length (array)
  (len (v0sa-values array)))

(defun v0sa-is-element-p (array position)
  (let ((stored-index
         (nth
          (nfix position)
          (v0sa-index array))))
    (and
     (<= 0 stored-index)
     (< stored-index (v0sa-card array))
     (equal
      (nth
       (nfix stored-index)
       (v0sa-back array))
      position))))

(defun v0sa-value (array position)
  (if (v0sa-is-element-p array position)
      (nth
       (nfix position)
       (v0sa-values array))
    (v0sa-default array)))

;; RESULT retains the source universal quantifier over the arbitrary element
;; carrier. Its premise is the exact branch relation produced by GET.

(defun-sk v0sa-all-get-results-p (array position)
  (forall (result)
    (implies
     (if (v0sa-is-element-p array position)
         (equal
          result
          (nth
           (nfix position)
           (v0sa-values array)))
       (equal result (v0sa-default array)))
     (equal
      result
      (v0sa-value array position)))))

(defun
  ntp4vc-pearl-vacid-0-sparse-array-sparsearray-getqtvc-statement
  (position array)
  (implies
   (and
    (integerp position)
    (v0sa-sparse-array-p array)
    (<= 0 position)
    (< position (v0sa-length array)))
   (and
    (<= 0 position)
    (< position (v0sa-length array))
    (implies
     (v0sa-is-element-p array position)
     (and
      (<= 0 position)
      (< position
         (len (v0sa-values array)))))
    (v0sa-all-get-results-p
     array position))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
