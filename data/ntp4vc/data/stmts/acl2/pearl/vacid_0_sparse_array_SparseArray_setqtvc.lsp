;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/vacid_0_sparse_array_SparseArray_setqtvc: the sparse-array set
;; verification condition, preserving the representation invariant while
;; updating values, index, and back arrays and establishing the pointwise
;; value postcondition. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; Why3 arrays have a mathematical-integer index domain. These conservative
;; interfaces retain arbitrary total arrays instead of replacing them by
;; finite lookup tables. Their native length and update laws are made explicit
;; in the statement predicate.

(defstub v0sas-array-p (array) t)
(defstub v0sas-array-length (array) t)
(defstub v0sas-array-get (array index) t)
(defstub v0sas-array-set (array index value) t)

(defun-sk v0sas-array-length-laws-p ()
  (forall (array)
    (implies
     (v0sas-array-p array)
     (and
      (integerp (v0sas-array-length array))
      (<= 0 (v0sas-array-length array))))))

(defun-sk v0sas-array-update-laws-p ()
  (forall (array index value argument)
    (implies
     (and
      (v0sas-array-p array)
      (integerp index)
      (<= 0 index)
      (< index (v0sas-array-length array))
      (integerp argument))
     (let ((updated
            (v0sas-array-set array index value)))
       (and
        (v0sas-array-p updated)
        (equal
         (v0sas-array-length updated)
         (v0sas-array-length array))
        (equal
         (v0sas-array-get updated argument)
         (if (equal argument index)
             value
           (v0sas-array-get array argument))))))))

(defun v0sas-array-theory-p ()
  (and
   (v0sas-array-length-laws-p)
   (v0sas-array-update-laws-p)))

;; Integer arrays retain integer values at every mathematical integer index.

(defun-sk v0sas-all-integer-entries-p (array)
  (forall (index)
    (implies
     (integerp index)
     (integerp
      (v0sas-array-get array index)))))

(defun v0sas-integer-array-p (array)
  (and
   (v0sas-array-p array)
   (v0sas-all-integer-entries-p array)))

;; Sparse arrays are exact records
;; (:V0SAS-SPARSE-ARRAY values index back card default).

(defun v0sas-sparse-array-shape-p (array)
  (and
   (true-listp array)
   (equal (len array) 6)
   (equal (car array) :v0sas-sparse-array)))

(defun v0sas-values (array)
  (cadr array))

(defun v0sas-index (array)
  (caddr array))

(defun v0sas-back (array)
  (cadddr array))

(defun v0sas-card (array)
  (car (cddddr array)))

(defun v0sas-default (array)
  (cadr (cddddr array)))

;; This is the complete Why3 record invariant, parameterized by its fields so
;; that the generated intermediate-state invariant conjuncts remain explicit.

(defun-sk
  v0sas-index-back-invariant-p
  (values index back card)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (and
       (<= 0 position)
       (< position card))
      (let ((stored-index
             (v0sas-array-get back position)))
        (and
         (<= 0 stored-index)
         (< stored-index
            (v0sas-array-length values))
         (equal
          (v0sas-array-get index stored-index)
          position)))))))

(defun
  v0sas-components-invariant-p
  (values index back card)
  (and
   (v0sas-array-p values)
   (v0sas-integer-array-p index)
   (v0sas-integer-array-p back)
   (integerp card)
   (<= 0 card)
   (<= card (v0sas-array-length values))
   (<= (v0sas-array-length values) 1000)
   (equal
    (v0sas-array-length values)
    (v0sas-array-length index))
   (equal
    (v0sas-array-length index)
    (v0sas-array-length back))
   (v0sas-index-back-invariant-p
    values index back card)))

(defun v0sas-sparse-array-p (array)
  (and
   (v0sas-sparse-array-shape-p array)
   (v0sas-components-invariant-p
    (v0sas-values array)
    (v0sas-index array)
    (v0sas-back array)
    (v0sas-card array))))

(defun v0sas-length (array)
  (v0sas-array-length
   (v0sas-values array)))

(defun v0sas-is-element-p (array position)
  (let ((stored-index
         (v0sas-array-get
          (v0sas-index array)
          position)))
    (and
     (<= 0 stored-index)
     (< stored-index (v0sas-card array))
     (equal
      (v0sas-array-get
       (v0sas-back array)
       stored-index)
      position))))

(defun v0sas-value (array position)
  (if (v0sas-is-element-p array position)
      (v0sas-array-get
       (v0sas-values array)
       position)
    (v0sas-default array)))

;; This preserves the exported extensional Function.update premise over every
;; mathematical integer, without collapsing negative indices through toNat.

(defun-sk
  v0sas-array-set-map-equal-p
  (array index value)
  (forall (argument)
    (implies
     (integerp argument)
     (equal
      (v0sas-array-get
       (v0sas-array-set array index value)
       argument)
      (if (equal argument index)
          value
        (v0sas-array-get array argument))))))

(defun
  v0sas-first-state-relation-p
  (original first updated-values)
  (and
   (equal
    (v0sas-default original)
    (v0sas-default first))
   (equal
    (v0sas-card original)
    (v0sas-card first))
   (equal
    (v0sas-back original)
    (v0sas-back first))
   (equal
    (v0sas-index original)
    (v0sas-index first))
   (equal
    updated-values
    (v0sas-values first))))

(defun
  v0sas-second-state-relation-p
  (first second updated-index updated-back)
  (and
   (equal
    (v0sas-default first)
    (v0sas-default second))
   (equal
    (+ (v0sas-card first) 1)
    (v0sas-card second))
   (equal
    updated-back
    (v0sas-back second))
   (equal
    updated-index
    (v0sas-index second))
   (equal
    (v0sas-values first)
    (v0sas-values second))))

(defun-sk
  v0sas-other-values-unchanged-p
  (updated original distinguished)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (not (equal position distinguished))
      (equal
       (v0sas-value updated position)
       (v0sas-value original position))))))

(defun
  v0sas-set-postcondition-p
  (updated original position value)
  (and
   (equal
    (v0sas-value updated position)
    value)
   (v0sas-other-values-unchanged-p
    updated original position)))

;; The final universally quantified record after insertion retains the full
;; incremented-card invariant and the exact field-update relation.

(defun-sk
  v0sas-all-second-states-p
  (original first position value updated-index updated-back)
  (forall (second)
    (implies
     (v0sas-sparse-array-p second)
     (and
      (v0sas-components-invariant-p
       (v0sas-values first)
       updated-index
       updated-back
       (+ (v0sas-card first) 1))
      (implies
       (v0sas-second-state-relation-p
        first second updated-index updated-back)
       (v0sas-set-postcondition-p
        second original position value))))))

;; This is the branch in which POSITION was not already represented. The
;; repeated length premises are retained exactly from the generated VC.

(defun
  v0sas-absent-element-branch-p
  (original first position value)
  (let* ((old-card
          (v0sas-card first))
         (old-index
          (v0sas-index first))
         (updated-index
          (v0sas-array-set
           old-index position old-card)))
    (and
     (<= 0 position)
     (< position
        (v0sas-array-length old-index))
     (implies
      (equal
       (v0sas-array-length updated-index)
       (v0sas-array-length old-index))
      (implies
       (equal
        (v0sas-array-length updated-index)
        (v0sas-array-length
         (v0sas-index first)))
       (implies
        (v0sas-array-set-map-equal-p
         old-index position old-card)
        (and
         (<= 0 (v0sas-card first))
         (< (v0sas-card first)
            (v0sas-array-length
             (v0sas-back first)))
         (let* ((old-back
                 (v0sas-back first))
                (updated-back
                 (v0sas-array-set
                  old-back
                  (v0sas-card first)
                  position)))
           (implies
            (equal
             (v0sas-array-length updated-back)
             (v0sas-array-length old-back))
            (implies
             (equal
              (v0sas-array-length updated-back)
              (v0sas-array-length
               (v0sas-back first)))
             (implies
              (v0sas-array-set-map-equal-p
               old-back
               (v0sas-card first)
               position)
              (v0sas-all-second-states-p
               original
               first
               position
               value
               updated-index
               updated-back))))))))))))

(defun
  v0sas-first-state-post-p
  (original first position value)
  (and
   (<= 0 position)
   (< position (v0sas-length first))
   (if (not
        (v0sas-is-element-p
         first position))
       (v0sas-absent-element-branch-p
        original first position value)
     (v0sas-set-postcondition-p
      first original position value))))

;; FIRST is the state after updating the values array. Its source type and
;; global invariant remain internal to the universal quantifier.

(defun-sk
  v0sas-all-first-states-p
  (original position value updated-values)
  (forall (first)
    (implies
     (v0sas-sparse-array-p first)
     (implies
      (equal
       (v0sas-array-length updated-values)
       (v0sas-array-length
        (v0sas-values original)))
      (implies
       (equal
        (v0sas-array-length updated-values)
        (v0sas-array-length
         (v0sas-values original)))
       (implies
        (v0sas-array-set-map-equal-p
         (v0sas-values original)
         position
         value)
        (and
         (v0sas-components-invariant-p
          updated-values
          (v0sas-index original)
          (v0sas-back original)
          (v0sas-card original))
         (implies
          (v0sas-first-state-relation-p
           original first updated-values)
          (v0sas-first-state-post-p
           original first position value)))))))))

(defun
  ntp4vc-pearl-vacid-0-sparse-array-sparsearray-setqtvc-statement
  (position original value)
  (implies
   (and
    (v0sas-array-theory-p)
    (integerp position)
    (v0sas-sparse-array-p original)
    (<= 0 position)
    (< position (v0sas-length original)))
   (let ((updated-values
          (v0sas-array-set
           (v0sas-values original)
           position
           value)))
     (and
      (<= 0 position)
      (< position
         (v0sas-array-length
          (v0sas-values original)))
      (v0sas-all-first-states-p
       original
       position
       value
       updated-values)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
