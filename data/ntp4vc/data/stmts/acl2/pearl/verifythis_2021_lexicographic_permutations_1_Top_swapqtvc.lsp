;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/verifythis_2021_lexicographic_permutations_1_Top_swapqtvc:
;; swapping two valid positions of an integer array exchanges their values,
;; preserves every other position, and preserves the represented permutation.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Why3 arrays and finite sequences of mathematical integers are represented
;; bijectively by proper ACL2 lists of unbounded ACL2 integers.

(defun lp-swap-int-list-p (sequence)
  (declare (xargs :measure (acl2-count sequence)))
  (if (consp sequence)
      (and
       (integerp (car sequence))
       (lp-swap-int-list-p (cdr sequence)))
    (equal sequence nil)))

;; Integer indexing follows the exported Int.toNat convention and uses the
;; source inhabited integer value zero outside the finite sequence.

(defun lp-swap-read-nat (index sequence)
  (declare (xargs :measure (nfix index)))
  (if (and
       (natp index)
       (< 0 index)
       (consp sequence))
      (lp-swap-read-nat (- index 1) (cdr sequence))
    (if (consp sequence) (car sequence) 0)))

(defun lp-swap-read (sequence index)
  (lp-swap-read-nat (nfix index) sequence))

;; Unlike ACL2's UPDATE-NTH, source List.set leaves a sequence unchanged when
;; its natural-number index is out of bounds.

(defun lp-swap-list-set (sequence index value)
  (declare (xargs :measure (acl2-count sequence)))
  (if (endp sequence)
      nil
    (if (zp index)
        (cons value (cdr sequence))
      (cons
       (car sequence)
       (lp-swap-list-set
        (cdr sequence)
        (- index 1)
        value)))))

;; Under the list representation, the source array-to-sequence operation is
;; extensionally the identity.

(defun lp-swap-to-seq (array)
  array)

;; Full-sequence occurrence counting is definitionally equivalent to the
;; source NUMOF count on the half-open interval [0, length).

(defun lp-swap-count (value sequence)
  (declare (xargs :measure (acl2-count sequence)))
  (if (consp sequence)
      (+
       (if (equal value (car sequence)) 1 0)
       (lp-swap-count value (cdr sequence)))
    0))

(defun-sk lp-swap-same-counts-p (left right)
  (forall (value)
    (implies
     (integerp value)
     (equal
      (lp-swap-count value left)
      (lp-swap-count value right)))))

(defun lp-swap-permutation-p (left right)
  (and
   (lp-swap-int-list-p left)
   (lp-swap-int-list-p right)
   (equal (len left) (len right))
   (lp-swap-same-counts-p left right)))

;; The generated VC retains the extensional equality between each List.set
;; lookup function and the corresponding single functional update.

(defun-sk lp-swap-set-function-equal-p
    (sequence index value)
  (forall (argument)
    (implies
     (integerp argument)
     (equal
      (lp-swap-read
       (lp-swap-list-set
        sequence
        (nfix index)
        value)
       argument)
      (if (equal argument index)
          value
        (lp-swap-read sequence argument))))))

(defun-sk lp-swap-other-positions-unchanged-p
    (swapped original first second)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index (len swapped)))
      (implies
       (not (equal index first))
       (implies
        (not (equal index second))
        (equal
         (lp-swap-read swapped index)
         (lp-swap-read original index))))))))

(defun lp-swap-final-conclusion-p
    (swapped original first second)
  (and
   (equal
    (lp-swap-read swapped first)
    (lp-swap-read original second))
   (equal
    (lp-swap-read swapped second)
    (lp-swap-read original first))
   (lp-swap-other-positions-unchanged-p
    swapped original first second)
   (lp-swap-permutation-p
    (lp-swap-to-seq swapped)
    (lp-swap-to-seq original))))

;; This preserves the source conclusion's conjunctions and right-associated
;; implications after the two sequential array updates.

(defun lp-swap-conclusion-p (first original second)
  (and
   (<= 0 first)
   (< first (len original))
   (let ((temporary
          (lp-swap-read original first)))
     (and
      (<= 0 second)
      (< second (len original))
      (let* ((second-value
              (lp-swap-read original second))
             (after-first
              (lp-swap-list-set
               original
               (nfix first)
               second-value)))
        (and
         (<= 0 first)
         (< first (len original))
         (implies
          (equal (len after-first) (len original))
          (implies
           (lp-swap-set-function-equal-p
            original first second-value)
           (and
            (<= 0 second)
            (< second (len after-first))
            (let ((swapped
                   (lp-swap-list-set
                    after-first
                    (nfix second)
                    temporary)))
              (implies
               (equal (len swapped) (len after-first))
               (implies
                (lp-swap-set-function-equal-p
                 after-first second temporary)
                (lp-swap-final-conclusion-p
                 swapped original first second)))))))))))))

(defun
    ntp4vc-pearl-verifythis-2021-lexicographic-permutations-1-top-swapqtvc-statement
    (first original second)
  (implies
   (and
    (integerp first)
    (lp-swap-int-list-p original)
    (integerp second)
    (<= 0 first)
    (< first (len original))
    (<= 0 second)
    (< second (len original)))
   (lp-swap-conclusion-p
    first original second)))

(value-triple :itpeval-statement-checked)
:q
