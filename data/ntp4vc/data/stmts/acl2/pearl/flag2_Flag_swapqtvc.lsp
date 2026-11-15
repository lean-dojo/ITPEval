;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/flag2_Flag_swapqtvc: swapping two in-range positions of a color list
;; exchanges their values, preserves all other positions, and preserves color
;; occurrence counts on every interval containing both positions.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These three ACL2 objects exactly represent the source color datatype.  The
;; source's chosen Inhabited value is represented by a conservative nullary
;; interface and constrained to be a color in the statement predicate.

(defun ntp4vc-swap-color-p (value)
  (or
   (equal value :blue)
   (equal value :white)
   (equal value :red)))

(defstub ntp4vc-swap-default-color () t)

(defun ntp4vc-swap-color-list-p (xs)
  (if (endp xs)
      (equal xs nil)
    (and
     (ntp4vc-swap-color-p (car xs))
     (ntp4vc-swap-color-list-p (cdr xs)))))

;; Int.toNat sends negative integers to zero.  Source getElem! returns the
;; chosen default color when the resulting natural index is out of bounds.

(defun ntp4vc-swap-int-to-nat (value)
  (if (and (integerp value) (< value 0))
      0
    (nfix value)))

(defun ntp4vc-swap-nth-color (xs index)
  (let ((tail
         (nthcdr
          (ntp4vc-swap-int-to-nat index)
          xs)))
    (if (consp tail)
        (car tail)
      (ntp4vc-swap-default-color))))

;; Unlike ACL2's update-nth, source List.set leaves a list unchanged when its
;; natural-number index is out of bounds.

(defun ntp4vc-swap-list-set (xs index value)
  (declare (xargs :measure (acl2-count xs)))
  (if (endp xs)
      nil
    (if (zp index)
        (cons value (cdr xs))
      (cons
       (car xs)
       (ntp4vc-swap-list-set
        (cdr xs)
        (- index 1)
        value)))))

;; This terminating definition is the source nb_occ recurrence specialized to
;; the total indexing function of a color list.

(defun ntp4vc-swap-nb-occ
    (xs lower upper color)
  (declare
   (xargs
    :measure
    (nfix
     (- (ifix upper)
        (ifix lower)))))
  (if (and
       (integerp lower)
       (integerp upper)
       (< lower upper))
      (+
       (if (equal
            (ntp4vc-swap-nth-color xs (- upper 1))
            color)
           1
         0)
       (ntp4vc-swap-nb-occ
        xs lower (- upper 1) color))
    0))

;; The source function equalities after each List.set are retained
;; extensionally over every mathematical integer argument.

(defun-sk ntp4vc-swap-set-function-equal-p
    (xs index value)
  (forall (argument)
    (implies
     (integerp argument)
     (equal
      (ntp4vc-swap-nth-color
       (ntp4vc-swap-list-set
        xs
        (ntp4vc-swap-int-to-nat index)
        value)
       argument)
      (if (equal argument index)
          value
        (ntp4vc-swap-nth-color xs argument))))))

;; The two quantified components of the final swap specification preserve
;; their original scopes over all integer indices and all source colors.

(defun-sk ntp4vc-swap-other-positions-unchanged-p
    (new old first second)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (not (equal index first))
       (not (equal index second)))
      (equal
       (ntp4vc-swap-nth-color new index)
       (ntp4vc-swap-nth-color old index))))))

(defun-sk ntp4vc-swap-interval-occurrences-preserved-p
    (new old first second)
  (forall (lower upper color)
    (implies
     (and
      (integerp lower)
      (integerp upper)
      (ntp4vc-swap-color-p color))
     (implies
      (and
       (<= lower first)
       (< first upper)
       (<= lower second)
       (< second upper))
      (equal
       (ntp4vc-swap-nb-occ
        new lower upper color)
       (ntp4vc-swap-nb-occ
        old lower upper color))))))

(defun ntp4vc-swap-final-conclusion-p
    (swapped original first second)
  (and
   (equal
    (ntp4vc-swap-nth-color swapped first)
    (ntp4vc-swap-nth-color original second))
   (equal
    (ntp4vc-swap-nth-color swapped second)
    (ntp4vc-swap-nth-color original first))
   (ntp4vc-swap-other-positions-unchanged-p
    swapped original first second)
   (ntp4vc-swap-interval-occurrences-preserved-p
    swapped original first second)))

;; This preserves the source conclusion's conjunctions and right-associated
;; implications, including both length and extensional update premises.

(defun ntp4vc-swap-conclusion-p (first original second)
  (and
   (<= 0 first)
   (< first (len original))
   (let ((first-value
          (ntp4vc-swap-nth-color original first)))
     (and
      (<= 0 second)
      (< second (len original))
      (let* ((second-value
              (ntp4vc-swap-nth-color original second))
             (after-first
              (ntp4vc-swap-list-set
               original
               (ntp4vc-swap-int-to-nat first)
               second-value)))
        (and
         (<= 0 first)
         (< first (len original))
         (implies
          (equal (len after-first) (len original))
          (implies
           (ntp4vc-swap-set-function-equal-p
            original first second-value)
           (and
            (<= 0 second)
            (< second (len after-first))
            (let ((swapped
                   (ntp4vc-swap-list-set
                    after-first
                    (ntp4vc-swap-int-to-nat second)
                    first-value)))
              (implies
               (equal (len swapped) (len after-first))
               (implies
                (ntp4vc-swap-set-function-equal-p
                 after-first second first-value)
                (ntp4vc-swap-final-conclusion-p
                 swapped original first second)))))))))))))

(defun
    ntp4vc-pearl-flag2-flag-swapqtvc-statement
    (first original second)
  (implies
   (and
    (integerp first)
    (ntp4vc-swap-color-list-p original)
    (integerp second)
    (ntp4vc-swap-color-p
     (ntp4vc-swap-default-color))
    (<= 0 first)
    (< first (len original))
    (<= 0 second)
    (< second (len original)))
   (ntp4vc-swap-conclusion-p
    first original second)))

(value-triple :itpeval-statement-checked)
:q
