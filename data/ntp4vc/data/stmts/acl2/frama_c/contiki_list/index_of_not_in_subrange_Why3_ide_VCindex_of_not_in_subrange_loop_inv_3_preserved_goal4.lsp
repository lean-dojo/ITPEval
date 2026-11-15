;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/index_of_not_in_subrange_Why3_ide_VCindex_of_not_in_subrange_loop_inv_3_preserved_goal4:
;; preservation of the index-of loop invariant when advancing past a
;; nonmatching pointer-array entry. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun ionisg4-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun ionisg4-address-base (address)
  (car address))

(defun ionisg4-address-offset (address)
  (cdr address))

(defun ionisg4-shift (address amount)
  (cons
   (ionisg4-address-base address)
   (+ (ionisg4-address-offset address) amount)))

;; These conservative symbols represent the universally arbitrary source
;; pointer function t, region operation, and imported l_index_of operation
;; specialized to that arbitrary pointer function.

(defstub ionisg4-t (address) t)
(defstub ionisg4-region (base) t)
(defstub ionisg4-l-index-of (item array down up) t)

(defun-sk ionisg4-function-types-p ()
  (forall (address base item array down up)
    (implies
     (and
      (ionisg4-address-p address)
      (integerp base)
      (ionisg4-address-p item)
      (ionisg4-address-p array)
      (integerp down)
      (integerp up))
     (and
      (ionisg4-address-p (ionisg4-t address))
      (integerp (ionisg4-region base))
      (integerp
       (ionisg4-l-index-of item array down up))))))

(defun ionisg4-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun-sk ionisg4-framed-p ()
  (forall (address)
    (implies
     (ionisg4-address-p address)
     (<=
      (ionisg4-region
       (ionisg4-address-base (ionisg4-t address)))
      0))))

;; These are exactly the three source axioms characterizing l_index_of for the
;; arbitrary pointer function t: exhausted interval, found item, and the
;; recursive step past a nonmatching item.

(defun-sk ionisg4-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and
      (ionisg4-address-p item)
      (ionisg4-address-p array)
      (integerp down)
      (integerp up))
     (and
      (implies
       (and
        (<= up down)
        (<= 0 up))
       (equal
        (ionisg4-l-index-of item array down up)
        up))
      (implies
       (and
        (equal
         (ionisg4-t (ionisg4-shift array down))
         item)
        (<= 0 down)
        (< down up))
       (equal
        (ionisg4-l-index-of item array down up)
        down))
      (implies
       (and
        (not
         (equal
          (ionisg4-t (ionisg4-shift array down))
          item))
        (<= 0 down)
        (< down up))
       (equal
        (ionisg4-l-index-of item array (+ 1 down) up)
        (ionisg4-l-index-of item array down up)))))))

(defun-sk ionisg4-no-item-in-range-p
    (item array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (< index upper)
      (<= lower index))
     (not
      (equal
       (ionisg4-t (ionisg4-shift array index))
       item)))))

(defun-sk ionisg4-index-value-stable-p
    (expected item array lower current upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (< index current)
      (<= lower index))
     (equal
      expected
      (ionisg4-l-index-of item array current upper)))))

(defun-sk
    ntp4vc-index-of-not-in-subrange-loop-inv-3-preserved-goal4-statement ()
  (forall
   (i2 a a1 i4 i i1 i3)
   (implies
    (and
     (ionisg4-function-types-p)
     (ionisg4-l-index-of-laws-p)
     (integerp i2)
     (ionisg4-address-p a)
     (ionisg4-address-p a1)
     (integerp i4)
     (integerp i)
     (integerp i1)
     (integerp i3))
    (let*
        ((x (+ 1 i2))
         (x1 (ionisg4-l-index-of a a1 i4 i)))
      (implies
       (and
        (not
         (equal
          (ionisg4-t (ionisg4-shift a1 i2))
          a))
        (<= 0 i)
        (<= i2 i1)
        (<= i4 i1)
        (< i2 i1)
        (<= i3 i2)
        (<= i4 i2)
        (<= i4 i3)
        (<= 0 i4)
        (<= (ionisg4-region (ionisg4-address-base a)) 0)
        (<= (ionisg4-region (ionisg4-address-base a1)) 0)
        (ionisg4-framed-p)
        (ionisg4-is-sint32-p i)
        (ionisg4-is-sint32-p i1)
        (ionisg4-is-sint32-p i2)
        (ionisg4-is-sint32-p i3)
        (ionisg4-is-sint32-p i4)
        (ionisg4-is-sint32-p x)
        (ionisg4-no-item-in-range-p a a1 i4 i1)
        (ionisg4-index-value-stable-p
         x1 a a1 i4 i2 i))
       (equal
        (ionisg4-l-index-of a a1 x i)
        x1))))))

(value-triple :itpeval-statement-checked)

:q
