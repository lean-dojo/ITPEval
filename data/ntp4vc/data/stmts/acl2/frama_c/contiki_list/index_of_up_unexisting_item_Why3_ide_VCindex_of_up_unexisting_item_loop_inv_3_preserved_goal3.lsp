;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/index_of_up_unexisting_item_Why3_ide_VCindex_of_up_unexisting_item_loop_inv_3_preserved_goal3:
;; preservation of an index-of loop invariant when advancing through
;; pointer-array entries known not to equal the requested item. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun iouug3-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun iouug3-address-base (address)
  (car address))

(defun iouug3-address-offset (address)
  (cdr address))

(defun iouug3-shift (address amount)
  (cons
   (iouug3-address-base address)
   (+ (iouug3-address-offset address) amount)))

;; These conservative symbols represent the universally arbitrary source
;; pointer function t, region operation, and imported l_index_of operation
;; specialized to that arbitrary pointer function.

(defstub iouug3-t (address) t)
(defstub iouug3-region (base) t)
(defstub iouug3-l-index-of (item array down up) t)

(defun-sk iouug3-function-types-p ()
  (forall (address base item array down up)
    (implies
     (and
      (iouug3-address-p address)
      (integerp base)
      (iouug3-address-p item)
      (iouug3-address-p array)
      (integerp down)
      (integerp up))
     (and
      (iouug3-address-p (iouug3-t address))
      (integerp (iouug3-region base))
      (integerp
       (iouug3-l-index-of item array down up))))))

(defun iouug3-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun-sk iouug3-framed-p ()
  (forall (address)
    (implies
     (iouug3-address-p address)
     (<=
      (iouug3-region
       (iouug3-address-base (iouug3-t address)))
      0))))

;; These are exactly the three source axioms characterizing l_index_of for the
;; arbitrary pointer function t: exhausted interval, found item, and the
;; recursive step past a nonmatching item.

(defun-sk iouug3-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and
      (iouug3-address-p item)
      (iouug3-address-p array)
      (integerp down)
      (integerp up))
     (and
      (implies
       (and
        (<= up down)
        (<= 0 up))
       (equal
        (iouug3-l-index-of item array down up)
        up))
      (implies
       (and
        (equal
         (iouug3-t (iouug3-shift array down))
         item)
        (<= 0 down)
        (< down up))
       (equal
        (iouug3-l-index-of item array down up)
        down))
      (implies
       (and
        (not
         (equal
          (iouug3-t (iouug3-shift array down))
          item))
        (<= 0 down)
        (< down up))
       (equal
        (iouug3-l-index-of item array (+ 1 down) up)
        (iouug3-l-index-of item array down up)))))))

(defun-sk iouug3-no-item-in-range-p
    (item array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (< index upper)
      (<= lower index))
     (not
      (equal
       (iouug3-t (iouug3-shift array index))
       item)))))

(defun-sk iouug3-index-value-invariant-p
    (item array lower current upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (< index current)
      (<= lower index))
     (equal
      (iouug3-l-index-of item array current upper)
      upper))))

(defun-sk
    ntp4vc-index-of-up-unexisting-item-loop-inv-3-preserved-goal3-statement ()
  (forall
   (i1 a a1 i3 i i2)
   (implies
    (and
     (iouug3-function-types-p)
     (iouug3-l-index-of-laws-p)
     (integerp i1)
     (iouug3-address-p a)
     (iouug3-address-p a1)
     (integerp i3)
     (integerp i)
     (integerp i2))
    (let ((x (+ 1 i1)))
      (implies
       (and
        (equal
         (iouug3-l-index-of a a1 i3 i)
         i)
        (<= i1 i)
        (<= i3 i)
        (< i1 i)
        (<= i2 i1)
        (<= i3 i1)
        (<= i3 i2)
        (<= 0 i3)
        (<= (iouug3-region (iouug3-address-base a)) 0)
        (<= (iouug3-region (iouug3-address-base a1)) 0)
        (iouug3-framed-p)
        (iouug3-is-sint32-p i)
        (iouug3-is-sint32-p i1)
        (iouug3-is-sint32-p i2)
        (iouug3-is-sint32-p i3)
        (iouug3-is-sint32-p x)
        (iouug3-no-item-in-range-p a a1 i3 i1)
        (iouug3-index-value-invariant-p
         a a1 i3 i1 i))
       (equal
        (iouug3-l-index-of a a1 x i)
        i))))))

(value-triple :itpeval-statement-checked)

:q
