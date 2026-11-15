;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/index_of_unexisting_item_Why3_ide_VCindex_of_unexisting_item_post_goal0:
;; correctness of the returned pointer-array upper index when no entry in the
;; searched interval equals the requested item. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun iui-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun iui-address-base (address)
  (car address))

(defun iui-address-offset (address)
  (cdr address))

(defun iui-shift (address amount)
  (cons
   (iui-address-base address)
   (+ (iui-address-offset address) amount)))

;; These conservative symbols represent the universally arbitrary source
;; pointer function t, region operation, and imported l_index_of operation
;; specialized to that arbitrary pointer function.

(defstub iui-t (address) t)
(defstub iui-region (base) t)
(defstub iui-l-index-of (item array down up) t)

(defun-sk iui-function-types-p ()
  (forall (address base item array down up)
    (implies
     (and
      (iui-address-p address)
      (integerp base)
      (iui-address-p item)
      (iui-address-p array)
      (integerp down)
      (integerp up))
     (and
      (iui-address-p (iui-t address))
      (integerp (iui-region base))
      (integerp
       (iui-l-index-of item array down up))))))

(defun iui-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun-sk iui-framed-p ()
  (forall (address)
    (implies
     (iui-address-p address)
     (<=
      (iui-region
       (iui-address-base (iui-t address)))
      0))))

;; These are exactly the three source axioms characterizing l_index_of for the
;; arbitrary pointer function t: exhausted interval, found item, and the
;; recursive step past a nonmatching item.

(defun-sk iui-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and
      (iui-address-p item)
      (iui-address-p array)
      (integerp down)
      (integerp up))
     (and
      (implies
       (and
        (<= up down)
        (<= 0 up))
       (equal
        (iui-l-index-of item array down up)
        up))
      (implies
       (and
        (equal
         (iui-t (iui-shift array down))
         item)
        (<= 0 down)
        (< down up))
       (equal
        (iui-l-index-of item array down up)
        down))
      (implies
       (and
        (not
         (equal
          (iui-t (iui-shift array down))
          item))
        (<= 0 down)
        (< down up))
       (equal
        (iui-l-index-of item array (+ 1 down) up)
        (iui-l-index-of item array down up)))))))

(defun-sk iui-no-item-in-range-p (item array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (< index upper)
      (<= lower index))
     (not
      (equal
       (iui-t (iui-shift array index))
       item)))))

(defun-sk ntp4vc-index-of-unexisting-item-post-goal0-statement ()
  (forall (i i1 a a1)
    (implies
     (and
      (iui-function-types-p)
      (iui-l-index-of-laws-p)
      (integerp i)
      (integerp i1)
      (iui-address-p a)
      (iui-address-p a1))
     (implies
      (and
       (<= 0 i)
       (<= 0 i1)
       (<= (iui-region (iui-address-base a)) 0)
       (<= (iui-region (iui-address-base a1)) 0)
       (iui-framed-p)
       (iui-is-sint32-p i)
       (iui-is-sint32-p i1)
       (iui-no-item-in-range-p a a1 i1 i))
      (equal
       (iui-l-index-of a a1 i1 i)
       i)))))

(value-triple :itpeval-statement-checked)

:q
