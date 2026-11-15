;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/index_of_Why3_ide_VCindex_of_post_part3_goal2:
;; correctness of the returned pointer-array upper index when no entry in the
;; searched interval equals the requested item. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun iof3-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun iof3-address-base (address)
  (car address))

(defun iof3-address-offset (address)
  (cdr address))

(defun iof3-shift (address amount)
  (cons
   (iof3-address-base address)
   (+ (iof3-address-offset address) amount)))

;; These conservative symbols represent the universally arbitrary source
;; pointer function t_1, integer function t, region and linked operations, and
;; the imported l_index_of operation specialized to t_1.

(defstub iof3-t1 (address) t)
(defstub iof3-t (index) t)
(defstub iof3-region (base) t)
(defstub iof3-linked-op () t)
(defstub iof3-l-index-of (item array down up) t)

(defun-sk iof3-function-types-p ()
  (forall (address index base item array down up)
    (implies
     (and
      (iof3-address-p address)
      (integerp index)
      (integerp base)
      (iof3-address-p item)
      (iof3-address-p array)
      (integerp down)
      (integerp up))
     (and
      (iof3-address-p (iof3-t1 address))
      (integerp (iof3-t index))
      (integerp (iof3-region base))
      (integerp
       (iof3-l-index-of item array down up))))))

(defun iof3-linked-p ()
  (if (iof3-linked-op) t nil))

(defun iof3-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun iof3-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (iof3-address-base address))
    (<= 0 (iof3-address-offset address))
    (<=
     (+ (iof3-address-offset address) length)
     (iof3-t (iof3-address-base address))))))

(defun-sk iof3-framed-p ()
  (forall (address)
    (implies
     (iof3-address-p address)
     (<=
      (iof3-region
       (iof3-address-base (iof3-t1 address)))
      0))))

;; These are exactly the three source axioms characterizing l_index_of for the
;; arbitrary pointer function t_1: exhausted interval, found item, and the
;; recursive step past a nonmatching item.

(defun-sk iof3-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and
      (iof3-address-p item)
      (iof3-address-p array)
      (integerp down)
      (integerp up))
     (and
      (implies
       (and
        (<= up down)
        (<= 0 up))
       (equal
        (iof3-l-index-of item array down up)
        up))
      (implies
       (and
        (equal (iof3-t1 (iof3-shift array down)) item)
        (<= 0 down)
        (< down up))
       (equal
        (iof3-l-index-of item array down up)
        down))
      (implies
       (and
        (not
         (equal (iof3-t1 (iof3-shift array down)) item))
        (<= 0 down)
        (< down up))
       (equal
        (iof3-l-index-of item array (+ 1 down) up)
        (iof3-l-index-of item array down up)))))))

(defun-sk iof3-no-item-p (item array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (< index upper)
      (<= lower index))
     (not
      (equal
       (iof3-t1 (iof3-shift array index))
       item)))))

(defun-sk
    ntp4vc-index-of-post-part3-goal2-statement ()
  (forall
   (i i1 i2 a a1)
   (implies
    (and
     (iof3-function-types-p)
     (iof3-l-index-of-laws-p)
     (integerp i)
     (integerp i1)
     (integerp i2)
     (iof3-address-p a)
     (iof3-address-p a1))
    (implies
     (and
      (<= 0 i)
      (<= i1 i)
      (<= i i1)
      (<= i2 i1)
      (<= 0 i2)
      (< i2 i)
      (<= (iof3-region (iof3-address-base a)) 0)
      (<= (iof3-region (iof3-address-base a1)) 0)
      (iof3-framed-p)
      (iof3-linked-p)
      (iof3-is-sint32-p i)
      (iof3-is-sint32-p i1)
      (iof3-is-sint32-p i2)
      (implies
       (<= i2 i)
       (iof3-valid-rw-p
        (iof3-shift a1 i2)
        (- i i2)))
      (iof3-no-item-p a a1 i2 i1))
     (equal
      (iof3-l-index-of a a1 i2 i1)
      i1)))))

(value-triple :itpeval-statement-checked)

:q
